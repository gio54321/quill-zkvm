use crate::{proof::circuit::Circuit, utils::virtual_polynomial::VirtualPolyExpr};
use ark_ff::PrimeField;

/// A target in the circuit: a specific cell in the witness matrix.
#[derive(Clone)]
pub struct TransitionCircuitTarget {
    pub col: usize,
}

impl TransitionCircuitTarget {
    /// Create a new TransitionCircuitTarget
    pub fn to_expr<F: PrimeField>(&self) -> VirtualPolyExpr<F> {
        VirtualPolyExpr::Input(self.col)
    }
}

#[derive(Clone)]
pub struct StateCell {
    pub current: TransitionCircuitTarget,
    pub next: TransitionCircuitTarget,
}

/// A special shape of circuit: a transition circuit that defines only the transition constraints
/// between consecutive rows of the witness.
#[derive(Clone)]
pub struct TransitionCircuit<F: PrimeField> {
    pub num_columns: usize,
    pub num_rows: usize,
    pub state_cells: Vec<StateCell>,
    pub initial_state_values: Vec<F>,
    pub recurring_constraints: Vec<VirtualPolyExpr<F>>,
    pub boundary_constraints: Vec<(usize, VirtualPolyExpr<F>)>,
}

impl<F: PrimeField> TransitionCircuit<F> {
    /// Create a new TransitionCircuit
    pub fn new(num_rows: usize) -> Self {
        Self {
            num_columns: 0,
            num_rows,
            recurring_constraints: Vec::new(),
            state_cells: Vec::new(),
            initial_state_values: Vec::new(),
            boundary_constraints: Vec::new(),
        }
    }

    pub fn allocate_witness_cell(&mut self) -> TransitionCircuitTarget {
        let index = self.num_columns;
        self.num_columns += 1;
        TransitionCircuitTarget { col: index }
    }

    /// Allocate a cell that is a "state", returns both the current state cella and the next state cell
    /// The circuit will enforce that the next state cell in row i equals the curr state cell in row i+1
    pub fn allocate_state_cell(&mut self) -> StateCell {
        let current_state = self.allocate_witness_cell();
        let next_state = self.allocate_witness_cell();
        let state_cell = StateCell {
            current: current_state.clone(),
            next: next_state.clone(),
        };
        self.state_cells.push(state_cell.clone());
        state_cell
    }

    /// Enforce a recurring constraint that must hold for every row
    pub fn enforce_constraint(&mut self, constraint: VirtualPolyExpr<F>) {
        self.recurring_constraints.push(constraint);
    }

    /// Enforce a boundary constraint that must hold at a specific row
    pub fn enforce_boundary_constraint(&mut self, row: usize, constraint: VirtualPolyExpr<F>) {
        self.boundary_constraints.push((row, constraint));
    }
}

impl<F: PrimeField> Circuit<F> for TransitionCircuit<F> {
    fn num_rows(&self) -> usize {
        self.num_rows
    }

    fn num_cols(&self) -> usize {
        self.num_columns.next_power_of_two()
    }

    fn num_preprocessed_columns(&self) -> usize {
        // we need to allocate one selector poly for each boundary constraint
        // NOTE: this could be reduced to log(n) selectors, probably, but the degree of the constraints would increase
        self.boundary_constraints.len()
    }

    fn preprocessed_values(&self) -> Vec<Vec<F>> {
        let mut preprocessed =
            vec![vec![F::zero(); self.num_rows()]; self.num_preprocessed_columns()];
        for (i, (row, _)) in self.boundary_constraints.iter().enumerate() {
            preprocessed[i][*row] = F::one();
        }
        preprocessed
    }

    fn zero_check_expressions(&self) -> Vec<VirtualPolyExpr<F>> {
        // the mapping is 0..num_cols() -> witness columns
        // num_cols()..num_cols()+num_preprocessed_columns() -> preprocessed columns
        // we already have the recurring constraints over the witness columns, so return them
        // as is
        let mut constraints = self.recurring_constraints.clone();

        // for boundary constraints, we need to multiply each constraint by the corresponding selector polynomial

        let padded_num_cols = self.num_cols();
        for (i, (_row, constraint)) in self.boundary_constraints.iter().enumerate() {
            constraints.push(VirtualPolyExpr::Mul(
                Box::new(VirtualPolyExpr::Input(i + padded_num_cols)), // selector poly
                Box::new(constraint.clone()),
            ));
        }
        constraints
    }

    fn permutation(&self) -> (Vec<F>, Vec<F>) {
        // Build the permutation mapping, we need to construct a permutation mapping for each state cell
        // for each row i in 0..num_rows-1, we map (current_state_cell, i) -> (next_state_cell, i+1)
        // and back (next_state_cell, i+1) -> (current_state_cell, i)

        let num_cells = self.num_rows() * self.num_cols();
        assert!(num_cells.is_power_of_two());
        let id_mapping = (0..num_cells)
            .map(|i| F::from(i as u64))
            .collect::<Vec<F>>();

        let mut permutation_mapping = id_mapping.clone();
        for state_cell in &self.state_cells {
            let current_index = state_cell.current.col;
            let next_index = state_cell.next.col;
            for row in 0..(self.num_rows() - 1) {
                let from = next_index * self.num_rows() + row;
                let to = current_index * self.num_rows() + (row + 1);
                permutation_mapping[from] = F::from(to as u64);
                permutation_mapping[to] = F::from(from as u64);
            }
        }

        // add 1 to each mapping to avoid zero values
        let id_mapping = id_mapping
            .iter()
            .map(|x| *x + F::one())
            .collect::<Vec<F>>();
        let permutation_mapping = permutation_mapping
            .iter()
            .map(|x| *x + F::one())
            .collect::<Vec<F>>();

        (id_mapping, permutation_mapping)
    }

    fn check_constraints(&self, witness: &Vec<Vec<F>>) -> Result<(), String> {
        // Check that the witness satisfies all the constraints
        for row in 0..self.num_rows() {
            // Recurring constraints
            let row_values = witness.iter().map(|col| col[row]).collect::<Vec<F>>();
            for constraint in &self.recurring_constraints {
                let eval = constraint.evaluate(&row_values);
                if eval != F::zero() {
                    return Err(
                    format!(
                        "Recurring constraint {} not satisfied at row {}: {:?} != 0\n row values: {:?}",
                        constraint,
                        row,
                        eval,
                        row_values
                    )
                );
                }
            }
        }

        // check boundary constraints
        for (row, constraint) in &self.boundary_constraints {
            let row_values = witness.iter().map(|col| col[*row]).collect::<Vec<F>>();
            let eval = constraint.evaluate(&row_values);
            if eval != F::zero() {
                return Err(
                    format!(
                        "Boundary constraint {} not satisfied at row {}: {:?} != 0\n row values: {:?}",
                        constraint,
                        row,
                        eval,
                        row_values
                    )
                );
            }
        }

        // check permutation constraints
        for state_cell in &self.state_cells {
            for row in 0..(self.num_rows() - 1) {
                let current_value = witness[state_cell.next.col][row];
                let next_value = witness[state_cell.current.col][row + 1];
                if current_value != next_value {
                    return Err(
                        format!(
                            "Permutation constraint not satisfied for state cell at row {}: current value {:?} != next value {:?}",
                            row,
                            current_value,
                            next_value
                        )
                    );
                }
            }
        }
        Ok(())
    }
}
