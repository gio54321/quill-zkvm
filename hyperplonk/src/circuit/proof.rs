use std::iter::zip;

use crate::{
    piops::{permutation_check::PermutationCheckProof, zerocheck::ZeroCheckProof},
    utils::virtual_polynomial::{
        VirtualPolyExpr, VirtualPolynomialInputRef, VirtualPolynomialStore,
    },
};
use ark_ff::PrimeField;
use quill_pcs::MultilinearPCS;
use quill_transcript::transcript::Transcript;

// A trait representing a general circuit
pub trait Circuit<F: PrimeField> {
    /// Number of rows in the circuit's trace
    /// Must be a power of two
    fn num_rows(&self) -> usize;

    /// Number of witness columns in the circuit's trace
    fn num_cols(&self) -> usize;

    /// Number of preprocessed columns (fixed by the circuit description)
    fn num_preprocessed_columns(&self) -> usize;

    /// Preprocessed values for the preprocessed columns.
    /// Must return a vector of length `num_preprocessed_columns()`,
    /// each containing a vector of length `num_rows()`.
    fn preprocessed_values(&self) -> Vec<Vec<F>>;

    /// Constraint expression that is enforced to be zero for every row, given
    /// the columns reference indices.
    /// All equations are checked to hold over each row of the trace.
    /// ASSUMES: the input allocation is as follows: input indices 0..num_cols()
    /// refer to the witness columns, while input indices
    /// num_cols()..num_cols()+num_preprocessed_columns() refer to the preprocessed columns.
    fn zero_check_expressions(&self) -> Vec<VirtualPolyExpr<F>>;

    /// Permutation mapping for the trace cells
    /// The canonical mapping is to represent a cell (row, col) as an index `col * num_rows + row`
    /// that is, the column index is in the most significant position, while the row index is in the least significant position.
    ///
    /// For example, a circuit with 4 rows and 3 columns would have the following canonical mapping:
    /// 0, 4, 8
    /// 1, 5, 9
    /// 2, 6, 10
    /// 3, 7, 11
    ///
    /// NOTE: preprocessed columns are not included in the permutation argument,
    /// only witness columns are considered.
    fn permutation(&self) -> Vec<usize>;
}

pub struct HyperPlonk<F: PrimeField, C: Circuit<F> + Clone, PCS: MultilinearPCS<F>> {
    pub vk: HyperPlonkVK<F, PCS, C>,
    pub id_poly: Vec<F>,
    pub permutation_poly: Vec<F>,
    pub circuit: C,
    pub _marker: std::marker::PhantomData<(F, PCS)>,
}

pub struct HyperPlonkProof<F: PrimeField, PCS: MultilinearPCS<F>> {
    // Proof elements would go here
    pub _marker: std::marker::PhantomData<(F, PCS)>,
}

#[derive(Clone)]
pub struct HyperPlonkVK<F: PrimeField, PCS: MultilinearPCS<F>, C: Circuit<F>> {
    pub padded_num_cols: usize,
    pub num_rows: usize,
    pub circuit: C,
    pub preprocessed_columns_commitments: Vec<PCS::Commitment>,
    pub id_commitment: PCS::Commitment,
    pub permutation_commitment: PCS::Commitment,
}

impl<F: PrimeField, C: Circuit<F> + Clone, PCS: MultilinearPCS<F>> HyperPlonk<F, C, PCS> {
    pub fn preprocess(circuit: C, pcs: &PCS) -> Self {
        assert!(
            circuit.num_rows().is_power_of_two(),
            "Number of rows must be a power of two"
        );
        let height = circuit.num_rows();

        // find the real trace width for witness columns
        let concrete_width = circuit.num_cols().next_power_of_two();

        let trace_num_vars = concrete_width + height;

        assert!(
            trace_num_vars.is_power_of_two(),
            "Total number of columns (witness + preprocessed) must be a power of two"
        );
        assert!(
            pcs.max_degree() == trace_num_vars,
            "PCS max degree must match the total number of columns"
        );

        let mut preprocessed_values = circuit.preprocessed_values();
        let preprocessed_commitments = preprocessed_values
            .iter_mut()
            .map(|col| {
                // pad each preprocessed column to the max poly degree
                col.extend(vec![F::zero(); trace_num_vars - col.len()]);
                // commit to the preprocessed column
                pcs.commit(col)
            })
            .collect::<Vec<_>>();

        // commit to the identity and permutation polynomials
        let mut id_evals = Vec::with_capacity(height * concrete_width);
        for col in 0..concrete_width {
            for row in 0..height {
                id_evals.push(F::from((col * height + row) as u64));
            }
        }

        let mut permutation_evals = Vec::with_capacity(height * concrete_width);
        let perm = circuit.permutation();
        for col in 0..concrete_width {
            for row in 0..height {
                if col < circuit.num_cols() {
                    let permuted_index = perm[col * height + row];
                    permutation_evals.push(F::from(permuted_index as u64));
                } else {
                    // padding columns follow the identity
                    permutation_evals.push(F::from((col * height + row) as u64));
                }
            }
        }

        let id_commitment = pcs.commit(&id_evals);
        let permutation_commitment = pcs.commit(&permutation_evals);

        let vk = HyperPlonkVK {
            padded_num_cols: concrete_width,
            num_rows: circuit.num_rows(),
            circuit: circuit.clone(),
            preprocessed_columns_commitments: preprocessed_commitments,
            id_commitment,
            permutation_commitment,
        };
        Self {
            vk,
            circuit,
            id_poly: id_evals,
            permutation_poly: permutation_evals,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn prove(&self, pcs: &PCS, witness: &Vec<Vec<F>>) -> HyperPlonkProof<F, PCS> {
        // construct the full padded witness
        assert_eq!(
            witness.len(),
            self.circuit.num_cols(),
            "Witness columns length mismatch"
        );
        for col in witness {
            assert_eq!(
                col.len(),
                self.circuit.num_rows(),
                "Witness column row length mismatch"
            );
        }

        let num_rows = self.circuit.num_rows();

        let mut padded_witness = witness.iter().flatten().cloned().collect::<Vec<F>>();
        let pad_cols = self.circuit.num_cols().next_power_of_two() - self.circuit.num_cols();
        let padding_length = pad_cols * self.circuit.num_rows();
        padded_witness.extend(vec![F::zero(); padding_length]);

        let log2_rows = num_rows.trailing_zeros() as usize;
        let log2_padded_cols =
            (self.circuit.num_cols().next_power_of_two()).trailing_zeros() as usize;

        let mut transcript = Transcript::new(b"hyperplonk_proof");

        let witness_commitment = pcs.commit(&padded_witness);
        transcript.append_serializable(&witness_commitment);

        // HACK: it is implicitly assumed that the allocated polys have
        // indices 0..num_cols() for witness columns
        // refactor this
        let mut poly_store: VirtualPolynomialStore<F> = VirtualPolynomialStore::new(log2_rows);
        for columns in witness {
            poly_store.allocate_polynomial(columns);
        }
        for preprocessed in self.circuit.preprocessed_values() {
            poly_store.allocate_polynomial(&preprocessed);
        }

        // batch together all constraints into a single zero-check expression
        let zero_check_exprs = self.circuit.zero_check_expressions();
        let alpha = transcript.draw_field_element::<F>();

        let alpha_powers = (0..zero_check_exprs.len())
            .map(|i| alpha.pow(&[i as u64]))
            .collect::<Vec<F>>();
        let mut zero_check_expr = VirtualPolyExpr::Const(F::zero());
        for (expr, alpha) in zip(zero_check_exprs, alpha_powers) {
            zero_check_expr = VirtualPolyExpr::Add(
                Box::new(zero_check_expr),
                Box::new(VirtualPolyExpr::Mul(
                    Box::new(VirtualPolyExpr::Const(alpha)),
                    Box::new(expr.clone()),
                )),
            );
        }
        let zero_check_virtual = poly_store.new_virtual_from_expr(zero_check_expr);

        let (zero_check_proof, zero_check_eval_claim) =
            ZeroCheckProof::prove(&mut poly_store, &zero_check_virtual, &mut transcript);

        // construct a new polynomial store for the permutation check
        // this check is done on the whole trace at once, without separating the columns
        let mut poly_store2 = VirtualPolynomialStore::new(log2_rows + log2_padded_cols);
        let witness_idx = poly_store2.allocate_polynomial(&padded_witness);
        let witness_virtual = poly_store2.new_virtual_from_input(&witness_idx);

        let permutation_check_proof = PermutationCheckProof::prove(
            &mut poly_store2,
            &witness_virtual,
            &witness_virtual,
            &self.id_poly,
            &self.permutation_poly,
            &mut transcript,
            pcs,
        );

        todo!()
    }
}
