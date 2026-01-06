use crate::utils::virtual_polynomial::VirtualPolyExpr;
use ark_ff::PrimeField;

/// Trait representing a general circuit that can be used to describe a relation to be proven
/// with HyperPlonk on a single trace.
pub trait Circuit<F: PrimeField> {
    /// Number of rows in the circuit's trace
    /// Must be a power of two
    fn num_rows(&self) -> usize;

    /// Number of witness columns in the circuit's trace
    /// Must be a power of two
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
    ///
    /// **ASSUMES**: the input allocation is as follows: input indices 0..num_cols()
    /// refer to the witness columns, while input indices
    /// num_cols()..num_cols()+num_preprocessed_columns() refer to the preprocessed columns.
    fn zero_check_expressions(&self) -> Vec<VirtualPolyExpr<F>>;

    /// Permutation mapping for the trace cells
    /// must return both the id mapping and the permutation mapping
    fn permutation(&self) -> (Vec<F>, Vec<F>);

    /// Check that the provided witness satisfies the circuit constraints.
    /// This is mainly intended for testing and sanity check purposes
    /// when generating the proof.
    fn check_constraints(&self, witness: &Vec<Vec<F>>) -> Result<(), String>;
}
