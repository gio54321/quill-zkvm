use ark_ff::PrimeField;

pub mod multiset_check;
pub mod permutation_check;
pub mod sumcheck;
pub mod zerocheck;

#[derive(Debug, Clone)]
pub struct EvaluationClaim<F: PrimeField> {
    pub point: Vec<F>,
    pub evaluation: F,
}
