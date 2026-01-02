use ark_ff::PrimeField;

pub mod sumcheck;
pub mod zerocheck;


pub struct EvaluationClaim<F: PrimeField> {
    pub point: Vec<F>,
    pub evaluation: F,
}