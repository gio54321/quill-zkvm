use ark_ff::PrimeField;
use quill_transcript::transcript::Transcript;


pub mod kzg;
pub mod ipa;
pub mod mlpcs;

pub trait MultilinearPCS<F: PrimeField> {
    type CRS;
    type Commitment;
    type Proof;


    fn trusted_setup(degree: usize) -> Self::CRS;
    fn commit(&self, crs: &Self::CRS, poly: &[F]) -> Self::Commitment;
    fn open(&self, crs: &Self::CRS, poly: &[F], eval_point: &[F], transcript: &mut Transcript) -> Self::Proof;
    fn verify(&self, crs: &Self::CRS, commitment: &Self::Commitment, proof: &Self::Proof, transcript: &mut Transcript) -> bool;
}