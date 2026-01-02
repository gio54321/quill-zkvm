use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use quill_transcript::transcript::Transcript;

pub mod ipa;
pub mod kzg;
pub mod mlpcs;

pub trait MultilinearPCSProof<F: PrimeField> {
    fn evaluation_point(&self) -> Vec<F>;
    fn claimed_evaluation(&self) -> F;
}

pub trait MultilinearPCS<F: PrimeField> {
    type CRS;
    type Commitment: Sized + Clone + CanonicalSerialize;
    type Proof: Sized + MultilinearPCSProof<F>;

    fn trusted_setup(degree: usize) -> Self::CRS;
    fn commit(&self, poly: &[F]) -> Self::Commitment;
    fn open(&self, poly: &[F], eval_point: &[F], transcript: &mut Transcript) -> Self::Proof;
    fn verify(
        &self,
        commitment: &Self::Commitment,
        proof: &Self::Proof,
        transcript: &mut Transcript,
    ) -> bool;
}
