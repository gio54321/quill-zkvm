use ark_ec::pairing::Pairing;
use ark_ff::Field;
use ark_poly::univariate::DensePolynomial;
use ark_poly::DenseUVPolynomial;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_std::{One, Zero};
use quill_transcript::transcript::Transcript;

use crate::ipa::InnerProductProof;
use crate::kzg::{KZGOpeningProof, KZG};
use crate::{MultilinearPCS, MultilinearPCSProof};

/// A proof for the evaluation of a multilinear polynomial committed using KZG.
/// The polynomial is assumed to be committed using a univariate polynomial that
/// encodes in its coefficients the evaluations of the multilinear polynomial at all points over
/// the hypercube {0,1}^n, that is
///
/// > f(x) = P(bin(0)) + P(bin(1)) * x + P(bin(2)) * x^2 + ... + P(bin(2^n-1)) * x^(2^n-1)
///
/// To prove that `v` is the evaluation of the multilinear polynomial `P` at point `[r0, r1, ..., rn]`
/// the prover proves the following inner product claim:
///
/// > v = P(bin(0)) * eq(bin(0), r) + P(bin(1)) * eq(bin(1), r) + ... + P(bin(2^n-1)) * eq(bin(2^n-1), r)
///
/// where `eq(bin(i), r)` is the multilinear polynomial that evaluates to 1 at point `bin(i)` and to 0 at all other points
/// over the hypercube. This is exactly proving the inner product of the coefficients of the polynomial `f(x)` and the coefficients
/// of the polynomial
///
/// > P_r(x) = eq(bin(0), r) + eq(bin(1), r) * x + eq(bin(2), r) * x^2 + ... + eq(bin(2^n-1), r) * x^(2^n-1)
///
/// Evaluations of `P_r(x)` can be computed efficiently in O(n) time without constructing the full polynomial.
pub struct MLEvalProof<E: Pairing> {
    /// The evaluation point
    pub evaluation_point: Vec<E::ScalarField>,
    /// The claimed evaluation
    pub evaluation: E::ScalarField,
    /// Commitment to the S polynomial
    pub s_comm: E::G1,
    // Opening proofs
    pub poly_opening: KZGOpeningProof<E>,
    pub poly_opening_inv: KZGOpeningProof<E>,
    pub s_opening: KZGOpeningProof<E>,
    pub s_opening_inv: KZGOpeningProof<E>,
}

impl<E: Pairing> MLEvalProof<E> {
    /// Evaluate P_r at a given evaluation point using the formula
    ///
    /// > P_r(x) = \prod_{i=0}^{n-1} (r_i * x^{2^i} + 1 - r_i)
    ///
    /// this takes O(n) time
    fn eval_pr(r: &[E::ScalarField], x: E::ScalarField) -> E::ScalarField {
        let n = r.len();

        let mut result = E::ScalarField::one();
        let mut x_pow = x; // x^{2^i}  for i=0: x^1
        for i in 0..n {
            let term = r[i] * x_pow + (E::ScalarField::one() - r[i]);
            result *= term;
            x_pow *= x_pow; // x^{2^i}
        }
        result
    }

    /// Compute the polynomial P_r(x) given the evaluation point r as bits. This evaluates P_r(x) on n
    /// points and then interpolates to get the coefficients using IFFT.
    /// This takes O(n * 2^n) time (assuming that the field is suitable for FFTs)
    pub fn compute_pr(r: &[E::ScalarField]) -> DensePolynomial<E::ScalarField> {
        let n: usize = r.len();
        let domain_size = 1 << n;
        let domain = GeneralEvaluationDomain::<E::ScalarField>::new(domain_size).unwrap();
        let evals = domain
            .elements()
            .map(|x| Self::eval_pr(r, x))
            .collect::<Vec<_>>();
        let pr_poly_coeffs = domain.ifft(&evals);
        DensePolynomial::from_coefficients_slice(&pr_poly_coeffs)
    }

    /// Prove the evaluation of a multilinear polynomial
    ///
    /// ASSUMES: the commitment to the polynomial has been already incorporated into the transcript
    pub fn prove(
        poly: &[E::ScalarField],
        eval_point: &[E::ScalarField],
        kzg: &super::kzg::KZG<E>,
        transcript: &mut Transcript,
    ) -> Self {
        // the first thing to do is to evaluate the polynomial at the given point
        let pr = Self::compute_pr(eval_point);
        let mut evaluation = E::ScalarField::zero();
        for (a, b) in poly.iter().zip(pr.coeffs.iter()) {
            evaluation += *a * *b;
        }

        let s_poly = InnerProductProof::<E>::compute_s_polynomial(poly, &pr.coeffs);
        let s_commitment = kzg.commit(&s_poly.coeffs);

        // incorporate the evaluation point, claimed evaluation and the commitment to S into the transcript
        transcript.append_serializable(&eval_point);
        transcript.append_serializable(&evaluation);
        transcript.append_serializable(&s_commitment);

        // draw random point r
        let r = transcript.draw_field_element::<E::ScalarField>();
        // TODO: if r = 0 then we would need to redraw, but the probability is negligible
        let r_inv = r.inverse().unwrap();

        let poly_opening = kzg.open(&poly, r);
        let poly_opening_inv = kzg.open(&poly, r_inv);

        let s_opening = kzg.open(&s_poly.coeffs, r);
        let s_opening_inv = kzg.open(&s_poly.coeffs, r_inv);

        MLEvalProof {
            evaluation_point: eval_point.to_vec(),
            evaluation,
            s_comm: s_commitment,
            poly_opening,
            poly_opening_inv,
            s_opening,
            s_opening_inv,
        }
    }

    pub fn verify(
        &self,
        commitment: &E::G1,
        kzg: &super::kzg::KZG<E>,
        transcript: &mut Transcript,
    ) -> bool {
        // reconstruct the transcript state
        transcript.append_serializable(&self.evaluation_point);
        transcript.append_serializable(&self.evaluation);
        transcript.append_serializable(&self.s_comm);

        // draw random point r
        let r = transcript.draw_field_element::<E::ScalarField>();
        let r_inv = r.inverse().unwrap();

        // verify the two openings
        let poly_valid = kzg.verify(commitment, &self.poly_opening);
        let poly_inv_valid = kzg.verify(commitment, &self.poly_opening_inv);
        let s_valid = kzg.verify(&self.s_comm, &self.s_opening);
        let s_inv_valid = kzg.verify(&self.s_comm, &self.s_opening_inv);

        if !poly_valid || !poly_inv_valid || !s_valid || !s_inv_valid {
            return false;
        }

        // verify the inner product equation at the random point r
        let pr_r = Self::eval_pr(&self.evaluation_point, r);
        let pr_r_inv = Self::eval_pr(&self.evaluation_point, r_inv);

        let lhs = self.poly_opening.y * pr_r_inv + self.poly_opening_inv.y * pr_r;
        let rhs = r * self.s_opening.y
            + r_inv * self.s_opening_inv.y
            + E::ScalarField::from(2u64) * self.evaluation;

        lhs == rhs
    }
}

impl<E: Pairing> MultilinearPCSProof<E::ScalarField> for MLEvalProof<E> {
    fn evaluation_point(&self) -> Vec<E::ScalarField> {
        self.evaluation_point.clone()
    }

    fn claimed_evaluation(&self) -> E::ScalarField {
        self.evaluation
    }
}

impl<E: Pairing> MultilinearPCS<E::ScalarField> for KZG<E> {
    type CRS = KZG<E>;
    type Commitment = E::G1;
    type Proof = MLEvalProof<E>;

    fn trusted_setup(degree: usize) -> Self::CRS {
        let mut rng = rand::thread_rng();
        KZG::<E>::trusted_setup(degree, &mut rng)
    }
    fn commit(&self, poly: &[E::ScalarField]) -> Self::Commitment {
        self.commit(poly)
    }
    fn open(
        &self,
        poly: &[E::ScalarField],
        eval_point: &[E::ScalarField],
        transcript: &mut Transcript,
    ) -> Self::Proof {
        MLEvalProof::prove(poly, eval_point, self, transcript)
    }
    fn verify(
        &self,
        commitment: &Self::Commitment,
        proof: &Self::Proof,
        transcript: &mut Transcript,
    ) -> bool {
        proof.verify(commitment, self, transcript)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kzg;
    use ark_bn254::Bn254;
    use ark_bn254::Fr;
    use ark_ff::UniformRand;
    use ark_std::test_rng;

    #[test]
    fn test_pr_computation() {
        // r = 0, 0, 0
        let r0 = vec![Fr::zero(), Fr::zero(), Fr::zero()];
        let pr0_poly = MLEvalProof::<Bn254>::compute_pr(&r0);
        println!("P_r0(x) coeffs: {:?}", pr0_poly.coeffs);
        assert_eq!(pr0_poly.coeffs, vec![Fr::one()]); // P_r0(x) = 1

        // r = 1, 0, 1
        let r1 = vec![Fr::one(), Fr::zero(), Fr::one()];
        let pr1_poly = MLEvalProof::<Bn254>::compute_pr(&r1);
        println!("P_r1(x) coeffs: {:?}", pr1_poly.coeffs);
        assert_eq!(
            pr1_poly.coeffs,
            vec![
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::one()
            ]
        ); // P_r1(x) = x^5
    }

    #[test]
    fn test_mlpcs_proof() {
        let num_vars = 5;
        let mut rng = test_rng();

        // generate a random multilinear polynomial
        let poly_size = 1 << num_vars;
        let poly: Vec<Fr> = (0..poly_size).map(|_| Fr::rand(&mut rng)).collect();

        // setup KZG
        let kzg = kzg::KZG::<Bn254>::trusted_setup(poly_size, &mut rng);

        // --- PROVER ---
        let mut transcript = Transcript::new(b"MLPCS Test");

        // commit to the polynomial
        let commitment = kzg.commit(&poly);
        transcript.append_serializable(&commitment);

        //get a random evaluation point
        let eval_point: Vec<Fr> = (0..num_vars)
            .map(|_| transcript.draw_field_element::<Fr>())
            .collect();

        // prove
        let proof = MLEvalProof::<Bn254>::prove(&poly, &eval_point, &kzg, &mut transcript);

        // --- VERIFIER ---
        let mut transcript = Transcript::new(b"MLPCS Test");
        // reconstruct the commitment in the transcript

        transcript.append_serializable(&commitment);

        // get the evaluation point and claimed evaluation in the transcript
        let eval_point: Vec<Fr> = (0..num_vars)
            .map(|_| transcript.draw_field_element::<Fr>())
            .collect();

        assert!(
            eval_point == proof.evaluation_point,
            "Evaluation points do not match"
        );
        assert!(proof.verify(&commitment, &kzg, &mut transcript));

        // --- VERIFIER (wrong proof) ---

        let wrong_proof = MLEvalProof {
            evaluation_point: proof.evaluation_point.clone(),
            evaluation: proof.evaluation + Fr::one(),
            s_comm: proof.s_comm,
            poly_opening: proof.poly_opening,
            poly_opening_inv: proof.poly_opening_inv,
            s_opening: proof.s_opening,
            s_opening_inv: proof.s_opening_inv,
        };
        let mut transcript = Transcript::new(b"MLPCS Test");
        // reconstruct the commitment in the transcript

        transcript.append_serializable(&commitment);

        // get the evaluation point and claimed evaluation in the transcript
        let eval_point: Vec<Fr> = (0..num_vars)
            .map(|_| transcript.draw_field_element::<Fr>())
            .collect();

        assert!(
            eval_point == proof.evaluation_point,
            "Evaluation points do not match"
        );
        assert!(!wrong_proof.verify(&commitment, &kzg, &mut transcript));
    }
}
