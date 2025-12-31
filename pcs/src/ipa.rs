use ark_ec::pairing::Pairing;
use ark_ff::Field;
use ark_std::{Zero};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{DenseUVPolynomial};
use quill_transcript::transcript::Transcript;

use crate::kzg::KZGOpeningProof;

/// A proof for the inner product of two polynomials committed using KZG.
/// The technique is inspired by Mercury (https://eprint.iacr.org/2025/385.pdf) and earlier papers.
/// 
/// Suppose we have two polynomials `f(x)` and `g(x)`, both of degree `d`. Then notice that the constant term
/// of the polynomial
/// 
/// > h(x) = f(x) * g(1/x)
/// 
/// is exactly the inner product of the coefficients of `f` and `g`.
/// 
/// To prove that `v` is the inner product of the coefficients of `f` and `g`, the prover decomposes a slightly modified
/// `h(x)` as
/// 
/// > h(x) = f(x) * g(1/x) + f(1/x) * g(x) = x * S(x) + 1/x * S(1/x) + 2*v
/// 
/// for some polynomials `S(x)`.
/// 
/// The prover sends commitments to `S(x)`, then the verifier samples a random challenge `r` and checks that
/// 
/// > f(r) * g(1/r) + f(1/r) * g(r) = r * S(r) + 1/r * S(1/r) + 2*v
/// 
/// using suitable KZG opening proofs.
pub struct InnerProductProof<E: Pairing> {
    /// The result of the inner product
    pub inner_product: E::ScalarField,
    /// Commitment to the S polynomial
    pub s_comm: E::G1,

    // Opening proofs
    pub f_opening : KZGOpeningProof<E>,
    pub f_opening_inv : KZGOpeningProof<E>,
    pub g_opening : KZGOpeningProof<E>,
    pub g_opening_inv : KZGOpeningProof<E>,
    pub s_opening : KZGOpeningProof<E>,
    pub s_opening_inv : KZGOpeningProof<E>,
}

impl<E: Pairing> InnerProductProof<E> {
    /// Prove the inner product of two polynomials
    /// 
    /// ASSUMES: the commitments to the polynomials have been already incorporated into the transcript
    pub fn prove(poly1 : &[E::ScalarField], poly2: &[E::ScalarField], kzg: &super::kzg::KZG<E>, transcript: &mut Transcript) -> Self {
        // the first thing to do is to find the inner product
        let mut inner_product = E::ScalarField::zero();
        for (a, b) in poly1.iter().zip(poly2.iter()) {
            inner_product += *a * *b;
        }

        // compute the S polynomial and its commitment
        let s_poly = Self::compute_s_polynomial(poly1, poly2);
        let s_commitment = kzg.commit(&s_poly.coeffs);

        // incorporate the inner product and the commitment to S into the transcript
        transcript.append_serializable(&inner_product);
        transcript.append_serializable(&s_commitment);

        // draw random point r
        let r = transcript.draw_field_element::<E::ScalarField>();

        // TODO: if r = 0 then we would need to redraw, but the probability is negligible
        let r_inv = r.inverse().unwrap();

        // compute a bunch of openings
        // TODO: batch these 6 openings into 3 for efficiency
        let f_opening = kzg.open(&poly1, r);
        let f_opening_inv = kzg.open(&poly1, r_inv);
        let g_opening = kzg.open(&poly2, r);
        let g_opening_inv = kzg.open(&poly2, r_inv);
        let s_opening = kzg.open(&s_poly.coeffs, r);
        let s_opening_inv = kzg.open(&s_poly.coeffs, r_inv);

        assert!(f_opening.y * g_opening_inv.y + f_opening_inv.y * g_opening.y ==
            r * s_opening.y + r_inv * s_opening_inv.y + E::ScalarField::from(2u64) * inner_product,
            "Inner product verification equation failed"
        );

        return InnerProductProof {
            inner_product,
            s_comm: s_commitment,
            f_opening,
            f_opening_inv,
            g_opening,
            g_opening_inv,
            s_opening,
            s_opening_inv
        }

    }

    /// To compute the polynomial S(x) we need to compute `h(x) = f(x) * g(1/x) + f(1/x) * g(x)`
    /// from the MERCURY paper: let's multiply f(x) * g(1/x) + f(1/x) * g(x) by x^d
    /// what we get is a polynomial of degree at most 2d, but the coefficients are nicer:
    /// (f0 + f1*x + f2*x^2 + ... + fd*x^d) * (gd + g{d-1}*x + ... + g0*x^d) +
    /// (fd + f{d-1}*x + ... + f0*x^d) * (g0 + g1*x + ... + gd*x^d)e S(x) polynomial we want satisfies:
    /// h(x) = x^d (x * S(x) + 1/x * S(1/x) + 2*inner_product)
    /// therefore, h(x) is of a very special structure:
    /// h(x).coeffs = [s{d-1}, s{d-2}, ...,s1, s0, 2*inner_product, s0, s1, ..., s{d-2}, s{d-1}]
    pub fn compute_s_polynomial(poly1 : &[E::ScalarField], poly2: &[E::ScalarField]) -> DensePolynomial<E::ScalarField> {
        let poly1 = DensePolynomial::from_coefficients_slice(poly1);
        let poly2 = DensePolynomial::from_coefficients_slice(poly2);
        let poly1_rev = DensePolynomial::from_coefficients_slice(&poly1.coeffs.iter().rev().cloned().collect::<Vec<_>>());
        let poly2_rev = DensePolynomial::from_coefficients_slice(&poly2.coeffs.iter().rev().cloned().collect::<Vec<_>>());

        //TODO: use FFTs here for efficiency, now we are doing naive multiplication which is O(n^2)
        let h_poly = &(&poly1 * &poly2_rev) + &(&poly1_rev * &poly2);

        let h_coeffs = &h_poly.coeffs;
        let s_coeffs = &h_coeffs[(h_coeffs.len() / 2 + 1)..];

        DensePolynomial::from_coefficients_slice(s_coeffs)
    }


    /// Verify the inner product proof
    pub fn verify(&self, comm1: &E::G1, comm2: &E::G1, kzg: &super::kzg::KZG<E>, transcript: &mut Transcript) -> bool {
        let InnerProductProof {
            inner_product,
            s_comm,
            f_opening,
            f_opening_inv,
            g_opening,
            g_opening_inv,
            s_opening,
            s_opening_inv
        } = self;

        // verify the openings
        let f1_valid = kzg.verify(comm1, f_opening);
        let f2_valid = kzg.verify(comm1, f_opening_inv);
        let g1_valid = kzg.verify(comm2, g_opening);
        let g2_valid = kzg.verify(comm2, g_opening_inv);
        let s1_valid = kzg.verify(s_comm, s_opening);
        let s2_valid = kzg.verify(s_comm, s_opening_inv);

        if !(f1_valid && f2_valid && g1_valid && g2_valid && s1_valid && s2_valid) {
            return false;
        }

        // recompute the challenge r
        transcript.append_serializable(inner_product);
        transcript.append_serializable(s_comm);

        let r = transcript.draw_field_element::<E::ScalarField>();
        let r_inv = r.inverse().unwrap();

        // check the main verification equation
        f_opening.y * g_opening_inv.y + f_opening_inv.y * g_opening.y ==
            r * s_opening.y + r_inv * s_opening_inv.y + E::ScalarField::from(2u64) * (*inner_product)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::Bn254;
    use ark_bn254::Fr;
    use ark_std::test_rng;
    use crate::kzg;
    use ark_std::One;

    #[test]
    fn test_inner_product_proof() {
        let poly1 = vec![Fr::from(1u64), Fr::from(2u64), Fr::from(3u64)];
        let poly2 = vec![Fr::from(4u64), Fr::from(5u64), Fr::from(6u64)];

        let kzg = kzg::KZG::<Bn254>::trusted_setup(4, &mut test_rng());

        // --- PROVER ---
        let mut transcript = Transcript::new(b"inner_product_test");
        let comm1 = kzg.commit(&poly1);
        let comm2 = kzg.commit(&poly2);

        transcript.append_serializable(&comm1);
        transcript.append_serializable(&comm2);

        let proof = InnerProductProof::<Bn254>::prove(&poly1, &poly2, &kzg, &mut transcript);
        assert_eq!(proof.inner_product, Fr::from(32u64)); // 1*4 + 2*5 + 3*6 = 32

        // --- VERIFIER ---
        let mut verifier_transcript = Transcript::new(b"inner_product_test");
        verifier_transcript.append_serializable(&comm1);
        verifier_transcript.append_serializable(&comm2);
        let is_valid = proof.verify(&comm1, &comm2, &kzg, &mut verifier_transcript);
        assert!(is_valid, "Inner product proof verification failed");

        let wrong_proof = InnerProductProof {
            inner_product: proof.inner_product + Fr::one(),
            s_comm: proof.s_comm,
            f_opening: proof.f_opening,
            f_opening_inv: proof.f_opening_inv,
            g_opening: proof.g_opening,
            g_opening_inv: proof.g_opening_inv,
            s_opening: proof.s_opening,
            s_opening_inv: proof.s_opening_inv,
        };

        let is_valid = wrong_proof.verify(&comm1, &comm2, &kzg, &mut verifier_transcript);
        assert!(!is_valid, "Inner product proof verification should have failed but didn't");
    }
}