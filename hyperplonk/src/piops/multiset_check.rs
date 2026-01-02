use crate::piops::{sumcheck::SumcheckProof, EvaluationClaim};
use crate::utils::eq_eval::{eq_eval, fast_eq_eval_hypercube};
use crate::utils::virtual_polynomial::{
    VirtualPolyExpr, VirtualPolynomialRef, VirtualPolynomialStore,
};
use ark_ff::PrimeField;
use quill_pcs::{MultilinearPCS, MultilinearPCSProof};
use quill_transcript::transcript::Transcript;

pub struct MultisetEqualityProof<F: PrimeField, PCS: MultilinearPCS<F>> {
    pub denom_left_commitment: PCS::Commitment,
    pub denom_right_commitment: PCS::Commitment,
    pub sumcheck_proof: SumcheckProof<F>,
    pub opening_proof_denom_left: PCS::Proof,
    pub opening_proof_denom_right: PCS::Proof,
}

impl<F: PrimeField, PCS: MultilinearPCS<F>> MultisetEqualityProof<F, PCS> {
    /// Returns the proof and the evaluation point for left and right h
    pub fn prove(
        store: &mut VirtualPolynomialStore<F>,
        h_left: &VirtualPolynomialRef,
        h_right: &VirtualPolynomialRef,
        transcript: &mut Transcript,
        pcs: &PCS,
    ) -> (Self, Vec<F>) {
        let num_vars = store.num_vars();

        // use Logup to prove multiset equality via two sumchecks
        let logup_eval_point = transcript.draw_field_element::<F>();

        // compute the evaluations of 1 / (eval_point + h_left(x)) and 1 / (eval_point + h_right(x))
        let log_derivative_left_evals = (0..(1 << num_vars))
            .map(|i| {
                let g_evals = store
                    .polynomials
                    .iter()
                    .map(|poly| poly.evaluations[i])
                    .collect::<Vec<F>>();
                let h_left_eval = store.evaluate_point(&g_evals, h_left);
                (logup_eval_point + h_left_eval).inverse().unwrap()
            })
            .collect::<Vec<F>>();

        let log_derivative_right_evals = (0..(1 << num_vars))
            .map(|i| {
                let g_evals = store
                    .polynomials
                    .iter()
                    .map(|poly| poly.evaluations[i])
                    .collect::<Vec<F>>();
                let h_right_eval = store.evaluate_point(&g_evals, h_right);
                (logup_eval_point + h_right_eval).inverse().unwrap()
            })
            .collect::<Vec<F>>();

        // commit to the polynomials
        let commitment_left = pcs.commit(&log_derivative_left_evals);
        let commitment_right = pcs.commit(&log_derivative_right_evals);
        transcript.append_serializable(&commitment_left);
        transcript.append_serializable(&commitment_right);

        // draw two batching challenge for the zero check and sumcheck
        let lambda = transcript.draw_field_element::<F>();
        let alpha = transcript.draw_field_element::<F>();

        // add the committed polynomials to the store
        let denom_left_index = store.allocate_polynomial(&log_derivative_left_evals);
        let denom_right_index = store.allocate_polynomial(&log_derivative_right_evals);

        // enforce over the hypercube that
        // denom_left(x) * (eval_point + h_left(x)) - 1 +
        // lambda * (denom_right(x) * (eval_point + h_right(x)) - 1) = 0
        //
        // Moreover, we need to prove that the sum of the two log derivatives is zero
        // we do this batching the two sumchecks into a single sumcheck
        //
        // \sum_{x in B_n} :
        // [denom_left(x) * (eval_point + h_left(x)) - 1 +
        // lambda * (denom_right(x) * (eval_point + h_right(x)) - 1)] * eq(x, z) * alpha
        // + denom_left(x) - denom_right(x) = 0
        // TODO: (1) need a better interface to do this
        // TODO: (2) we should be able to do it using the standard zero-check interface, but right now
        // we cannot
        let zerocheck_expr = denom_left_index.to_expr::<F>()
            * (VirtualPolyExpr::Const(logup_eval_point)
                + store.virtual_polys[h_left.index].clone())
            - VirtualPolyExpr::Const(F::one())
            + VirtualPolyExpr::Const(lambda)
                * (denom_right_index.to_expr::<F>()
                    * (VirtualPolyExpr::Const(logup_eval_point)
                        + store.virtual_polys[h_right.index].clone())
                    - VirtualPolyExpr::Const(F::one()));

        // random point for the zero check
        let zerocheck_random_point = (0..num_vars)
            .map(|_| transcript.draw_field_element::<F>())
            .collect::<Vec<F>>();

        // get evaluations of eq(x, random_point) over {0,1}^n
        let eq_evals = fast_eq_eval_hypercube(num_vars, zerocheck_random_point.as_slice());
        let eq_poly_index = store.allocate_polynomial(&eq_evals);
        // h_hat = zerocheck_expr * eq_poly
        let h_hat = store.new_virtual_from_expr(zerocheck_expr);
        store.mul_in_place(&h_hat, &eq_poly_index);

        // batch this sumcheck with the sumcheck that proves that the sum of the two log derivatives is zero
        store.mul_const_in_place(&h_hat, alpha);
        store.add_in_place(&h_hat, &denom_left_index);
        store.sub_in_place(&h_hat, &denom_right_index);

        // at this point
        // h_hat = zerocheck_expr * eq_poly * alpha + (denom_left - denom_right)
        // the sum should be zero
        let (sumcheck_proof, sumcheck_evaluation_claim) =
            SumcheckProof::prove(num_vars, store, &h_hat, F::zero(), transcript);

        let evaluation_point = sumcheck_evaluation_claim.point;

        let opening_proof_denom_left =
            pcs.open(&log_derivative_left_evals, &evaluation_point, transcript);
        let opening_proof_denom_right =
            pcs.open(&log_derivative_right_evals, &evaluation_point, transcript);

        (
            Self {
                denom_left_commitment: commitment_left,
                denom_right_commitment: commitment_right,
                sumcheck_proof,
                opening_proof_denom_left,
                opening_proof_denom_right,
            },
            evaluation_point,
        )
    }

    /// Assumes that the left and right evaluation claims have been verified separately
    pub fn verify(
        &self,
        transcript: &mut Transcript,
        pcs: &PCS,
        left_h_eval: EvaluationClaim<F>,
        right_h_eval: EvaluationClaim<F>,
    ) -> Result<(), String> {
        // recompute eval_point
        let logup_eval_point = transcript.draw_field_element::<F>();

        // recompute commitments
        transcript.append_serializable(&self.denom_left_commitment);
        transcript.append_serializable(&self.denom_right_commitment);

        // recompute challenges
        let lambda = transcript.draw_field_element::<F>();
        let alpha = transcript.draw_field_element::<F>();

        let zerocheck_random_point = (0..left_h_eval.point.len())
            .map(|_| transcript.draw_field_element::<F>())
            .collect::<Vec<F>>();

        if self.sumcheck_proof.claimed_sum != F::zero() {
            return Err("Multiset equality sumcheck claimed sum is not zero".to_string());
        }

        // verify the sumcheck
        let sumcheck_evaluation_claim = self.sumcheck_proof.verify(transcript)?;

        // verify the openings
        let left_proof_valid = pcs.verify(
            &self.denom_left_commitment,
            &self.opening_proof_denom_left,
            transcript,
        );

        let right_proof_valid = pcs.verify(
            &self.denom_right_commitment,
            &self.opening_proof_denom_right,
            transcript,
        );

        if !left_proof_valid || !right_proof_valid {
            return Err("Multiset equality opening proof verification failed".to_string());
        }

        // check that the points are consistent with the reduced sumcheck evaluation claim
        let claimed_point_left = self.opening_proof_denom_left.evaluation_point();
        let claimed_point_right = self.opening_proof_denom_right.evaluation_point();
        if claimed_point_left != sumcheck_evaluation_claim.point
            || claimed_point_right != sumcheck_evaluation_claim.point
        {
            return Err(
                "Multiset equality opening proof evaluation point does not match sumcheck"
                    .to_string(),
            );
        }

        let left_h_eval_point = left_h_eval.point;
        let right_h_eval_point = right_h_eval.point;
        if left_h_eval_point != sumcheck_evaluation_claim.point
            || right_h_eval_point != sumcheck_evaluation_claim.point
        {
            return Err("Multiset equality h evaluation point does not match sumcheck".to_string());
        }

        // check the equation at the evaluation point
        let denom_left_eval = self.opening_proof_denom_left.claimed_evaluation();
        let denom_right_eval = self.opening_proof_denom_right.claimed_evaluation();
        let left_h_eval_value = left_h_eval.evaluation;
        let right_h_eval_value = right_h_eval.evaluation;

        let zerocheck_eval = denom_left_eval * (logup_eval_point + left_h_eval_value) - F::one()
            + lambda * (denom_right_eval * (logup_eval_point + right_h_eval_value) - F::one());

        let eq_eval = eq_eval(&zerocheck_random_point, &left_h_eval_point);
        let final_eval = zerocheck_eval * eq_eval * alpha + denom_left_eval - denom_right_eval;

        if final_eval != sumcheck_evaluation_claim.evaluation {
            return Err("Multiset equality final evaluation does not match sumcheck".to_string());
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::Fr;
    use ark_ff::UniformRand;
    use ark_poly::{DenseMultilinearExtension, Polynomial};
    use ark_std::rand::prelude::SliceRandom;
    use ark_std::test_rng;
    use ark_std::One;
    use quill_pcs::kzg::KZG;

    #[test]
    fn test_multiset_equality_proof() {
        let mut rng = test_rng();
        let num_vars = 7;

        println!("KZG setup...");
        let pcs = KZG::<ark_bn254::Bn254>::trusted_setup(1 << num_vars, &mut rng);
        println!("KZG setup done.");

        // generate a random degree 2^num_vars polynomial
        let poly_degree = 1 << num_vars;
        let poly_coeffs = (0..poly_degree)
            .map(|_| Fr::rand(&mut rng))
            .collect::<Vec<Fr>>();
        let permuted_coeffs = {
            let mut coeffs = poly_coeffs.clone();
            coeffs.shuffle(&mut rng);
            coeffs
        };

        println!("Creating virtual polynomial store...");

        let mut store = VirtualPolynomialStore::new(num_vars);
        let h_left_index = store.allocate_polynomial(&poly_coeffs);
        let h_right_index = store.allocate_polynomial(&permuted_coeffs);

        let h_left_virtual = store.new_virtual_from_input(&h_left_index);
        let h_right_virtual = store.new_virtual_from_input(&h_right_index);

        let mut transcript = Transcript::new(b"multiset_equality_test");

        println!("Proving multiset equality...");
        let (proof, evaluation_point) = MultisetEqualityProof::prove(
            &mut store,
            &h_left_virtual,
            &h_right_virtual,
            &mut transcript,
            &pcs,
        );

        // -- Verifier --
        let mut verifier_transcript = Transcript::new(b"multiset_equality_test");
        let left_evaluation_claim = EvaluationClaim {
            point: evaluation_point.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(num_vars, poly_coeffs)
                .evaluate(&evaluation_point),
        };

        let right_evaluation_claim = EvaluationClaim {
            point: evaluation_point.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(num_vars, permuted_coeffs)
                .evaluate(&evaluation_point),
        };

        println!("Verifying multiset equality proof...");
        let verify_result = proof.verify(
            &mut verifier_transcript,
            &pcs,
            left_evaluation_claim,
            right_evaluation_claim,
        );

        assert!(
            verify_result.is_ok(),
            "Multiset equality proof verification failed: {:?}",
            verify_result.err()
        );
        println!("Multiset equality proof verified successfully.");
    }

    #[test]
    fn test_multiset_equality_proof_invalid() {
        let mut rng = test_rng();
        let num_vars = 7;

        println!("KZG setup...");
        let pcs = KZG::<ark_bn254::Bn254>::trusted_setup(1 << num_vars, &mut rng);
        println!("KZG setup done.");

        // generate a random degree 2^num_vars polynomial
        let poly_degree = 1 << num_vars;
        let poly_coeffs = (0..poly_degree)
            .map(|_| Fr::rand(&mut rng))
            .collect::<Vec<Fr>>();
        let mut permuted_coeffs = {
            let mut coeffs = poly_coeffs.clone();
            coeffs.shuffle(&mut rng);
            coeffs
        };

        permuted_coeffs[0] += Fr::one(); // make the two polynomials different as multisets

        println!("Creating virtual polynomial store...");

        let mut store = VirtualPolynomialStore::new(num_vars);
        let h_left_index = store.allocate_polynomial(&poly_coeffs);
        let h_right_index = store.allocate_polynomial(&permuted_coeffs);

        let h_left_virtual = store.new_virtual_from_input(&h_left_index);
        let h_right_virtual = store.new_virtual_from_input(&h_right_index);

        let mut transcript = Transcript::new(b"multiset_equality_test");

        println!("Proving multiset equality...");
        let (proof, evaluation_point) = MultisetEqualityProof::prove(
            &mut store,
            &h_left_virtual,
            &h_right_virtual,
            &mut transcript,
            &pcs,
        );

        // -- Verifier --
        let mut verifier_transcript = Transcript::new(b"multiset_equality_test");
        let left_evaluation_claim = EvaluationClaim {
            point: evaluation_point.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(num_vars, poly_coeffs)
                .evaluate(&evaluation_point),
        };

        let right_evaluation_claim = EvaluationClaim {
            point: evaluation_point.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(num_vars, permuted_coeffs)
                .evaluate(&evaluation_point),
        };

        println!("Verifying multiset equality proof...");
        let verify_result = proof.verify(
            &mut verifier_transcript,
            &pcs,
            left_evaluation_claim,
            right_evaluation_claim,
        );

        assert!(
            verify_result.is_err(),
            "Multiset equality proof verification should have failed"
        );
    }
}
