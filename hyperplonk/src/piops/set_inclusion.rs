use crate::piops::sumcheck::SumcheckProof;
use crate::utils::eq_eval::{eq_eval, fast_eq_eval_hypercube};
use crate::utils::virtual_polynomial::{
    VirtualPolyExpr, VirtualPolynomialRef, VirtualPolynomialStore,
};
use ark_ff::PrimeField;
use quill_pcs::EvaluationClaim;
use quill_pcs::{MultilinearPCS, MultilinearPCSProof};
use quill_transcript::transcript::Transcript;

/// A set inclusion proof that supports different table sizes.
/// Proves that all values in h_left are included in h_right, with multiplicities given by m(x).
///
/// The verifier samples a random evaluation point `eval_point`, and the prover commits to the
/// log-derivative polynomials:
///
/// > log_deriv_left(x) = 1 / (eval_point + h_left(x))
/// >
/// > log_deriv_right(x) = m(x) / (eval_point + h_right(x))
///
/// Then we need to enforce over the hypercube that the denominators are correct:
///
/// > denom_left(x) * (eval_point + h_left(x)) - 1 = 0         for x in B_left
/// >
/// > (denom_right(x) * (eval_point + h_right(x)) - m(x)) = 0     for x in B_right
///
/// moreover, prove that
///
/// > \sum_{x in B_left} denom_left(x) = v1
/// >
/// > \sum_{x in B_right} denom_right(x) = v2
///
/// the verifier will check that v1 = v2. Notice that B_left and B_right can be different.
///
/// We enforce the first relation using a zero-check, and we batch the
/// two left sumchecks together, and the two right sumchecks together
/// given
/// - a random evaluation point for the zero check `z1` and `z2`
/// - random folding challenges `alpha` and `beta` for left and right
///
/// The prover proves the following two identities using two sumcheck proofs:
///
/// > \sum_{x in B_left}
/// >    [denom_left(x) * (eval_point + h_left(x) - 1)] * eq(x, z1) +
/// >    alpha * denom_left(x)
/// >    = alpha * v1
/// >
/// > \sum_{x in B_right}
/// >    [denom_right(x) * (eval_point + h_right(x) - m(x))] * eq(x, z2) +
/// >    beta * denom_right(x)
/// >    = beta * v2
pub struct SetInclusionProof<F: PrimeField, PCS: MultilinearPCS<F>> {
    pub denom_left_commitment: PCS::Commitment,
    pub denom_right_commitment: PCS::Commitment,

    pub sumcheck_proof_left: SumcheckProof<F>,
    pub sumcheck_proof_right: SumcheckProof<F>,

    pub opening_proof_denom_left: PCS::Proof,
    pub opening_proof_denom_right: PCS::Proof,
}

pub struct SetInclusionEvaluationPoints<F: PrimeField> {
    pub left_sumcheck_point: Vec<F>,
    pub right_sumcheck_point: Vec<F>,
}

pub struct SetInclusionEvaluationClaims<F: PrimeField> {
    pub h_left_sumcheck_claim: EvaluationClaim<F>,
    pub h_right_sumcheck_claim: EvaluationClaim<F>,
    pub multiplicities_claim: EvaluationClaim<F>,
}

impl<F: PrimeField, PCS: MultilinearPCS<F>> SetInclusionProof<F, PCS> {
    /// Returns the proof and the evaluation points for left and right h
    /// with possibly different number of variables!
    pub fn prove(
        store_left: &mut VirtualPolynomialStore<F>,
        h_left: &VirtualPolynomialRef,
        store_right: &mut VirtualPolynomialStore<F>,
        h_right: &VirtualPolynomialRef,
        multiplicities: &VirtualPolynomialRef, // assumed to be in store_right
        transcript: &mut Transcript,
        pcs: &PCS,
    ) -> (Self, SetInclusionEvaluationPoints<F>) {
        let num_vars_left = store_left.num_vars();
        let num_vars_right = store_right.num_vars();

        // use Logup to prove set inclusion via two sumchecks
        let logup_eval_point = transcript.draw_field_element::<F>();

        // compute the evaluations of 1 / (eval_point + h_left(x)) and 1 / (eval_point + h_right(x))
        let log_derivative_left_evals = (0..(1 << num_vars_left))
            .map(|i| {
                let g_evals = store_left
                    .polynomials
                    .iter()
                    .map(|poly| poly.evaluations[i])
                    .collect::<Vec<F>>();
                let h_left_eval = store_left.evaluate_point(&g_evals, h_left);
                (logup_eval_point + h_left_eval).inverse().unwrap()
            })
            .collect::<Vec<F>>();

        let mut log_derivative_right_evals = (0..(1 << num_vars_right))
            .map(|i| {
                let g_evals = store_right
                    .polynomials
                    .iter()
                    .map(|poly| poly.evaluations[i])
                    .collect::<Vec<F>>();
                let h_right_eval = store_right.evaluate_point(&g_evals, h_right);
                (logup_eval_point + h_right_eval).inverse().unwrap()
            })
            .collect::<Vec<F>>();

        // in subset mode, we need to multiply the right log derivative by the multiplicities
        let multiplicities_evals = (0..(1 << num_vars_right))
            .map(|i| {
                let g_evals = store_right
                    .polynomials
                    .iter()
                    .map(|poly| poly.evaluations[i])
                    .collect::<Vec<F>>();
                store_right.evaluate_point(&g_evals, multiplicities)
            })
            .collect::<Vec<F>>();

        for i in 0..log_derivative_right_evals.len() {
            log_derivative_right_evals[i] *= multiplicities_evals[i];
        }

        // commit to the polynomials
        let commitment_left = pcs.commit(&log_derivative_left_evals);
        let commitment_right = pcs.commit(&log_derivative_right_evals);
        transcript.append_serializable(&commitment_left);
        transcript.append_serializable(&commitment_right);

        // get challenges for left sumcheck
        let z1 = (0..num_vars_left)
            .map(|_| transcript.draw_field_element::<F>())
            .collect::<Vec<_>>();
        let alpha = transcript.draw_field_element::<F>();

        // add the committed polynomials to the store
        let denom_left_index = store_left.allocate_polynomial(&log_derivative_left_evals);
        let denom_right_index = store_right.allocate_polynomial(&log_derivative_right_evals);

        let m_expr = store_right.virtual_polys[multiplicities.index].clone();
        let h_left_expr = store_left.virtual_polys[h_left.index].clone();
        let h_right_expr = store_right.virtual_polys[h_right.index].clone();

        let eq_evals = fast_eq_eval_hypercube(num_vars_left, z1.as_slice());
        let eq_poly_index = store_left.allocate_polynomial(&eq_evals);

        let mut sumcheck_virtual_left_expr = denom_left_index.to_expr()
            * (VirtualPolyExpr::Const(logup_eval_point) + h_left_expr)
            - VirtualPolyExpr::Const(F::one());
        sumcheck_virtual_left_expr = sumcheck_virtual_left_expr * eq_poly_index.to_expr()
            + denom_left_index.to_expr() * VirtualPolyExpr::Const(alpha);

        let sumcheck_virtual_left = store_left.new_virtual_from_expr(sumcheck_virtual_left_expr);

        // compute claimed sum = denom_left_sum over B_left * alpha
        let sumcheck_claimed_sum_left = (0..1 << num_vars_left)
            .map(|i| log_derivative_left_evals[i])
            .fold(F::zero(), |acc, x| acc + x)
            * alpha;

        let (sumcheck_proof_left, sumcheck_eval_claim_left) = SumcheckProof::prove(
            num_vars_left,
            store_left,
            &sumcheck_virtual_left,
            sumcheck_claimed_sum_left,
            transcript,
        );

        // get challenges for right sumcheck
        let z2 = (0..num_vars_right)
            .map(|_| transcript.draw_field_element::<F>())
            .collect::<Vec<_>>();
        let beta = transcript.draw_field_element::<F>();

        let eq_evals = fast_eq_eval_hypercube(num_vars_right, z2.as_slice());
        let eq_poly_index = store_right.allocate_polynomial(&eq_evals);
        let mut sumcheck_virtual_right_expr = denom_right_index.to_expr()
            * (VirtualPolyExpr::Const(logup_eval_point) + h_right_expr)
            - m_expr;
        sumcheck_virtual_right_expr = sumcheck_virtual_right_expr * eq_poly_index.to_expr()
            + denom_right_index.to_expr() * VirtualPolyExpr::Const(beta);

        let sumcheck_virtual_right = store_right.new_virtual_from_expr(sumcheck_virtual_right_expr);

        // compute claimed sum = denom_right_sum over B_right * beta
        let sumcheck_claimed_sum_right = (0..1 << num_vars_right)
            .map(|i| log_derivative_right_evals[i])
            .fold(F::zero(), |acc, x| acc + x)
            * beta;

        let (sumcheck_proof_right, sumcheck_eval_claim_right) = SumcheckProof::prove(
            num_vars_right,
            store_right,
            &sumcheck_virtual_right,
            sumcheck_claimed_sum_right,
            transcript,
        );

        let opening_proof_denom_left = pcs.open(
            &log_derivative_left_evals,
            &sumcheck_eval_claim_left.point,
            transcript,
        );

        let opening_proof_denom_right = pcs.open(
            &log_derivative_right_evals,
            &sumcheck_eval_claim_right.point,
            transcript,
        );

        let proof = Self {
            denom_left_commitment: commitment_left,
            denom_right_commitment: commitment_right,
            sumcheck_proof_left,
            sumcheck_proof_right,
            opening_proof_denom_left,
            opening_proof_denom_right,
        };

        let points = SetInclusionEvaluationPoints {
            left_sumcheck_point: sumcheck_eval_claim_left.point,
            right_sumcheck_point: sumcheck_eval_claim_right.point,
        };

        (proof, points)
    }

    /// Assumes that all the evaluations claims in evals have been checked separately
    pub fn verify(
        &self,
        transcript: &mut Transcript,
        pcs: &PCS,
        evals: SetInclusionEvaluationClaims<F>,
    ) -> Result<(), String> {
        let num_vars_left = evals.h_left_sumcheck_claim.point.len();
        let num_vars_right = evals.h_right_sumcheck_claim.point.len();

        // replay the prover's transcript to get the same challenges
        let logup_eval_point = transcript.draw_field_element::<F>();

        transcript.append_serializable(&self.denom_left_commitment);
        transcript.append_serializable(&self.denom_right_commitment);

        // get challenges for left sumcheck
        let z1 = (0..num_vars_left)
            .map(|_| transcript.draw_field_element::<F>())
            .collect::<Vec<_>>();
        let alpha = transcript.draw_field_element::<F>();

        // verify left sumcheck
        let denom_left_claim = self.sumcheck_proof_left.verify(transcript)?;

        // extract the claimed sum v1 from the final polynomial evaluation
        // The sumcheck proves: sum over B_left of [zerocheck_term * eq(x, z1) + alpha * denom_left(x)] = alpha * v1
        // where v1 = sum over B_left of denom_left(x)
        // At the evaluation point, we can extract v1 by working backwards from the sumcheck evaluation

        // get challenges for right sumcheck
        let z2 = (0..num_vars_right)
            .map(|_| transcript.draw_field_element::<F>())
            .collect::<Vec<_>>();
        let beta = transcript.draw_field_element::<F>();

        // verify right sumcheck
        let denom_right_claim = self.sumcheck_proof_right.verify(transcript)?;

        // verify the PCS opening proofs
        if !pcs.verify(
            &self.denom_left_commitment,
            &self.opening_proof_denom_left,
            transcript,
        ) {
            return Err("Left denominator opening proof failed".to_string());
        }

        if !pcs.verify(
            &self.denom_right_commitment,
            &self.opening_proof_denom_right,
            transcript,
        ) {
            return Err("Right denominator opening proof failed".to_string());
        }

        // Extract evaluation from the proof
        let denom_left_eval = self.opening_proof_denom_left.evaluation();
        let denom_right_eval = self.opening_proof_denom_right.evaluation();

        // Check that the sumcheck evaluation points match the PCS opening points
        if denom_left_claim.point != self.opening_proof_denom_left.point() {
            return Err("Left sumcheck point does not match PCS opening point".to_string());
        }

        if evals.h_left_sumcheck_claim.point != denom_left_claim.point
            || evals.h_right_sumcheck_claim.point != denom_right_claim.point
            || evals.multiplicities_claim.point != denom_right_claim.point
        {
            return Err("Mismatched evaluation points for set inclusion".to_string());
        }

        if denom_right_claim.point != self.opening_proof_denom_right.point() {
            return Err("Right sumcheck point does not match PCS opening point".to_string());
        }

        // Reconstruct the left sumcheck evaluation
        let eq_z1_eval = eq_eval(&denom_left_claim.point, &z1);
        let h_left_eval = evals.h_left_sumcheck_claim.evaluation;

        let left_zerocheck_term = denom_left_eval * (logup_eval_point + h_left_eval) - F::one();
        let left_sumcheck_eval = left_zerocheck_term * eq_z1_eval + alpha * denom_left_eval;

        if left_sumcheck_eval != denom_left_claim.evaluation {
            return Err("Left sumcheck evaluation mismatch".to_string());
        }

        // Reconstruct the right sumcheck evaluation
        let eq_z2_eval = eq_eval(&denom_right_claim.point, &z2);
        let h_right_eval = evals.h_right_sumcheck_claim.evaluation;
        let m_eval = evals.multiplicities_claim.evaluation;

        let right_zerocheck_term = denom_right_eval * (logup_eval_point + h_right_eval) - m_eval;
        let right_sumcheck_eval = right_zerocheck_term * eq_z2_eval + beta * denom_right_eval;

        if right_sumcheck_eval != denom_right_claim.evaluation {
            return Err("Right sumcheck evaluation mismatch".to_string());
        }

        // Extract v1 and v2 from the sumcheck evaluations and check they are equal
        // From the sumcheck: alpha * v1 = sumcheck_claimed_sum_left
        // v1 = sumcheck_claimed_sum_left / alpha
        let v1 = self.sumcheck_proof_left.claimed_sum / alpha;
        let v2 = self.sumcheck_proof_right.claimed_sum / beta;

        if v1 != v2 {
            return Err("Log-derivative sums do not match".to_string());
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::Fr;
    use ark_poly::{DenseMultilinearExtension, Polynomial};
    use ark_std::test_rng;
    use ark_std::One;
    use ark_std::Zero;
    use quill_pcs::kzg::KZG;
    use rand::Rng;

    #[test]
    fn test_bytes_lookup_inclusion() {
        let mut rng = test_rng();
        let num_vars_source = 10;
        let num_vars_table = 8; // 256 elements

        println!("KZG setup...");
        let pcs = KZG::<ark_bn254::Bn254>::trusted_setup(1 << num_vars_source, &mut rng);
        println!("KZG setup done.");

        // generate a random degree 2^num_vars polynomial
        let poly_degree = 1 << num_vars_source;
        let claimed_bytes_u8 = (0..poly_degree)
            .map(|_| rng.gen_range(0..256) as u8)
            .collect::<Vec<u8>>();

        let claimed_bytes = claimed_bytes_u8
            .iter()
            .map(|&b| Fr::from(b as u64))
            .collect::<Vec<Fr>>();

        let bytes_table = (0..(1 << num_vars_table))
            .map(|i| Fr::from(i as u64))
            .collect::<Vec<Fr>>();

        // compute multiplicities
        let mut multiplicities_table = vec![Fr::zero(); bytes_table.len()];
        for &b in claimed_bytes_u8.iter() {
            let b_usize: usize = b as usize;
            multiplicities_table[b_usize] += Fr::one();
        }

        println!("Creating virtual polynomial store...");

        let mut store1 = VirtualPolynomialStore::new(num_vars_source);
        let source = store1.allocate_polynomial(&claimed_bytes);
        let source_virtual = store1.new_virtual_from_input(&source);

        let mut store2 = VirtualPolynomialStore::new(num_vars_table);
        let dest = store2.allocate_polynomial(&bytes_table);
        let multiplicities = store2.allocate_polynomial(&multiplicities_table);
        let dest_virtual = store2.new_virtual_from_input(&dest);
        let multiplicities_virtual = store2.new_virtual_from_input(&multiplicities);

        let mut transcript = Transcript::new(b"lookup_test");

        println!("Proving set inclusion...");
        let (proof, evaluations) = SetInclusionProof::prove(
            &mut store1,
            &source_virtual,
            &mut store2,
            &dest_virtual,
            &multiplicities_virtual,
            &mut transcript,
            &pcs,
        );

        // -- Verifier --
        let mut verifier_transcript = Transcript::new(b"lookup_test");
        let source_eval_claim = EvaluationClaim {
            point: evaluations.left_sumcheck_point.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(
                num_vars_source,
                claimed_bytes,
            )
            .evaluate(&evaluations.left_sumcheck_point),
        };

        let dest_eval_claim = EvaluationClaim {
            point: evaluations.right_sumcheck_point.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(
                num_vars_table,
                bytes_table,
            )
            .evaluate(&evaluations.right_sumcheck_point),
        };

        let multiplicities_eval_claim = EvaluationClaim {
            point: evaluations.right_sumcheck_point.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(
                num_vars_table,
                multiplicities_table,
            )
            .evaluate(&evaluations.right_sumcheck_point),
        };

        println!("Verifying set inclusion proof...");
        let verify_result = proof.verify(
            &mut verifier_transcript,
            &pcs,
            SetInclusionEvaluationClaims {
                h_left_sumcheck_claim: source_eval_claim,
                h_right_sumcheck_claim: dest_eval_claim,
                multiplicities_claim: multiplicities_eval_claim,
            },
        );

        assert!(
            verify_result.is_ok(),
            "Set inclusion proof verification failed: {:?}",
            verify_result.err()
        );
        println!("Set inclusion proof verified successfully.");
    }

    #[test]
    fn test_bytes_lookup_inclusion_invalid() {
        let mut rng = test_rng();
        let num_vars_source = 10;
        let num_vars_table = 8; // 256 elements

        println!("KZG setup...");
        let pcs = KZG::<ark_bn254::Bn254>::trusted_setup(1 << num_vars_source, &mut rng);
        println!("KZG setup done.");

        // generate a random degree 2^num_vars polynomial
        let poly_degree = 1 << num_vars_source;
        let claimed_bytes_u8 = (0..poly_degree)
            .map(|_| rng.gen_range(0..256) as u8)
            .collect::<Vec<u8>>();

        let mut claimed_bytes = claimed_bytes_u8
            .iter()
            .map(|&b| Fr::from(b as u64))
            .collect::<Vec<Fr>>();

        // Introduce an invalid element not in the table
        claimed_bytes[0] = Fr::from(255u64 + 1u64); // 256, not in table

        let bytes_table = (0..(1 << num_vars_table))
            .map(|i| Fr::from(i as u64))
            .collect::<Vec<Fr>>();

        // compute multiplicities
        let mut multiplicities_table = vec![Fr::zero(); bytes_table.len()];
        for &b in claimed_bytes_u8.iter() {
            let b_usize: usize = b as usize;
            multiplicities_table[b_usize] += Fr::one();
        }

        println!("Creating virtual polynomial store...");

        let mut store1 = VirtualPolynomialStore::new(num_vars_source);
        let source = store1.allocate_polynomial(&claimed_bytes);
        let source_virtual = store1.new_virtual_from_input(&source);

        let mut store2 = VirtualPolynomialStore::new(num_vars_table);
        let dest = store2.allocate_polynomial(&bytes_table);
        let multiplicities = store2.allocate_polynomial(&multiplicities_table);
        let dest_virtual = store2.new_virtual_from_input(&dest);
        let multiplicities_virtual = store2.new_virtual_from_input(&multiplicities);

        let mut transcript = Transcript::new(b"lookup_test");

        println!("Proving Set inclusion...");
        let (proof, evaluations) = SetInclusionProof::prove(
            &mut store1,
            &source_virtual,
            &mut store2,
            &dest_virtual,
            &multiplicities_virtual,
            &mut transcript,
            &pcs,
        );

        // -- Verifier --
        let mut verifier_transcript = Transcript::new(b"lookup_test");
        let source_eval_claim = EvaluationClaim {
            point: evaluations.left_sumcheck_point.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(
                num_vars_source,
                claimed_bytes,
            )
            .evaluate(&evaluations.left_sumcheck_point),
        };

        let dest_eval_claim = EvaluationClaim {
            point: evaluations.right_sumcheck_point.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(
                num_vars_table,
                bytes_table,
            )
            .evaluate(&evaluations.right_sumcheck_point),
        };

        let multiplicities_eval_claim = EvaluationClaim {
            point: evaluations.right_sumcheck_point.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(
                num_vars_table,
                multiplicities_table,
            )
            .evaluate(&evaluations.right_sumcheck_point),
        };

        println!("Verifying Set inclusion proof...");
        let verify_result = proof.verify(
            &mut verifier_transcript,
            &pcs,
            SetInclusionEvaluationClaims {
                h_left_sumcheck_claim: source_eval_claim,
                h_right_sumcheck_claim: dest_eval_claim,
                multiplicities_claim: multiplicities_eval_claim,
            },
        );

        assert!(
            verify_result.is_err(),
            "Set inclusion proof verification should have failed but succeeded"
        );
        println!("Set inclusion proof verified successfully.");
    }
}
