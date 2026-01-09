use crate::piops::set_inclusion::{
    SetInclusionEvaluationClaims, SetInclusionEvaluationPoints, SetInclusionProof,
};
use crate::utils::virtual_polynomial::{
    VirtualPolyExpr, VirtualPolynomialRef, VirtualPolynomialStore,
};
use ark_ff::PrimeField;
use quill_pcs::EvaluationClaim;
use quill_pcs::MultilinearPCS;
use quill_transcript::transcript::Transcript;

/// A lookup proof proves that all elements in the source columns, taken as a vector of tuples
/// appear somewhere in the target columns (taken as a vector of tuples as well)
pub struct LookupProof<F: PrimeField, PCS: MultilinearPCS<F>> {
    pub set_inclusion_proof: SetInclusionProof<F, PCS>,
}

pub type LookupEvaluationPoints<F> = SetInclusionEvaluationPoints<F>;
pub struct LookupEvaluationClaims<F: PrimeField> {
    pub source_claims: Vec<EvaluationClaim<F>>,
    pub dests_claims: Vec<EvaluationClaim<F>>,
    pub multiplicities_claim: EvaluationClaim<F>,
}

impl<F: PrimeField, PCS: MultilinearPCS<F>> LookupProof<F, PCS> {
    /// Returns the proof and the evaluation points for left and right columns
    /// with possibly different number of variables!
    pub fn prove(
        source_store: &mut VirtualPolynomialStore<F>,
        source_cols: &Vec<VirtualPolynomialRef>,
        dest_store: &mut VirtualPolynomialStore<F>,
        dest_cols: &Vec<VirtualPolynomialRef>,
        multiplicities: &VirtualPolynomialRef, // assumed to be in dest_store
        transcript: &mut Transcript,
        pcs: &PCS,
    ) -> (Self, LookupEvaluationPoints<F>) {
        assert_eq!(
            source_cols.len(),
            dest_cols.len(),
            "The number of source and destination columns must be equal"
        );

        let n = source_cols.len();
        transcript.append_serializable(&n);

        assert!(n > 0, "Lookup must be applied to at least one column");

        let alpha = transcript.draw_field_element::<F>();
        let alpha_powers: Vec<F> = (0..n).map(|i| alpha.pow(&[i as u64])).collect();

        let mut batched_left_expr = source_store.get_expr(&source_cols[0]);
        let mut batched_right_expr = dest_store.get_expr(&dest_cols[0]);
        for i in 1..n {
            batched_left_expr = batched_left_expr
                + (VirtualPolyExpr::Const(alpha_powers[i])
                    * source_store.get_expr(&source_cols[i]));
            batched_right_expr = batched_right_expr
                + (VirtualPolyExpr::Const(alpha_powers[i]) * dest_store.get_expr(&dest_cols[i]));
        }

        println!("batched_left: {:?}", batched_left_expr);
        println!("batched_right: {:?}", batched_right_expr);

        let batched_virtual_left = source_store.new_virtual_from_expr(batched_left_expr);
        let batched_virtual_right = dest_store.new_virtual_from_expr(batched_right_expr);

        let (proof, eval_points) = SetInclusionProof::prove(
            source_store,
            &batched_virtual_left,
            dest_store,
            &batched_virtual_right,
            multiplicities,
            transcript,
            pcs,
        );

        (
            LookupProof {
                set_inclusion_proof: proof,
            },
            eval_points,
        )
    }

    /// Assumes that all the evaluations claims in evals have been checked separately
    /// and are openings of the corret polynomials
    pub fn verify(
        &self,
        transcript: &mut Transcript,
        pcs: &PCS,
        evals: LookupEvaluationClaims<F>,
    ) -> Result<(), String> {
        let n = evals.source_claims.len();
        if evals.dests_claims.len() != n {
            return Err("Mismatched lookup evaluation vector lengths".to_string());
        }
        transcript.append_serializable(&n);
        let alpha = transcript.draw_field_element::<F>();
        let alpha_powers: Vec<F> = (0..n).map(|i| alpha.pow(&[i as u64])).collect();

        // check that all eval points on the left and right are equal,
        // before reducing to one batched claim
        let source_eval_point = evals.source_claims[0].point.clone();
        let dest_eval_point = evals.dests_claims[0].point.clone();

        for i in 0..n {
            if evals.source_claims[i].point != source_eval_point
                || evals.source_claims[i].point != source_eval_point
            {
                return Err("Lookup evaluation points for columns are inconsistent".to_string());
            }
        }

        // compute the new evaluations
        let source_batched_eval = (0..n)
            .map(|i| evals.source_claims[i].evaluation * alpha_powers[i])
            .fold(F::zero(), |acc, x| acc + x);
        let dest_batched_eval = (0..n)
            .map(|i| evals.dests_claims[i].evaluation * alpha_powers[i])
            .fold(F::zero(), |acc, x| acc + x);

        let source_eval_claim = EvaluationClaim {
            point: source_eval_point,
            evaluation: source_batched_eval,
        };
        let dest_eval_claim = EvaluationClaim {
            point: dest_eval_point,
            evaluation: dest_batched_eval,
        };

        self.set_inclusion_proof.verify(
            transcript,
            pcs,
            SetInclusionEvaluationClaims {
                h_left_sumcheck_claim: source_eval_claim,
                h_right_sumcheck_claim: dest_eval_claim,
                multiplicities_claim: evals.multiplicities_claim,
            },
        )?;

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

    fn get_xor_42_table() -> (Vec<Fr>, Vec<Fr>) {
        let mut xor_col1 = vec![Fr::zero(); 256];
        let mut xor_col2 = vec![Fr::zero(); 256];

        for i in 0..256 {
            xor_col1[i] = Fr::from(i as u64);
            xor_col2[i] = Fr::from((i as u64) ^ 42);
        }
        (xor_col1, xor_col2)
    }

    fn generate_claimed_columns<R: Rng>(
        num_vars: usize,
        rng: &mut R,
    ) -> (Vec<Fr>, Vec<Fr>, Vec<Fr>) {
        let poly_degree = 1 << num_vars;
        let claimed_bytes_u8 = (0..poly_degree)
            .map(|_| rng.gen_range(0..256) as u8)
            .collect::<Vec<u8>>();
        let claimed_outputs: Vec<_> = claimed_bytes_u8.iter().map(|x| x ^ 42).collect();

        let claimed_bytes = claimed_bytes_u8
            .iter()
            .map(|&b| Fr::from(b as u64))
            .collect::<Vec<Fr>>();
        let claimed_outputs = claimed_outputs
            .iter()
            .map(|&b| Fr::from(b as u64))
            .collect::<Vec<Fr>>();

        // compute multiplicities
        let mut multiplicities_table = vec![Fr::zero(); 256];

        // NOTE: exploits the fact that the first column are the bytes 0..255
        for &b in claimed_bytes_u8.iter() {
            let b_usize: usize = b as usize;
            multiplicities_table[b_usize] += Fr::one();
        }
        (claimed_bytes, claimed_outputs, multiplicities_table)
    }

    #[test]
    fn test_byte_xor_42() {
        let mut rng = test_rng();
        let num_vars_source = 10;
        let num_vars_table = 8;

        println!("KZG setup...");
        let pcs = KZG::<ark_bn254::Bn254>::trusted_setup(1 << num_vars_source, &mut rng);
        println!("KZG setup done.");

        let (xor_col1, xor_col2) = get_xor_42_table();
        let (claimed_bytes, claimed_outputs, multiplicities_table) =
            generate_claimed_columns(num_vars_source, &mut rng);

        println!("Creating virtual polynomial store...");

        let mut store1 = VirtualPolynomialStore::new(num_vars_source);
        let source1 = store1.allocate_polynomial(&claimed_bytes);
        let source2 = store1.allocate_polynomial(&claimed_outputs);
        let source1_virtual = store1.new_virtual_from_input(&source1);
        let source2_virtual = store1.new_virtual_from_input(&source2);

        let mut store2 = VirtualPolynomialStore::new(num_vars_table);
        let dest1 = store2.allocate_polynomial(&xor_col1);
        let dest2 = store2.allocate_polynomial(&xor_col2);
        let multiplicities = store2.allocate_polynomial(&multiplicities_table);
        let dest1_virtual = store2.new_virtual_from_input(&dest1);
        let dest2_virtual = store2.new_virtual_from_input(&dest2);
        let multiplicities_virtual = store2.new_virtual_from_input(&multiplicities);

        let mut transcript = Transcript::new(b"lookup_test");

        println!("Proving set inclusion...");
        let (proof, evaluations) = LookupProof::prove(
            &mut store1,
            &vec![source1_virtual, source2_virtual],
            &mut store2,
            &vec![dest1_virtual, dest2_virtual],
            &multiplicities_virtual,
            &mut transcript,
            &pcs,
        );

        // -- Verifier --
        let mut verifier_transcript = Transcript::new(b"lookup_test");
        let source1_eval_claim = EvaluationClaim {
            point: evaluations.left.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(
                num_vars_source,
                claimed_bytes,
            )
            .evaluate(&evaluations.left),
        };
        let source2_eval_claim = EvaluationClaim {
            point: evaluations.left.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(
                num_vars_source,
                claimed_outputs,
            )
            .evaluate(&evaluations.left),
        };

        let dest1_eval_claim = EvaluationClaim {
            point: evaluations.right.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(num_vars_table, xor_col1)
                .evaluate(&evaluations.right),
        };
        let dest2_eval_claim = EvaluationClaim {
            point: evaluations.right.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(num_vars_table, xor_col2)
                .evaluate(&evaluations.right),
        };

        let multiplicities_eval_claim = EvaluationClaim {
            point: evaluations.right.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(
                num_vars_table,
                multiplicities_table,
            )
            .evaluate(&evaluations.right),
        };

        println!("Verifying set inclusion proof...");
        let verify_result = proof.verify(
            &mut verifier_transcript,
            &pcs,
            LookupEvaluationClaims {
                source_claims: vec![source1_eval_claim, source2_eval_claim],
                dests_claims: vec![dest1_eval_claim, dest2_eval_claim],
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
    fn test_byte_xor_42_invalid() {
        let mut rng = test_rng();
        let num_vars_source = 10;
        let num_vars_table = 8;

        println!("KZG setup...");
        let pcs = KZG::<ark_bn254::Bn254>::trusted_setup(1 << num_vars_source, &mut rng);
        println!("KZG setup done.");

        let (xor_col1, xor_col2) = get_xor_42_table();
        let (claimed_bytes, mut claimed_outputs, multiplicities_table) =
            generate_claimed_columns(num_vars_source, &mut rng);

        claimed_outputs[0] += Fr::one();

        println!("Creating virtual polynomial store...");

        let mut store1 = VirtualPolynomialStore::new(num_vars_source);
        let source1 = store1.allocate_polynomial(&claimed_bytes);
        let source2 = store1.allocate_polynomial(&claimed_outputs);
        let source1_virtual = store1.new_virtual_from_input(&source1);
        let source2_virtual = store1.new_virtual_from_input(&source2);

        let mut store2 = VirtualPolynomialStore::new(num_vars_table);
        let dest1 = store2.allocate_polynomial(&xor_col1);
        let dest2 = store2.allocate_polynomial(&xor_col2);
        let multiplicities = store2.allocate_polynomial(&multiplicities_table);
        let dest1_virtual = store2.new_virtual_from_input(&dest1);
        let dest2_virtual = store2.new_virtual_from_input(&dest2);
        let multiplicities_virtual = store2.new_virtual_from_input(&multiplicities);

        let mut transcript = Transcript::new(b"lookup_test");

        println!("Proving set inclusion...");
        let (proof, evaluations) = LookupProof::prove(
            &mut store1,
            &vec![source1_virtual, source2_virtual],
            &mut store2,
            &vec![dest1_virtual, dest2_virtual],
            &multiplicities_virtual,
            &mut transcript,
            &pcs,
        );

        // -- Verifier --
        let mut verifier_transcript = Transcript::new(b"lookup_test");
        let source1_eval_claim = EvaluationClaim {
            point: evaluations.left.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(
                num_vars_source,
                claimed_bytes,
            )
            .evaluate(&evaluations.left),
        };
        let source2_eval_claim = EvaluationClaim {
            point: evaluations.left.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(
                num_vars_source,
                claimed_outputs,
            )
            .evaluate(&evaluations.left),
        };

        let dest1_eval_claim = EvaluationClaim {
            point: evaluations.right.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(num_vars_table, xor_col1)
                .evaluate(&evaluations.right),
        };
        let dest2_eval_claim = EvaluationClaim {
            point: evaluations.right.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(num_vars_table, xor_col2)
                .evaluate(&evaluations.right),
        };

        let multiplicities_eval_claim = EvaluationClaim {
            point: evaluations.right.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(
                num_vars_table,
                multiplicities_table,
            )
            .evaluate(&evaluations.right),
        };

        println!("Verifying set inclusion proof...");
        let verify_result = proof.verify(
            &mut verifier_transcript,
            &pcs,
            LookupEvaluationClaims {
                source_claims: vec![source1_eval_claim, source2_eval_claim],
                dests_claims: vec![dest1_eval_claim, dest2_eval_claim],
                multiplicities_claim: multiplicities_eval_claim,
            },
        );

        assert!(verify_result.is_err(), "Lookup proof should have failed");
        println!("Set inclusion proof verified successfully.");
    }
}
