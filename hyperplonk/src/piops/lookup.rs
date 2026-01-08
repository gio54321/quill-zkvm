use crate::piops::multiset_check::{LookupMode, MultisetEqualityProof};
use crate::utils::virtual_polynomial::{
    VirtualPolyExpr, VirtualPolynomialInputRef, VirtualPolynomialStore,
};
use ark_ff::{PrimeField, Zero};
use quill_pcs::EvaluationClaim;
use quill_pcs::MultilinearPCS;
use quill_transcript::transcript::Transcript;

pub struct LookupProof<F: PrimeField, PCS: MultilinearPCS<F>> {
    pub multiset_equality_proof: MultisetEqualityProof<F, PCS>,
}

impl<F: PrimeField, PCS: MultilinearPCS<F>> LookupProof<F, PCS> {
    pub fn prove(
        store: &mut VirtualPolynomialStore<F>,
        sources: &Vec<VirtualPolynomialInputRef>,
        dests: &Vec<VirtualPolynomialInputRef>,
        multiplicities: &VirtualPolynomialInputRef,
        transcript: &mut Transcript,
        pcs: &PCS,
    ) -> (Self, Vec<F>) {
        assert_eq!(
            sources.len(),
            dests.len(),
            "Source and destination columns must have the same length"
        );
        let n = sources.len();

        // draw value batching challenges
        let alphas = (0..n)
            .map(|_| transcript.draw_field_element::<F>())
            .collect::<Vec<F>>();

        // construct source_hat = sum_{i} alpha_i * source_cols[i]
        let mut source_hat_expr = VirtualPolyExpr::zero();
        for i in 0..n {
            source_hat_expr =
                source_hat_expr + (sources[i].to_expr() * VirtualPolyExpr::Const(alphas[i]));
        }

        let mut dest_hat_expr = VirtualPolyExpr::zero();
        for i in 0..n {
            dest_hat_expr =
                dest_hat_expr + (dests[i].to_expr() * VirtualPolyExpr::Const(alphas[i]));
        }

        let source_hat = store.new_virtual_from_expr(source_hat_expr);
        let dest_hat = store.new_virtual_from_expr(dest_hat_expr);
        let multiplicities_virtual = store.new_virtual_from_input(multiplicities);

        let (multiset_equality_proof, evaluation_point) = MultisetEqualityProof::prove(
            store,
            &source_hat,
            &dest_hat,
            transcript,
            pcs,
            LookupMode::Subset,
            Some(&multiplicities_virtual),
        );

        (
            Self {
                multiset_equality_proof,
            },
            evaluation_point,
        )
    }

    /// Assumes that the four evaluation claims have been verified separately
    pub fn verify(
        &self,
        transcript: &mut Transcript,
        pcs: &PCS,
        source_evals: Vec<EvaluationClaim<F>>,
        dest_evals: Vec<EvaluationClaim<F>>,
        multiplicities_eval: EvaluationClaim<F>,
    ) -> Result<(), String> {
        let n = source_evals.len();

        let alphas = (0..n)
            .map(|_| transcript.draw_field_element::<F>())
            .collect::<Vec<F>>();

        // recompute source_hat evaluation claim
        let mut source_hat_eval = EvaluationClaim {
            point: source_evals[0].point.clone(),
            evaluation: F::zero(),
        };
        for i in 0..n {
            source_hat_eval.evaluation += source_evals[i].evaluation * alphas[i];
        }

        // recompute dest_hat evaluation claim
        let mut dest_hat_eval = EvaluationClaim {
            point: dest_evals[0].point.clone(),
            evaluation: F::zero(),
        };
        for i in 0..n {
            dest_hat_eval.evaluation += dest_evals[i].evaluation * alphas[i];
        }

        self.multiset_equality_proof.verify(
            transcript,
            pcs,
            source_hat_eval,
            dest_hat_eval,
            LookupMode::Subset,
            Some(multiplicities_eval),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::Fr;
    use ark_poly::{DenseMultilinearExtension, Polynomial};
    use ark_std::test_rng;
    use ark_std::{One, Zero};
    use quill_pcs::kzg::KZG;
    use rand::Rng;

    #[test]
    fn test_bytes_lookup() {
        let mut rng = test_rng();
        let num_vars = 10;

        println!("KZG setup...");
        let pcs = KZG::<ark_bn254::Bn254>::trusted_setup(1 << num_vars, &mut rng);
        println!("KZG setup done.");

        // generate a random degree 2^num_vars polynomial
        let poly_degree = 1 << num_vars;
        let claimed_bytes_u8 = (0..poly_degree)
            .map(|_| rng.gen_range(0..256) as u8)
            .collect::<Vec<u8>>();

        let claimed_bytes = claimed_bytes_u8
            .iter()
            .map(|&b| Fr::from(b as u64))
            .collect::<Vec<Fr>>();

        let mut bytes_table = (0..256).map(|i| Fr::from(i as u64)).collect::<Vec<Fr>>();
        bytes_table.resize(poly_degree, Fr::zero());

        // compute multiplicities
        let mut multiplicities_table = vec![Fr::zero(); bytes_table.len()];
        for &b in claimed_bytes_u8.iter() {
            let b_usize: usize = b as usize;
            multiplicities_table[b_usize] += Fr::one();
        }

        println!("Creating virtual polynomial store...");

        let mut store = VirtualPolynomialStore::new(num_vars);
        let source = store.allocate_polynomial(&claimed_bytes);
        let dest = store.allocate_polynomial(&bytes_table);
        let multiplicities = store.allocate_polynomial(&multiplicities_table);

        let mut transcript = Transcript::new(b"permutation_test");

        println!("Proving multiset equality...");
        let (proof, evaluation_point) = LookupProof::prove(
            &mut store,
            &vec![source],
            &vec![dest],
            &multiplicities,
            &mut transcript,
            &pcs,
        );

        // -- Verifier --
        let mut verifier_transcript = Transcript::new(b"permutation_test");
        let source_eval_claim = EvaluationClaim {
            point: evaluation_point.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(num_vars, claimed_bytes)
                .evaluate(&evaluation_point),
        };

        let dest_eval_claim = EvaluationClaim {
            point: evaluation_point.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(num_vars, bytes_table)
                .evaluate(&evaluation_point),
        };

        let multiplicities_eval_claim = EvaluationClaim {
            point: evaluation_point.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(
                num_vars,
                multiplicities_table,
            )
            .evaluate(&evaluation_point),
        };

        println!("Verifying multiset equality proof...");
        let verify_result = proof.verify(
            &mut verifier_transcript,
            &pcs,
            vec![source_eval_claim],
            vec![dest_eval_claim],
            multiplicities_eval_claim,
        );

        assert!(
            verify_result.is_ok(),
            "Multiset equality proof verification failed: {:?}",
            verify_result.err()
        );
        println!("Multiset equality proof verified successfully.");
    }

    #[test]
    fn test_bytes_lookup_invalid() {
        let mut rng = test_rng();
        let num_vars = 10;

        println!("KZG setup...");
        let pcs = KZG::<ark_bn254::Bn254>::trusted_setup(1 << num_vars, &mut rng);
        println!("KZG setup done.");

        // generate a random degree 2^num_vars polynomial
        let poly_degree = 1 << num_vars;
        let claimed_bytes_u8 = (0..poly_degree)
            .map(|_| rng.gen_range(0..256) as u8)
            .collect::<Vec<u8>>();

        let mut claimed_bytes = claimed_bytes_u8
            .iter()
            .map(|&b| Fr::from(b as u64))
            .collect::<Vec<Fr>>();

        claimed_bytes[0] = Fr::from(256); // not a byte

        let mut bytes_table = (0..256).map(|i| Fr::from(i as u64)).collect::<Vec<Fr>>();
        bytes_table.resize(poly_degree, Fr::zero());

        // compute multiplicities
        let mut multiplicities_table = vec![Fr::zero(); bytes_table.len()];
        for &b in claimed_bytes_u8.iter() {
            let b_usize: usize = b as usize;
            multiplicities_table[b_usize] += Fr::one();
        }

        println!("Creating virtual polynomial store...");

        let mut store = VirtualPolynomialStore::new(num_vars);
        let source = store.allocate_polynomial(&claimed_bytes);
        let dest = store.allocate_polynomial(&bytes_table);
        let multiplicities = store.allocate_polynomial(&multiplicities_table);

        let mut transcript = Transcript::new(b"permutation_test");

        println!("Proving multiset equality...");
        let (proof, evaluation_point) = LookupProof::prove(
            &mut store,
            &vec![source],
            &vec![dest],
            &multiplicities,
            &mut transcript,
            &pcs,
        );

        // -- Verifier --
        let mut verifier_transcript = Transcript::new(b"permutation_test");
        let source_eval_claim = EvaluationClaim {
            point: evaluation_point.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(num_vars, claimed_bytes)
                .evaluate(&evaluation_point),
        };

        let dest_eval_claim = EvaluationClaim {
            point: evaluation_point.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(num_vars, bytes_table)
                .evaluate(&evaluation_point),
        };

        let multiplicities_eval_claim = EvaluationClaim {
            point: evaluation_point.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(
                num_vars,
                multiplicities_table,
            )
            .evaluate(&evaluation_point),
        };

        println!("Verifying multiset equality proof...");
        let verify_result = proof.verify(
            &mut verifier_transcript,
            &pcs,
            vec![source_eval_claim],
            vec![dest_eval_claim],
            multiplicities_eval_claim,
        );

        assert!(
            verify_result.is_err(),
            "Multiset equality proof verification should have failed"
        );
    }
}
