use crate::piops::multiset_check::MultisetEqualityProof;
use crate::piops::EvaluationClaim;
use crate::utils::virtual_polynomial::{VirtualPolynomialRef, VirtualPolynomialStore};
use ark_ff::PrimeField;
use quill_pcs::MultilinearPCS;
use quill_transcript::transcript::Transcript;

pub struct PermutationCheckProof<F: PrimeField, PCS: MultilinearPCS<F>> {
    pub multiset_equality_proof: MultisetEqualityProof<F, PCS>,
}

impl<F: PrimeField, PCS: MultilinearPCS<F>> PermutationCheckProof<F, PCS> {
    pub fn prove(
        store: &mut VirtualPolynomialStore<F>,
        h_left: &VirtualPolynomialRef,
        h_right: &VirtualPolynomialRef,
        permutation_indices: &Vec<F>,
        transcript: &mut Transcript,
        pcs: &PCS,
    ) -> (Self, Vec<F>) {
        let num_vars = store.num_vars();

        // compute the id and permutation polynomials
        let id_poly_evals = (0..1 << num_vars).map(|i| F::from(i)).collect::<Vec<_>>();

        assert_eq!(permutation_indices.len(), 1 << num_vars);

        let id_ref = store.allocate_polynomial(&id_poly_evals);
        let perm_ref = store.allocate_polynomial(permutation_indices);

        let alpha = transcript.draw_field_element::<F>();

        // construct left_hat = id(x) + alpha * h_left(x)
        let h_left_hat = store.new_virtual_from_virtual(h_left);
        store.mul_const_in_place(&h_left_hat, alpha);
        store.add_in_place(&h_left_hat, &id_ref);

        // construct right_hat = perm(x) + alpha * h_right(x)
        let h_right_hat = store.new_virtual_from_virtual(h_right);
        store.mul_const_in_place(&h_right_hat, alpha);
        store.add_in_place(&h_right_hat, &perm_ref);

        let (multiset_equality_proof, evaluation_point) =
            MultisetEqualityProof::prove(store, &h_left_hat, &h_right_hat, transcript, pcs);

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
        left_h_eval: EvaluationClaim<F>,
        right_h_eval: EvaluationClaim<F>,
        id_eval: EvaluationClaim<F>,
        perm_eval: EvaluationClaim<F>,
    ) -> Result<(), String> {
        let alpha = transcript.draw_field_element::<F>();

        // construct left_hat evaluation claim
        let left_hat_eval = EvaluationClaim {
            point: left_h_eval.point.clone(),
            evaluation: id_eval.evaluation + alpha * left_h_eval.evaluation,
        };

        // construct right_hat evaluation claim
        let right_hat_eval = EvaluationClaim {
            point: right_h_eval.point.clone(),
            evaluation: perm_eval.evaluation + alpha * right_h_eval.evaluation,
        };

        self.multiset_equality_proof
            .verify(transcript, pcs, left_hat_eval, right_hat_eval)
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
    use ark_std::Zero;
    use quill_pcs::kzg::KZG;

    #[test]
    fn test_permutation_proof() {
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

        // generate a permutation
        let id_coeffs = (0..poly_degree).collect::<Vec<usize>>();
        let permuted_indices = {
            let mut coeffs = id_coeffs.clone();
            coeffs.shuffle(&mut rng);
            coeffs
        };

        // construct the permuted polynomial evaluations based on the permuted indices
        let permuted_coeffs = {
            let mut vec = vec![Fr::zero(); poly_degree];
            for (i, &perm_index) in permuted_indices.iter().enumerate() {
                vec[i] = poly_coeffs[perm_index];
            }
            vec
        };

        let permuted_indices_field = permuted_indices
            .iter()
            .map(|&idx| Fr::from(idx as u64))
            .collect::<Vec<Fr>>();

        println!("Creating virtual polynomial store...");

        let mut store = VirtualPolynomialStore::new(num_vars);
        let h_left_index = store.allocate_polynomial(&poly_coeffs);
        let h_right_index = store.allocate_polynomial(&permuted_coeffs);
        let h_left_virtual = store.new_virtual_from_input(&h_left_index);
        let h_right_virtual = store.new_virtual_from_input(&h_right_index);

        let mut transcript = Transcript::new(b"permutation_test");

        println!("Proving multiset equality...");
        let (proof, evaluation_point) = PermutationCheckProof::prove(
            &mut store,
            &h_left_virtual,
            &h_right_virtual,
            &permuted_indices_field,
            &mut transcript,
            &pcs,
        );

        // -- Verifier --
        let mut verifier_transcript = Transcript::new(b"permutation_test");
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

        let id_evaluation_claim = EvaluationClaim {
            point: evaluation_point.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(
                num_vars,
                id_coeffs.iter().map(|&x| Fr::from(x as u64)).collect(),
            )
            .evaluate(&evaluation_point),
        };

        let perm_evaluation_claim = EvaluationClaim {
            point: evaluation_point.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(
                num_vars,
                permuted_indices_field.clone(),
            )
            .evaluate(&evaluation_point),
        };

        println!("Verifying multiset equality proof...");
        let verify_result = proof.verify(
            &mut verifier_transcript,
            &pcs,
            left_evaluation_claim,
            right_evaluation_claim,
            id_evaluation_claim,
            perm_evaluation_claim,
        );

        assert!(
            verify_result.is_ok(),
            "Multiset equality proof verification failed: {:?}",
            verify_result.err()
        );
        println!("Multiset equality proof verified successfully.");
    }

    #[test]
    fn test_permutation_proof_invalid() {
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

        // generate a permutation
        let id_coeffs = (0..poly_degree).collect::<Vec<usize>>();
        let permuted_indices = {
            let mut coeffs = id_coeffs.clone();
            coeffs.shuffle(&mut rng);
            coeffs
        };

        // construct the permuted polynomial evaluations based on the permuted indices
        let mut permuted_coeffs = {
            let mut vec = vec![Fr::zero(); poly_degree];
            for (i, &perm_index) in permuted_indices.iter().enumerate() {
                vec[i] = poly_coeffs[perm_index];
            }
            vec
        };

        // swap two values to make the permutation a different permutation
        // the multiset equality however still holds
        (permuted_coeffs[0], permuted_coeffs[1]) = (permuted_coeffs[1], permuted_coeffs[0]);

        let permuted_indices_field = permuted_indices
            .iter()
            .map(|&idx| Fr::from(idx as u64))
            .collect::<Vec<Fr>>();

        println!("Creating virtual polynomial store...");

        let mut store = VirtualPolynomialStore::new(num_vars);
        let h_left_index = store.allocate_polynomial(&poly_coeffs);
        let h_right_index = store.allocate_polynomial(&permuted_coeffs);
        let h_left_virtual = store.new_virtual_from_input(&h_left_index);
        let h_right_virtual = store.new_virtual_from_input(&h_right_index);

        let mut transcript = Transcript::new(b"permutation_test");

        println!("Proving multiset equality...");
        let (proof, evaluation_point) = PermutationCheckProof::prove(
            &mut store,
            &h_left_virtual,
            &h_right_virtual,
            &permuted_indices_field,
            &mut transcript,
            &pcs,
        );

        // -- Verifier --
        let mut verifier_transcript = Transcript::new(b"permutation_test");
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

        let id_evaluation_claim = EvaluationClaim {
            point: evaluation_point.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(
                num_vars,
                id_coeffs.iter().map(|&x| Fr::from(x as u64)).collect(),
            )
            .evaluate(&evaluation_point),
        };

        let perm_evaluation_claim = EvaluationClaim {
            point: evaluation_point.clone(),
            evaluation: DenseMultilinearExtension::from_evaluations_vec(
                num_vars,
                permuted_indices_field.clone(),
            )
            .evaluate(&evaluation_point),
        };

        println!("Verifying multiset equality proof...");
        let verify_result = proof.verify(
            &mut verifier_transcript,
            &pcs,
            left_evaluation_claim,
            right_evaluation_claim,
            id_evaluation_claim,
            perm_evaluation_claim,
        );

        assert!(
            verify_result.is_err(),
            "Multiset equality proof verification did not fail as expected",
        );
    }
}
