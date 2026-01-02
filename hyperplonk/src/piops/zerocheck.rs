use ark_ff::PrimeField;
use quill_transcript::transcript::Transcript;
use crate::piops::EvaluationClaim;
use crate::piops::sumcheck::SumcheckProof;
use crate::utils::virtual_polynomial::{VirtualPolynomialStore, VirtualPolynomialRef};
use crate::utils::eq_eval::{eq_eval, fast_eq_eval_hypercube};


pub struct ZeroCheckProof<F: PrimeField> {
    pub num_vars: usize,
    pub sumcheck_proof: SumcheckProof<F>,
}

impl<F: PrimeField> ZeroCheckProof<F> {
    pub fn prove(store: &mut VirtualPolynomialStore<F>, h: &VirtualPolynomialRef, transcript: &mut Transcript) -> Self {
        let num_vars = store.num_vars();
        let random_point = (0..num_vars).map(|_| transcript.draw_field_element::<F>()).collect::<Vec<F>>();

        // get evaluations of eq(x, random_point) over {0,1}^n
        let eq_evals = fast_eq_eval_hypercube(num_vars, random_point.as_slice());

        let eq_poly_index = store.allocate_polynomial(&eq_evals);
        let h_hat = store.new_virtual_from_virtual(&h);
        store.mul_in_place(&h_hat, &eq_poly_index);

        let sumcheck_proof = SumcheckProof::prove(
            num_vars,
            store,
            &h_hat,
            F::zero(),
            transcript,
        );

        Self {
            num_vars,
            sumcheck_proof
        }
    }

    pub fn verify(&self, transcript: &mut Transcript) -> Result<EvaluationClaim<F>, String> {
        let num_vars = self.num_vars;
        let random_point = (0..num_vars).map(|_| transcript.draw_field_element::<F>()).collect::<Vec<F>>();

        if self.sumcheck_proof.claimed_sum != F::zero() {
            return Err("Sumcheck claimed sum is not zero".to_string());
        }

        if self.sumcheck_proof.num_vars != num_vars {
            return Err("Sumcheck proof num_vars does not match zerocheck num_vars".to_string());
        }

        let sumcheck_eval_claim = self.sumcheck_proof.verify(
            transcript,
        )?;

        // compute the zerocheck evaluation claim from the sumcheck evaluation claim
        let eq_eval = eq_eval(
            &random_point,
            &sumcheck_eval_claim.point,
        );

        Ok(EvaluationClaim {
            point: sumcheck_eval_claim.point,
            // sumcheck_claimed_evaluation = h(r) * eq_eval
            evaluation: sumcheck_eval_claim.evaluation / eq_eval,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::Fr;
    use ark_std::{Zero, One};
    use ark_poly::{Polynomial, DenseMultilinearExtension};

    #[test]
    fn test_zerocheck_proof() {
        let num_vars = 3;


        let g1 = DenseMultilinearExtension::from_evaluations_vec(
            num_vars,
            vec![
                Fr::zero(), Fr::one(), Fr::from(2u64), Fr::from(3u64),
                Fr::from(4u64), Fr::from(5u64), Fr::from(6u64), Fr::from(7u64),
            ],
        );

        let g2 = DenseMultilinearExtension::from_evaluations_vec(
            num_vars,
            vec![
                Fr::zero(), Fr::one(), Fr::from(4u64), Fr::from(9u64),
                Fr::from(16u64), Fr::from(25u64), Fr::from(36u64), Fr::from(49u64),
            ],
        );
        

        // create a virtual polynomial h(g1, g2) = g1 * g1 - g2
        // we want to prove that h sums to zero over {0,1}^n
        let mut store = VirtualPolynomialStore::new(num_vars);
        let g1_ref = store.allocate_polynomial(&g1.evaluations);
        let g2_ref = store.allocate_polynomial(&g2.evaluations);
        let h = store.new_virtual_from_input(&g1_ref);
        store.mul_in_place(&h, &g1_ref);
        store.sub_in_place(&h, &g2_ref);

        let proof = ZeroCheckProof::prove(
            &mut store,
            &h,
            &mut Transcript::new(b"zerocheck_test"),
        );

        let evaluation_claim = proof.verify(
            &mut Transcript::new(b"zerocheck_test"),
        ).unwrap();

        let point = &evaluation_claim.point;

        // check manually the evaluation claim
        let g1_at_r : Fr = g1.evaluate(&point);
        let g2_at_r : Fr = g2.evaluate(&point);
        let mut store = VirtualPolynomialStore::new(num_vars);
        let g1_ref = store.allocate_polynomial(&g1.evaluations);
        let g2_ref = store.allocate_polynomial(&g2.evaluations);
        let h = store.new_virtual_from_input(&g1_ref);
        store.mul_in_place(&h, &g1_ref);
        store.sub_in_place(&h, &g2_ref);
        let h_at_r = store.evaluate_point(&vec![g1_at_r, g2_at_r], &h);
        
        assert_eq!(evaluation_claim.evaluation, h_at_r, "Evaluation claim should match g1 at the evaluation point");
    }


      #[test]
    fn test_zerocheck_proof_not_zero() {
        let num_vars = 3;

        let g1 = DenseMultilinearExtension::from_evaluations_vec(
            num_vars,
            vec![
                Fr::zero(), Fr::one(), Fr::from(2u64), Fr::from(3u64),
                Fr::from(4u64), Fr::from(5u64), Fr::from(6u64), Fr::from(7u64),
            ],
        );

        let g2 = DenseMultilinearExtension::from_evaluations_vec(
            num_vars,
            vec![
                Fr::zero(), Fr::one(), Fr::from(4u64), Fr::from(9u64),
                Fr::from(16u64), Fr::from(25u64), Fr::from(36u64), Fr::from(50u64), // changed from 49 to 50
            ],
        );
        

        // create a virtual polynomial h(g1, g2) = g1 * g1 - g2
        // we want to prove that h sums to zero over {0,1}^n
        let mut store = VirtualPolynomialStore::new(num_vars);
        let g1_ref = store.allocate_polynomial(&g1.evaluations);
        let g2_ref = store.allocate_polynomial(&g2.evaluations);
        let h = store.new_virtual_from_input(&g1_ref);
        store.mul_in_place(&h, &g1_ref);
        store.sub_in_place(&h, &g2_ref);

        let proof = ZeroCheckProof::prove(
            &mut store,
            &h,
            &mut Transcript::new(b"zerocheck_test"),
        );

        let res = proof.verify(
            &mut Transcript::new(b"zerocheck_test"),
        );

        match res {
            Err(_) => {}, // expected
            Ok(_) => panic!("Zerocheck proof should not verify for non-zero polynomial"),
        }
    }
}