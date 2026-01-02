use std::iter::Sum;

use ark_ff::PrimeField;
use quill_transcript::transcript::Transcript;
use crate::piops::{sumcheck::SumcheckProof, zerocheck::ZeroCheckProof};
use quill_pcs::MultilinearPCS;
use crate::utils::virtual_polynomial::{VirtualPolynomialStore, VirtualPolynomialRef, VirtualPolyExpr};

pub struct MultisetEqualityProof<F: PrimeField, PCS: MultilinearPCS<F>> {
    pub zero_check_proof: ZeroCheckProof<F>,
    pub sumcheck_proof: SumcheckProof<F>,
    _phantom: core::marker::PhantomData<PCS>,
}

impl<F: PrimeField, PCS:MultilinearPCS<F>> MultisetEqualityProof<F, PCS> {
    fn index_to_point(index: usize, num_vars: usize) -> Vec<F> {
        (0..num_vars)
            .map(|i| {
                if (index >> i) & 1 == 1 {
                    F::one()
                } else {
                    F::zero()
                }
            })
            .collect()
    }

    pub fn prove(
        store: &mut VirtualPolynomialStore<F>,
        h_left: &VirtualPolynomialRef,
        h_right: &VirtualPolynomialRef,
        transcript: &mut Transcript,
        pcs: &PCS,
    ) -> Self {
        let num_vars = store.num_vars();

        // use Logup to prove multiset equality via two sumchecks
        let eval_point = transcript.draw_field_element::<F>();

        // compute the evaluations of 1 / (eval_point + h_left(x)) and 1 / (eval_point + h_right(x)) 
        let log_derivative_left_evals = (0..(1 << num_vars))
            .map(|i| {
                let h_left_eval = store.evaluate_point(&Self::index_to_point(i, num_vars), h_left);
                (eval_point + h_left_eval).inverse().unwrap()
            })
            .collect::<Vec<F>>();
        
        let log_derivative_right_evals = (0..(1 << num_vars))
            .map(|i| {
                let h_right_eval = store.evaluate_point(&Self::index_to_point(i, num_vars), h_right);
                (eval_point + h_right_eval).inverse().unwrap()
            })
            .collect::<Vec<F>>();

        // commit to the polynomials
        let commitment_left = pcs.commit(&log_derivative_left_evals);
        let commitment_right = pcs.commit(&log_derivative_right_evals);
        transcript.append_serializable(&commitment_left);
        transcript.append_serializable(&commitment_right);

        // draw a batching challenge for the zero check
        let lambda = transcript.draw_field_element::<F>();

        // add the committed polynomials to the store
        let denom_left_index = store.allocate_polynomial(&log_derivative_left_evals);
        let denom_right_index = store.allocate_polynomial(&log_derivative_right_evals);

        // enforce over the hypercube that
        // log_derivative_left(x) * (eval_point + h_left(x)) - 1 +
        // lambda * (log_derivative_right(x) * (eval_point + h_right(x)) - 1) = 0

        // TODO: need a better interface to do this
        let constraint_expr =
            denom_left_index.to_expr::<F>() * (VirtualPolyExpr::Const(eval_point) + store.virtual_polys[h_left.index].clone()) - VirtualPolyExpr::Const(F::one()) +
            VirtualPolyExpr::Const(lambda) *
            (denom_right_index.to_expr::<F>() * (VirtualPolyExpr::Const(eval_point) + store.virtual_polys[h_right.index].clone()) - VirtualPolyExpr::Const(F::one()));
        
        let constraint_index = store.new_virtual_from_expr(constraint_expr);


        let zero_check_proof = ZeroCheckProof::prove(
            store,
            &constraint_index,
            transcript,
        );

        // allocate a new virtual polynomial to ensure that the sum of the two log derivatives is zero
        let diff_virtual = store.new_virtual_from_expr(
            denom_left_index.to_expr::<F>() - denom_right_index.to_expr::<F>()
        );
        let sumcheck_proof = SumcheckProof::prove(
            num_vars,
            store,
            &diff_virtual,
            F::zero(),
            transcript,
        );

        Self {
            zero_check_proof,
            sumcheck_proof,
            _phantom: core::marker::PhantomData,
        }
    }
}