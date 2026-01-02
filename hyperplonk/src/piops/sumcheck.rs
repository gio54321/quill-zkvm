use ark_ff::fields::PrimeField;
use ark_poly::{DenseUVPolynomial, univariate::DensePolynomial};
use quill_transcript::transcript::Transcript;
use ark_std::{Zero};
use ark_poly::{Polynomial};
use crate::{piops::EvaluationClaim, utils::virtual_polynomial::VirtualPolynomial};

/// A sumcheck proof for a virtual polynomial of the form h(g_1(x), ..., g_k(x))
/// Reduces checking the sum over {0,1}^n of h(g_1(x), ..., g_k(x))
/// to checking the evaluations of that expression at a random point.
/// 
/// NOTE: the evaluation claim has to be checked separately
#[derive(Clone, Debug)]
pub struct SumcheckProof<F: PrimeField> {
    pub num_vars: usize,
    pub claimed_sum: F,
    pub r_polys: Vec<DensePolynomial<F>>,
}

impl<F: PrimeField> SumcheckProof<F> {
    /// General sumcheck prover for a function of the form h(g_1(x), ..., g_k(x))
    /// where each g_i is a multilinear polynomial in n variables, represented
    /// as a vector of evaluations over {0,1}^n, and h is a function F^k -> F
    /// that can be evaluated efficiently.
    /// 
    /// ASSUMES: the commitments to each g_i have already been incorporated into the transcript
    pub fn prove(num_vars: usize, h : &VirtualPolynomial<F>, claimed_sum: F, transcript: &mut Transcript) -> Self {
        transcript.append_serializable(&num_vars);
        transcript.append_serializable(&claimed_sum);

        let mut output_r_polys : Vec<DensePolynomial<F>> = Vec::with_capacity(num_vars);
        let mut evaluation_point : Vec<F> = Vec::with_capacity(num_vars);
        let mut gs_local : Vec<Vec<F>> = h.polynomials.clone();

        for i in (0..num_vars).rev() {
            let mut r_polys : Vec<Vec<DensePolynomial<F>>> = Vec::with_capacity(gs_local.len());
            for point in 0..(1<<i) {
                let mut r_polys_i: Vec<DensePolynomial<F>> = Vec::with_capacity(1 << i);
                for g in &gs_local {

                    let low = g[point << 1];
                    let high = g[(point << 1) + 1];
                    // poly = (1-x) * low + x * high = low + x * (high - low)
                    let poly = DensePolynomial::from_coefficients_vec(vec![low, high - low]);
                    r_polys_i.push(poly);   
                }
                r_polys.push(r_polys_i);
            }

            // compute h(r_1(x), ..., r_k(x)) for each poly in r_polys, and sum them up to get the
            // next message polynomial
            let next_message: DensePolynomial<F> = r_polys.iter().map(|g_polys_i| {
                h.evaluate_poly(g_polys_i)
            }).fold(DensePolynomial::zero(), |acc, x| acc + x);

            // append the polynomial to the transcript
            transcript.append_serializable(&next_message);
            output_r_polys.push(next_message);

            // draw a random challenge
            let r = transcript.draw_field_element::<F>();
            evaluation_point.push(r);

            // update gs_local to be the evaluations of r_polys at r
            let mut new_gs_local = Vec::with_capacity(gs_local.len());
            for g_index in 0..gs_local.len() {
                let mut new_g_evals : Vec<F> = Vec::with_capacity(gs_local.len());
                for point in 0..(1<<i) {
                    let poly = &r_polys[point][g_index];
                    let eval = poly.evaluate(&r);
                    new_g_evals.push(eval);
                }
                new_gs_local.push(new_g_evals);
            }

            gs_local = new_gs_local;

            println!("Sumcheck round {} done, gs_local: {:?}", num_vars - i, gs_local);
        }
        
        Self {
            num_vars: num_vars,
            claimed_sum: claimed_sum,
            r_polys: output_r_polys,
        }
    }


    pub fn verify(&self, transcript: &mut Transcript) -> Result<EvaluationClaim<F>, String> {
        // reconstruct the transcript state
        transcript.append_serializable(&self.num_vars);
        transcript.append_serializable(&self.claimed_sum);

        let mut v = self.claimed_sum;
        let mut evaluation_point : Vec<F> = Vec::with_capacity(self.num_vars);

        for transcript_poly in &self.r_polys {

            // check that r(0) + r(1) == v
            let eval_at_0 = transcript_poly.evaluate(&F::zero());
            let eval_at_1 = transcript_poly.evaluate(&F::one());
            println!("Verifying sumcheck round {}, v = {:?}", evaluation_point.len() + 1, v);
            println!("r(0) = {:?}, r(1) = {:?}", eval_at_0, eval_at_1);
            // check that r_i(0) + r_i(1) == v
            if eval_at_0 + eval_at_1 != v {
                return Err("Sumcheck polynomial does not sum to previous value".to_string());
            }

            // incorporate the sent polynomial into the transcript
            transcript.append_serializable(transcript_poly);
            
            // draw the random challenge
            let r = transcript.draw_field_element::<F>();
            evaluation_point.push(r);

            // update v to be the evaluation of the sent univariate polynomial at r
            v = transcript_poly.evaluate(&r);
        }

        // return the evaluation claim
        Ok(EvaluationClaim {
            point: evaluation_point,
            evaluation: v,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::utils::virtual_polynomial::VirtualPolyExpr;

    use super::*;
    use ark_bn254::Fr;
    use ark_std::One;

    #[test]
    fn test_sumcheck_proof() {
        let num_vars = 3;
        // define g_1(x1,x2,x3) = x1 + 2*x2 + 3*x3
        let g1_evals : Vec<Fr> = (0..(1 << num_vars))
            .map(|i| {
                let x1 = Fr::from(((i >> 0) & 1) as u64);
                let x2 = Fr::from(((i >> 1) & 1) as u64);
                let x3 = Fr::from(((i >> 2) & 1) as u64);
                x1 + Fr::from(2u64) * x2 + Fr::from(3u64) * x3
            })
            .collect();

        // define g_2(x1,x2,x3) = x1 * 2 * x2 + 3 * x1 * x3
        let g2_evals : Vec<Fr> = (0..(1 << num_vars))
            .map(|i| {
                let x1 = Fr::from(((i >> 0) & 1) as u64);
                let x2 = Fr::from(((i >> 1) & 1) as u64);
                let x3 = Fr::from(((i >> 2) & 1) as u64);
                x1 * Fr::from(2u64) * x2 + Fr::from(3u64) * x1 * x3
            })
            .collect();

        // create a virtual polynomial h(g1, g2) = g1 * g2
        let (mut virtual_poly, _g1_ref) = VirtualPolynomial::from_poly_evals(num_vars, &g1_evals);
        let g2_ref = virtual_poly.allocate_input_mle(&g2_evals);
        virtual_poly.mul_mle(g2_ref);

        let claimed_sum: Fr = g1_evals.iter().zip(g2_evals.iter()).map(|(a,b)| *a * *b).sum();

        
        let proof = SumcheckProof::prove(
            num_vars,
            &virtual_poly,
            claimed_sum,
            &mut Transcript::new(b"sumcheck_test"),
        );

        let evaluation_claim = proof.verify(
            &mut Transcript::new(b"sumcheck_test"),
        ).unwrap();

        let point = &evaluation_claim.point;


        // check manually the evaluation claim
        let g1_at_r : Fr = point[0] + 
            Fr::from(2u64)* point[1] +
            Fr::from(3u64) * point[2];
        
        let g2_at_r : Fr = point[0] * Fr::from(2u64) * point[1] +
            Fr::from(3u64) * point[0] * point[2];
        
        let h_at_r = virtual_poly.evaluate_point(&vec![g1_at_r, g2_at_r]);
        
        assert_eq!(evaluation_claim.evaluation, h_at_r, "Evaluation claim should match g1 at the evaluation point");
    }
}