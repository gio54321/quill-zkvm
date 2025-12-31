use ark_ff::fields::PrimeField;
use ark_poly::{DenseUVPolynomial, univariate::DensePolynomial};
use quill_transcript::transcript::Transcript;
use ark_std::{Zero};
use ark_poly::{Polynomial};

/// A sumcheck proof for a function h(g_1(x), ..., g_k(x))
/// Reduces checking the sum over {0,1}^n of h(g_1(x), ..., g_k(x))
/// to checking the evaluations of that expression at a random point.
/// 
/// NOTE: the evaluation claim has to be checked separately
pub struct SumcheckProof<F: PrimeField> {
    pub num_vars: usize,
    pub claimed_sum: F,
    pub r_polys: Vec<DensePolynomial<F>>,
    pub evaluation_point: Vec<F>,
    pub evaluation_claim : F
}

impl<F: PrimeField> SumcheckProof<F> {
    /// General sumcheck prover for a function of the form h(g_1(x), ..., g_k(x))
    /// where each g_i is a multilinear polynomial in n variables, represented
    /// as a vector of evaluations over {0,1}^n, and h is a function F^k -> F
    /// that can be evaluated efficiently.
    /// 
    /// ASSUMES: the commitments to each g_i have already been incorporated into the transcript
    pub fn prove(num_vars: usize, gs: Vec<Vec<F>>, h: impl Fn(&[DensePolynomial<F>]) -> DensePolynomial<F>, transcript: &mut Transcript) -> Self {
        for g in &gs {
            assert_eq!(g.len(), 1 << num_vars);
        }

        let mut gs_local = gs.clone();
        
        // compute h(g_1, ..., g_k) for every evaluation point, and sum them up
        let mut claimed_sum: F = F::zero();
        for i in 0..(1 << num_vars) {
            let g_evals_at_i = gs_local.iter()
                .map(|g| g[i])
                .collect::<Vec<F>>();

            // println!("g_evals_at_{}: {:?}", i, g_evals_at_i);

            // TODO: this is not linear time if computing h is not O(1).
            // We should compute h "symbolically" using the low-depth trick.
            let g_evals_polys = g_evals_at_i
                .iter()
                .map(|&val| DensePolynomial::from_coefficients_slice(&[val]))
                .collect::<Vec<_>>();

                let h_eval = h(&g_evals_polys);
            claimed_sum += h_eval.evaluate(&F::zero());
        }

        transcript.append_serializable(&num_vars);
        transcript.append_serializable(&claimed_sum);

        let mut output_r_polys : Vec<DensePolynomial<F>> = Vec::with_capacity(gs.len());
        let mut evaluation_point : Vec<F> = Vec::with_capacity(num_vars);

        for i in (0..num_vars).rev() {
            println!("Sumcheck round {}", i);
            let mut r_polys : Vec<Vec<DensePolynomial<F>>> = Vec::with_capacity(gs.len());
            for g in &gs_local {
                let mut r_polys_i = Vec::with_capacity(1 << i);
                for j in 0..(1 << i) {
                    let low = g[j << 1];
                    let high = g[(j << 1) + 1];
                    // poly = (1-x) * low + x * high = low + x * (high - low)
                    let poly = DensePolynomial::from_coefficients_vec(vec![low, high - low]);
                    r_polys_i.push(poly);
                }
                r_polys.push(r_polys_i);
            }

            // compute h(r_1(x), ..., r_k(x)) for each poly in r_polys
            let mut h_polys : Vec<DensePolynomial<F>> = Vec::with_capacity(1 << i);
            for j in 0..(1 << i) {
                let r_evals = r_polys.iter()
                    .map(|r_polys_i| r_polys_i[j].clone())
                    .collect::<Vec<DensePolynomial<F>>>();
                let h_poly = h(&r_evals);
                h_polys.push(h_poly);
            }

            // sum all h_polys to get the next message
            let mut next_message = DensePolynomial::zero();
            for h_poly in &h_polys {
                next_message += h_poly;
            }

            // append the polynomial to the transcript
            transcript.append_serializable(&next_message);
            output_r_polys.push(next_message);

            // draw a random challenge
            let r = transcript.draw_field_element::<F>();
            evaluation_point.push(r);

            // update gs_local to be the evaluations of r_polys at r
            let mut new_gs_local = Vec::with_capacity(gs_local.len());
            for r_poly in r_polys {
                let mut new_g = Vec::with_capacity(1 << i);
                for poly in r_poly {
                    let eval = poly.evaluate(&r);
                    new_g.push(eval);
                }
                new_gs_local.push(new_g);
            }

            gs_local = new_gs_local;
        }

        // after all rounds, gs_local should have one element with one evaluation
        let evaluation_claim = gs_local[0][0];
        
        Self {
            num_vars: num_vars,
            claimed_sum: claimed_sum,
            r_polys: output_r_polys,
            evaluation_point,
            evaluation_claim
        }
    }

    pub fn verify(&self, transcript: &mut Transcript) -> bool {
        // reconstruct the transcript state
        transcript.append_serializable(&self.num_vars);
        transcript.append_serializable(&self.claimed_sum);

        let mut v = self.claimed_sum;

        for r_poly in &self.r_polys {
            // get the polynomial from the transcript
            let transcript_poly: DensePolynomial<F> = r_poly.clone();
            transcript.append_serializable(&transcript_poly);

            // check that r(0) + r(1) == v
            let eval_at_0 = transcript_poly.evaluate(&F::zero());
            let eval_at_1 = transcript_poly.evaluate(&F::one());
            if eval_at_0 + eval_at_1 != v {
                return false;
            }

            // draw the random challenge
            let r = transcript.draw_field_element::<F>();

            // evaluate current_sum_poly at r
            v = transcript_poly.evaluate(&r);
        }

        // finally, check that the evaluation claim matches h(g_1(r), ..., g_k(r))
        v == self.evaluation_claim
    }
}

#[cfg(test)]
mod tests {
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

        println!("g1_evals: {:?}", g1_evals);
        
        let proof = SumcheckProof::prove(
            num_vars,
            vec![g1_evals],
            |gs: &[DensePolynomial<Fr>]| {
                // h(g1, g2, ..., gk = prod(gi)
                let mut result = DensePolynomial::from_coefficients_vec(vec![Fr::one()]);
                for g in gs {
                    result = result*g;
                }
                result
            },
            &mut Transcript::new(b"sumcheck_test"),
        );

        let is_valid = proof.verify(
            &mut Transcript::new(b"sumcheck_test"),
        );

        assert!(is_valid, "Sumcheck proof should be valid");

        // check manually the evaluation claim
        let g1_at_r : Fr = proof.evaluation_point[0] + 
            Fr::from(2u64)* proof.evaluation_point[1] +
            Fr::from(3u64) * proof.evaluation_point[2];
        
        assert_eq!(proof.evaluation_claim, g1_at_r, "Evaluation claim should match g1 at the evaluation point");
    }
}