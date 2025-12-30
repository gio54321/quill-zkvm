use ark_ff::fields::PrimeField;
use ark_poly::{DenseUVPolynomial, univariate::DensePolynomial};
use quill_transcript::transcript::Transcript;
use ark_std::{Zero, One};
use ark_poly::{Polynomial};

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

        println!("claimed_sum: {:?}", claimed_sum);

        transcript.append_serializable(&num_vars);
        transcript.append_serializable(&claimed_sum);

        let mut output_r_polys : Vec<DensePolynomial<F>> = Vec::with_capacity(gs.len());

        for i in (0..num_vars-1).rev() {
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
        
        Self {
            num_vars: num_vars,
            claimed_sum: claimed_sum,
            r_polys: output_r_polys,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::result;

    use super::*;
    use ark_bn254::Bn254;
    use ark_bn254::Fr;
    use ark_ff::UniformRand;
    use ark_std::test_rng;

    #[test]
    fn test_sumcheck_proof() {
        let num_vars = 3;
        let mut rng = test_rng();
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
    }
}