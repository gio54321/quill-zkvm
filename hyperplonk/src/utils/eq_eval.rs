use ark_ff::fields::PrimeField;

/// Evaluate eq(x, r) = prod_{i=1}^n (x_i * r_i + (1 - x_i) * (1 - r_i))
/// for every point in {0,1}^n
/// This function takes linear O(2^n) time
pub fn fast_eq_eval_hypercube<F: PrimeField>(
    n : usize,
    point: &[F],
) -> Vec<F> {
    assert_eq!(point.len(), n);

    // at each iteration, we have a vector of size 2^i, containing
    // the evaluations of eq on the first i variables
    let mut evals : Vec<F> = vec![F::one()];
    for i in (0..n).rev() {
        let r_i = point[i];
        let one_minus_r_i = F::one() - r_i;

        let mut new_evals : Vec<F> = Vec::with_capacity(evals.len() * 2);
        for &eval in &evals {
            // eq(0, x_i+1,...,x_n) = eq(x_1,...,x_n) * (1 - r_{i+1})
            let eval_0 = eval * one_minus_r_i;
            new_evals.push(eval_0);

            // eq(1, x_i+1,...,x_n) = eq(x_1,...,x_n) * r_{i+1}
            let eval_1 = eval * r_i;
            new_evals.push(eval_1);
        }
        evals = new_evals;
    }

    assert_eq!(evals.len(), 1 << n);
    evals
}

pub fn eq_eval<F: PrimeField>(
    x: &[F],
    r: &[F],
) -> F {
    assert_eq!(x.len(), r.len());
    let n = x.len();

    let mut result = F::one();
    for i in 0..n {
        let term = x[i] * r[i] + (F::one() - x[i]) * (F::one() - r[i]);
        result *= term;
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::Fr;
    use ark_std::test_rng;
    use ark_ff::UniformRand;
    use ark_std::{Zero, One};

    #[test]
    fn test_fast_eq_eval() {
        let n = 5;
        let mut rng = test_rng();
        let point = (0..n).map(|_| Fr::rand(&mut rng)).collect::<Vec<Fr>>();
        let evals = fast_eq_eval_hypercube(n, &point);

        // verify correctness naively
        for i in 0..(1 << n) {
            let mut expected_eval = Fr::one();
            for j in 0..n {
                let x_j = if (i >> j) & 1 == 1 { Fr::one() } else { Fr::zero() };
                let r_j = point[j];
                let term = x_j * r_j + (Fr::one() - x_j) * (Fr::one() - r_j);
                expected_eval *= term;
            }
            assert_eq!(evals[i], expected_eval);
        }
    }
}