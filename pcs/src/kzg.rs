use ark_ff::Field;
use ark_poly::{DenseUVPolynomial, Polynomial, polynomial};
use ark_poly::univariate::DensePolynomial;
use ark_std::rand::Rng;
use ark_std::UniformRand;
use ark_ec::pairing::Pairing;
use ark_std::{Zero, One};


pub struct KZG<E: Pairing> {
    /// Maximum degree of polynomials supported
    pub max_degree: usize,

    /// Generator point for G1
    pub g1 : E::G1,
    /// Generator point for G2
    pub g2 : E::G2,

    /// Powers of tau in G1: `g1, g1^tau, g1^{tau^2}, ..., g1^{tau^max_degree}`
    pub g1_points: Vec<E::G1>,
    /// Powers of tau in G2: `g2, g2^tau, g2^{tau^2}, ..., g2^{tau^max_degree}`
    pub g2_points: Vec<E::G2>,
}

pub struct KZGOpeningProof<E: Pairing> {
    /// The evaluation point
    pub x: E::ScalarField,
    /// The evaluation result
    pub y: E::ScalarField,
    /// Commitment to the quotient polynomial
    pub proof: E::G1,
}

impl<E: Pairing> KZG<E> {
    pub fn trusted_setup(max_degree: usize, rng: &mut impl Rng) -> KZG<E> {
        let g1_generator = E::G1::rand(rng);
        let g2_generator = E::G2::rand(rng);

        let tau = E::ScalarField::rand(rng);

        let mut g1_points = Vec::with_capacity(max_degree + 1);
        let mut g2_points = Vec::with_capacity(max_degree + 1);

        for i in 0..=max_degree {
            let tau_i = tau.pow([i as u64]);
            g1_points.push(g1_generator * tau_i);
            g2_points.push(g2_generator * tau_i);
        }

        KZG {
            max_degree,
            g1: g1_generator,
            g2: g2_generator,
            g1_points,
            g2_points,
        }        
    }

    pub fn commit(&self, polynomial: &[E::ScalarField]) -> E::G1 {
        assert!(polynomial.len() <= self.max_degree + 1, "Polynomial degree exceeds max degree");

        let mut commitment = E::G1::zero();
        for (i, coeff) in polynomial.iter().enumerate() {
            commitment += self.g1_points[i] * (*coeff);
        }
        commitment
    }

    pub fn open(&self, polynomial: &[E::ScalarField], x: E::ScalarField) -> KZGOpeningProof<E> {
        // y = compute p(X)
        let poly = DensePolynomial::from_coefficients_slice(polynomial);
        let y = poly.evaluate(&x);
        
        // compute q(X) = (p(X) - y) / (X - x)
        let numerator = &poly - &DensePolynomial::from_coefficients_slice(&[y]);
        let denominator = DensePolynomial::from_coefficients_slice(&[-x, E::ScalarField::one()]); 
        
        let q = &numerator / &denominator;
        assert!(&q * &denominator == numerator, "Polynomial division failed");

        // compute the commitment to q(x)
        let q_coefficients = q.coeffs;
        let q_commitment = self.commit(&q_coefficients);

        KZGOpeningProof {
            x,
            y,
            proof: q_commitment,
        }
    }

    pub fn verify(&self, commitment: &E::G1, proof: &KZGOpeningProof<E>) -> bool {
        let KZGOpeningProof {x, y, proof} = proof;

        // verify that q(tau) * (tau - x) = p(tau) - y
        // by verifying the pairing equation e(C - y*G1, G2) = e(proof, G2 * x + G2[0])
        let comm_tau_minus_x = self.g2_points[1] - self.g2_points[0] * x;
        let left = E::pairing(*commitment - (self.g1 * y), self.g2);
        let right = E::pairing(proof, comm_tau_minus_x);

        left == right
    }
}


mod tests {
    use super::*;
    use ark_bn254::Bn254;
    use ark_bn254::Fr;
    use ark_std::test_rng;

    #[test]
    fn test_kzg() {
        let mut rng = test_rng();
        let kzg = KZG::<Bn254>::trusted_setup(4, &mut rng);

        println!("G1 Generator: {:?}", kzg.g1);
        println!("{:?}", kzg.g1_points);

        // p(x) = 2 + 1*x + 3*x^2
        let poly_coeffs = vec![
            Fr::from(2u64),
            Fr::from(1u64),
            Fr::from(3u64),
        ];

        let commitment = kzg.commit(&poly_coeffs);

        let x = Fr::from(5u64);
        let proof = kzg.open(&poly_coeffs, x);

        println!("Opening proof at x = {:?}, y = {:?}", proof.x, proof.y);

        let is_valid = kzg.verify(&commitment, &proof);
        assert!(is_valid, "KZG proof verification failed");


        let wrong_proof = KZGOpeningProof {
            x: proof.x,
            y: proof.y + Fr::one(),
            proof: proof.proof,
        };

        let is_valid = kzg.verify(&commitment, &wrong_proof);
        assert!(!is_valid, "KZG proof verification should have failed but didn't");
    }
}