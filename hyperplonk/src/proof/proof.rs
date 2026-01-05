use crate::proof::circuit::Circuit;
use crate::{
    piops::{permutation_check::PermutationCheckProof, zerocheck::ZeroCheckProof, EvaluationClaim},
    utils::virtual_polynomial::{VirtualPolyExpr, VirtualPolynomialStore},
};
use ark_ff::PrimeField;
use quill_pcs::{MultilinearPCS, MultilinearPCSProof};
use quill_transcript::transcript::Transcript;
use std::iter::zip;

pub struct HyperPlonk<F: PrimeField, C: Circuit<F> + Clone, PCS: MultilinearPCS<F>> {
    pub vk: HyperPlonkVK<F, PCS, C>,
    pub id_poly: Vec<F>,
    pub permutation_poly: Vec<F>,
    pub circuit: C,
    pub preprocessed_values: Vec<Vec<F>>,
    pub _marker: std::marker::PhantomData<(F, PCS)>,
}

pub struct HyperPlonkProof<F: PrimeField, PCS: MultilinearPCS<F>> {
    pub witness_commitment: PCS::Commitment,
    pub zero_check_proof: ZeroCheckProof<F>,
    pub permutation_check_proof: PermutationCheckProof<F, PCS>,
    pub openings_zero_check: Vec<PCS::Proof>,
    pub openings_preprocessed: Vec<PCS::Proof>,
    pub opening_id: PCS::Proof,
    pub opening_permutation: PCS::Proof,
    pub opening_permutation_trace: PCS::Proof,
}

#[derive(Clone)]
pub struct HyperPlonkVK<F: PrimeField, PCS: MultilinearPCS<F>, C: Circuit<F>> {
    pub num_cols: usize,
    pub num_rows: usize,
    pub circuit: C,
    pub preprocessed_columns_commitments: Vec<PCS::Commitment>,
    pub id_commitment: PCS::Commitment,
    pub permutation_commitment: PCS::Commitment,
}

impl<F: PrimeField, C: Circuit<F> + Clone, PCS: MultilinearPCS<F>> HyperPlonk<F, C, PCS> {
    pub fn preprocess(circuit: C, pcs: &PCS) -> Self {
        assert!(
            circuit.num_rows().is_power_of_two(),
            "Number of rows must be a power of two"
        );
        assert!(
            circuit.num_cols().is_power_of_two(),
            "Number of columns must be a power of two"
        );

        let trace_num_vars = circuit.num_rows().trailing_zeros() as usize
            + circuit.num_cols().trailing_zeros() as usize;

        assert!(
            pcs.max_degree() == 1 << trace_num_vars,
            "PCS max degree mismatch"
        );

        // pad the preprocessed columns to the full trace size with zeros and commit to them
        let mut preprocessed_values = circuit.preprocessed_values();
        for i in 0..preprocessed_values.len() {
            assert_eq!(
                preprocessed_values[i].len(),
                circuit.num_rows(),
                "Preprocessed column length mismatch"
            );
            preprocessed_values[i]
                .extend(vec![F::zero(); (1 << trace_num_vars) - circuit.num_rows()]);
        }

        let preprocessed_commitments = preprocessed_values
            .iter()
            .map(|col| pcs.commit(col))
            .collect::<Vec<_>>();

        // commit to the identity and permutation polynomials
        let (id_evals, permutation_evals) = circuit.permutation();

        assert_eq!(
            id_evals.len(),
            1 << trace_num_vars,
            "ID polynomial length mismatch"
        );
        assert_eq!(
            permutation_evals.len(),
            1 << trace_num_vars,
            "Permutation polynomial length mismatch"
        );

        let id_commitment = pcs.commit(&id_evals);
        let permutation_commitment = pcs.commit(&permutation_evals);

        let vk = HyperPlonkVK {
            num_cols: circuit.num_cols(),
            num_rows: circuit.num_rows(),
            circuit: circuit.clone(),
            preprocessed_columns_commitments: preprocessed_commitments,
            id_commitment,
            permutation_commitment,
        };
        Self {
            vk,
            circuit,
            id_poly: id_evals,
            permutation_poly: permutation_evals,
            preprocessed_values,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn prove(&self, pcs: &PCS, witness: &Vec<Vec<F>>) -> HyperPlonkProof<F, PCS> {
        // assert that the witness has the correct shape
        assert_eq!(
            witness.len(),
            self.circuit.num_cols(),
            "Witness columns length mismatch"
        );
        for col in witness {
            assert_eq!(
                col.len(),
                self.circuit.num_rows(),
                "Witness column row length mismatch"
            );
        }

        // first of all, do a sanity check that the witness satisfies the circuit constraints
        self.circuit.check_constraints(witness).unwrap();

        let num_rows = self.circuit.num_rows();

        let full_witness = witness.iter().flatten().cloned().collect::<Vec<F>>();

        assert_eq!(
            full_witness.len(),
            self.circuit.num_cols() * self.circuit.num_rows(),
            "Padded witness length mismatch"
        );

        let log2_rows = num_rows.trailing_zeros() as usize;
        let log2_cols = self.circuit.num_cols().trailing_zeros() as usize;

        // initialize a new transcript
        let mut transcript = Transcript::new(b"hyperplonk_proof");

        // the prover commits to the full witness polynomial
        let witness_commitment = pcs.commit(&full_witness);
        transcript.append_serializable(&witness_commitment);

        // HACK: it is implicitly assumed that the allocated polys have
        // indices 0..num_cols() for witness columns
        // refactor this
        let mut poly_store: VirtualPolynomialStore<F> = VirtualPolynomialStore::new(log2_rows);
        for column in witness {
            poly_store.allocate_polynomial(column);
        }
        for preprocessed in self.circuit.preprocessed_values() {
            poly_store.allocate_polynomial(&preprocessed);
        }

        // batch together all constraints into a single expression using a random alpha
        let zero_check_exprs = self.circuit.zero_check_expressions();
        let alpha = transcript.draw_field_element::<F>();

        let alpha_powers = (0..zero_check_exprs.len())
            .map(|i| alpha.pow(&[i as u64]))
            .collect::<Vec<F>>();
        let mut zero_check_expr = VirtualPolyExpr::Const(F::zero());
        for (expr, alpha) in zip(zero_check_exprs, alpha_powers) {
            zero_check_expr = zero_check_expr + VirtualPolyExpr::Const(alpha) * expr;
        }

        // prove the zero-check relation
        let zero_check_virtual = poly_store.new_virtual_from_expr(zero_check_expr);
        let (zero_check_proof, zero_check_eval_claim) =
            ZeroCheckProof::prove(&mut poly_store, &zero_check_virtual, &mut transcript);

        // construct a new polynomial store for the permutation check
        // this check is done on the whole trace at once, without separating the columns
        let mut poly_store2 = VirtualPolynomialStore::new(log2_rows + log2_cols);
        let witness_idx = poly_store2.allocate_polynomial(&full_witness);
        let witness_virtual = poly_store2.new_virtual_from_input(&witness_idx);

        let (permutation_check_proof, permutation_check_claim) = PermutationCheckProof::prove(
            &mut poly_store2,
            &witness_virtual,
            &witness_virtual,
            &self.id_poly,
            &self.permutation_poly,
            &mut transcript,
            pcs,
        );

        // compute openings for the witness polynomial at the zero-check evaluation point
        let mut openings_zero_check = vec![];
        for col in 0..self.circuit.num_cols() {
            let mut point = zero_check_eval_claim.point.clone();
            for i in (0..log2_cols).rev() {
                point.push(F::from(((col >> i) & 1) as u64));
            }
            let opening = pcs.open(&full_witness, &point, &mut transcript);
            openings_zero_check.push(opening);
        }

        // compute openings for the preprocessed columns at the zero-check evaluation point
        // this is not strictly necessary, but it saves some work to the verifier
        let preprocessed_columns = self.circuit.preprocessed_values();
        let mut openings_preprocessed = vec![];
        for i in 0..self.circuit.num_preprocessed_columns() {
            let opening = pcs.open(
                &preprocessed_columns[i],
                &zero_check_eval_claim.point,
                &mut transcript,
            );
            openings_preprocessed.push(opening);
        }

        // compute openings for the id and permutation polynomials at the permutation check evaluation point
        let opening_id = pcs.open(&self.id_poly, &permutation_check_claim, &mut transcript);
        let opening_permutation = pcs.open(
            &self.permutation_poly,
            &permutation_check_claim,
            &mut transcript,
        );
        let opening_permutation_trace =
            pcs.open(&full_witness, &permutation_check_claim, &mut transcript);

        HyperPlonkProof {
            witness_commitment,
            zero_check_proof,
            permutation_check_proof,
            openings_zero_check,
            openings_preprocessed,
            opening_id,
            opening_permutation,
            opening_permutation_trace,
        }
    }
}

impl<F: PrimeField, PCS: MultilinearPCS<F>> HyperPlonkProof<F, PCS> {
    pub fn verify<C: Circuit<F>>(
        &self,
        vk: &HyperPlonkVK<F, PCS, C>,
        pcs: &PCS,
    ) -> Result<(), String> {
        let mut transcript = Transcript::new(b"hyperplonk_proof");

        transcript.append_serializable(&self.witness_commitment);

        let alpha = transcript.draw_field_element::<F>();

        let zero_check_eval_claim = self.zero_check_proof.verify(&mut transcript)?;
        let log2_cols = (vk.num_cols).trailing_zeros() as usize;

        let id_evaluation_claim = EvaluationClaim {
            point: self.opening_id.evaluation_point(),
            evaluation: self.opening_id.claimed_evaluation(),
        };

        let permutation_evaluation_claim = EvaluationClaim {
            point: self.opening_permutation.evaluation_point(),
            evaluation: self.opening_permutation.claimed_evaluation(),
        };

        let permutation_trace_evaluation_claim = EvaluationClaim {
            point: self.opening_permutation_trace.evaluation_point(),
            evaluation: self.opening_permutation_trace.claimed_evaluation(),
        };

        self.permutation_check_proof.verify(
            &mut transcript,
            &pcs,
            permutation_trace_evaluation_claim.clone(),
            permutation_trace_evaluation_claim.clone(),
            id_evaluation_claim.clone(),
            permutation_evaluation_claim.clone(),
        )?;

        let mut points = vec![];
        for col in 0..vk.circuit.num_cols() {
            let mut point = zero_check_eval_claim.point.clone();
            for i in (0..log2_cols).rev() {
                point.push(F::from(((col >> i) & 1) as u64));
            }
            points.push(point);
        }

        // verify zero check openings
        let mut col_evaluations = vec![];
        for (i, opening) in self.openings_zero_check.iter().enumerate() {
            if opening.evaluation_point() != points[i] {
                return Err("Zero check opening point mismatch".to_string());
            }

            let valid = pcs.verify(&self.witness_commitment, opening, &mut transcript);
            if !valid {
                return Err("Zero check opening verification failed".to_string());
            }

            col_evaluations.push(opening.claimed_evaluation());
        }

        // check preprocessed openings
        for (i, opening) in self.openings_preprocessed.iter().enumerate() {
            if opening.evaluation_point() != zero_check_eval_claim.point {
                return Err("Preprocessed opening point mismatch".to_string());
            }

            let valid = pcs.verify(
                &vk.preprocessed_columns_commitments[i],
                opening,
                &mut transcript,
            );
            if !valid {
                return Err("Preprocessed opening verification failed".to_string());
            }
            col_evaluations.push(opening.claimed_evaluation());
        }

        // check that the zero-check reduced evaluation match the computed one
        let mut recomputed_zero_check_evaluation = F::zero();
        let alpha_powers = (0..vk.circuit.zero_check_expressions().len())
            .map(|i| alpha.pow(&[i as u64]))
            .collect::<Vec<F>>();
        for (expr, alpha) in zip(vk.circuit.zero_check_expressions(), alpha_powers) {
            let eval = expr.evaluate(&col_evaluations);
            recomputed_zero_check_evaluation += alpha * eval;
        }

        if recomputed_zero_check_evaluation != zero_check_eval_claim.evaluation {
            return Err("Zero check evaluation mismatch".to_string());
        }

        // verify id opening
        if self.opening_id.evaluation_point() != permutation_trace_evaluation_claim.point {
            return Err("ID opening point mismatch".to_string());
        }
        let valid = pcs.verify(&vk.id_commitment, &self.opening_id, &mut transcript);
        if !valid {
            return Err("ID opening verification failed".to_string());
        }

        // verify permutation opening
        if self.opening_permutation.evaluation_point() != permutation_trace_evaluation_claim.point {
            return Err("Permutation opening point mismatch".to_string());
        }
        let valid = pcs.verify(
            &vk.permutation_commitment,
            &self.opening_permutation,
            &mut transcript,
        );
        if !valid {
            return Err("Permutation opening verification failed".to_string());
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::frontend::transition_circuit::TransitionCircuit;

    use super::*;
    use ark_bn254;
    use ark_bn254::Fr;
    use ark_ff::UniformRand;
    use ark_std::test_rng;
    use ark_std::Zero;
    use quill_pcs::kzg::KZG;
    use rand::SeedableRng;

    #[test]
    fn test_pcs_interface() {
        let mut rng = test_rng();
        let num_vars = 10;
        let kzg = KZG::<ark_bn254::Bn254>::trusted_setup(1 << num_vars, &mut rng);

        let poly_coeffs = (0..(1 << num_vars))
            .map(|_| Fr::rand(&mut rng))
            .collect::<Vec<Fr>>();

        let mut transcript = Transcript::new(b"test_transcript");

        let commitment = MultilinearPCS::commit(&kzg, &poly_coeffs);

        let x = (0..num_vars)
            .map(|_| Fr::rand(&mut rng))
            .collect::<Vec<Fr>>();
        let proof = MultilinearPCS::open(&kzg, &poly_coeffs, &x, &mut transcript);

        println!(
            "Opening proof at x = {:?}, y = {:?}",
            proof.evaluation_point(),
            proof.claimed_evaluation()
        );

        let mut transcript = Transcript::new(b"test_transcript");
        let is_valid = MultilinearPCS::verify(&kzg, &commitment, &proof, &mut transcript);
        assert!(is_valid, "PCS proof verification failed");
    }

    #[test]
    fn test_hyperplonk_proof() {
        let seed = [0u8; 32];
        let mut rng = rand::rngs::StdRng::from_seed(seed);

        // simple fibonacci circuit
        let mut circuit: TransitionCircuit<Fr> = TransitionCircuit::new(8);
        let state1 = circuit.allocate_state_cell();
        let state2 = circuit.allocate_state_cell();
        circuit.enforce_boundary_constraint(0, state1.current.to_expr());
        circuit.enforce_boundary_constraint(
            0,
            state2.current.to_expr() - VirtualPolyExpr::Const(Fr::from(1u64)),
        );

        circuit.enforce_constraint(
            state2.next.to_expr() - (state1.current.to_expr() + state2.current.to_expr()),
        );
        circuit.enforce_constraint(state1.next.to_expr() - state2.current.to_expr());

        let max_degree = circuit.num_cols().next_power_of_two() * circuit.num_rows();
        assert!(
            max_degree.is_power_of_two(),
            "Max degree must be a power of two"
        );
        println!("KZG setup...");
        let pcs = KZG::<ark_bn254::Bn254>::trusted_setup(max_degree, &mut rng);
        println!("KZG setup done.");

        let hyperplonk = HyperPlonk::preprocess(circuit.clone(), &pcs);
        println!("HyperPlonk preprocessing done.");

        // construct a valid witness for fibonacci
        let mut witness: Vec<Vec<Fr>> =
            vec![vec![Fr::zero(); circuit.num_rows()]; circuit.num_cols()];
        for row in 0..circuit.num_rows() {
            if row == 0 {
                witness[state1.current.col][row] = Fr::from(0u64);
                witness[state2.current.col][row] = Fr::from(1u64);
                witness[state1.next.col][row] = Fr::from(1u64);
                witness[state2.next.col][row] = Fr::from(1u64);
            } else {
                witness[state1.current.col][row] = witness[state1.next.col][row - 1];
                witness[state2.current.col][row] = witness[state2.next.col][row - 1];
                witness[state1.next.col][row] = witness[state2.current.col][row];
                witness[state2.next.col][row] =
                    witness[state2.current.col][row] + witness[state1.current.col][row];
            }
        }

        let proof = hyperplonk.prove(&pcs, &witness);

        proof.verify(&hyperplonk.vk, &pcs).unwrap();
        println!("HyperPlonk proof verified.");
    }
}
