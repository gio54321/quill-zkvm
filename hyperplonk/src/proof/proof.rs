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
    pub trace_vks: Vec<TraceVK<F, PCS, C>>,
    pub trace_pks: Vec<TracePK<F>>,
}

pub struct TraceProof<F: PrimeField, PCS: MultilinearPCS<F>> {
    pub zero_check_proof: ZeroCheckProof<F>,
    pub permutation_check_proof: PermutationCheckProof<F, PCS>,
    pub openings_zero_check: Vec<PCS::Proof>,
    pub openings_preprocessed: Vec<PCS::Proof>,
    pub opening_id: PCS::Proof,
    pub opening_permutation: PCS::Proof,
    pub opening_permutation_trace: PCS::Proof,
}

pub struct HyperPlonkProof<F: PrimeField, PCS: MultilinearPCS<F>> {
    pub witness_commitment: Vec<PCS::Commitment>,
    pub trace_proofs: Vec<TraceProof<F, PCS>>,
}

pub struct TraceVK<F: PrimeField, PCS: MultilinearPCS<F>, C: Circuit<F>> {
    pub circuit: C,
    pub preprocessed_columns_commitments: Vec<PCS::Commitment>,
    pub id_commitment: PCS::Commitment,
    pub permutation_commitment: PCS::Commitment,
}

impl<F: PrimeField, PCS: MultilinearPCS<F>, C: Circuit<F> + Clone> Clone for TraceVK<F, PCS, C> {
    fn clone(&self) -> Self {
        TraceVK {
            circuit: self.circuit.clone(),
            preprocessed_columns_commitments: self.preprocessed_columns_commitments.clone(),
            id_commitment: self.id_commitment.clone(),
            permutation_commitment: self.permutation_commitment.clone(),
        }
    }
}

pub struct TracePK<F: PrimeField> {
    pub id_poly: Vec<F>,
    pub permutation_poly: Vec<F>,
    pub preprocessed_values: Vec<Vec<F>>,
}

pub struct HyperPlonkVK<F: PrimeField, PCS: MultilinearPCS<F>, C: Circuit<F>> {
    pub trace_vks: Vec<TraceVK<F, PCS, C>>,
}

pub struct TraceWitness<F: PrimeField>(pub Vec<Vec<F>>);

impl<F: PrimeField, C: Circuit<F> + Clone, PCS: MultilinearPCS<F>> HyperPlonk<F, C, PCS> {
    fn preprocess_trace(circuit: &C, pcs: &PCS) -> (TracePK<F>, TraceVK<F, PCS, C>) {
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

        // TODO: make those into a single polynomial
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

        let vk = TraceVK {
            circuit: circuit.clone(),
            preprocessed_columns_commitments: preprocessed_commitments,
            id_commitment,
            permutation_commitment,
        };
        let pk = TracePK {
            id_poly: id_evals,
            permutation_poly: permutation_evals,
            preprocessed_values,
        };
        (pk, vk)
    }

    pub fn preprocess(circuits: Vec<C>, pcs: &PCS) -> Self {
        let mut trace_pks = vec![];
        let mut trace_vks = vec![];
        for circuit in &circuits {
            let (trace_pk, trace_vk) = Self::preprocess_trace(&circuit, pcs);
            trace_pks.push(trace_pk);
            trace_vks.push(trace_vk);
        }

        Self {
            trace_pks,
            trace_vks,
        }
    }

    pub fn to_vk(&self) -> HyperPlonkVK<F, PCS, C> {
        HyperPlonkVK {
            trace_vks: self.trace_vks.clone(),
        }
    }

    fn prove_trace(
        &self,
        pcs: &PCS,
        witness: &Vec<Vec<F>>,
        full_witness: &Vec<F>,
        transcript: &mut Transcript,
        pk: &TracePK<F>,
        circuit: &C,
    ) -> TraceProof<F, PCS> {
        let log2_rows = circuit.num_rows().trailing_zeros() as usize;
        let log2_cols = circuit.num_cols().trailing_zeros() as usize;
        // HACK: it is implicitly assumed that the allocated polys have
        // indices 0..num_cols() for witness columns
        // refactor this
        let mut poly_store: VirtualPolynomialStore<F> = VirtualPolynomialStore::new(log2_rows);
        for column in witness {
            poly_store.allocate_polynomial(column);
        }
        for preprocessed in circuit.preprocessed_values() {
            poly_store.allocate_polynomial(&preprocessed);
        }

        // batch together all constraints into a single expression using a random alpha
        let zero_check_exprs = circuit.zero_check_expressions();
        let alpha = transcript.draw_field_element::<F>();
        println!("[Prover] Zero-check alpha: {:?}", alpha);

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
            ZeroCheckProof::prove(&mut poly_store, &zero_check_virtual, transcript);

        // construct a new polynomial store for the permutation check
        // this check is done on the whole trace at once, without separating the columns
        let mut poly_store2 = VirtualPolynomialStore::new(log2_rows + log2_cols);
        let witness_idx = poly_store2.allocate_polynomial(&full_witness);
        let witness_virtual = poly_store2.new_virtual_from_input(&witness_idx);

        let (permutation_check_proof, permutation_check_claim) = PermutationCheckProof::prove(
            &mut poly_store2,
            &witness_virtual,
            &witness_virtual,
            &pk.id_poly,
            &pk.permutation_poly,
            transcript,
            pcs,
        );

        // compute openings for the witness polynomial at the zero-check evaluation point
        let mut openings_zero_check = vec![];
        for col in 0..circuit.num_cols() {
            let mut point = zero_check_eval_claim.point.clone();
            for i in (0..log2_cols).rev() {
                point.push(F::from(((col >> i) & 1) as u64));
            }
            let opening = pcs.open(&full_witness, &point, transcript);
            openings_zero_check.push(opening);
        }

        // compute openings for the preprocessed columns at the zero-check evaluation point
        // this is not strictly necessary, but it saves some work to the verifier
        let preprocessed_columns = circuit.preprocessed_values();
        let mut openings_preprocessed = vec![];
        for i in 0..circuit.num_preprocessed_columns() {
            let opening = pcs.open(
                &preprocessed_columns[i],
                &zero_check_eval_claim.point,
                transcript,
            );
            openings_preprocessed.push(opening);
        }

        // compute openings for the id and permutation polynomials at the permutation check evaluation point
        let opening_id = pcs.open(&pk.id_poly, &permutation_check_claim, transcript);
        let opening_permutation =
            pcs.open(&pk.permutation_poly, &permutation_check_claim, transcript);
        let opening_permutation_trace =
            pcs.open(&full_witness, &permutation_check_claim, transcript);

        TraceProof {
            zero_check_proof,
            permutation_check_proof,
            openings_zero_check,
            openings_preprocessed,
            opening_id,
            opening_permutation,
            opening_permutation_trace,
        }
    }

    pub fn prove(
        &self,
        pcs: &PCS,
        witness_traces: &Vec<TraceWitness<F>>,
    ) -> HyperPlonkProof<F, PCS> {
        // initialize a new transcript
        let mut transcript = Transcript::new(b"hyperplonk_proof");

        // perform sanity checks and commut to the traces
        let mut trace_commitments = vec![];
        let mut full_traces = vec![];
        for (trace_witness, vk) in zip(witness_traces.iter(), self.trace_vks.iter()) {
            let witness = &trace_witness.0;
            let circuit = &vk.circuit;
            assert_eq!(
                witness.len(),
                circuit.num_cols(),
                "Witness columns length mismatch"
            );
            for col in witness {
                assert_eq!(
                    col.len(),
                    circuit.num_rows(),
                    "Witness column row length mismatch"
                );
            }

            // first of all, do a sanity check that the witness satisfies the circuit constraints
            circuit.check_constraints(witness).unwrap();

            // concatenate the witness columns into a single full witness
            let full_witness = witness.iter().flatten().cloned().collect::<Vec<F>>();

            assert_eq!(
                full_witness.len(),
                circuit.num_cols() * circuit.num_rows(),
                "Padded witness length mismatch"
            );

            // the prover commits to the full witness polynomial
            let witness_commitment = pcs.commit(&full_witness);
            transcript.append_serializable(&witness_commitment);

            trace_commitments.push(witness_commitment);
            full_traces.push(full_witness);
        }

        let mut trace_proofs = vec![];
        for i in 0..witness_traces.len() {
            let witness = &witness_traces[i].0;
            let full_witness = &full_traces[i];
            let circuit = &self.trace_vks[i].circuit;
            let pk = &self.trace_pks[i];
            let trace_proof =
                self.prove_trace(pcs, witness, full_witness, &mut transcript, &pk, &circuit);
            trace_proofs.push(trace_proof);
        }

        HyperPlonkProof {
            witness_commitment: trace_commitments,
            trace_proofs: trace_proofs,
        }
    }
}

impl<F: PrimeField, PCS: MultilinearPCS<F>> HyperPlonkProof<F, PCS> {
    fn verify_trace_proof<C: Circuit<F>>(
        &self,
        witness_commitment: &PCS::Commitment,
        vk: &TraceVK<F, PCS, C>,
        pcs: &PCS,
        proof: &TraceProof<F, PCS>,
        transcript: &mut Transcript,
    ) -> Result<(), String> {
        let alpha = transcript.draw_field_element::<F>();
        println!("[Verifier] Zero-check alpha: {:?}", alpha);

        let zero_check_eval_claim = proof.zero_check_proof.verify(transcript)?;
        let log2_cols = (vk.circuit.num_cols()).trailing_zeros() as usize;

        let id_evaluation_claim = EvaluationClaim {
            point: proof.opening_id.evaluation_point(),
            evaluation: proof.opening_id.claimed_evaluation(),
        };

        let permutation_evaluation_claim = EvaluationClaim {
            point: proof.opening_permutation.evaluation_point(),
            evaluation: proof.opening_permutation.claimed_evaluation(),
        };

        let permutation_trace_evaluation_claim = EvaluationClaim {
            point: proof.opening_permutation_trace.evaluation_point(),
            evaluation: proof.opening_permutation_trace.claimed_evaluation(),
        };

        proof.permutation_check_proof.verify(
            transcript,
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
        for (i, opening) in proof.openings_zero_check.iter().enumerate() {
            if opening.evaluation_point() != points[i] {
                return Err("Zero check opening point mismatch".to_string());
            }

            let valid = pcs.verify(&witness_commitment, opening, transcript);
            if !valid {
                return Err("Zero check opening verification failed".to_string());
            }

            col_evaluations.push(opening.claimed_evaluation());
        }

        // check preprocessed openings
        for (i, opening) in proof.openings_preprocessed.iter().enumerate() {
            if opening.evaluation_point() != zero_check_eval_claim.point {
                return Err("Preprocessed opening point mismatch".to_string());
            }

            let valid = pcs.verify(&vk.preprocessed_columns_commitments[i], opening, transcript);
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
        if proof.opening_id.evaluation_point() != permutation_trace_evaluation_claim.point {
            return Err("ID opening point mismatch".to_string());
        }
        if !pcs.verify(&vk.id_commitment, &proof.opening_id, transcript) {
            return Err("ID opening verification failed".to_string());
        }

        // verify permutation opening
        if proof.opening_permutation.evaluation_point() != permutation_trace_evaluation_claim.point
        {
            return Err("Permutation opening point mismatch".to_string());
        }
        if !pcs.verify(
            &vk.permutation_commitment,
            &proof.opening_permutation,
            transcript,
        ) {
            return Err("Permutation opening verification failed".to_string());
        }

        // verify permutation trace opening
        if proof.opening_permutation_trace.evaluation_point()
            != permutation_trace_evaluation_claim.point
        {
            return Err("Permutation trace opening point mismatch".to_string());
        }
        if !pcs.verify(
            &witness_commitment,
            &proof.opening_permutation_trace,
            transcript,
        ) {
            return Err("Permutation trace opening verification failed".to_string());
        }

        Ok(())
    }

    pub fn verify<C: Circuit<F>>(
        &self,
        vk: &HyperPlonkVK<F, PCS, C>,
        pcs: &PCS,
    ) -> Result<(), String> {
        let mut transcript = Transcript::new(b"hyperplonk_proof");

        for commitment in &self.witness_commitment {
            transcript.append_serializable(commitment);
        }

        if vk.trace_vks.len() != self.trace_proofs.len() {
            return Err("Number of trace VKS and proofs mismatch".to_string());
        }

        for i in 0..vk.trace_vks.len() {
            let witness_commitment = &self.witness_commitment[i];
            let trace_vk = &vk.trace_vks[i];
            let trace_proof = &self.trace_proofs[i];
            self.verify_trace_proof(
                witness_commitment,
                trace_vk,
                pcs,
                trace_proof,
                &mut transcript,
            )?;
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

    fn get_fibonacci_circuit_and_trace() -> (TransitionCircuit<Fr>, TraceWitness<Fr>) {
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

        let trace_witness = TraceWitness(witness.clone());
        (circuit, trace_witness)
    }

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

        let (circuit, trace_witness) = get_fibonacci_circuit_and_trace();

        let witness_traces = vec![trace_witness];

        let max_degree = circuit.num_cols().next_power_of_two() * circuit.num_rows();
        assert!(
            max_degree.is_power_of_two(),
            "Max degree must be a power of two"
        );
        println!("KZG setup...");
        let pcs = KZG::<ark_bn254::Bn254>::trusted_setup(max_degree, &mut rng);
        println!("KZG setup done.");

        let hyperplonk = HyperPlonk::preprocess(vec![circuit.clone()], &pcs);
        println!("HyperPlonk preprocessing done.");

        let proof = hyperplonk.prove(&pcs, &witness_traces);

        let vk = hyperplonk.to_vk();
        proof.verify(&vk, &pcs).unwrap();
        println!("HyperPlonk proof verified.");
    }

    #[test]
    fn test_hyperplonk_proof_multitrace() {
        let seed = [0u8; 32];
        let mut rng = rand::rngs::StdRng::from_seed(seed);

        let (circuit1, trace_witness1) = get_fibonacci_circuit_and_trace();
        let (circuit2, trace_witness2) = get_fibonacci_circuit_and_trace();

        let witness_traces = vec![trace_witness1, trace_witness2];

        let max_degree = circuit1.num_cols().next_power_of_two() * circuit1.num_rows();
        assert!(
            max_degree.is_power_of_two(),
            "Max degree must be a power of two"
        );
        println!("KZG setup...");
        let pcs = KZG::<ark_bn254::Bn254>::trusted_setup(max_degree, &mut rng);
        println!("KZG setup done.");

        let circuits = vec![circuit1.clone(), circuit2.clone()];

        let hyperplonk = HyperPlonk::preprocess(circuits, &pcs);
        println!("HyperPlonk preprocessing done.");

        let proof = hyperplonk.prove(&pcs, &witness_traces);

        let vk = hyperplonk.to_vk();
        proof.verify(&vk, &pcs).unwrap();
        println!("HyperPlonk proof verified.");
    }
}
