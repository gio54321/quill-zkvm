use crate::proof::circuit::Circuit;
use crate::{
    piops::{permutation_check::PermutationCheckProof, zerocheck::ZeroCheckProof},
    utils::virtual_polynomial::{VirtualPolyExpr, VirtualPolynomialStore},
};
use ark_ff::PrimeField;
use quill_pcs::EvaluationClaim;
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
    pub openings_public: Vec<PCS::Proof>,
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
    pub public_columns_commitments: Vec<PCS::Commitment>,
    pub id_commitment: PCS::Commitment,
    pub permutation_commitment: PCS::Commitment,
}

impl<F: PrimeField, PCS: MultilinearPCS<F>, C: Circuit<F> + Clone> Clone for TraceVK<F, PCS, C> {
    fn clone(&self) -> Self {
        TraceVK {
            circuit: self.circuit.clone(),
            public_columns_commitments: self.public_columns_commitments.clone(),
            id_commitment: self.id_commitment.clone(),
            permutation_commitment: self.permutation_commitment.clone(),
        }
    }
}

pub struct TracePK<F: PrimeField> {
    pub id_poly: Vec<F>,
    pub permutation_poly: Vec<F>,
    pub public_values: Vec<Vec<F>>,
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

        // pad the public columns to the full trace size with zeros and commit to them
        let mut public_values = circuit.public_values();
        for i in 0..public_values.len() {
            assert_eq!(
                public_values[i].len(),
                circuit.num_rows(),
                "Public column length mismatch"
            );
            public_values[i].extend(vec![F::zero(); (1 << trace_num_vars) - circuit.num_rows()]);
        }

        // TODO: make those into a single polynomial
        let public_commitments = public_values
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
            public_columns_commitments: public_commitments,
            id_commitment,
            permutation_commitment,
        };
        let pk = TracePK {
            id_poly: id_evals,
            permutation_poly: permutation_evals,
            public_values,
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

        let mut poly_store: VirtualPolynomialStore<F> = VirtualPolynomialStore::new(log2_rows);
        for column in witness {
            poly_store.allocate_polynomial(column);
        }
        for public in circuit.public_values() {
            poly_store.allocate_polynomial(&public);
        }

        // batch together all constraints into a single expression using a random alpha
        let zero_check_exprs = circuit.zero_check_expressions();
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
        // TODO: we only need to open the columns that appear in the constraints, here
        // we open also padding columns that are not used. The circuit should expose both padded
        // and unpadded num cols. For now it's ok, to keep things simple.
        let mut openings_zero_check = vec![];
        for col in 0..circuit.num_cols() {
            let mut point = zero_check_eval_claim.point.clone();
            for i in 0..log2_cols {
                point.push(F::from(((col >> i) & 1) as u64));
            }
            let opening = pcs.open(&full_witness, &point, transcript);
            openings_zero_check.push(opening);
        }

        // compute openings for the public columns at the zero-check evaluation point
        // this is not strictly necessary, but it saves some work to the verifier
        let public_columns = circuit.public_values();
        let mut openings_public = vec![];
        for i in 0..circuit.num_public_columns() {
            let opening = pcs.open(&public_columns[i], &zero_check_eval_claim.point, transcript);
            openings_public.push(opening);
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
            openings_public,
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
    fn verify_opening(
        comm: &PCS::Commitment,
        proof: &PCS::Proof,
        expected_point: Option<Vec<F>>,
        expected_num_vars: usize,
        pcs: &PCS,
        transcript: &mut Transcript,
    ) -> bool {
        if proof.point().len() != expected_num_vars {
            return false;
        }
        match expected_point {
            Some(point) => {
                if proof.point() != point {
                    return false;
                }
            }
            None => {}
        }
        pcs.verify(comm, proof, transcript)
    }

    /// Get evaluation claims for each column
    /// Verifies that the point matches the zero-check returned evaluation point
    /// Returns the evaluations of each column (both witness and public) in order
    fn get_and_verify_column_evaluations(
        &self,
        vk: &TraceVK<F, PCS, impl Circuit<F>>,
        pcs: &PCS,
        proof: &TraceProof<F, PCS>,
        witness_commitment: &PCS::Commitment,
        zero_check_reconstructed_eval_claim: &EvaluationClaim<F>,
        log2_cols: usize,
        log2_rows: usize,
        transcript: &mut Transcript,
    ) -> Result<Vec<F>, String> {
        if zero_check_reconstructed_eval_claim.point.len() != log2_rows {
            return Err("Zero check evaluation claim point length mismatch".to_string());
        }

        let mut points = vec![];
        for col in 0..vk.circuit.num_cols() {
            let mut point = zero_check_reconstructed_eval_claim.point.clone();
            for i in 0..log2_cols {
                point.push(F::from(((col >> i) & 1) as u64));
            }
            points.push(point);
        }

        // verify zero check openings
        let mut col_evaluations = vec![];
        for (i, opening) in proof.openings_zero_check.iter().enumerate() {
            if opening.point() != points[i] {
                return Err("Zero check opening point mismatch".to_string());
            }

            let valid = pcs.verify(&witness_commitment, opening, transcript);
            if !valid {
                return Err("Zero check opening verification failed".to_string());
            }

            col_evaluations.push(opening.evaluation());
        }

        // check public columns openings
        for (i, proof) in proof.openings_public.iter().enumerate() {
            if !Self::verify_opening(
                &vk.public_columns_commitments[i],
                proof,
                Some(zero_check_reconstructed_eval_claim.point.clone()),
                log2_rows,
                pcs,
                transcript,
            ) {
                return Err("Public opening verification failed".to_string());
            }
            col_evaluations.push(proof.evaluation());
        }

        Ok(col_evaluations)
    }

    fn recover_zerocheck_expr_evaluation(
        &self,
        vk: &TraceVK<F, PCS, impl Circuit<F>>,
        col_evaluations: &Vec<F>,
        alpha: F,
    ) -> F {
        let mut recomputed_zero_check_evaluation = F::zero();
        let alpha_powers = (0..vk.circuit.zero_check_expressions().len())
            .map(|i| alpha.pow(&[i as u64]))
            .collect::<Vec<F>>();
        for (expr, alpha) in zip(vk.circuit.zero_check_expressions(), alpha_powers) {
            let eval = expr.evaluate(&col_evaluations);
            recomputed_zero_check_evaluation += alpha * eval;
        }
        recomputed_zero_check_evaluation
    }

    fn verify_trace_proof<C: Circuit<F>>(
        &self,
        witness_commitment: &PCS::Commitment,
        vk: &TraceVK<F, PCS, C>,
        pcs: &PCS,
        proof: &TraceProof<F, PCS>,
        transcript: &mut Transcript,
    ) -> Result<(), String> {
        let alpha = transcript.draw_field_element::<F>();

        let zero_check_reconstructed_eval_claim = proof.zero_check_proof.verify(transcript)?;
        let log2_cols = (vk.circuit.num_cols()).trailing_zeros() as usize;
        let log2_rows = (vk.circuit.num_rows()).trailing_zeros() as usize;

        // ensure that the sumcheck is applied to the correct number of variables
        if zero_check_reconstructed_eval_claim.point.len() != log2_rows {
            return Err("Zero check evaluation claim point length mismatch".to_string());
        }

        let id_evaluation_claim = proof.opening_id.evaluation_claim();
        let permutation_evaluation_claim = proof.opening_permutation.evaluation_claim();
        let permutation_trace_evaluation_claim = proof.opening_permutation_trace.evaluation_claim();

        proof.permutation_check_proof.verify(
            transcript,
            &pcs,
            permutation_trace_evaluation_claim.clone(),
            permutation_trace_evaluation_claim.clone(),
            id_evaluation_claim.clone(),
            permutation_evaluation_claim.clone(),
        )?;

        let col_evaluations = self.get_and_verify_column_evaluations(
            vk,
            pcs,
            proof,
            witness_commitment,
            &zero_check_reconstructed_eval_claim,
            log2_cols,
            log2_rows,
            transcript,
        )?;

        let recomputed_zero_check_evaluation =
            self.recover_zerocheck_expr_evaluation(vk, &col_evaluations, alpha);

        if recomputed_zero_check_evaluation != zero_check_reconstructed_eval_claim.evaluation {
            return Err("Zero check evaluation mismatch".to_string());
        }

        // verify id opening
        if !Self::verify_opening(
            &vk.id_commitment,
            &proof.opening_id,
            None, // point already checked in permutation check
            log2_rows + log2_cols,
            pcs,
            transcript,
        ) {
            return Err("ID commitment opening verification failed".to_string());
        }

        // verify permutation opening
        if !Self::verify_opening(
            &vk.permutation_commitment,
            &proof.opening_permutation,
            None, // point already checked in permutation check
            log2_rows + log2_cols,
            pcs,
            transcript,
        ) {
            return Err("Permutation commitment opening verification failed".to_string());
        }

        // verify permutation trace opening
        if !Self::verify_opening(
            &witness_commitment,
            &proof.opening_permutation_trace,
            None, // point already checked in permutation check
            log2_rows + log2_cols,
            pcs,
            transcript,
        ) {
            return Err("Permutation trace commitment opening verification failed".to_string());
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
