use ark_bn254;
use ark_bn254::Fr;
use ark_ff::UniformRand;
use ark_std::test_rng;
use ark_std::Zero;
use quill_hyperplonk::frontend::transition_circuit::TransitionCircuit;
use quill_hyperplonk::proof::circuit::Circuit;
use quill_hyperplonk::proof::proof::HyperPlonk;
use quill_hyperplonk::proof::proof::TraceWitness;
use quill_hyperplonk::utils::virtual_polynomial::VirtualPolyExpr;
use quill_pcs::kzg::KZG;
use quill_pcs::MultilinearPCS;
use quill_pcs::MultilinearPCSProof;
use quill_transcript::transcript::Transcript;
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
    let mut witness: Vec<Vec<Fr>> = vec![vec![Fr::zero(); circuit.num_rows()]; circuit.num_cols()];
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

fn get_modified_fibonacci_circuit_and_trace() -> (TransitionCircuit<Fr>, TraceWitness<Fr>) {
    // yet another fibonacci-style circuit, but some more constraints
    // compute f(0) = 1, f(1) = 1, f(n) = f(n-1) + f(n-1) * f(n-2)

    let mut circuit: TransitionCircuit<Fr> = TransitionCircuit::new(8);
    let state1 = circuit.allocate_state_cell();
    let state2 = circuit.allocate_state_cell();
    let tmp = circuit.allocate_witness_cell();
    circuit.enforce_boundary_constraint(
        0,
        state1.current.to_expr() - VirtualPolyExpr::Const(Fr::from(1u64)),
    );
    circuit.enforce_boundary_constraint(
        0,
        state2.current.to_expr() - VirtualPolyExpr::Const(Fr::from(1u64)),
    );

    // tmp = state1.current * state2.current
    circuit.enforce_constraint(tmp.to_expr() - state1.current.to_expr() * state2.current.to_expr());

    // state2.next = state1.current + tmp
    circuit.enforce_constraint(state2.next.to_expr() - (state1.current.to_expr() + tmp.to_expr()));

    // state1.next = state2.current
    circuit.enforce_constraint(state1.next.to_expr() - state2.current.to_expr());

    let mut witness: Vec<Vec<Fr>> = vec![vec![Fr::zero(); circuit.num_rows()]; circuit.num_cols()];
    for row in 0..circuit.num_rows() {
        if row == 0 {
            witness[state1.current.col][row] = Fr::from(1u64);
            witness[state2.current.col][row] = Fr::from(1u64);
        } else {
            witness[state1.current.col][row] = witness[state1.next.col][row - 1];
            witness[state2.current.col][row] = witness[state2.next.col][row - 1];
        }
        witness[state1.next.col][row] = witness[state2.current.col][row];
        witness[tmp.col][row] = witness[state1.current.col][row] * witness[state2.current.col][row];
        witness[state2.next.col][row] = witness[state1.current.col][row] + witness[tmp.col][row];
    }

    // print the trace
    for row in 0..circuit.num_rows() {
        let mut row_vals = vec![];
        for col in 0..circuit.num_cols() {
            row_vals.push(witness[col][row]);
        }
        println!("Row {}: {:?}", row, row_vals);
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
        proof.point(),
        proof.evaluation()
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
    let (circuit2, trace_witness2) = get_modified_fibonacci_circuit_and_trace();

    let witness_traces = vec![trace_witness1, trace_witness2];

    let max_degree1 = circuit1.num_cols().next_power_of_two() * circuit1.num_rows();
    let max_degree2 = circuit2.num_cols().next_power_of_two() * circuit2.num_rows();
    let max_degree = std::cmp::max(max_degree1, max_degree2);
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
