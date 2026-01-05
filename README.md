# Quill zkvm
> Building a zkvm from scratch is easy, actually

Quill is a zkvm implemented from scratch in Rust. The only dependencies are arkworks finite fields, polynomials and pairings, everything else is homegrown.

## Roadmap

- **Polynomial commitment scheme**
  - [x] Univariate PCS based on KZG
  - [x] IPA proof on top of a univariate PCS
  - [x] Multilinear PCS based on IPA
  - [ ] Degree check for Multilinear PCS, enforcing arbitrary degree bounds
  - [ ] Linear time prover for Multilinear PCS (see [this paper](https://eprint.iacr.org/2025/385))
  - [ ] Batch openings for Multilinear PCS
  - [ ] Jagged PCS adaptor on top of Multilinear PCS

- **Core proof system**
  - [x] Sumcheck linear-time prover and verifier
  - [x] Zero-check protocol
  - [x] Multiset equality protocol, this differs from the one in [HyperPlonk](https://eprint.iacr.org/2022/1355) as we do not use a grand produc argument, but it is entirely Logup-based.
  - [ ] Logup-GKR for avoiding the commitment of the quotient polynomials during multiset equality
  - [x] HyperPlonk proof system
  - [ ] Public inputs
  - [ ] Multi-table proof system
  - [ ] Cross-table lookups (using logup)
  - [ ] More sumcheck batching

- **Circuit builder interface**
  - [x] Basic builder for a "transition" circuit, with copy constraints for the state
  - [ ] Circuit builder for an "every row" circuit, without copy constraints; useful for precompiles
  - [ ] More friendly API for witness generation
  - [ ] Higher level abstractions for common operations

- **VM circuits**
  - [ ] Basic vm state transition circuit (ISA?)
  - [ ] Read-write memory using offline memory checking
  - [ ] Syscalls for public memory claims
  - [ ] Precompiles for common arithmetic operations
