use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use blake3::Hasher;

pub struct Transcript {
    pub domain: Vec<u8>,
    pub state: Vec<u8>,
}

// TODO: add domain separation and proper Fiat-Shamir implementation.
// This should be ok for now, but has some pitfalls if not used carefully.

impl Transcript {
    pub fn new(domain: &[u8]) -> Self {
        let mut hasher = Hasher::new();
        hasher.update(domain);

        Transcript {
            domain: domain.to_vec(),
            state: hasher.finalize().as_bytes().to_vec(),
        }
    }

    /// Append a message to the transcript
    pub fn append_bytes(&mut self, message: &[u8]) {
        let mut hasher = Hasher::new();
        hasher.update(&self.state);
        hasher.update(message);

        self.state = hasher.finalize().as_bytes().to_vec();
    }

    pub fn append_serializable<T: CanonicalSerialize>(&mut self, obj: &T) {
        let mut bytes = vec![];
        obj.serialize_uncompressed(&mut bytes).unwrap();
        self.append_bytes(&bytes);
    }

    pub fn append_serializables<T: CanonicalSerialize>(&mut self, objs: &[T]) {
        let mut bytes = vec![];
        for obj in objs {
            obj.serialize_uncompressed(&mut bytes).unwrap();
        }
        self.append_bytes(&bytes);
    }

    /// Draw `n` bytes of challenge from the transcript
    pub fn draw_challenge(&mut self, n: usize) -> Vec<u8> {
        let mut challenge_drawer = Hasher::new();
        challenge_drawer.update(&self.state);
        challenge_drawer.update(b"challenge");

        let mut output_reader = challenge_drawer.finalize_xof();
        let mut challenge = vec![0u8; n];
        output_reader.fill(&mut challenge);

        // TODO: there are more efficient ways of incorporating
        // the challenge back into the transcript state.
        self.append_bytes(&challenge);

        challenge
    }

    /// Draw a random field element from the transcript
    ///
    /// NOTE: this function samples a distribution at least 2^-128-close to the uniform distribution
    /// over the field (assuming that the bytes drawn by the transcript are uniform)
    /// by reducing a uniform integer that has at least field modulus bits + 128 bits.
    /// An alternative approach would be to use rejection sampling to get exact uniformity.
    pub fn draw_field_element<F: PrimeField>(&mut self) -> F {
        let num_bytes = (F::MODULUS_BIT_SIZE + 128 + 7) / 8;
        let bytes = self.draw_challenge(num_bytes as usize);
        F::from_le_bytes_mod_order(&bytes)
    }
}
