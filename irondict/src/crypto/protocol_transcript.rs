use ark_ff::{PrimeField, Zero};

use crate::{Field, field};

/// Fiat-Shamir transcript for protocol-level statements (separate from the DeepFold transcript)
pub struct ProtocolTranscript {
    state: blake3::Hasher,
    counter: u64,
}

impl ProtocolTranscript {
    pub fn new(domain: &[u8]) -> Self {
        let mut state = blake3::Hasher::new();
        append(&mut state, b"protocol", b"irondict-deepfold-poc/v1");
        append(&mut state, b"domain", domain);
        Self { state, counter: 0 }
    }

    pub fn append_bytes(&mut self, label: &[u8], value: &[u8]) {
        append(&mut self.state, label, value);
    }

    pub fn append_u64(&mut self, label: &[u8], value: u64) {
        self.append_bytes(label, &value.to_le_bytes());
    }

    pub fn append_field(&mut self, label: &[u8], value: &Field) {
        self.append_bytes(label, &field::encode_array(value));
    }

    pub fn challenge_field(&mut self, label: &[u8]) -> Field {
        loop {
            let mut challenge = self.state.clone();
            append(&mut challenge, b"challenge-label", label);
            challenge.update(&self.counter.to_le_bytes());
            self.counter += 1;
            let mut wide = [0u8; 64];
            challenge.finalize_xof().fill(&mut wide);
            let value = Field::from_le_bytes_mod_order(&wide);
            if !value.is_zero() {
                self.append_field(b"derived-challenge", &value);
                return value;
            }
        }
    }

    pub fn challenge_fields(&mut self, label: &[u8], count: usize) -> Vec<Field> {
        (0..count).map(|_| self.challenge_field(label)).collect()
    }

    pub fn digest(&self) -> [u8; 32] {
        self.state.finalize().into()
    }
}

pub fn hash_to_nonzero_field(domain: &[u8], input: &[u8]) -> Field {
    let mut transcript = ProtocolTranscript::new(b"hash-to-field");
    transcript.append_bytes(b"subdomain", domain);
    transcript.append_bytes(b"input", input);
    transcript.challenge_field(b"output")
}

fn append(hasher: &mut blake3::Hasher, label: &[u8], value: &[u8]) {
    hasher.update(&(label.len() as u64).to_le_bytes());
    hasher.update(label);
    hasher.update(&(value.len() as u64).to_le_bytes());
    hasher.update(value);
}
