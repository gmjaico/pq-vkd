//! Fiat-Shamir transcript for DeepFold

use ark_ff::{PrimeField, Zero};

use crate::{Field, Parameters, field};

pub struct Transcript {
    state: blake3::Hasher,
    counter: u64,
}

impl Transcript {
    pub fn new(label: &'static [u8]) -> Self {
        let mut state = blake3::Hasher::new();
        state.update(b"deepfold-pcs/v1/transcript");
        state.update(&(label.len() as u64).to_le_bytes());
        state.update(label);
        Self { state, counter: 0 }
    }

    pub fn append_bytes(&mut self, label: &'static [u8], value: &[u8]) {
        self.state.update(&(label.len() as u64).to_le_bytes());
        self.state.update(label);
        self.state.update(&(value.len() as u64).to_le_bytes());
        self.state.update(value);
    }

    pub fn append_field(&mut self, label: &'static [u8], value: &Field) {
        self.append_bytes(label, &field::encode(value));
    }

    pub fn append_parameters(&mut self, parameters: &Parameters) {
        self.append_bytes(b"num-vars", &(parameters.num_vars as u64).to_le_bytes());
        self.append_bytes(b"log-blowup", &(parameters.log_blowup as u64).to_le_bytes());
        self.append_bytes(
            b"num-queries",
            &(parameters.num_queries as u64).to_le_bytes(),
        );
        self.append_bytes(
            b"security-bits",
            &(parameters.security_bits as u64).to_le_bytes(),
        );
    }

    pub fn challenge_field(&mut self, label: &'static [u8]) -> Field {
        loop {
            let mut reader = self.challenge_reader(label);
            let mut bytes = [0u8; 64];
            reader.fill(&mut bytes);
            let challenge = Field::from_le_bytes_mod_order(&bytes);
            if !challenge.is_zero() {
                self.append_field(b"challenge", &challenge);
                return challenge;
            }
        }
    }

    pub fn challenge_index(&mut self, label: &'static [u8], upper: usize) -> usize {
        let mut reader = self.challenge_reader(label);
        let mut bytes = [0u8; 8];
        reader.fill(&mut bytes);
        let index = (u64::from_le_bytes(bytes) as usize) % upper;
        self.append_bytes(b"index", &(index as u64).to_le_bytes());
        index
    }

    fn challenge_reader(&mut self, label: &'static [u8]) -> blake3::OutputReader {
        let counter = self.counter;
        self.counter += 1;
        let mut challenge_state = self.state.clone();
        challenge_state.update(b"challenge-request");
        challenge_state.update(&(label.len() as u64).to_le_bytes());
        challenge_state.update(label);
        challenge_state.update(&counter.to_le_bytes());
        challenge_state.finalize_xof()
    }
}
