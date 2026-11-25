//! Byte encoding of an opening proof, used to measure proof sizes,
//! useful for benchmarking and results, which is used in the report

use crate::crypto::merkle::Digest;
use crate::pcs::deepfold::prover::OpeningProof;
use crate::{Field, field};

/// bytes per part of an encoded proof, for the size breakdown tables
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ProofSizeBreakdown {
    pub deep_folding_message_bytes: usize,
    pub merkle_leaf_value_bytes: usize,
    pub merkle_authentication_bytes: usize,
    pub intermediate_root_bytes: usize,
    pub metadata_bytes: usize,
}

impl ProofSizeBreakdown {
    pub fn field_element_bytes(&self) -> usize {
        self.deep_folding_message_bytes + self.merkle_leaf_value_bytes
    }

    pub fn total_bytes(&self) -> usize {
        self.deep_folding_message_bytes
            + self.merkle_leaf_value_bytes
            + self.merkle_authentication_bytes
            + self.intermediate_root_bytes
            + self.metadata_bytes
    }
}

impl OpeningProof {
    /// bytes we report as proof size, commitment and point
    /// are not included because the verifier already has them
    pub fn to_bytes(&self, claimed_value: Field) -> Vec<u8> {
        self.to_bytes_with_breakdown(claimed_value).0
    }

    pub fn to_bytes_with_breakdown(&self, claimed_value: Field) -> (Vec<u8>, ProofSizeBreakdown) {
        let mut encoder = ProofEncoder::default();
        encoder.deep_field(&claimed_value);

        encoder.length(self.rounds.len());
        for round in &self.rounds {
            encoder.length(round.lines.len());
            for (at_zero, at_one) in &round.lines {
                encoder.deep_field(at_zero);
                encoder.deep_field(at_one);
            }
            match round.next_root {
                Some(root) => {
                    encoder.metadata(&[1]);
                    encoder.root(&root);
                }
                None => encoder.metadata(&[0]),
            }
        }
        encoder.deep_field(&self.final_value);

        encoder.length(self.queries.len());
        for round in &self.queries {
            encoder.length(round.leaves.len());
            for leaf in &round.leaves {
                encoder.metadata(
                    &u64::try_from(leaf.index)
                        .expect("Merkle leaf index exceeds u64::MAX")
                        .to_le_bytes(),
                );
                encoder.leaf_field(&leaf.positive);
                encoder.leaf_field(&leaf.negative);
            }
            encoder.length(round.authentication.siblings.len());
            for digest in &round.authentication.siblings {
                encoder.authentication(digest);
            }
        }

        debug_assert_eq!(encoder.bytes.len(), encoder.breakdown.total_bytes());
        (encoder.bytes, encoder.breakdown)
    }
}

#[derive(Default)]
struct ProofEncoder {
    bytes: Vec<u8>,
    breakdown: ProofSizeBreakdown,
}

impl ProofEncoder {
    fn length(&mut self, len: usize) {
        let len = u32::try_from(len).expect("proof collection length exceeds u32::MAX");
        self.metadata(&len.to_le_bytes());
    }

    fn deep_field(&mut self, value: &Field) {
        let encoded = field::encode_array(value);
        self.bytes.extend_from_slice(&encoded);
        self.breakdown.deep_folding_message_bytes += encoded.len();
    }

    fn leaf_field(&mut self, value: &Field) {
        let encoded = field::encode_array(value);
        self.bytes.extend_from_slice(&encoded);
        self.breakdown.merkle_leaf_value_bytes += encoded.len();
    }

    fn authentication(&mut self, digest: &Digest) {
        self.bytes.extend_from_slice(digest);
        self.breakdown.merkle_authentication_bytes += digest.len();
    }

    fn root(&mut self, digest: &Digest) {
        self.bytes.extend_from_slice(digest);
        self.breakdown.intermediate_root_bytes += digest.len();
    }

    fn metadata(&mut self, value: &[u8]) {
        self.bytes.extend_from_slice(value);
        self.breakdown.metadata_bytes += value.len();
    }
}
