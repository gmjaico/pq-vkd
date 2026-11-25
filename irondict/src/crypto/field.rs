//! The field used by DeepFold and the protocol, and its 32-byte encoding

use ark_bls12_381::Fr;
use ark_serialize::CanonicalSerialize;

pub const FIELD_BYTES: usize = 32;

/// DeepFold (Value and Randomizer) works over the BLS12-381 scalar field
pub type Field = Fr;

pub fn encode(value: &Field) -> Vec<u8> {
    encode_array(value).to_vec()
}

pub fn encode_array(value: &Field) -> [u8; FIELD_BYTES] {
    let mut bytes = [0; FIELD_BYTES];
    value
        .serialize_compressed(&mut bytes[..])
        .expect("serializing into a fixed-size field buffer cannot fail");
    bytes
}
