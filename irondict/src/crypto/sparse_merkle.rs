//! Sparse Merkle tree for the Index (which slot holds which label),
//! depth is n, one leaf per slot, only the non-empty part is stored

use std::collections::{BTreeMap, HashMap};

use crate::crypto::index_hash::{DIGEST_ZERO, encode_digest, h_leaf, h_node};
pub use crate::crypto::index_hash::{Digest, DigestBytes, label_identifier};
use crate::{Error, Result};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IndexLeaf {
    Empty,
    Occupied(Digest),
}

impl IndexLeaf {
    pub fn hash(&self) -> Digest {
        match self {
            Self::Empty => DIGEST_ZERO,
            Self::Occupied(identifier) => h_leaf(identifier),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// Path for one slot, the leaf and its n siblings
pub struct MerkleProof {
    pub slot: usize,
    pub leaf: IndexLeaf,
    pub siblings: Vec<Digest>,
}

impl MerkleProof {
    pub fn encoded_len(&self) -> usize {
        self.to_bytes().len()
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&(self.slot as u64).to_le_bytes());
        match &self.leaf {
            IndexLeaf::Empty => out.push(0),
            IndexLeaf::Occupied(identifier) => {
                out.push(1);
                out.extend_from_slice(&encode_digest(identifier));
            }
        }
        out.extend_from_slice(&(self.siblings.len() as u32).to_le_bytes());
        for sibling in &self.siblings {
            out.extend_from_slice(&encode_digest(sibling));
        }
        out
    }

    pub fn root(&self, depth: usize) -> Result<Digest> {
        path_root(depth, self.slot, self.leaf.hash(), &self.siblings)
    }

    pub fn verify(&self, depth: usize, expected_root: &DigestBytes) -> Result<()> {
        if encode_digest(&self.root(depth)?) != *expected_root {
            return Err(Error::VerificationFailed(
                "invalid sparse Merkle authentication path",
            ));
        }
        Ok(())
    }
}

pub fn path_root(depth: usize, slot: usize, leaf: Digest, siblings: &[Digest]) -> Result<Digest> {
    check_slot(depth, slot)?;
    if siblings.len() != depth {
        return Err(Error::MalformedProof("incorrect sparse Merkle path length"));
    }
    let mut digest = leaf;
    for (level, sibling) in siblings.iter().enumerate() {
        digest = if (slot >> level) & 1 == 0 {
            h_node(&digest, sibling)
        } else {
            h_node(sibling, &digest)
        };
    }
    Ok(digest)
}

#[derive(Clone, Debug)]
pub struct SparseMerkleTree {
    depth: usize,
    defaults: Vec<Digest>,
    // Only nodes that differ from the empty-subtree hash, keyed by (level, index)
    nodes: HashMap<(usize, usize), Digest>,
    leaves: BTreeMap<usize, Digest>,
}

impl SparseMerkleTree {
    pub fn new(depth: usize) -> Result<Self> {
        if depth == 0 || depth > crate::Parameters::MAX_NUM_VARS {
            return Err(Error::InvalidParameters(
                "sparse Merkle depth must be in 1..=MAX_NUM_VARS",
            ));
        }
        Ok(Self {
            depth,
            defaults: default_hashes(depth),
            nodes: HashMap::new(),
            leaves: BTreeMap::new(),
        })
    }

    pub fn root(&self) -> DigestBytes {
        encode_digest(&self.root_digest())
    }
    pub fn root_digest(&self) -> Digest {
        self.node(self.depth, 0)
    }
    pub fn empty_root(depth: usize) -> Result<DigestBytes> {
        Ok(Self::new(depth)?.root())
    }

    pub fn proof(&self, slot: usize) -> Result<MerkleProof> {
        check_slot(self.depth, slot)?;
        let leaf = self
            .leaves
            .get(&slot)
            .copied()
            .map_or(IndexLeaf::Empty, IndexLeaf::Occupied);
        let siblings = (0..self.depth)
            .map(|level| self.node(level, (slot >> level) ^ 1))
            .collect();
        Ok(MerkleProof {
            slot,
            leaf,
            siblings,
        })
    }
    /// Put a label in an empty slot and update the path to the root, returns
    /// the path from before the insert, which is what the STARK needs
    pub fn insert(&mut self, slot: usize, label: &[u8]) -> Result<MerkleProof> {
        check_slot(self.depth, slot)?;
        if label.is_empty() {
            return Err(Error::InvalidInput("Index labels must not be empty"));
        }
        if self.leaves.contains_key(&slot) {
            return Err(Error::InvalidState(
                "cannot overwrite an occupied Index leaf",
            ));
        }
        let witness = self.proof(slot)?;
        let identifier = label_identifier(label);
        self.leaves.insert(slot, identifier);
        let mut digest = h_leaf(&identifier);
        self.set_node(0, slot, digest);
        for level in 0..self.depth {
            let node_index = slot >> level;
            let sibling = self.node(level, node_index ^ 1);
            digest = if node_index & 1 == 0 {
                h_node(&digest, &sibling)
            } else {
                h_node(&sibling, &digest)
            };
            self.set_node(level + 1, node_index >> 1, digest);
        }
        Ok(witness)
    }
    pub fn retained_bytes(&self) -> usize {
        self.nodes.len() * (2 * std::mem::size_of::<usize>() + 32)
            + self.leaves.len() * (std::mem::size_of::<usize>() + 32)
            + self.defaults.len() * 32
    }
    fn node(&self, level: usize, index: usize) -> Digest {
        self.nodes
            .get(&(level, index))
            .copied()
            .unwrap_or(self.defaults[level])
    }
    fn set_node(&mut self, level: usize, index: usize, digest: Digest) {
        if digest == self.defaults[level] {
            self.nodes.remove(&(level, index));
        } else {
            self.nodes.insert((level, index), digest);
        }
    }
}

/// root for empty subtree
pub fn default_hashes(depth: usize) -> Vec<Digest> {
    let mut defaults = Vec::with_capacity(depth + 1);
    defaults.push(DIGEST_ZERO);
    for level in 0..depth {
        defaults.push(h_node(&defaults[level], &defaults[level]));
    }
    defaults
}

fn check_slot(depth: usize, slot: usize) -> Result<()> {
    if depth >= usize::BITS as usize || slot >= (1usize << depth) {
        return Err(Error::InvalidInput("Index slot is out of range"));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::PrimeCharacteristicRing;

    #[test]
    fn insert_and_verify_paths() {
        let mut tree = SparseMerkleTree::new(4).unwrap();
        let empty = tree.root();
        assert_eq!(empty, SparseMerkleTree::empty_root(4).unwrap());
        let proof = tree.proof(5).unwrap();
        proof.verify(4, &empty).unwrap();

        tree.insert(5, b"alice").unwrap();
        assert_ne!(tree.root(), empty);
        let proof = tree.proof(5).unwrap();
        proof.verify(4, &tree.root()).unwrap();
        assert!(tree.insert(5, b"bob").is_err());

        tree.insert(13, b"bob").unwrap();
        let mut forged = tree.proof(13).unwrap();
        forged.siblings[0][0] += crate::crypto::index_hash::F::ONE;
        assert!(forged.verify(4, &tree.root()).is_err());
        assert!(tree.proof(16).is_err());
    }

    #[test]
    fn path_order_and_tampering() {
        let mut tree = SparseMerkleTree::new(3).unwrap();
        tree.insert(0, b"zero").unwrap();
        tree.insert(1, b"one").unwrap();
        tree.insert(4, b"four").unwrap();
        let root = tree.root();
        for slot in 0..8 {
            tree.proof(slot).unwrap().verify(3, &root).unwrap();
        }
        let proof = tree.proof(4).unwrap();
        let slot_five = tree.proof(5).unwrap();
        assert_eq!(proof.siblings[0], slot_five.leaf.hash());
        assert_eq!(slot_five.leaf.hash(), DIGEST_ZERO);
        let mut wrong_leaf = proof.clone();
        wrong_leaf.leaf = IndexLeaf::Occupied(label_identifier(b"other"));
        assert!(wrong_leaf.verify(3, &root).is_err());
        let mut wrong_slot = proof.clone();
        wrong_slot.slot = 5;
        assert!(wrong_slot.verify(3, &root).is_err());
        let mut short = proof.clone();
        short.siblings.pop();
        assert!(short.verify(3, &root).is_err());
        let mut wrong_root = root;
        wrong_root[0] ^= 1;
        assert!(proof.verify(3, &wrong_root).is_err());
    }

    #[test]
    fn default_hashes_are_consistent() {
        let defaults = default_hashes(3);
        assert_eq!(defaults[0], DIGEST_ZERO);
        assert_eq!(defaults[1], h_node(&DIGEST_ZERO, &DIGEST_ZERO));
        assert_eq!(SparseMerkleTree::new(3).unwrap().root_digest(), defaults[3]);
    }
}
