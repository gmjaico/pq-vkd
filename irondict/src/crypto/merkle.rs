//! Merkle tree and multiproofs for DeepFold codewords

use crate::{Error, Field, Result, field};
use rayon::prelude::*;

pub type Digest = [u8; 32];

#[derive(Clone, Debug, Default, PartialEq, Eq)]
/// Sibling nodes needed to recompute the root from several opened leaves
pub struct MerkleMultiProof {
    pub siblings: Vec<Digest>,
}

#[derive(Clone)]
/// BLAKE3 Merkle tree over a DeepFold codeword, the bottom cutoff levels are not stored and
/// get recomputed from the codeword when a leaf is opened, which saves memory for big codewords
pub struct MerkleTree {
    leaf_count: usize,
    cutoff: usize,
    levels: Vec<Vec<Digest>>,
}

impl MerkleTree {
    const DEFAULT_CUTOFF: usize = 2;

    /// Builds the paired-leaf tree on the current Rayon pool (prover side only)
    pub fn from_field_pairs_parallel(codeword: &[Field]) -> Result<Self> {
        Self::from_field_pairs_with_cutoff_impl(codeword, Self::DEFAULT_CUTOFF, true)
    }

    fn from_field_pairs_with_cutoff_impl(
        codeword: &[Field],
        requested_cutoff: usize,
        parallel: bool,
    ) -> Result<Self> {
        if codeword.len() < 2 || !codeword.len().is_power_of_two() {
            return Err(Error::InvalidParameters(
                "paired Merkle codeword length must be a power of two of at least two",
            ));
        }
        let leaf_count = codeword.len() / 2;
        Self::from_leaf_hasher(leaf_count, requested_cutoff, parallel, |index| {
            paired_field_leaf_digest(index, &codeword[index], &codeword[index + leaf_count])
        })
    }

    fn from_leaf_hasher(
        leaf_count: usize,
        requested_cutoff: usize,
        parallel: bool,
        leaf_digest: impl Fn(usize) -> Digest + Sync,
    ) -> Result<Self> {
        let cutoff = requested_cutoff.min(leaf_count.ilog2() as usize);
        let block_size = 1usize << cutoff;
        // Small trees (late folding rounds) are faster built without rayon
        const PARALLEL_MIN_LEAVES: usize = 8192;
        let block_count = leaf_count / block_size;
        let first = if parallel && leaf_count >= PARALLEL_MIN_LEAVES {
            (0..block_count)
                .into_par_iter()
                .map(|block| subtree_root_from_hasher(block * block_size, block_size, &leaf_digest))
                .collect::<Vec<_>>()
        } else {
            (0..block_count)
                .map(|block| subtree_root_from_hasher(block * block_size, block_size, &leaf_digest))
                .collect::<Vec<_>>()
        };
        let mut levels = vec![first];
        while levels.last().map_or(0, Vec::len) > 1 {
            let previous = levels.last().expect("a level exists");
            let next = if parallel && previous.len() >= PARALLEL_MIN_LEAVES {
                previous
                    .par_chunks_exact(2)
                    .map(|pair| hash_node(&pair[0], &pair[1]))
                    .collect()
            } else {
                previous
                    .chunks_exact(2)
                    .map(|pair| hash_node(&pair[0], &pair[1]))
                    .collect()
            };
            levels.push(next);
        }
        Ok(Self {
            leaf_count,
            cutoff,
            levels,
        })
    }

    pub fn root(&self) -> Digest {
        self.levels.last().expect("tree has a root")[0]
    }

    pub fn open_multi_pairs(
        &self,
        codeword: &[Field],
        requested_indices: &[usize],
    ) -> Result<MerkleMultiProof> {
        if codeword.len() / 2 != self.leaf_count
            || codeword.len() < 2
            || !codeword.len().is_power_of_two()
        {
            return Err(Error::InconsistentProverData);
        }
        let half = codeword.len() / 2;
        self.open_multi_with(requested_indices, |index| {
            paired_field_leaf_digest(index, &codeword[index], &codeword[index + half])
        })
    }

    fn open_multi_with(
        &self,
        requested_indices: &[usize],
        leaf_digest: impl Fn(usize) -> Digest,
    ) -> Result<MerkleMultiProof> {
        let mut indices = requested_indices.to_vec();
        indices.sort_unstable();
        indices.dedup();
        if indices.is_empty() || indices.iter().any(|index| *index >= self.leaf_count) {
            return Err(Error::MalformedProof(
                "Merkle multiproof index out of range",
            ));
        }

        let height = self.leaf_count.ilog2() as usize;
        let mut siblings = Vec::new();
        for level in 0..height {
            let mut next = Vec::with_capacity(indices.len().div_ceil(2));
            let mut position = 0;
            while position < indices.len() {
                let index = indices[position];
                if index & 1 == 0
                    && position + 1 < indices.len()
                    && indices[position + 1] == index + 1
                {
                    position += 2;
                } else {
                    siblings.push(self.node_digest(level, index ^ 1, &leaf_digest)?);
                    position += 1;
                }
                let parent = index >> 1;
                if next.last().copied() != Some(parent) {
                    next.push(parent);
                }
            }
            indices = next;
        }
        Ok(MerkleMultiProof { siblings })
    }

    fn node_digest(
        &self,
        level: usize,
        index: usize,
        leaf_digest: &impl Fn(usize) -> Digest,
    ) -> Result<Digest> {
        if level >= self.cutoff {
            return self
                .levels
                .get(level - self.cutoff)
                .and_then(|nodes| nodes.get(index))
                .copied()
                .ok_or(Error::InconsistentProverData);
        }

        let width = 1usize << level;
        let start = index
            .checked_mul(width)
            .ok_or(Error::InconsistentProverData)?;
        if start + width > self.leaf_count {
            return Err(Error::InconsistentProverData);
        }
        Ok(subtree_root_from_hasher(start, width, leaf_digest))
    }

    pub fn retained_bytes(&self) -> usize {
        self.levels.iter().map(Vec::len).sum::<usize>() * std::mem::size_of::<Digest>()
    }
}

/// Recompute the root from the opened (index, leaf hash) pairs and the siblings
pub fn verify_multi(
    root: &Digest,
    leaf_count: usize,
    opened_leaves: &[(usize, Digest)],
    proof: &MerkleMultiProof,
) -> bool {
    if leaf_count == 0
        || !leaf_count.is_power_of_two()
        || opened_leaves.is_empty()
        || opened_leaves.iter().any(|(index, _)| *index >= leaf_count)
        || opened_leaves.windows(2).any(|pair| pair[0].0 >= pair[1].0)
    {
        return false;
    }

    let height = leaf_count.ilog2() as usize;
    let mut active = opened_leaves.to_vec();
    let mut proof_position = 0;
    for _ in 0..height {
        let mut next = Vec::with_capacity(active.len().div_ceil(2));
        let mut position = 0;
        while position < active.len() {
            let (index, digest) = active[position];
            let parent_digest;
            if index & 1 == 0 && position + 1 < active.len() && active[position + 1].0 == index + 1
            {
                parent_digest = hash_node(&digest, &active[position + 1].1);
                position += 2;
            } else {
                let Some(sibling) = proof.siblings.get(proof_position) else {
                    return false;
                };
                proof_position += 1;
                parent_digest = if index & 1 == 0 {
                    hash_node(&digest, sibling)
                } else {
                    hash_node(sibling, &digest)
                };
                position += 1;
            }
            next.push((index >> 1, parent_digest));
        }
        active = next;
    }

    proof_position == proof.siblings.len()
        && active.len() == 1
        && active[0].0 == 0
        && active[0].1 == *root
}

fn subtree_root_from_hasher(
    start: usize,
    width: usize,
    leaf_digest: &impl Fn(usize) -> Digest,
) -> Digest {
    let mut level = (start..start + width).map(leaf_digest).collect::<Vec<_>>();
    while level.len() > 1 {
        level = level
            .chunks_exact(2)
            .map(|pair| hash_node(&pair[0], &pair[1]))
            .collect();
    }
    level[0]
}

/// Leaf hash of the pair (f(x), f(-x)) at position index
pub fn paired_field_leaf_digest(index: usize, positive: &Field, negative: &Field) -> Digest {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"deepfold-pcs/v1/merkle-paired-leaf");
    hasher.update(&(index as u64).to_le_bytes());
    hasher.update(&(2 * field::FIELD_BYTES as u64).to_le_bytes());
    hasher.update(&field::encode_array(positive));
    hasher.update(&field::encode_array(negative));
    hasher.finalize().into()
}

fn hash_node(left: &Digest, right: &Digest) -> Digest {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"deepfold-pcs/v1/merkle-node");
    hasher.update(left);
    hasher.update(right);
    hasher.finalize().into()
}

#[cfg(test)]
mod tests {
    use super::*;

    // 8 codeword values, so 4 paired leaves: leaf i = (values[i], values[i + 4])
    fn codeword() -> Vec<Field> {
        (0..8).map(|value| Field::from(value as u64 + 1)).collect()
    }

    fn opened(values: &[Field], indices: &[usize]) -> Vec<(usize, Digest)> {
        let half = values.len() / 2;
        let mut indices = indices.to_vec();
        indices.sort_unstable();
        indices.dedup();
        indices
            .into_iter()
            .map(|i| {
                (
                    i,
                    paired_field_leaf_digest(i, &values[i], &values[i + half]),
                )
            })
            .collect()
    }

    #[test]
    fn multiproof_verifies() {
        let values = codeword();
        let tree = MerkleTree::from_field_pairs_parallel(&values).unwrap();
        let proof = tree.open_multi_pairs(&values, &[3, 1, 0, 1, 3]).unwrap();
        assert!(verify_multi(
            &tree.root(),
            4,
            &opened(&values, &[0, 1, 3]),
            &proof
        ));
    }

    #[test]
    fn changed_leaf_is_rejected() {
        let values = codeword();
        let tree = MerkleTree::from_field_pairs_parallel(&values).unwrap();
        let proof = tree.open_multi_pairs(&values, &[0, 3]).unwrap();
        let mut opened = opened(&values, &[0, 3]);
        opened[0].1[0] ^= 1;
        assert!(!verify_multi(&tree.root(), 4, &opened, &proof));
    }

    #[test]
    fn changed_missing_and_extra_nodes_are_rejected() {
        let values = codeword();
        let tree = MerkleTree::from_field_pairs_parallel(&values).unwrap();
        let proof = tree.open_multi_pairs(&values, &[0, 3]).unwrap();
        let opened = opened(&values, &[0, 3]);

        let mut changed = proof.clone();
        changed.siblings[0][0] ^= 1;
        assert!(!verify_multi(&tree.root(), 4, &opened, &changed));

        let mut missing = proof.clone();
        missing.siblings.pop();
        assert!(!verify_multi(&tree.root(), 4, &opened, &missing));

        let mut extra = proof;
        extra.siblings.push([0; 32]);
        assert!(!verify_multi(&tree.root(), 4, &opened, &extra));
    }

    #[test]
    fn one_leaf_tree_needs_no_authentication_nodes() {
        let values = vec![Field::from(9u64), Field::from(10u64)];
        let tree = MerkleTree::from_field_pairs_parallel(&values).unwrap();
        let proof = tree.open_multi_pairs(&values, &[0, 0]).unwrap();
        assert!(proof.siblings.is_empty());
        assert!(verify_multi(
            &tree.root(),
            1,
            &opened(&values, &[0]),
            &proof
        ));
    }

    #[test]
    fn pair_order_matters() {
        let values = codeword();
        let tree = MerkleTree::from_field_pairs_parallel(&values).unwrap();
        let proof = tree.open_multi_pairs(&values, &[0, 2]).unwrap();
        let mut opened = opened(&values, &[0, 2]);
        assert!(verify_multi(&tree.root(), 4, &opened, &proof));
        opened[0].1 = paired_field_leaf_digest(0, &values[4], &values[0]);
        assert!(!verify_multi(&tree.root(), 4, &opened, &proof));
    }
}
