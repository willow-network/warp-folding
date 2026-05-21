//! Keccak-256 binary Merkle tree over field-element leaves.
//!
//! Used by Construction 7.2 to bind the codeword `f ∈ F^n` before
//! the verifier samples OOD points or shift queries. The hash choice
//! matches Orion's existing Keccak-Merkle convention.
//!
//! Leaf hash: `Keccak256(serialize(f[i]))`.
//! Node hash: `Keccak256(left_digest || right_digest)`.
//! Root: the digest at the top of the binary tree (length `n` is
//! padded to the next power of two with the all-zeros leaf hash).

use expander_arith::Field;
use serdes::ExpSerde;
use sha3::{Digest, Keccak256};

pub type Digest32 = [u8; 32];

/// A binary Merkle tree storing all internal levels for opening.
#[derive(Clone, Debug)]
pub struct MerkleTree {
    /// `levels[0]` = leaf hashes; `levels[depth]` = root.
    /// Each level is a power-of-two number of digests, half the size
    /// of the level below it.
    levels: Vec<Vec<Digest32>>,
}

/// Authentication path for one leaf — the sibling digest at each level.
#[derive(Clone, Debug, PartialEq, Eq, serdes::ExpSerde)]
pub struct MerklePath {
    pub siblings: Vec<Digest32>,
}

impl MerkleTree {
    /// Build the tree over `leaves`. `leaves.len()` must be a power of
    /// two ≥ 1.
    pub fn build<F: Field + ExpSerde>(leaves: &[F]) -> Self {
        assert!(
            leaves.len().is_power_of_two(),
            "MerkleTree requires power-of-two leaf count (got {})",
            leaves.len()
        );

        const PAR_THRESHOLD: usize = 1024;
        use rayon::prelude::*;
        let leaf_hashes: Vec<Digest32> = if leaves.len() >= PAR_THRESHOLD {
            leaves.par_iter().map(hash_leaf::<F>).collect()
        } else {
            leaves.iter().map(hash_leaf::<F>).collect()
        };
        let mut levels = vec![leaf_hashes];

        while levels.last().unwrap().len() > 1 {
            let cur = levels.last().unwrap();
            let next: Vec<Digest32> = if cur.len() >= PAR_THRESHOLD {
                cur.par_chunks_exact(2)
                    .map(|pair| hash_node(&pair[0], &pair[1]))
                    .collect()
            } else {
                cur.chunks_exact(2)
                    .map(|pair| hash_node(&pair[0], &pair[1]))
                    .collect()
            };
            levels.push(next);
        }

        Self { levels }
    }

    pub fn root(&self) -> Digest32 {
        self.levels.last().unwrap()[0]
    }

    pub fn n_leaves(&self) -> usize {
        self.levels[0].len()
    }

    pub fn depth(&self) -> usize {
        self.levels.len() - 1
    }

    /// Generate the authentication path for leaf index `idx`.
    pub fn open(&self, idx: usize) -> MerklePath {
        assert!(idx < self.n_leaves());
        let mut siblings = Vec::with_capacity(self.depth());
        let mut cur = idx;
        for level in &self.levels[..self.depth()] {
            let sibling = if cur & 1 == 0 { cur + 1 } else { cur - 1 };
            siblings.push(level[sibling]);
            cur >>= 1;
        }
        MerklePath { siblings }
    }
}

/// Re-derive the root from a leaf, its index, and an authentication
/// path. Returns `true` iff the recomputed root matches `expected`.
pub fn verify_path<F: Field + ExpSerde>(
    expected_root: &Digest32,
    leaf: &F,
    idx: usize,
    n_leaves: usize,
    path: &MerklePath,
) -> bool {
    let depth = n_leaves.trailing_zeros() as usize;
    if !n_leaves.is_power_of_two() || path.siblings.len() != depth || idx >= n_leaves {
        return false;
    }

    let mut cur = hash_leaf::<F>(leaf);
    let mut cur_idx = idx;
    for sibling in &path.siblings {
        cur = if cur_idx & 1 == 0 {
            hash_node(&cur, sibling)
        } else {
            hash_node(sibling, &cur)
        };
        cur_idx >>= 1;
    }
    cur == *expected_root
}

fn hash_leaf<F: Field + ExpSerde>(f: &F) -> Digest32 {
    let mut buf = Vec::new();
    f.serialize_into(&mut buf).expect("ExpSerde Vec write");
    let mut hasher = Keccak256::new();
    hasher.update(b"warp-merkle/leaf");
    hasher.update(&buf);
    hasher.finalize().into()
}

fn hash_node(left: &Digest32, right: &Digest32) -> Digest32 {
    let mut hasher = Keccak256::new();
    hasher.update(b"warp-merkle/node");
    hasher.update(left);
    hasher.update(right);
    hasher.finalize().into()
}

#[cfg(test)]
mod tests {
    use super::*;
    use expander_mersenne31::M31Ext6;

    type F = M31Ext6;
    fn f(n: u32) -> F {
        F::from(n)
    }

    fn make_leaves(n: usize) -> Vec<F> {
        (0..n).map(|i| f(i as u32 + 1)).collect()
    }

    #[test]
    fn build_round_trip_per_leaf() {
        let leaves = make_leaves(8);
        let tree = MerkleTree::build(&leaves);
        let root = tree.root();
        for (i, leaf) in leaves.iter().enumerate() {
            let path = tree.open(i);
            assert!(
                verify_path(&root, leaf, i, leaves.len(), &path),
                "leaf {i} failed to verify"
            );
        }
    }

    #[test]
    fn wrong_leaf_rejected() {
        let leaves = make_leaves(8);
        let tree = MerkleTree::build(&leaves);
        let path = tree.open(3);
        assert!(!verify_path(&tree.root(), &f(999), 3, leaves.len(), &path));
    }

    #[test]
    fn wrong_index_rejected() {
        let leaves = make_leaves(8);
        let tree = MerkleTree::build(&leaves);
        let path = tree.open(3);
        // Same path applied to a different leaf index can't recompute
        // the root in general (siblings line up wrong).
        assert!(!verify_path(
            &tree.root(),
            &leaves[3],
            5,
            leaves.len(),
            &path
        ));
    }

    #[test]
    fn tampered_sibling_rejected() {
        let leaves = make_leaves(16);
        let tree = MerkleTree::build(&leaves);
        let mut path = tree.open(7);
        path.siblings[0][0] ^= 1;
        assert!(!verify_path(
            &tree.root(),
            &leaves[7],
            7,
            leaves.len(),
            &path
        ));
    }

    #[test]
    fn tree_root_changes_when_leaf_changes() {
        let mut leaves = make_leaves(8);
        let r0 = MerkleTree::build(&leaves).root();
        leaves[3] = f(123);
        let r1 = MerkleTree::build(&leaves).root();
        assert_ne!(r0, r1);
    }

    #[test]
    fn depth_log_n() {
        for log_n in 0..6 {
            let n = 1usize << log_n;
            let leaves = make_leaves(n);
            let tree = MerkleTree::build(&leaves);
            assert_eq!(tree.depth(), log_n);
            assert_eq!(tree.n_leaves(), n);
        }
    }
}
