// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Orbit extraction from verified transpositions via union-find.
//!
//! Given a set of verified variable transpositions (swaps), the swap graph
//! has variables as nodes and swaps as edges. Connected components of this
//! graph are "orbits" -- sets of variables that are mutually interchangeable
//! under composition of the detected symmetries.
//!
//! BreakID breaks the full symmetric group of each orbit by emitting
//! lex-leader constraints along the orbit ordering, producing O(k) binary
//! clauses per orbit of size k.
//!
//! Reference: Devriendt, Bogaerts, Bruynooghe, Denecker. "Improved Static
//! Symmetry Breaking for SAT." (BreakID, SAT 2016), Section 4.

use std::collections::BTreeMap;

use crate::Variable;

use super::BinarySwap;

/// Extract orbits (connected components) from a set of verified transpositions.
///
/// Uses a simple union-find to group variables connected by swaps. Each
/// resulting orbit is sorted by variable ID for deterministic output.
pub(crate) fn extract_orbits(swaps: &[BinarySwap]) -> Vec<Vec<Variable>> {
    if swaps.is_empty() {
        return Vec::new();
    }

    // Collect all variables and assign indices.
    let mut var_set: BTreeMap<Variable, usize> = BTreeMap::new();
    let mut vars: Vec<Variable> = Vec::new();
    for swap in swaps {
        for v in [swap.lhs, swap.rhs] {
            let next_idx = vars.len();
            var_set.entry(v).or_insert_with(|| {
                vars.push(v);
                next_idx
            });
        }
    }

    // Union-find.
    let n = vars.len();
    let mut parent: Vec<usize> = (0..n).collect();
    let mut rank: Vec<u8> = vec![0; n];

    for swap in swaps {
        let a = var_set[&swap.lhs];
        let b = var_set[&swap.rhs];
        union(&mut parent, &mut rank, a, b);
    }

    // Group by root.
    let mut components: BTreeMap<usize, Vec<Variable>> = BTreeMap::new();
    for (i, &var) in vars.iter().enumerate() {
        let root = find(&mut parent, i);
        components.entry(root).or_default().push(var);
    }

    // Return only non-trivial orbits (size >= 2), sorted by variable ID.
    components
        .into_values()
        .filter(|orbit| orbit.len() >= 2)
        .map(|mut orbit| {
            orbit.sort();
            orbit
        })
        .collect()
}

fn find(parent: &mut [usize], x: usize) -> usize {
    if parent[x] != x {
        parent[x] = find(parent, parent[x]);
    }
    parent[x]
}

fn union(parent: &mut [usize], rank: &mut [u8], a: usize, b: usize) {
    let ra = find(parent, a);
    let rb = find(parent, b);
    if ra == rb {
        return;
    }
    match rank[ra].cmp(&rank[rb]) {
        std::cmp::Ordering::Less => parent[ra] = rb,
        std::cmp::Ordering::Greater => parent[rb] = ra,
        std::cmp::Ordering::Equal => {
            parent[rb] = ra;
            rank[ra] = rank[ra].saturating_add(1);
        }
    }
}

/// Encode lex-leader SBP clauses for an ordered orbit of variables.
///
/// Given an orbit `[v0, v1, ..., vk]` where all variables are interchangeable
/// under the symmetry group, we enforce `v0 >= v1 >= ... >= vk` by emitting
/// binary clauses `(vi \/ ~v_{i+1})` for each consecutive pair.
///
/// This is the BreakID "row interchangeability" encoding: for a row-symmetric
/// matrix, ordering adjacent rows lexicographically breaks the full symmetric
/// group S_k with only O(k) binary clauses.
///
/// Reference: Devriendt, Bogaerts, Bruynooghe, Denecker. "Improved Static
/// Symmetry Breaking for SAT." (BreakID, SAT 2016), Section 4.
pub(crate) fn encode_orbit_lex_leader_sbp(orbit: &[Variable]) -> Vec<Vec<crate::Literal>> {
    if orbit.len() < 2 {
        return Vec::new();
    }
    let mut clauses = Vec::with_capacity(orbit.len() - 1);
    for pair in orbit.windows(2) {
        // Enforce pair[0] >= pair[1]: clause (pair[0] \/ ~pair[1])
        clauses.push(vec![
            crate::Literal::positive(pair[0]),
            crate::Literal::negative(pair[1]),
        ]);
    }
    clauses
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Variable;

    #[test]
    fn test_extract_orbits_single_swap() {
        let swaps = vec![BinarySwap {
            lhs: Variable(0),
            rhs: Variable(1),
        }];
        let orbits = extract_orbits(&swaps);
        assert_eq!(orbits.len(), 1);
        assert_eq!(orbits[0], vec![Variable(0), Variable(1)]);
    }

    #[test]
    fn test_extract_orbits_chain() {
        // Swaps: (0,1), (1,2), (2,3) -> single orbit [0,1,2,3]
        let swaps = vec![
            BinarySwap {
                lhs: Variable(0),
                rhs: Variable(1),
            },
            BinarySwap {
                lhs: Variable(1),
                rhs: Variable(2),
            },
            BinarySwap {
                lhs: Variable(2),
                rhs: Variable(3),
            },
        ];
        let orbits = extract_orbits(&swaps);
        assert_eq!(orbits.len(), 1);
        assert_eq!(
            orbits[0],
            vec![Variable(0), Variable(1), Variable(2), Variable(3)]
        );
    }

    #[test]
    fn test_extract_orbits_disjoint() {
        // Swaps: (0,1), (2,3) -> two orbits
        let swaps = vec![
            BinarySwap {
                lhs: Variable(0),
                rhs: Variable(1),
            },
            BinarySwap {
                lhs: Variable(2),
                rhs: Variable(3),
            },
        ];
        let mut orbits = extract_orbits(&swaps);
        orbits.sort_by_key(|o| o[0]);
        assert_eq!(orbits.len(), 2);
        assert_eq!(orbits[0], vec![Variable(0), Variable(1)]);
        assert_eq!(orbits[1], vec![Variable(2), Variable(3)]);
    }

    #[test]
    fn test_extract_orbits_empty() {
        let orbits = extract_orbits(&[]);
        assert!(orbits.is_empty());
    }

    #[test]
    fn test_lex_leader_sbp_encoding() {
        let orbit = vec![Variable(0), Variable(1), Variable(2)];
        let clauses = encode_orbit_lex_leader_sbp(&orbit);
        assert_eq!(clauses.len(), 2);
        // First clause: v0 >= v1 -> (v0 \/ ~v1)
        assert_eq!(clauses[0][0], crate::Literal::positive(Variable(0)));
        assert_eq!(clauses[0][1], crate::Literal::negative(Variable(1)));
        // Second clause: v1 >= v2 -> (v1 \/ ~v2)
        assert_eq!(clauses[1][0], crate::Literal::positive(Variable(1)));
        assert_eq!(clauses[1][1], crate::Literal::negative(Variable(2)));
    }

    #[test]
    fn test_lex_leader_sbp_single_var() {
        let orbit = vec![Variable(0)];
        let clauses = encode_orbit_lex_leader_sbp(&orbit);
        assert!(clauses.is_empty());
    }
}
