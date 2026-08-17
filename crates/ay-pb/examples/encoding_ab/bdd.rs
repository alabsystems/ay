// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BDD dry-run estimation for the encoding A/B measurement harness.

/// BDD dry run: count reachable memoized `(i, slack)` states of `encode_bdd`
/// (coefficient-descending order, suffix-sum pruning). Clauses <= 2*nodes + 1.
pub(super) fn bdd_estimate(coeffs: &[i128], rhs: i128, max_nodes: u64) -> (u64, bool) {
    use std::collections::BTreeSet;
    let mut sorted: Vec<i128> = coeffs.to_vec();
    sorted.sort_unstable_by(|a, b| b.cmp(a));
    let n = sorted.len();
    let mut suffix = vec![0i128; n + 1];
    for i in (0..n).rev() {
        suffix[i] = suffix[i + 1].saturating_add(sorted[i]);
    }
    // Level-by-level reachable slack values (deduped), pruned like build_bdd:
    // terminal when s <= 0 (true) or suffix[i] < s (false).
    let mut level: BTreeSet<i128> = BTreeSet::new();
    if rhs > 0 && suffix[0] >= rhs {
        level.insert(rhs);
    }
    let mut nodes: u64 = 0;
    for i in 0..n {
        if level.is_empty() {
            break;
        }
        nodes += level.len() as u64;
        if nodes > max_nodes {
            return (nodes, false);
        }
        let mut next: BTreeSet<i128> = BTreeSet::new();
        for &s in &level {
            for s2 in [s - sorted[i], s] {
                if s2 > 0 && i + 1 < n && suffix[i + 1] >= s2 {
                    next.insert(s2);
                }
            }
        }
        level = next;
    }
    (nodes, true)
}
