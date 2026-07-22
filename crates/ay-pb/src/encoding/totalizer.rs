// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Generalized Totalizer encoding for PB constraints (Joshi et al. 2015).
//!
//! Tree-based encoding that generalizes the unary totalizer from cardinality
//! constraints to weighted pseudo-Boolean constraints. Builds a binary tree
//! where leaves are the input literals (weighted) and internal nodes merge
//! the weight sets of their children.
//!
//! Each internal node has output variables representing "total weight from
//! this subtree >= w" for each reachable weight value. Merging two children
//! produces clauses linking parent and child outputs bidirectionally:
//! - Forward: children justify parent (if children prove weight, parent is set)
//! - Backward: parent requires justification (if parent is set, some children
//!   must provide the weight)
//!
//! # References
//! - Joshi, Rao, Martins, Manquinho, "Generalized Totalizer Encoding for
//!   Pseudo-Boolean Constraints", 2015

use std::collections::BTreeSet;

const STOP_POLL_INTERVAL: usize = 64;

/// Root outputs of a generalized totalizer tree.
///
/// Each `(weight, lit)` pair means `lit` is true iff the encoded subtree can
/// prove weight at least `weight`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TotalizerOutputs {
    pub(crate) weights: Vec<i128>,
    pub(crate) outputs: Vec<i32>,
}

/// Represents the output variables of a totalizer subtree.
///
/// `outputs[i]` is the DIMACS variable meaning "weight from this subtree >= weights[i]".
/// `weights` is sorted in ascending order, and `weights[i]` corresponds to `outputs[i]`.
struct TotalizerNode {
    /// Distinct reachable weight values (ascending), capped at rhs.
    weights: Vec<i128>,
    /// DIMACS auxiliary variables: `outputs[i]` means "subtree weight >= weights[i]".
    outputs: Vec<i32>,
}

impl TotalizerNode {
    /// Creates a leaf node for a single literal with the given coefficient.
    fn leaf(lit: i32, coeff: i128, rhs: i128) -> Self {
        let capped = coeff.min(rhs);
        Self {
            weights: vec![capped],
            outputs: vec![lit],
        }
    }

    /// Returns the output variable for the smallest weight >= w, or None.
    fn var_ge(&self, w: i128) -> Option<i32> {
        self.weights
            .iter()
            .position(|&wt| wt >= w)
            .map(|idx| self.outputs[idx])
    }

    /// Returns the output variable for exact weight w, or None.
    fn var_eq(&self, w: i128) -> Option<i32> {
        self.weights
            .iter()
            .position(|&wt| wt == w)
            .map(|idx| self.outputs[idx])
    }

    /// Maximum reachable weight.
    fn max_weight(&self) -> i128 {
        self.weights.last().copied().unwrap_or(0)
    }
}

/// Encodes a normalized `sum(coeffs[i] * lits[i]) >= rhs` using the
/// generalized totalizer encoding.
///
/// All coefficients must be positive and `rhs > 0`.
/// Clauses are appended to `clauses`; new variables are allocated via `next_var`.
pub(crate) fn encode_totalizer(
    coeffs: &[i128],
    lits: &[i32],
    rhs: i128,
    clauses: &mut Vec<Vec<i32>>,
    next_var: &mut u32,
) {
    let n = coeffs.len();
    debug_assert!(n > 0);
    debug_assert!(rhs > 0);
    debug_assert!(coeffs.iter().all(|&c| c > 0));

    let root = build_totalizer_root(coeffs, lits, rhs, clauses, next_var);

    // The root node's output for weight >= rhs must be true.
    if let Some(root_var) = root.var_ge(rhs) {
        clauses.push(vec![root_var]);
    } else {
        // rhs is not reachable -- constraint is UNSAT.
        clauses.push(Vec::new());
    }
}

/// Interruptible variant of [`encode_totalizer`].
///
/// Returns `true` when encoding was interrupted and partial output should be
/// discarded by the caller.
pub(crate) fn encode_totalizer_interruptible<F>(
    coeffs: &[i128],
    lits: &[i32],
    rhs: i128,
    clauses: &mut Vec<Vec<i32>>,
    next_var: &mut u32,
    should_stop: &mut F,
) -> bool
where
    F: FnMut() -> bool,
{
    let n = coeffs.len();
    debug_assert!(n > 0);
    debug_assert!(rhs > 0);
    debug_assert!(coeffs.iter().all(|&c| c > 0));

    if should_stop() {
        return true;
    }

    let Some(root) =
        build_totalizer_root_interruptible(coeffs, lits, rhs, clauses, next_var, should_stop)
    else {
        return true;
    };

    // The root node's output for weight >= rhs must be true.
    if let Some(root_var) = root.var_ge(rhs) {
        clauses.push(vec![root_var]);
    } else {
        // rhs is not reachable -- constraint is UNSAT.
        clauses.push(Vec::new());
    }

    false
}

/// Interruptible variant of [`encode_totalizer_with_outputs`].
pub(crate) fn encode_totalizer_with_outputs_interruptible<F>(
    coeffs: &[i128],
    lits: &[i32],
    rhs: i128,
    clauses: &mut Vec<Vec<i32>>,
    next_var: &mut u32,
    should_stop: &mut F,
) -> Option<TotalizerOutputs>
where
    F: FnMut() -> bool,
{
    let root =
        build_totalizer_root_interruptible(coeffs, lits, rhs, clauses, next_var, should_stop)?;
    Some(TotalizerOutputs {
        weights: root.weights,
        outputs: root.outputs,
    })
}

fn build_totalizer_root(
    coeffs: &[i128],
    lits: &[i32],
    rhs: i128,
    clauses: &mut Vec<Vec<i32>>,
    next_var: &mut u32,
) -> TotalizerNode {
    let mut nodes: Vec<TotalizerNode> = coeffs
        .iter()
        .zip(lits.iter())
        .map(|(&c, &l)| TotalizerNode::leaf(l, c, rhs))
        .collect();

    while nodes.len() > 1 {
        let mut next_level = Vec::with_capacity(nodes.len().div_ceil(2));
        let mut i = 0;
        while i < nodes.len() {
            if i + 1 < nodes.len() {
                let merged = merge_nodes(&nodes[i], &nodes[i + 1], rhs, clauses, next_var);
                next_level.push(merged);
                i += 2;
            } else {
                next_level.push(TotalizerNode {
                    weights: std::mem::take(&mut nodes[i].weights),
                    outputs: std::mem::take(&mut nodes[i].outputs),
                });
                i += 1;
            }
        }
        nodes = next_level;
    }

    nodes
        .pop()
        .expect("non-empty totalizer must produce a root")
}

/// Hard internal ceiling on aux (output) variables minted by one interruptible
/// totalizer build. Matches the scale of `MAX_UNARY_ENCODING_AUX` in
/// `encoding/mod.rs`: past this, the weighted totalizer is the wrong tool and
/// the caller's fallback (adder / decline) must take over. The non-interruptible
/// `encode_totalizer` has no failure channel and stays caller-gated
/// (`clamp_unary_strategy`).
const MAX_TOTALIZER_AUX_OUTPUTS: usize = 2_000_000;

fn build_totalizer_root_interruptible<F>(
    coeffs: &[i128],
    lits: &[i32],
    rhs: i128,
    clauses: &mut Vec<Vec<i32>>,
    next_var: &mut u32,
    should_stop: &mut F,
) -> Option<TotalizerNode>
where
    F: FnMut() -> bool,
{
    if should_stop() {
        return None;
    }

    let mut poll_counter = 0usize;
    let mut remaining_aux = MAX_TOTALIZER_AUX_OUTPUTS;
    let mut nodes: Vec<TotalizerNode> = coeffs
        .iter()
        .zip(lits.iter())
        .map(|(&c, &l)| TotalizerNode::leaf(l, c, rhs))
        .collect();

    while nodes.len() > 1 {
        if stop_requested(should_stop, &mut poll_counter) {
            return None;
        }

        let mut next_level = Vec::with_capacity(nodes.len().div_ceil(2));
        let mut i = 0;
        while i < nodes.len() {
            if stop_requested(should_stop, &mut poll_counter) {
                return None;
            }

            if i + 1 < nodes.len() {
                let merged = merge_nodes_interruptible(
                    &nodes[i],
                    &nodes[i + 1],
                    rhs,
                    clauses,
                    next_var,
                    should_stop,
                    &mut poll_counter,
                    &mut remaining_aux,
                )?;
                next_level.push(merged);
                i += 2;
            } else {
                next_level.push(TotalizerNode {
                    weights: std::mem::take(&mut nodes[i].weights),
                    outputs: std::mem::take(&mut nodes[i].outputs),
                });
                i += 1;
            }
        }
        nodes = next_level;
    }

    if stop_requested(should_stop, &mut poll_counter) {
        return None;
    }

    nodes.pop()
}

/// Merges two totalizer nodes, producing a parent node.
///
/// Generates both forward implications (children -> parent) and backward
/// implications (parent -> children) to ensure the encoding is sound.
fn merge_nodes(
    left: &TotalizerNode,
    right: &TotalizerNode,
    rhs: i128,
    clauses: &mut Vec<Vec<i32>>,
    next_var: &mut u32,
) -> TotalizerNode {
    // Compute all reachable weight values for the merged node.
    let mut weight_set = BTreeSet::new();

    // Weight 0 is implicit (not tracked). We only track positive weights.
    // Reachable weights: left alone, right alone, or left + right.
    for &wl in &left.weights {
        if wl <= rhs {
            weight_set.insert(wl);
        }
    }
    for &wr in &right.weights {
        if wr <= rhs {
            weight_set.insert(wr);
        }
    }
    for &wl in &left.weights {
        for &wr in &right.weights {
            let sum = wl.saturating_add(wr);
            if sum <= rhs {
                weight_set.insert(sum);
            } else {
                weight_set.insert(rhs);
            }
        }
    }

    let weights: Vec<i128> = weight_set.into_iter().collect();
    let outputs: Vec<i32> = weights
        .iter()
        .map(|_| {
            let v = *next_var as i32;
            *next_var += 1;
            v
        })
        .collect();

    // Also add monotonicity: parent >= w_i implies parent >= w_{i-1}.
    for i in 1..weights.len() {
        // outputs[i] (>= weights[i]) -> outputs[i-1] (>= weights[i-1])
        clauses.push(vec![-outputs[i], outputs[i - 1]]);
    }

    // Generate linking clauses for each parent weight.
    for (idx, &w) in weights.iter().enumerate() {
        let pvar = outputs[idx];

        // === Forward implications: children -> parent ===
        // If children provide enough weight, parent must be true.

        // For each way to decompose w as wl + wr where:
        //   wl comes from left (or 0), wr comes from right (or 0), wl + wr >= w

        // Case: left alone provides >= w.
        if let Some(lv) = left.var_ge(w) {
            clauses.push(vec![-lv, pvar]);
        }

        // Case: right alone provides >= w.
        if let Some(rv) = right.var_ge(w) {
            clauses.push(vec![-rv, pvar]);
        }

        // Case: left provides wl and right provides >= w - wl.
        for &wl in &left.weights {
            if wl >= w {
                continue; // Already covered above.
            }
            let needed = w - wl;
            if needed > right.max_weight() {
                continue; // Not reachable by right alone.
            }
            if let Some(lv) = left.var_eq(wl) {
                if let Some(rv) = right.var_ge(needed) {
                    clauses.push(vec![-lv, -rv, pvar]);
                }
            }
        }

        // === Backward implications: parent -> children ===
        // If parent says weight >= w, there must be a valid decomposition.
        //
        // parent >= w -> OR(justifications)
        // where each justification is:
        //   left >= w (alone sufficient)
        //   right >= w (alone sufficient)
        //   left >= wl AND right >= (w - wl) for each valid wl
        //
        // We encode this using the Tseitin-style approach from the totalizer
        // literature: for each pair of "boundary" values (a, b) where
        // a is a left weight level and b is a right weight level:
        //   parent >= w AND NOT(left >= a+1) -> right >= (w - a)
        //   parent >= w AND NOT(right >= b+1) -> left >= (w - b)
        //
        // This says: if the parent claims >= w, and the left can't provide
        // more than a, then the right must provide at least w - a.

        // Left boundary decomposition:
        // For left weight = 0 (left provides nothing): parent -> right >= w.
        // For each left weight level wl_i: if left < wl_{i+1} then right >= w - wl_i.
        // For left weight = max: if left < max but... covered by next level.

        // Process left weight levels: 0, wl_0, wl_1, ..., wl_max.
        // At boundary "left < wl_next", right must provide >= (w - wl_prev).

        let mut left_boundaries: Vec<i128> = vec![0]; // left provides 0
        left_boundaries.extend_from_slice(&left.weights);

        for (bi, &boundary_wl) in left_boundaries.iter().enumerate() {
            if boundary_wl >= w {
                break; // Left alone is sufficient, no right needed.
            }
            let right_needed = w - boundary_wl;
            if right_needed > right.max_weight() {
                // Right can't provide enough even at max. This decomposition
                // is impossible. We need the next boundary.

                // If this is the first boundary (left=0), we need left to provide
                // something. Add: parent -> left >= (smallest left weight).
                // But we can't do this per-boundary -- we need the full disjunction.
                // Fall through to the disjunctive backward clause below.
                continue;
            }

            // Get the "NOT left >= next_level" literal.
            // If bi == 0: boundary is 0, meaning "left provides 0", which
            // needs condition "NOT(left >= smallest_left_weight)".
            // If bi > 0: boundary is left.weights[bi-1], meaning
            // "left provides at most left.weights[bi-1]", which needs
            // condition "NOT(left >= left.weights[bi])" if bi < left.weights.len().

            let not_left_above: Option<i32> = if bi < left.weights.len() {
                // NOT(left >= left.weights[bi])
                left.var_eq(left.weights[bi]).map(|v| -v)
            } else {
                // We're past all left weight levels: left is at max.
                // This is always true (left can't exceed max), so the
                // clause is: parent -> right >= right_needed.
                None // unconditional
            };

            if let Some(rv) = right.var_ge(right_needed) {
                match not_left_above {
                    Some(not_l) => {
                        // parent AND NOT(left >= next) -> right >= needed
                        // i.e., NOT parent OR left >= next OR right >= needed
                        clauses.push(vec![-pvar, -not_l, rv]);
                    }
                    None => {
                        // parent -> right >= needed (unconditional on left)
                        clauses.push(vec![-pvar, rv]);
                    }
                }
            }
        }

        // Right boundary decomposition (symmetric):
        let mut right_boundaries: Vec<i128> = vec![0];
        right_boundaries.extend_from_slice(&right.weights);

        for (bi, &boundary_wr) in right_boundaries.iter().enumerate() {
            if boundary_wr >= w {
                break;
            }
            let left_needed = w - boundary_wr;
            if left_needed > left.max_weight() {
                continue;
            }

            let not_right_above: Option<i32> = if bi < right.weights.len() {
                right.var_eq(right.weights[bi]).map(|v| -v)
            } else {
                None
            };

            if let Some(lv) = left.var_ge(left_needed) {
                match not_right_above {
                    Some(not_r) => {
                        clauses.push(vec![-pvar, -not_r, lv]);
                    }
                    None => {
                        clauses.push(vec![-pvar, lv]);
                    }
                }
            }
        }
    }

    TotalizerNode { weights, outputs }
}

fn merge_nodes_interruptible<F>(
    left: &TotalizerNode,
    right: &TotalizerNode,
    rhs: i128,
    clauses: &mut Vec<Vec<i32>>,
    next_var: &mut u32,
    should_stop: &mut F,
    poll_counter: &mut usize,
    remaining_aux: &mut usize,
) -> Option<TotalizerNode>
where
    F: FnMut() -> bool,
{
    if stop_requested(should_stop, poll_counter) {
        return None;
    }

    // Compute all reachable weight values for the merged node.
    let mut weight_set = BTreeSet::new();

    for &wl in &left.weights {
        if stop_requested(should_stop, poll_counter) {
            return None;
        }
        if wl <= rhs {
            weight_set.insert(wl);
        }
    }
    for &wr in &right.weights {
        if stop_requested(should_stop, poll_counter) {
            return None;
        }
        if wr <= rhs {
            weight_set.insert(wr);
        }
    }
    for &wl in &left.weights {
        if stop_requested(should_stop, poll_counter) {
            return None;
        }
        for &wr in &right.weights {
            if stop_requested(should_stop, poll_counter) {
                return None;
            }
            let sum = wl.saturating_add(wr);
            if sum <= rhs {
                weight_set.insert(sum);
            } else {
                weight_set.insert(rhs);
            }
            // INTERNAL AUX CEILING: the merged node mints one aux variable per
            // reachable weighted sum, which grows with the product of the
            // children's weight sets. Callers gate their inputs, but this
            // defensive budget makes the builder itself refuse (fail closed to
            // None = decline, never a verdict) instead of relying on every
            // caller gating correctly.
            if weight_set.len() > *remaining_aux {
                return None;
            }
        }
    }

    let weights: Vec<i128> = weight_set.into_iter().collect();
    *remaining_aux -= weights.len();
    let outputs: Vec<i32> = weights
        .iter()
        .map(|_| {
            let v = *next_var as i32;
            *next_var += 1;
            v
        })
        .collect();

    for i in 1..weights.len() {
        if stop_requested(should_stop, poll_counter) {
            return None;
        }
        clauses.push(vec![-outputs[i], outputs[i - 1]]);
    }

    for (idx, &w) in weights.iter().enumerate() {
        if stop_requested(should_stop, poll_counter) {
            return None;
        }

        let pvar = outputs[idx];

        if let Some(lv) = left.var_ge(w) {
            clauses.push(vec![-lv, pvar]);
        }

        if let Some(rv) = right.var_ge(w) {
            clauses.push(vec![-rv, pvar]);
        }

        for &wl in &left.weights {
            if stop_requested(should_stop, poll_counter) {
                return None;
            }
            if wl >= w {
                continue;
            }
            let needed = w - wl;
            if needed > right.max_weight() {
                continue;
            }
            if let Some(lv) = left.var_eq(wl) {
                if let Some(rv) = right.var_ge(needed) {
                    clauses.push(vec![-lv, -rv, pvar]);
                }
            }
        }

        let mut left_boundaries: Vec<i128> = vec![0];
        left_boundaries.extend_from_slice(&left.weights);
        for (bi, &boundary_wl) in left_boundaries.iter().enumerate() {
            if stop_requested(should_stop, poll_counter) {
                return None;
            }
            if boundary_wl >= w {
                break;
            }
            let right_needed = w - boundary_wl;
            if right_needed > right.max_weight() {
                continue;
            }

            let not_left_above: Option<i32> = if bi < left.weights.len() {
                left.var_eq(left.weights[bi]).map(|v| -v)
            } else {
                None
            };

            if let Some(rv) = right.var_ge(right_needed) {
                match not_left_above {
                    Some(not_l) => clauses.push(vec![-pvar, -not_l, rv]),
                    None => clauses.push(vec![-pvar, rv]),
                }
            }
        }

        let mut right_boundaries: Vec<i128> = vec![0];
        right_boundaries.extend_from_slice(&right.weights);
        for (bi, &boundary_wr) in right_boundaries.iter().enumerate() {
            if stop_requested(should_stop, poll_counter) {
                return None;
            }
            if boundary_wr >= w {
                break;
            }
            let left_needed = w - boundary_wr;
            if left_needed > left.max_weight() {
                continue;
            }

            let not_right_above: Option<i32> = if bi < right.weights.len() {
                right.var_eq(right.weights[bi]).map(|v| -v)
            } else {
                None
            };

            if let Some(lv) = left.var_ge(left_needed) {
                match not_right_above {
                    Some(not_r) => clauses.push(vec![-pvar, -not_r, lv]),
                    None => clauses.push(vec![-pvar, lv]),
                }
            }
        }
    }

    Some(TotalizerNode { weights, outputs })
}

fn stop_requested<F>(should_stop: &mut F, poll_counter: &mut usize) -> bool
where
    F: FnMut() -> bool,
{
    *poll_counter += 1;
    (*poll_counter == 1 || (*poll_counter).is_multiple_of(STOP_POLL_INTERVAL)) && should_stop()
}

#[cfg(test)]
mod aux_ceiling_tests {
    use super::*;
    use std::time::{Duration, Instant};

    #[test]
    fn test_interruptible_totalizer_declines_past_internal_aux_ceiling() {
        // 40 power-of-two weights with an unreachable-large rhs make every
        // subset sum distinct, so the merged weight sets grow multiplicatively
        // (~2^40 reachable sums at the root). Without the internal ceiling
        // this build would allocate terabytes; with it, the builder must
        // DECLINE (None) once the aux budget is exhausted. The deadline
        // closure turns a ceiling regression into a test failure instead of
        // a hang.
        let coeffs: Vec<i128> = (0..40).map(|i| 1_i128 << i).collect();
        let lits: Vec<i32> = (1..=40).collect();
        let rhs: i128 = 1_i128 << 41;
        let mut clauses = Vec::new();
        let mut next_var = 41_u32;
        let deadline = Instant::now() + Duration::from_mins(1);
        let mut should_stop = || Instant::now() >= deadline;

        let start = Instant::now();
        let result = encode_totalizer_with_outputs_interruptible(
            &coeffs,
            &lits,
            rhs,
            &mut clauses,
            &mut next_var,
            &mut should_stop,
        );

        assert!(
            result.is_none(),
            "over-budget totalizer build must decline, not complete"
        );
        assert!(
            start.elapsed() < Duration::from_secs(50),
            "decline must come from the aux ceiling, not the deadline"
        );
    }
}
