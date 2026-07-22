// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV bit-group aware invariant discovery (#7044).
//!
//! After BvToBool preprocessing, each BV(N) argument becomes N consecutive Bool
//! arguments. Standard invariant discovery only examines Int-sorted variables,
//! making it blind to the 70-90% of state space that is Bool-encoded.
//!
//! This module discovers invariants over BV bit-groups:
//! - **Equality**: `x = y` (all corresponding bits equal) — O(G^2) where G is
//!   the number of BV groups, not O(N^2) where N is the total Bool variable count.
//! - **Constant**: `x = 0` (all bits false) — O(G) per constant value checked.
//! - **Bit bounds**: Per-bit constant discovery — individual bits fixed to 0/1.
//!   Captures leading-zero patterns (x < 2^k) common in bounded BV variables.
//! - **Ordering**: Unsigned `x <= y` between same-width groups — O(G^2) with
//!   O(W) formula size per candidate (W = bit width).

use super::super::super::PdrSolver;
use crate::{ChcExpr, ChcSort, PredicateId};

/// Resolved BV bit-group: (group_index, canonical_var_indices, bit_width).
struct BvGroup {
    var_indices: Vec<usize>,
    width: u32,
}

impl PdrSolver {
    /// Resolve `config.bv_bit_groups` into predicate variable index vectors.
    ///
    /// Each `(start_arg_index, bit_width)` entry becomes a vector of canonical
    /// variable indices `start..start+width`. Validates that all referenced
    /// indices exist in the predicate's canonical vars and have Bool sort.
    fn resolve_bv_groups(&self, pred_id: PredicateId) -> Vec<BvGroup> {
        let canonical_vars = match self.canonical_vars(pred_id) {
            Some(v) => v,
            None => return Vec::new(),
        };

        self.config
            .bv_bit_groups
            .iter()
            .filter_map(|&(start, width)| {
                let end = start + width as usize;
                if end > canonical_vars.len() {
                    return None;
                }
                // Validate all vars in range are Bool
                if !canonical_vars[start..end]
                    .iter()
                    .all(|v| matches!(v.sort, ChcSort::Bool))
                {
                    return None;
                }
                let var_indices: Vec<usize> = (start..end).collect();
                Some(BvGroup { var_indices, width })
            })
            .collect()
    }

    /// Discover BV group equality invariants (#7044).
    ///
    /// For each pair of same-width BV groups, builds `(x_0=y_0 ∧ ... ∧ x_n=y_n)`
    /// and checks if it's a valid invariant (init-valid AND self-inductive).
    ///
    /// Complexity: O(G^2) where G = number of BV groups (typically 4-8 for model-checker-consumer),
    /// vs O(N^2) where N = total Bool vars (typically 80-140) for naive Bool equality.
    pub(in crate::pdr::solver) fn discover_bv_group_equalities(&mut self) {
        if self.config.bv_bit_groups.is_empty() {
            return;
        }

        let predicates: Vec<_> = self.problem.predicates().to_vec();

        for pred in &predicates {
            if self.is_cancelled() {
                return;
            }
            if !self.predicate_has_facts(pred.id) {
                continue;
            }

            let groups = self.resolve_bv_groups(pred.id);
            if groups.len() < 2 {
                continue;
            }

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // Check each pair of same-width groups
            for i in 0..groups.len() {
                if self.is_cancelled() {
                    return;
                }
                for j in (i + 1)..groups.len() {
                    if groups[i].width != groups[j].width {
                        continue;
                    }

                    // Build conjunction: (x_0=y_0 ∧ x_1=y_1 ∧ ... ∧ x_n=y_n)
                    let eq_conjuncts: Vec<ChcExpr> = groups[i]
                        .var_indices
                        .iter()
                        .zip(groups[j].var_indices.iter())
                        .map(|(&vi, &vj)| {
                            ChcExpr::eq(
                                ChcExpr::var(canonical_vars[vi].clone()),
                                ChcExpr::var(canonical_vars[vj].clone()),
                            )
                        })
                        .collect();

                    let eq_invariant = ChcExpr::and_all(eq_conjuncts);

                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: #7044 BV group equality candidate for pred {}: \
                             group[{}] (width={}) = group[{}]",
                            pred.id.index(),
                            i,
                            groups[i].width,
                            j,
                        );
                    }

                    let added = self.add_discovered_invariant(pred.id, eq_invariant, 1);

                    if added && self.config.verbose {
                        safe_eprintln!(
                            "PDR: #7044 BV group equality ADDED for pred {}: \
                             group[{}] = group[{}]",
                            pred.id.index(),
                            i,
                            j,
                        );
                    }
                }
            }
        }
    }

    /// Discover BV group constant-value invariants (#7044).
    ///
    /// For each BV group, checks if the group has a constant value (all bits
    /// fixed) that is preserved by transitions. Discovers invariants like
    /// "x is always 0" expressed as `(¬x_0 ∧ ¬x_1 ∧ ... ∧ ¬x_n)`.
    ///
    /// Checks constant 0 (all false) for each group. This covers the common
    /// case of BV variables initialized to zero that are preserved or dead.
    pub(in crate::pdr::solver) fn discover_bv_group_constants(&mut self) {
        if self.config.bv_bit_groups.is_empty() {
            return;
        }

        let predicates: Vec<_> = self.problem.predicates().to_vec();

        for pred in &predicates {
            if self.is_cancelled() {
                return;
            }
            if !self.predicate_has_facts(pred.id) {
                continue;
            }

            let groups = self.resolve_bv_groups(pred.id);
            if groups.is_empty() {
                continue;
            }

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            for (gi, group) in groups.iter().enumerate() {
                if self.is_cancelled() {
                    return;
                }

                // Check constant 0: all bits are false
                let zero_conjuncts: Vec<ChcExpr> = group
                    .var_indices
                    .iter()
                    .map(|&vi| ChcExpr::not(ChcExpr::var(canonical_vars[vi].clone())))
                    .collect();

                let zero_invariant = ChcExpr::and_all(zero_conjuncts);

                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: #7044 BV group constant-zero candidate for pred {}: group[{}] (width={})",
                        pred.id.index(),
                        gi,
                        group.width,
                    );
                }

                let added = self.add_discovered_invariant(pred.id, zero_invariant, 1);

                if added && self.config.verbose {
                    safe_eprintln!(
                        "PDR: #7044 BV group constant-zero ADDED for pred {}: group[{}] = 0",
                        pred.id.index(),
                        gi,
                    );
                }
            }
        }
    }

    /// Discover per-bit constant invariants for BV groups (#7044, Packet 2).
    ///
    /// For each bit in each BV group, checks if that bit is individually constant
    /// (always false or always true). More fine-grained than `discover_bv_group_constants`
    /// which only checks "all bits zero".
    ///
    /// Captures leading-zero patterns: if a BV(8) variable is always < 16,
    /// bits 4-7 are always false. Each constant bit is discovered individually
    /// so partial patterns (e.g., only top 2 bits fixed) are captured.
    ///
    /// Complexity: O(G * W) where G = groups, W = max bit width.
    pub(in crate::pdr::solver) fn discover_bv_group_bit_bounds(&mut self) {
        if self.config.bv_bit_groups.is_empty() {
            return;
        }

        let predicates: Vec<_> = self.problem.predicates().to_vec();

        for pred in &predicates {
            if self.is_cancelled() {
                return;
            }
            if !self.predicate_has_facts(pred.id) {
                continue;
            }

            let groups = self.resolve_bv_groups(pred.id);
            if groups.is_empty() {
                continue;
            }

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            for (gi, group) in groups.iter().enumerate() {
                if self.is_cancelled() {
                    return;
                }

                // Check each bit individually for being constant
                for (bit_pos, &vi) in group.var_indices.iter().enumerate() {
                    if self.is_cancelled() {
                        return;
                    }

                    let var_expr = ChcExpr::var(canonical_vars[vi].clone());

                    // Try bit = false (common for high bits of bounded variables)
                    let false_inv = ChcExpr::not(var_expr.clone());
                    let added = self.add_discovered_invariant(pred.id, false_inv, 1);
                    if added && self.config.verbose {
                        safe_eprintln!(
                            "PDR: #7044 BV bit bound ADDED for pred {}: \
                             group[{}].bit[{}] = false",
                            pred.id.index(),
                            gi,
                            bit_pos,
                        );
                    }

                    // Try bit = true only if false didn't work
                    if !added {
                        let true_inv = var_expr;
                        let added_true = self.add_discovered_invariant(pred.id, true_inv, 1);
                        if added_true && self.config.verbose {
                            safe_eprintln!(
                                "PDR: #7044 BV bit bound ADDED for pred {}: \
                                 group[{}].bit[{}] = true",
                                pred.id.index(),
                                gi,
                                bit_pos,
                            );
                        }
                    }
                }
            }
        }
    }

    /// Discover unsigned ordering invariants between BV groups (#7044, Packet 2).
    ///
    /// For each pair of same-width BV groups, checks if `unsigned(x) <= unsigned(y)`
    /// is an invariant. Encodes the unsigned LE comparison as a Bool formula over
    /// the bit-groups.
    ///
    /// The unsigned LE comparator for N-bit values x, y (bit 0 = LSB) is:
    ///   At each bit position from MSB down: if x[i]=0 or y[i]=1, ok at this level.
    ///   If bits are equal, defer to lower bits. Base case: true (equal values).
    ///
    /// Complexity: O(G^2) group pairs, O(W) formula size per candidate.
    pub(in crate::pdr::solver) fn discover_bv_group_ordering(&mut self) {
        if self.config.bv_bit_groups.is_empty() {
            return;
        }

        let predicates: Vec<_> = self.problem.predicates().to_vec();

        for pred in &predicates {
            if self.is_cancelled() {
                return;
            }
            if !self.predicate_has_facts(pred.id) {
                continue;
            }

            let groups = self.resolve_bv_groups(pred.id);
            if groups.len() < 2 {
                continue;
            }

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // Skip very wide BV groups to avoid large formulas.
            // 32 bits → 96-term formula is reasonable; 64+ gets expensive for SMT.
            const MAX_ORDERING_WIDTH: u32 = 32;

            for i in 0..groups.len() {
                if self.is_cancelled() {
                    return;
                }
                for j in (i + 1)..groups.len() {
                    if groups[i].width != groups[j].width {
                        continue;
                    }
                    if groups[i].width > MAX_ORDERING_WIDTH {
                        continue;
                    }

                    // Build unsigned LE: x <= y
                    let ule_xy = Self::build_unsigned_le(
                        &groups[i].var_indices,
                        &groups[j].var_indices,
                        &canonical_vars,
                    );

                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: #7044 BV group ordering candidate for pred {}: \
                             group[{}] ule group[{}] (width={})",
                            pred.id.index(),
                            i,
                            j,
                            groups[i].width,
                        );
                    }

                    let added = self.add_discovered_invariant(pred.id, ule_xy, 1);
                    if added && self.config.verbose {
                        safe_eprintln!(
                            "PDR: #7044 BV group ordering ADDED for pred {}: \
                             group[{}] ule group[{}]",
                            pred.id.index(),
                            i,
                            j,
                        );
                    }

                    if !added {
                        // Try reverse: y <= x
                        let ule_yx = Self::build_unsigned_le(
                            &groups[j].var_indices,
                            &groups[i].var_indices,
                            &canonical_vars,
                        );
                        let added_rev = self.add_discovered_invariant(pred.id, ule_yx, 1);
                        if added_rev && self.config.verbose {
                            safe_eprintln!(
                                "PDR: #7044 BV group ordering ADDED for pred {}: \
                                 group[{}] ule group[{}]",
                                pred.id.index(),
                                j,
                                i,
                            );
                        }
                    }
                }
            }
        }
    }

    /// Build an unsigned less-or-equal comparator as a Bool formula.
    ///
    /// For bit groups x[0..N-1] and y[0..N-1] (bit 0 = LSB, bit N-1 = MSB):
    ///   At each bit from LSB to MSB, accumulate the comparison.
    ///   Result: true iff unsigned(x) <= unsigned(y).
    fn build_unsigned_le(
        x_indices: &[usize],
        y_indices: &[usize],
        canonical_vars: &[crate::ChcVar],
    ) -> ChcExpr {
        debug_assert_eq!(x_indices.len(), y_indices.len());
        let width = x_indices.len();
        if width == 0 {
            return ChcExpr::bool_const(true);
        }

        // Build from LSB (index 0) to MSB (index width-1).
        // result accumulates "x[0..i] <= y[0..i]" from lower bits up.
        // At each bit i: ule = (¬x[i] ∨ y[i]) ∧ (¬(x[i] = y[i]) ∨ ule_lower)
        let mut result = ChcExpr::bool_const(true);

        for bit in 0..width {
            let xi = ChcExpr::var(canonical_vars[x_indices[bit]].clone());
            let yi = ChcExpr::var(canonical_vars[y_indices[bit]].clone());

            // bit_ok: if x has 1, y must too (¬x[i] ∨ y[i])
            let bit_ok = ChcExpr::or(ChcExpr::not(xi.clone()), yi.clone());

            // bits_equal: x[i] = y[i]
            let bits_equal = ChcExpr::eq(xi, yi);

            // If bits differ, bit_ok decides. If equal, defer to lower bits.
            // ule = bit_ok ∧ (¬bits_equal ∨ result_lower)
            let deferred = ChcExpr::or(ChcExpr::not(bits_equal), result);
            result = ChcExpr::and(bit_ok, deferred);
        }

        result
    }
}
