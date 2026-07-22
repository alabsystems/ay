// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! BV bit-group generalizer for bit-blasted PDR problems (#5877).
//!
//! After BvToBool preprocessing, each BV(N) argument becomes N consecutive Bool
//! arguments. The standard `DropLiteralGeneralizer` tries dropping one Bool at a
//! time — O(N_bits) SMT queries. This generalizer knows the BV grouping and
//! tries dropping all N bits of a BV variable at once, reducing to O(N_bv_vars).
//!
//! Reference: Z3 Spacer `expand_literals` in `spacer_util.cpp:319-374`.

use crate::expr::ChcExpr;

use super::{LemmaGeneralizer, TransitionSystemRef};

/// BV bit-group generalizer: drops entire BV variable groups at once (#5877).
///
/// For each BV bit group `(start, width)`:
/// 1. Identify the `width` conjuncts corresponding to this group
/// 2. Try removing all of them at once
/// 3. If inductive, the entire BV variable is irrelevant
pub(crate) struct BvBitGroupGeneralizer {
    groups: Vec<(usize, u32)>,
}

impl BvBitGroupGeneralizer {
    pub(crate) fn new(groups: Vec<(usize, u32)>) -> Self {
        Self { groups }
    }

    /// Extract the canonical arg index from a Bool point-assignment conjunct.
    /// Canonical vars are named `__p{N}_a{M}`.
    fn canonical_arg_index(expr: &ChcExpr) -> Option<usize> {
        let var_name = match expr {
            ChcExpr::Var(v) => &v.name,
            ChcExpr::Op(crate::expr::ChcOp::Not, args) if args.len() == 1 => {
                if let ChcExpr::Var(v) = &*args[0] {
                    &v.name
                } else {
                    return None;
                }
            }
            _ => return None,
        };
        let a_pos = var_name.rfind("_a")?;
        var_name[a_pos + 2..].parse::<usize>().ok()
    }

    /// Check if a conjunct index belongs to a specific group.
    fn in_group(idx: usize, start: usize, width: u32) -> bool {
        idx >= start && idx < start + width as usize
    }

    /// Check if a conjunct (by its canonical arg index) is in any dropped group.
    fn is_in_dropped_group(&self, idx: usize, dropped_groups: &[bool]) -> bool {
        dropped_groups.iter().enumerate().any(|(gi, &dropped)| {
            if !dropped {
                return false;
            }
            let (start, width) = self.groups[gi];
            Self::in_group(idx, start, width)
        })
    }

    /// Filter conjuncts, keeping those not in the specified group or any dropped groups.
    fn filter_conjuncts(
        &self,
        conjuncts: &[ChcExpr],
        conjunct_indices: &[Option<usize>],
        dropped_groups: &[bool],
        exclude_group: Option<(usize, u32)>,
    ) -> Vec<ChcExpr> {
        conjuncts
            .iter()
            .enumerate()
            .filter(|(ci, _)| {
                let Some(idx) = conjunct_indices[*ci] else {
                    return true;
                };
                if let Some((start, width)) = exclude_group {
                    if Self::in_group(idx, start, width) {
                        return false;
                    }
                }
                !self.is_in_dropped_group(idx, dropped_groups)
            })
            .map(|(_, c)| c.clone())
            .collect()
    }
}

impl LemmaGeneralizer for BvBitGroupGeneralizer {
    fn generalize(&self, lemma: &ChcExpr, level: u32, ts: &mut dyn TransitionSystemRef) -> ChcExpr {
        if self.groups.is_empty() {
            return lemma.clone();
        }
        let conjuncts = lemma.collect_conjuncts();
        if conjuncts.len() <= 1 {
            return lemma.clone();
        }
        let conjunct_indices: Vec<Option<usize>> =
            conjuncts.iter().map(Self::canonical_arg_index).collect();
        let mut dropped_groups: Vec<bool> = vec![false; self.groups.len()];

        for (gi, &(start, width)) in self.groups.iter().enumerate() {
            let has_group = conjunct_indices
                .iter()
                .any(|opt| opt.map_or(false, |idx| Self::in_group(idx, start, width)));
            if !has_group {
                continue;
            }
            let candidate = self.filter_conjuncts(
                &conjuncts,
                &conjunct_indices,
                &dropped_groups,
                Some((start, width)),
            );
            if candidate.is_empty() {
                continue;
            }
            if ts.check_inductive(&ChcExpr::and_all(candidate.iter().cloned()), level) {
                dropped_groups[gi] = true;
            }
        }

        if !dropped_groups.iter().any(|&d| d) {
            return lemma.clone();
        }
        let result = self.filter_conjuncts(&conjuncts, &conjunct_indices, &dropped_groups, None);
        if result.is_empty() {
            return lemma.clone();
        }
        ChcExpr::and_all(result.iter().cloned())
    }

    fn name(&self) -> &'static str {
        "bv-bit-group"
    }
}
