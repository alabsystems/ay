// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LraSolver {
    /// Maximum row width for touched-row bound analysis (#6617).
    /// Used by `compute_implied_bounds`. The Z3 reference (`bound_analyzer_on_row`)
    /// has no width cap; 300 is the current widened limit from #6615.
    pub(crate) const MAX_TOUCHED_ROW_BOUND_SCAN_WIDTH: usize = 300;

    pub(crate) fn fixed_term_sort_key(&self, var_id: u32) -> Option<bool> {
        let term = *self.var_to_term.get(&var_id)?;
        Some(matches!(self.terms().sort(term), Sort::Int))
    }

    /// Self-verified row fixing (#qfuflia-a5-fixed-eqs): when `var` is
    /// implied-fixed via a tableau row whose every OTHER variable is
    /// DIRECT-bounds-fixed, recompute the value from the row equation and
    /// return it with the union of all support atoms. This does not trust
    /// the stored implied bound or the generic reason collector (whose
    /// completeness accounting was measured to lie for this flow): the
    /// entailment `atoms => var = value` is re-derived here from row
    /// semantics (basic = sum coeffs*vars + constant) and direct bounds
    /// only. Returns None unless every support var is direct-fixed with
    /// non-sentinel atom reasons.
    pub fn row_fixing_with_direct_support(
        &self,
        var_id: u32,
    ) -> Option<(Rational, Vec<TheoryLit>)> {
        let mut visiting = std::collections::HashSet::new();
        self.row_fixing_verified(var_id, &mut visiting, 0)
    }

    /// Recursive worker: a var's fixing verifies when its bounds pin it
    /// DIRECTLY (atom reasons), or when it is the basic var of a row whose
    /// every other variable's fixing verifies recursively. Cycle-guarded by
    /// `visiting`; depth-capped. The value is recomputed from row semantics
    /// at each level and cross-checked against the stored implied bound.
    fn row_fixing_verified(
        &self,
        var_id: u32,
        visiting: &mut std::collections::HashSet<u32>,
        depth: usize,
    ) -> Option<(Rational, Vec<TheoryLit>)> {
        if depth > 16 || !visiting.insert(var_id) {
            return None;
        }
        let result = self.row_fixing_verified_inner(var_id, visiting, depth);
        visiting.remove(&var_id);
        result
    }

    fn row_fixing_verified_inner(
        &self,
        var_id: u32,
        visiting: &mut std::collections::HashSet<u32>,
        depth: usize,
    ) -> Option<(Rational, Vec<TheoryLit>)> {
        let vi = var_id as usize;
        // Direct fixing first: asserted lo == hi with atom reasons.
        if let Some(info) = self.vars.get(vi) {
            if let (Some(lo), Some(hi)) = (&info.lower, &info.upper) {
                if !lo.strict && !hi.strict && lo.value == hi.value {
                    let mut reasons = Vec::new();
                    for (term, val) in lo.reason_pairs().chain(hi.reason_pairs()) {
                        if term.is_sentinel() {
                            continue;
                        }
                        let lit = TheoryLit::new(term, val);
                        if !reasons.contains(&lit) {
                            reasons.push(lit);
                        }
                    }
                    if !reasons.is_empty() {
                        return Some((lo.value.clone(), reasons));
                    }
                }
            }
        }
        // Row-verified fixing: recurse over the row's support variables.
        let (Some(lb), Some(ub)) = self.implied_bounds.get(vi)?.clone() else {
            return None;
        };
        if lb.strict || ub.strict || lb.value != ub.value || lb.row_idx == usize::MAX {
            return None;
        }
        let row = self.rows.get(lb.row_idx)?;
        if row.basic_var != var_id {
            return None; // only the basic-var direction is a definition
        }
        let mut value = row.constant.clone();
        let mut reasons: Vec<TheoryLit> = Vec::new();
        for &(v, ref coeff) in &row.coeffs {
            if v == var_id {
                return None; // self-referential row: bail
            }
            let (vval, vreasons) = self.row_fixing_verified(v, visiting, depth + 1)?;
            value += &(&vval * coeff);
            for lit in vreasons {
                if !reasons.contains(&lit) {
                    reasons.push(lit);
                }
            }
        }
        if value != lb.value {
            return None; // stored implied bound disagrees with the row: stale
        }
        Some((value, reasons))
    }

    /// Debug view of a var's implied + direct bounds
    /// (#qfuflia-a5-fixed-eqs audit).
    pub fn implied_bounds_debug(&self, var_id: u32) -> String {
        let vi = var_id as usize;
        let direct = self.vars.get(vi).map(|i| {
            (
                i.lower
                    .as_ref()
                    .map(|b| format!("{}{}", b.value, if b.strict { "<" } else { "<=" })),
                i.upper
                    .as_ref()
                    .map(|b| format!("{}{}", b.value, if b.strict { "<" } else { "<=" })),
            )
        });
        let implied = self.implied_bounds.get(vi).map(|(l, u)| {
            (
                l.as_ref().map(|b| {
                    format!(
                        "{}{} row={}",
                        b.value,
                        if b.strict { "<" } else { "<=" },
                        if b.row_idx == usize::MAX {
                            "direct".to_string()
                        } else {
                            b.row_idx.to_string()
                        }
                    )
                }),
                u.as_ref().map(|b| {
                    format!(
                        "{}{} row={}",
                        b.value,
                        if b.strict { "<" } else { "<=" },
                        if b.row_idx == usize::MAX {
                            "direct".to_string()
                        } else {
                            b.row_idx.to_string()
                        }
                    )
                }),
            )
        });
        // Row contents for any non-sentinel deriving rows.
        let mut rows = String::new();
        if let Some((l, u)) = self.implied_bounds.get(vi) {
            for b in [l, u].into_iter().flatten() {
                if b.row_idx != usize::MAX {
                    if let Some(row) = self.rows.get(b.row_idx) {
                        rows.push_str(&format!(" row{}:[{:?}]", b.row_idx, row));
                    }
                }
            }
        }
        format!("direct={direct:?} implied={implied:?}{rows}")
    }

    /// DIRECT-bounds-only fixed key (#qfuflia-a5-fixed-eqs): Some only when
    /// the var's ASSERTED bounds pin it (lower == upper, both non-strict).
    /// Implied-bound fixings are excluded — their reason chains are the
    /// historically-subtle part (cf. #6564) and under-justified reasons on
    /// exported equalities poison conflict analysis into false refutations
    /// (measured twice on xs-06-07-4-5-4-2).
    pub fn direct_fixed_term_key(&self, var_id: u32) -> Option<(Rational, bool)> {
        let is_int = self.fixed_term_sort_key(var_id)?;
        let info = self.vars.get(var_id as usize)?;
        let (Some(lower), Some(upper)) = (&info.lower, &info.upper) else {
            return None;
        };
        if lower.strict || upper.strict || lower.value != upper.value {
            return None;
        }
        Some((lower.value.clone(), is_int))
    }

    /// Fixed value and integrality of `var_id` if its lower and upper bounds
    /// (asserted or implied) pin it to a single non-strict value.
    ///
    /// Bound checks run BEFORE the sort-key lookup (#certora-fixed-key-order):
    /// the overwhelmingly-common outcome on large industrial files is "not
    /// pinned", which the bound vectors answer with two indexed loads, while
    /// `fixed_term_sort_key` costs a `var_to_term` hash lookup. The result is
    /// identical either way — an unpinned var returns `None` regardless of
    /// whether it has a term, and a pinned termless var returns `None` in
    /// both orders.
    pub fn fixed_term_key(&self, var_id: u32) -> Option<(Rational, bool)> {
        let vi = var_id as usize;

        if let Some((Some(lb), Some(ub))) = self.implied_bounds.get(vi) {
            if !lb.strict && !ub.strict && lb.value == ub.value {
                let is_int = self.fixed_term_sort_key(var_id)?;
                return Some((lb.value.clone(), is_int));
            }
        }

        let info = self.vars.get(vi)?;
        let (Some(lower), Some(upper)) = (&info.lower, &info.upper) else {
            return None;
        };
        if lower.strict || upper.strict || lower.value != upper.value {
            return None;
        }
        let is_int = self.fixed_term_sort_key(var_id)?;
        Some((lower.value.clone(), is_int))
    }

    pub(crate) fn enqueue_pending_fixed_term_equality(&mut self, var_id: u32, representative: u32) {
        if var_id == representative {
            return;
        }
        if self
            .pending_fixed_term_equalities
            .iter()
            .any(|&(lhs, rhs)| lhs == var_id && rhs == representative)
        {
            return;
        }
        self.pending_fixed_term_equalities
            .push((var_id, representative));
    }

    pub(crate) fn reassign_fixed_term_representative(
        &mut self,
        key: &(Rational, bool),
        removed_var: u32,
    ) {
        if self.fixed_term_value_table.get(key) != Some(&removed_var) {
            return;
        }

        self.fixed_term_value_table.remove(key);

        let replacement = self
            .fixed_term_value_members
            .iter()
            .find_map(|(&candidate, candidate_key)| (candidate_key == key).then_some(candidate));
        let Some(representative) = replacement else {
            return;
        };

        self.fixed_term_value_table
            .insert(key.clone(), representative);

        let followers = self
            .fixed_term_value_members
            .iter()
            .filter_map(|(&candidate, candidate_key)| {
                (candidate != representative && candidate_key == key).then_some(candidate)
            })
            .collect::<Vec<_>>();
        for candidate in followers {
            self.enqueue_pending_fixed_term_equality(candidate, representative);
        }
    }

    pub(crate) fn register_fixed_term_var(&mut self, var_id: u32) {
        let current_key = self.fixed_term_key(var_id);
        // Fast exit for the overwhelmingly-common untracked case
        // (#certora-fixed-key-order): an unpinned var that was never
        // registered needs no bookkeeping — and cloning the previous key's
        // `Rational` for every scanned var was a measurable cost on
        // full-scan overlays over 10^5 vars.
        if current_key.is_none() && !self.fixed_term_value_members.contains_key(&var_id) {
            return;
        }
        let previous_key = self.fixed_term_value_members.get(&var_id).cloned();

        if current_key == previous_key {
            if let Some(key) = current_key {
                self.fixed_term_value_table.entry(key).or_insert(var_id);
            }
            return;
        }

        if previous_key.is_some() {
            self.pending_fixed_term_equalities
                .retain(|(lhs, rhs)| *lhs != var_id && *rhs != var_id);
        }

        if let Some(old_key) = previous_key {
            self.fixed_term_value_members.remove(&var_id);
            self.reassign_fixed_term_representative(&old_key, var_id);
        }

        let Some(key) = current_key else {
            return;
        };

        let representative = self.fixed_term_value_table.get(&key).copied();
        self.fixed_term_value_members.insert(var_id, key.clone());

        match representative {
            Some(existing) if existing != var_id => {
                self.enqueue_pending_fixed_term_equality(var_id, existing);
            }
            _ => {
                self.fixed_term_value_table.insert(key, var_id);
            }
        }
    }
}
