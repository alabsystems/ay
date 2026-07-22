// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Classification of a bound lemma for subsumption.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BoundKind {
    /// Lower bound: var >= C
    Ge,
    /// Upper bound: var <= C
    Le,
}

impl Frame {
    /// Remove lemmas subsumed by stronger bounds for the same variable.
    ///
    /// Detects syntactic patterns:
    /// - `(>= var C1)` subsumes `(>= var C2)` when C1 > C2
    /// - `(<= var C1)` subsumes `(<= var C2)` when C1 < C2
    /// - `(> var C)` / `(< var C)` normalized to `>=` / `<=` for integers
    /// - `(not (= var C))` / `(distinct var C)` subsumed by bounds excluding C
    ///
    /// No SMT calls — pure syntactic analysis. Returns count of removed lemmas.
    pub(crate) fn subsume_redundant_bounds(&mut self) -> usize {
        use ay_core::kani_compat::DetHashMap as HashMap;

        // Phase 1: Collect strongest bounds per (predicate, variable)
        #[derive(Debug)]
        struct BoundInfo {
            lower: Option<i128>, // var >= lower
            upper: Option<i128>, // var <= upper
        }

        let mut bounds: HashMap<(usize, String), BoundInfo> = HashMap::default();

        for lemma in &self.lemmas {
            if let Some((var_name, op, constant)) = Self::extract_bound(&lemma.formula) {
                let key = (lemma.predicate.index(), var_name);
                let entry = bounds.entry(key).or_insert(BoundInfo {
                    lower: None,
                    upper: None,
                });
                match op {
                    BoundKind::Ge => {
                        entry.lower = Some(entry.lower.map_or(constant, |c| c.max(constant)));
                    }
                    BoundKind::Le => {
                        entry.upper = Some(entry.upper.map_or(constant, |c| c.min(constant)));
                    }
                }
            }
        }

        if bounds.is_empty() {
            return 0;
        }

        // Phase 2: Remove subsumed lemmas
        let original_len = self.lemmas.len();
        let mut keys_to_remove: Vec<(usize, u64)> = Vec::new();

        self.lemmas.retain(|lemma| {
            if let Some((var_name, op, constant)) = Self::extract_bound(&lemma.formula) {
                let key = (lemma.predicate.index(), var_name);
                if let Some(info) = bounds.get(&key) {
                    let subsumed = match op {
                        BoundKind::Ge => info.lower.is_some_and(|strongest| strongest > constant),
                        BoundKind::Le => info.upper.is_some_and(|strongest| strongest < constant),
                    };
                    if subsumed {
                        keys_to_remove.push((lemma.predicate.index(), lemma.formula_hash));
                        return false;
                    }
                }
            }

            if let Some((var_name, excluded_val)) = Self::extract_not_eq(&lemma.formula) {
                let key = (lemma.predicate.index(), var_name);
                if let Some(info) = bounds.get(&key) {
                    let subsumed_by_lower = info.lower.is_some_and(|lb| lb > excluded_val);
                    let subsumed_by_upper = info.upper.is_some_and(|ub| ub < excluded_val);
                    if subsumed_by_lower || subsumed_by_upper {
                        keys_to_remove.push((lemma.predicate.index(), lemma.formula_hash));
                        return false;
                    }
                }
            }

            // #7048: Parity subsumption — (= (mod var k) c) is redundant when
            // var has tight bounds var >= lo AND var <= lo (constant variable).
            // Also subsumes when the range [lo, hi] is narrow enough that all
            // values in the range have the same residue mod k.
            if let Some((var_name, k, c)) = Self::extract_parity(&lemma.formula) {
                let key = (lemma.predicate.index(), var_name);
                if let Some(info) = bounds.get(&key) {
                    if let (Some(lo), Some(hi)) = (info.lower, info.upper) {
                        // Constant variable: lo == hi -> parity is trivially implied
                        if lo == hi {
                            keys_to_remove.push((lemma.predicate.index(), lemma.formula_hash));
                            return false;
                        }
                        // Narrow range: if all values in [lo, hi] have residue c mod k,
                        // then the parity lemma is implied by the bounds.
                        if k > 0 && hi - lo < k {
                            let all_same_residue = (lo..=hi).all(|v| v.rem_euclid(k) == c);
                            if all_same_residue {
                                keys_to_remove.push((lemma.predicate.index(), lemma.formula_hash));
                                return false;
                            }
                        }
                    }
                }
            }

            // #7048: All-constant subsumption — any lemma whose Int variables
            // ALL have tight bounds (lo == hi) is trivially implied by the
            // bounds themselves. Skip bounds lemmas (they're the sources).
            // This catches relational equalities like (= A (+ (* -3 B) 1))
            // and orderings like (>= A B) when A and B are both constant.
            if Self::extract_bound(&lemma.formula).is_none() {
                let int_vars = lemma.formula.vars();
                let int_vars: Vec<_> = int_vars
                    .iter()
                    .filter(|v| matches!(v.sort, ChcSort::Int))
                    .collect();
                if !int_vars.is_empty() {
                    let all_constant = int_vars.iter().all(|v| {
                        let key = (lemma.predicate.index(), v.name.clone());
                        bounds.get(&key).is_some_and(|info| {
                            matches!((info.lower, info.upper), (Some(lo), Some(hi)) if lo == hi)
                        })
                    });
                    if all_constant {
                        keys_to_remove.push((lemma.predicate.index(), lemma.formula_hash));
                        return false;
                    }
                }
            }

            true
        });

        self.rebuild_lemma_keys();

        let removed = original_len - self.lemmas.len();
        if removed > 0 {
            for (pred_idx, _) in &keys_to_remove {
                let pred = PredicateId::new(*pred_idx as u32);
                *self.lemma_revisions.entry(pred).or_default() += 1;
            }
            // Release excess capacity after bulk eviction (#8601).
            self.lemmas.shrink_to_fit();
            self.lemma_keys.shrink_to_fit();
        }
        self.debug_assert_frame_invariants();
        removed
    }

    /// Remove lemmas subsumed by the conjunction of other lemmas (SMT-based).
    ///
    /// Ports Z3 Spacer's `unit_subsumption_tactic` approach:
    /// for each lemma L in a predicate group, checks if the conjunction of
    /// all other lemmas implies L (i.e., `AND(others) AND NOT(L)` is UNSAT).
    /// If so, L is redundant and removed.
    ///
    /// This catches patterns that syntactic subsumption misses:
    /// - `x >= 0 AND y >= 0` subsumes `x + y >= 0`
    /// - Multi-variable relational implications
    ///
    /// Only runs on predicate groups with 2+ lemmas and <= `max_group_size`.
    /// Returns count of removed lemmas.
    pub(crate) fn subsume_semantic(
        &mut self,
        smt: &mut SmtContext,
        max_group_size: usize,
    ) -> usize {
        // Group lemma indices by predicate
        let mut pred_groups: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
        for (idx, lemma) in self.lemmas.iter().enumerate() {
            pred_groups
                .entry(lemma.predicate.index())
                .or_default()
                .push(idx);
        }

        let mut deleted: Vec<bool> = vec![false; self.lemmas.len()];
        let mut deleted_count = 0usize;

        // Sort groups by predicate index for deterministic subsumption (#3060)
        let mut sorted_groups: Vec<_> = pred_groups.into_iter().collect();
        sorted_groups.sort_unstable_by_key(|(pid, _)| *pid);
        for (_, indices) in &sorted_groups {
            let group_size = indices.len();
            if group_size < 2 || group_size > max_group_size {
                continue;
            }

            // For each lemma in the group, check if it's implied by the others
            for &target_idx in indices {
                if deleted[target_idx] {
                    continue;
                }

                // Build conjunction of all other non-deleted lemmas in this predicate
                let mut others: Vec<ChcExpr> = Vec::with_capacity(group_size - 1);
                for &other_idx in indices {
                    if other_idx != target_idx && !deleted[other_idx] {
                        others.push(self.lemmas[other_idx].formula.clone());
                    }
                }

                if others.is_empty() {
                    continue;
                }

                // Query: AND(others) AND NOT(target) — UNSAT means target is subsumed
                let conjunction = others
                    .into_iter()
                    .reduce(ChcExpr::and)
                    .expect("others is non-empty");
                let negated_target = ChcExpr::not(self.lemmas[target_idx].formula.clone());
                let query = ChcExpr::and(conjunction, negated_target);

                smt.reset();
                match smt.check_sat(&query) {
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {
                        deleted[target_idx] = true;
                        deleted_count += 1;
                    }
                    _ => {}
                }
            }
        }

        if deleted_count == 0 {
            return 0;
        }

        // Remove deleted lemmas and update bookkeeping
        let mut affected_preds: FxHashSet<PredicateId> = FxHashSet::default();

        let mut idx = 0;
        self.lemmas.retain(|lemma| {
            let keep = !deleted[idx];
            if !keep {
                affected_preds.insert(lemma.predicate);
            }
            idx += 1;
            keep
        });

        self.rebuild_lemma_keys();
        for pred in &affected_preds {
            *self.lemma_revisions.entry(*pred).or_default() += 1;
        }
        // Release excess capacity after bulk eviction (#8601).
        self.lemmas.shrink_to_fit();
        self.lemma_keys.shrink_to_fit();

        self.debug_assert_frame_invariants();
        deleted_count
    }

    /// Extract a bound pattern: `(>= var C)`, `(> var C)`, `(<= var C)`, `(< var C)`.
    /// Normalizes `>` to `>=` and `<` to `<=` for integer arithmetic.
    fn extract_bound(formula: &ChcExpr) -> Option<(String, BoundKind, i128)> {
        if let ChcExpr::Op(op, args) = formula {
            if args.len() == 2 {
                match (op, args[0].as_ref(), args[1].as_ref()) {
                    (ChcOp::Ge, ChcExpr::Var(v), ChcExpr::Int(c)) => {
                        return Some((v.name.clone(), BoundKind::Ge, *c));
                    }
                    (ChcOp::Gt, ChcExpr::Var(v), ChcExpr::Int(c)) => {
                        return Some((v.name.clone(), BoundKind::Ge, c.checked_add(1)?));
                    }
                    (ChcOp::Le, ChcExpr::Var(v), ChcExpr::Int(c)) => {
                        return Some((v.name.clone(), BoundKind::Le, *c));
                    }
                    (ChcOp::Lt, ChcExpr::Var(v), ChcExpr::Int(c)) => {
                        return Some((v.name.clone(), BoundKind::Le, c.checked_sub(1)?));
                    }
                    (ChcOp::Ge, ChcExpr::Int(c), ChcExpr::Var(v)) => {
                        return Some((v.name.clone(), BoundKind::Le, *c));
                    }
                    (ChcOp::Gt, ChcExpr::Int(c), ChcExpr::Var(v)) => {
                        return Some((v.name.clone(), BoundKind::Le, c.checked_sub(1)?));
                    }
                    (ChcOp::Le, ChcExpr::Int(c), ChcExpr::Var(v)) => {
                        return Some((v.name.clone(), BoundKind::Ge, *c));
                    }
                    (ChcOp::Lt, ChcExpr::Int(c), ChcExpr::Var(v)) => {
                        return Some((v.name.clone(), BoundKind::Ge, c.checked_add(1)?));
                    }
                    _ => {}
                }
            }
        }
        None
    }

    /// Extract `(not (= var C))` or `(distinct var C)` pattern.
    fn extract_not_eq(formula: &ChcExpr) -> Option<(String, i128)> {
        match formula {
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                if let ChcExpr::Op(ChcOp::Eq, eq_args) = args[0].as_ref() {
                    if eq_args.len() == 2 {
                        match (eq_args[0].as_ref(), eq_args[1].as_ref()) {
                            (ChcExpr::Var(v), ChcExpr::Int(c))
                            | (ChcExpr::Int(c), ChcExpr::Var(v)) => {
                                return Some((v.name.clone(), *c));
                            }
                            _ => {}
                        }
                    }
                }
            }
            ChcExpr::Op(ChcOp::Ne, args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Var(v), ChcExpr::Int(c)) | (ChcExpr::Int(c), ChcExpr::Var(v)) => {
                        return Some((v.name.clone(), *c));
                    }
                    _ => {}
                }
            }
            _ => {}
        }
        None
    }

    /// Extract `(= (mod var k) c)` parity pattern. Returns (var_name, k, c).
    fn extract_parity(formula: &ChcExpr) -> Option<(String, i128, i128)> {
        let ChcExpr::Op(ChcOp::Eq, args) = formula else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }
        // Try both orderings: (mod var k) = c or c = (mod var k)
        Self::extract_mod_var_k(&args[0], &args[1])
            .or_else(|| Self::extract_mod_var_k(&args[1], &args[0]))
    }

    /// Helper: extract (var_name, k, c) from mod_side=(mod var k), const_side=c.
    fn extract_mod_var_k(mod_side: &ChcExpr, const_side: &ChcExpr) -> Option<(String, i128, i128)> {
        let ChcExpr::Op(ChcOp::Mod, mod_args) = mod_side else {
            return None;
        };
        if mod_args.len() != 2 {
            return None;
        }
        let ChcExpr::Var(v) = mod_args[0].as_ref() else {
            return None;
        };
        let ChcExpr::Int(k) = mod_args[1].as_ref() else {
            return None;
        };
        if *k <= 0 {
            return None;
        }
        let ChcExpr::Int(c) = const_side else {
            return None;
        };
        Some((v.name.clone(), *k, *c))
    }
}
