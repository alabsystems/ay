// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Const-array facts over whole equivalence classes (2026-09-24 arrays
//! fix-up, session 5). The fail-closed conflict verifier
//! (`verify_mixed_conflict_semantic`) re-solves a conflict's literals in a
//! fresh solver; a fact the search's solver reached through an atom or an
//! event the fresh one never sees made it call a valid conflict SATISFIABLE,
//! and the whole AUFLIA pass then fail-closed to `unknown`.
//!
//! * Store chains over const-arrays with provably distinct defaults in ONE
//!   class (below).
//! * Reads of an array whose class holds a const-array
//!   ([`ArraySolver::enqueue_const_reads_by_class`]).
//!
//! `store_chain_default_conflict_reasons` draws the conflict for a DIRECT
//! equality atom between two such chains. Two chains the equality graph merges
//! only transitively -- `a2 = store(K0, i, v)` and `a2 = store(K1, i, v)` --
//! are equal all the same, and the fresh solver the fail-closed conflict
//! verifier (`verify_mixed_conflict_semantic`) runs on a conflict's literals
//! sees only such paths: the search derived the conflict on an equality atom
//! between the two chains, explained it by the path through `a2`, and the
//! verifier, holding no atom between the chains, called the three literals
//! SATISFIABLE and the whole AUFLIA pass fail-closed to `unknown` (the
//! verifier's variant d4d_013, `sat` at once on main and z3 5.1.0).

use super::*;

/// At most this many distinct const-array defaults are compared per class.
const MAX_CLASS_DEFAULTS: usize = 16;

impl ArraySolver<'_> {
    /// A conflict when some equivalence class of a TRUE array equality holds
    /// two store chains (or const-arrays) over const-arrays with provably
    /// distinct defaults and the index sort is infinite: some index misses
    /// every write of both finite chains, and there they read the two
    /// defaults. The conflict carries the path that makes the two members
    /// equal, the paths to both const-arrays and the defaults' distinctness;
    /// no premise about the written indices.
    pub(crate) fn check_store_chain_class_default_conflict(&self) -> Option<TheoryResult> {
        let mut seen_classes: HashSet<TermId> = HashSet::default();
        for &(eq_term, lhs, _) in &self.pending_array_eqs {
            if self.assigns.get(&eq_term) != Some(&true) {
                continue;
            }
            let Sort::Array(array_sort) = self.terms.sort(lhs) else {
                continue;
            };
            if !matches!(array_sort.index_sort, Sort::Int | Sort::Real) {
                continue;
            }
            let class = self.equiv_class_shared(lhs);
            let Some(&representative) = class.iter().min() else {
                continue;
            };
            if !seen_classes.insert(representative) {
                continue;
            }
            if let Some(conflict) = self.class_default_conflict(&class) {
                return Some(conflict);
            }
        }
        None
    }

    fn class_default_conflict(&self, class: &[TermId]) -> Option<TheoryResult> {
        let mut members: Vec<TermId> = class.to_vec();
        members.sort_unstable_by_key(|t| t.0);
        // One member per distinct default term, with the reasons that reach
        // its const-array.
        let mut chains: Vec<(TermId, TermId, Vec<TheoryLit>)> = Vec::new();
        for member in members {
            let base = self.structural_store_base(member);
            let found = if base == member {
                self.const_array_cache
                    .get(&member)
                    .map(|&default| (default, Vec::new()))
            } else {
                self.find_const_array_through_eq(base)
            };
            let Some((default, base_reasons)) = found else {
                continue;
            };
            if chains.iter().any(|&(_, seen, _)| seen == default) {
                continue;
            }
            chains.push((member, default, base_reasons));
            if chains.len() >= MAX_CLASS_DEFAULTS {
                break;
            }
        }
        for (i, (lhs, lhs_default, lhs_reasons)) in chains.iter().enumerate() {
            for (rhs, rhs_default, rhs_reasons) in &chains[i + 1..] {
                let Some(mut reasons) =
                    self.explain_distinct_if_provable(*lhs_default, *rhs_default)
                else {
                    continue;
                };
                let Some(path) = self.explain_equal_if_provable(*lhs, *rhs) else {
                    continue;
                };
                reasons.extend(path);
                reasons.extend(lhs_reasons.iter().copied());
                reasons.extend(rhs_reasons.iter().copied());
                if let Some(conflict) = self.conflict_reasons_to_lemma(reasons) {
                    return Some(conflict);
                }
            }
        }
        None
    }

    /// Queue `(select, const-array)` for every read whose array's class holds
    /// a const-array, for `check_const_array_read` to decide.
    ///
    /// That queue is event-driven: a read is queued when it is registered or
    /// when an equality notification pairs it with a const-array, and a read
    /// that became equal to a const-array only through the rest of its class
    /// can be missed. On fresh storeeq_2809_0025 (`sat` at once on main) the
    /// search's conflict `{b = K1, a0 = b, 7 = (select a0 j), ...}` reached the
    /// fresh verification solver with the class of `a0` also holding two store
    /// chains; the read was never queued there, `final_check` answered `Sat`
    /// (with the three literals alone it finds the conflict) and the verifier
    /// rejected the conflict. `final_check` now queues every such read once per
    /// pass; the check keeps both of its guards (the equality must be provable
    /// without speculative edges, the value distinctness must carry reasons).
    pub(crate) fn enqueue_const_reads_by_class(&mut self) {
        if self.const_array_cache.is_empty() {
            return;
        }
        let mut reads: Vec<(TermId, TermId)> = self
            .select_cache
            .iter()
            .map(|(&select, &(array, _))| (select, array))
            .collect();
        reads.sort_unstable_by_key(|&(select, _)| select.0);
        for (select, array) in reads {
            let class = self.equiv_class_shared(array);
            for &member in class.iter() {
                if self.const_array_cache.contains_key(&member) {
                    self.pending_const_reads.push((select, member));
                }
            }
        }
    }

    /// The OUTERMOST write of a chain equal to `const(d)` is effective whatever
    /// the chain's other indices are, so `store(.., t, v) = const(d)` with a
    /// structurally distinct `v != d` is a conflict under the equality, the
    /// path to the const-array and the path to the store alone.
    /// `check_const_array_store_chain_conflict` otherwise needs the chain's
    /// COMPLETE effective map (every index relation decided) before it reads
    /// any written value. Fresh storeeq_2809_0597 (`sat` at once on main):
    /// `(= K1 (store (store (store K1 j j) i 2) (+ j 2) 3))` alone is a
    /// conflict (`3 != 1` at `j + 2`), but with `i` and `j` unrelated the
    /// fail-closed conflict verifier called it satisfiable.
    ///
    /// Like the complete-map obligation, only a STRUCTURAL distinctness
    /// (empty reasons) fires, which keeps the emission bounded.
    pub(crate) fn const_chain_outermost_write_conflict(
        &self,
        eq_term: TermId,
        const_reasons: &[TheoryLit],
        default_val: TermId,
        chain_side: TermId,
    ) -> Option<TheoryResult> {
        let (_, value, store_reasons) = self.outermost_store_write(chain_side)?;
        let value_reasons = self.explain_distinct_if_provable(value, default_val)?;
        if !value_reasons.is_empty() {
            return None;
        }
        let mut reasons = vec![TheoryLit::new(eq_term, true)];
        reasons.extend(const_reasons.iter().copied());
        reasons.extend(store_reasons);
        self.conflict_reasons_to_lemma(reasons)
    }
}
