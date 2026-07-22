// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Atom registration and literal assertion for the LRA theory solver.

use super::*;

impl LraSolver {
    pub(super) fn register_atom_impl(&mut self, atom: TermId) {
        // Unwrap NOT and cache (#6590 Packet 1). Copy inner TermId to avoid
        // holding a borrow on self.terms() while mutating cache fields.
        let (term, is_not) = {
            let td = self.terms().get(atom);
            match td {
                TermData::Not(inner) => (*inner, true),
                _ => (atom, false),
            }
        };
        self.not_inner_cache.entry(atom).or_insert((term, is_not));
        // Cache constant-Bool status for check() hot path (#6590 Packet 1).
        if !self.const_bool_cache.contains_key(&term) {
            let val = {
                let td = self.terms().get(term);
                if let TermData::Const(Constant::Bool(b)) = td {
                    Some(*b)
                } else {
                    None
                }
            };
            self.const_bool_cache.insert(term, val);
        }
        // Cache refinement eligibility and integer-sort for bound refinement
        // warm path (#6590 Packet 1).
        if !self.refinement_eligible_cache.contains_key(&term) {
            let eligible = self.term_supports_bound_refinement(term);
            self.refinement_eligible_cache.insert(term, eligible);
        }
        if !self.is_integer_sort_cache.contains_key(&term) {
            let is_int = *self.terms().sort(term) == Sort::Int;
            self.is_integer_sort_cache.insert(term, is_int);
        }
        // Fast path: if this atom was already fully registered (parsing + indexing),
        // skip structural work but refresh dirty reseeding. This is essential for the
        // structural snapshot path (#6590) where atom_index, var_to_atoms, etc. are
        // already populated from a previous iteration. Without this guard, imported
        // atoms would get duplicate index entries.
        if self.registered_atoms.contains(&term) {
            if let Some(Some(info)) = self.atom_cache.get(&term) {
                if info.expr.coeffs.len() > 1 {
                    for &(v, _) in &info.expr.coeffs {
                        self.propagation_dirty_vars.insert(v);
                    }
                    let mut key: Vec<_> = info
                        .expr
                        .coeffs
                        .iter()
                        .map(|(v, c)| (*v, c.clone()))
                        .collect();
                    key.sort_by_key(|(v, _)| *v);
                    let key_rat: Vec<(u32, Rational)> =
                        key.iter().map(|(v, c)| (*v, Rational::from(c))).collect();
                    if let Some(&(slack, _)) = self.expr_to_slack.get(&key_rat) {
                        self.propagation_dirty_vars.insert(slack);
                    }
                } else if let Some(&(var, _)) = info.expr.coeffs.first() {
                    self.propagation_dirty_vars.insert(var);
                }
            }
            return;
        }
        let parsed = if let Some(cached) = self.atom_cache.get(&term) {
            cached.clone()
        } else {
            // Set current_parsing_atom so that parse_linear_expr can track
            // which atom has unsupported sub-expressions (#6167). Without this,
            // mark_current_atom_unsupported() is a no-op and the unsupported
            // status is lost — causing false SAT when check() finds the cache hit.
            self.current_parsing_atom = Some(term);
            let mut parsed = self.parse_atom(term).map(|(expr, is_le, strict)| {
                let is_eq = matches!(self.terms().get(term), TermData::App(Symbol::Named(name), _) if name == "=");
                let is_distinct = matches!(self.terms().get(term), TermData::App(Symbol::Named(name), _) if name == "distinct");
                let has_unsupported = self.persistent_unsupported_atoms.contains(&term);
                ParsedAtomInfo { expr, is_le, strict, is_eq, is_distinct, has_unsupported, compound_slack: None }
            });
            self.current_parsing_atom = None;
            // Precompute compound_slack for atoms with multiple variables (#perf).
            // Avoids per-assertion Vec alloc + BigRational clone + sort in assert_literal.
            if let Some(info) = parsed.as_mut() {
                if !info.is_eq && !info.is_distinct && info.expr.coeffs.len() > 1 {
                    let mut key: Vec<(u32, Rational)> = info
                        .expr
                        .coeffs
                        .iter()
                        .map(|(v, c)| (*v, c.clone()))
                        .collect();
                    key.sort_by_key(|(v, _)| *v);
                    let key_rat: Vec<(u32, Rational)> =
                        key.iter().map(|(v, c)| (*v, Rational::from(c))).collect();
                    if let Some(&(slack, _)) = self.expr_to_slack.get(&key_rat) {
                        info.compound_slack = Some(slack);
                    }
                }
            }
            self.atom_cache.insert(term, parsed.clone());
            parsed
        };
        let Some(info) = parsed else { return };
        // #8373: Skip atom_index registration for atoms with unsupported
        // sub-expressions (e.g., ITE conditions unknown at registration time).
        // The expression contains fresh variables that over-approximate the ITE,
        // causing wrong bound values in atom_index. Propagations based on these
        // wrong bounds are unsound (caught by debug-only
        // verify_propagation_semantic but pass through in release builds,
        // corrupting the search and causing model-validation-failures on
        // QF_LRA benchmarks like tgc_io-safe-13 and simple_startup_14nodes).
        //
        // The atom is still added to registered_atoms and atom_cache so it can
        // be re-parsed in process_check_atoms when ITE conditions become
        // available. register_atom_index_for_resolved_atom() handles the
        // deferred atom_index registration at that point.
        if info.has_unsupported {
            // Still add to var_to_atoms for unassigned_atom_count tracking
            // (needed for compute_implied_bounds row-interest gating), but
            // do NOT add to atom_index (which drives propagation).
            for &(v, _) in &info.expr.coeffs {
                self.var_to_atoms.entry(v).or_default().push(term);
            }
            self.registered_atoms.insert(term);
            self.decision_index_note_registered(term, info.is_eq, info.is_distinct);
            return;
        }
        if info.is_eq || info.is_distinct {
            // Equality and distinct atoms are NOT registered in atom_index because
            // the axiom generator (mk_bound_axiom_terms) assumes atoms represent
            // single-direction bounds. Registering equalities as both upper+lower
            // would cause unsound axioms (e.g., "eq ∨ bound" which is invalid when
            // eq is false and bound is also false). Instead, one-directional axioms
            // for equalities are generated separately at lines 5307+ (#4919).
            // var_to_atoms and unassigned_atom_count are still updated below so
            // that propagation and implied-bound detection include equality atoms.
            for &(v, _) in &info.expr.coeffs {
                self.var_to_atoms.entry(v).or_default().push(term);
            }
            for &(v, _) in &info.expr.coeffs {
                let vi = v as usize;
                if vi >= self.unassigned_atom_count.len() {
                    self.unassigned_atom_count.resize(vi + 1, 0);
                }
                self.unassigned_atom_count[vi] += 1;
            }
            self.registered_atoms.insert(term);
            self.decision_index_note_registered(term, info.is_eq, info.is_distinct);
            return;
        }
        // Build reverse index: var -> atoms referencing it (#4919 propagation opt).
        // Used by propagate() to only re-check atoms whose variables changed bounds.
        for &(v, _) in &info.expr.coeffs {
            self.var_to_atoms.entry(v).or_default().push(term);
        }
        // Track unassigned atom count for ALL atoms (single + compound) so that
        // compute_implied_bounds() knows a row is "interesting" if any variable
        // participates in an unasserted atom. Previously only single-variable atoms
        // were counted, causing compute_implied_bounds to skip rows whose variables
        // only appear in compound atoms — preventing bound derivation that feeds
        // interval propagation on compound atoms (#4919 Phase D).
        for &(v, _) in &info.expr.coeffs {
            let vi = v as usize;
            if vi >= self.unassigned_atom_count.len() {
                self.unassigned_atom_count.resize(vi + 1, 0);
            }
            self.unassigned_atom_count[vi] += 1;
        }
        // #8008: Z3-style sub-expression term row internalization.
        // For compound atoms, Z3 creates separate simplex rows for the LHS and
        // RHS sub-expressions of comparison atoms (internalize_def in theory_lra.cpp:937).
        // These extra rows provide additional implied-bound propagation targets.
        // For example, in `(< (+ x y) z)`, Z3 creates a variable for `(+ x y)`
        // with row `v = x + y`, plus the main atom row. AY's default flattening
        // combines everything into `x + y - z`, losing the intermediate variable.
        if info.expr.coeffs.len() > 1 && !info.is_eq && !info.is_distinct {
            self.internalize_atom_sub_terms(term);
        }

        if info.expr.coeffs.len() == 1 {
            // Single-variable atom: register directly in atom_index
            let (var, ref coeff) = info.expr.coeffs[0];
            if coeff.is_zero() {
                return;
            }
            let k = -info.expr.constant.clone() / coeff.clone();
            let coeff_positive = coeff.is_positive();
            let is_upper = match (info.is_le, coeff_positive) {
                (true, true) | (false, false) => true,
                (true, false) | (false, true) => false,
            };
            let atom_ref = AtomRef {
                term,
                bound_value: k,
                is_upper,
                strict: info.strict,
            };
            if self.debug_lra {
                safe_eprintln!(
                    "[LRA] register_atom: indexed atom {:?} for var {} ({}={}, strict={})",
                    atom_ref.term,
                    var,
                    if atom_ref.is_upper { "upper" } else { "lower" },
                    atom_ref.bound_value,
                    atom_ref.strict,
                );
            }
            self.atom_index.entry(var).or_default().push(atom_ref);
            self.registered_atoms.insert(term);
            self.decision_index_note_registered(term, info.is_eq, info.is_distinct);
            // #8352: Invalidate JIT propagators — new atom changes the atom_index.
            self.theory_prop_jit_compiled = false;
        } else if info.expr.coeffs.len() > 1 {
            // Compound atom: create slack variable at registration time and
            // register it in atom_index for same-variable chain propagation (#4919).
            // Z3 does this in internalize_atom() (theory_lra.cpp:891-943).
            let (slack, orig_constant) = self.get_or_create_slack(&info.expr);
            // Update compound_slack in atom_cache so assert_literal can decrement
            // the slack's unassigned_atom_count (#7851 D2 fix). The initial parse
            // couldn't set this because expr_to_slack wasn't populated yet.
            if let Some(Some(cached_info)) = self.atom_cache.get_mut(&term) {
                cached_info.compound_slack = Some(slack);
            }
            let bound_value = &orig_constant - &info.expr.constant;
            // The atom is `expr OP 0` where OP is `<=` (is_le) or `>=` (!is_le).
            // Slack `s` = sum(coeffs) + orig_constant. The atom becomes:
            //   is_le=true:  s <= orig_constant - atom_constant = bound_value  → upper bound
            //   is_le=false: s >= orig_constant - atom_constant = bound_value  → lower bound
            // BUG FIX (#6242): was hardcoded `is_upper: true`, causing incorrect
            // bound axiom generation for `>=` compound atoms. This produced false-UNSAT
            // on 6 QF_LRA benchmarks.
            let atom_ref = AtomRef {
                term,
                bound_value,
                is_upper: info.is_le,
                strict: info.strict,
            };
            if self.debug_lra {
                safe_eprintln!(
                    "[LRA] register_atom: compound atom {:?} -> slack {} (dir={}, bound={}, strict={}, expr={:?})",
                    atom_ref.term,
                    slack,
                    if atom_ref.is_upper { "upper" } else { "lower" },
                    atom_ref.bound_value,
                    atom_ref.strict,
                    info.expr,
                );
            }
            let si = slack as usize;
            if si >= self.unassigned_atom_count.len() {
                self.unassigned_atom_count.resize(si + 1, 0);
            }
            self.unassigned_atom_count[si] += 1;
            self.atom_index.entry(slack).or_default().push(atom_ref);
            let compound_ref = CompoundAtomRef {
                term,
                slack,
                strict: info.strict,
            };
            for &(v, _) in &info.expr.coeffs {
                self.compound_use_index
                    .entry(v)
                    .or_default()
                    .push(compound_ref);
                // Keep compound source vars dirty so the post-simplex wake
                // pass can actually discover the use-list entries it tracks.
                // This is especially important after warm resets, where the
                // persistent theory loop depends on dirty reseeding rather
                // than a fresh structural rebuild.
                self.propagation_dirty_vars.insert(v);
            }
            // Wake same-expression atoms when the shared slack tightens even if no
            // constituent variable bound changed (e.g. one compound bound implies
            // another weaker bound on the same normalized expression).
            self.compound_use_index
                .entry(slack)
                .or_default()
                .push(compound_ref);
            self.propagation_dirty_vars.insert(slack);
            // Register compound atom under slack in var_to_atoms (#4919 Phase 5).
            // The dedicated compound path now uses `compound_use_index`, but the
            // generic reverse map is kept as a fallback/recount structure.
            self.var_to_atoms.entry(slack).or_default().push(term);
            self.registered_atoms.insert(term);
            self.decision_index_note_registered(term, info.is_eq, info.is_distinct);
            // #8352: Invalidate JIT propagators — new atom changes the atom_index.
            self.theory_prop_jit_compiled = false;
        }
    }

    /// Deferred atom_index registration for atoms whose ITE conditions
    /// have been resolved after initial registration (#8373).
    ///
    /// Called from `process_check_atoms_inner` when re-parsing succeeds
    /// (has_unsupported becomes false). At registration time, the atom was
    /// skipped in atom_index because its expression contained fresh variables
    /// over-approximating unresolved ITEs. Now that the expression is correct,
    /// we perform the index registration that was deferred.
    ///
    /// This mirrors the atom_index registration logic at the bottom of
    /// `register_atom_impl` but operates on a freshly-parsed `ParsedAtomInfo`.
    pub(crate) fn register_atom_index_for_resolved_atom(
        &mut self,
        term: TermId,
        info: &ParsedAtomInfo,
    ) {
        // Skip equality/distinct — they are never registered in atom_index
        // (same logic as register_atom_impl).
        if info.is_eq || info.is_distinct {
            return;
        }

        // Update var_to_atoms for the NEW expression variables. The old
        // fresh-variable entries from registration time may reference wrong
        // variables, but they are harmless (just extra entries that won't
        // match any real atom during propagation). Adding the correct ones
        // here ensures compute_implied_bounds row-interest gating works.
        for &(v, _) in &info.expr.coeffs {
            self.var_to_atoms.entry(v).or_default().push(term);
        }
        // Update unassigned_atom_count for correct variables.
        for &(v, _) in &info.expr.coeffs {
            let vi = v as usize;
            if vi >= self.unassigned_atom_count.len() {
                self.unassigned_atom_count.resize(vi + 1, 0);
            }
            self.unassigned_atom_count[vi] += 1;
        }

        // Sub-expression internalization for compound atoms.
        if info.expr.coeffs.len() > 1 {
            self.internalize_atom_sub_terms(term);
        }

        if info.expr.coeffs.len() == 1 {
            // Single-variable atom
            let (var, ref coeff) = info.expr.coeffs[0];
            if coeff.is_zero() {
                return;
            }
            let k = -info.expr.constant.clone() / coeff.clone();
            let coeff_positive = coeff.is_positive();
            let is_upper = match (info.is_le, coeff_positive) {
                (true, true) | (false, false) => true,
                (true, false) | (false, true) => false,
            };
            let atom_ref = AtomRef {
                term,
                bound_value: k,
                is_upper,
                strict: info.strict,
            };
            if self.debug_lra {
                safe_eprintln!(
                    "[LRA] #8373 deferred register: indexed atom {:?} for var {} ({}={}, strict={})",
                    atom_ref.term,
                    var,
                    if atom_ref.is_upper { "upper" } else { "lower" },
                    atom_ref.bound_value,
                    atom_ref.strict,
                );
            }
            self.atom_index.entry(var).or_default().push(atom_ref);
            self.theory_prop_jit_compiled = false;
        } else if info.expr.coeffs.len() > 1 {
            // Compound atom
            let (slack, orig_constant) = self.get_or_create_slack(&info.expr);
            // Update compound_slack in atom_cache.
            if let Some(Some(cached_info)) = self.atom_cache.get_mut(&term) {
                cached_info.compound_slack = Some(slack);
            }
            let bound_value = &orig_constant - &info.expr.constant;
            let atom_ref = AtomRef {
                term,
                bound_value,
                is_upper: info.is_le,
                strict: info.strict,
            };
            if self.debug_lra {
                safe_eprintln!(
                    "[LRA] #8373 deferred register: compound atom {:?} -> slack {} (dir={}, bound={}, strict={})",
                    atom_ref.term,
                    slack,
                    if atom_ref.is_upper { "upper" } else { "lower" },
                    atom_ref.bound_value,
                    atom_ref.strict,
                );
            }
            let si = slack as usize;
            if si >= self.unassigned_atom_count.len() {
                self.unassigned_atom_count.resize(si + 1, 0);
            }
            self.unassigned_atom_count[si] += 1;
            self.atom_index.entry(slack).or_default().push(atom_ref);
            let compound_ref = CompoundAtomRef {
                term,
                slack,
                strict: info.strict,
            };
            for &(v, _) in &info.expr.coeffs {
                self.compound_use_index
                    .entry(v)
                    .or_default()
                    .push(compound_ref);
                self.propagation_dirty_vars.insert(v);
            }
            self.compound_use_index
                .entry(slack)
                .or_default()
                .push(compound_ref);
            self.propagation_dirty_vars.insert(slack);
            self.var_to_atoms.entry(slack).or_default().push(term);
            self.theory_prop_jit_compiled = false;
        }
    }

    pub(super) fn assert_literal_impl(&mut self, literal: TermId, value: bool) {
        // Unwrap NOT using cache (#6590 Packet 1). Falls back to self.terms on miss.
        let (term, val) = if let Some(&(inner, negated)) = self.not_inner_cache.get(&literal) {
            (inner, if negated { !value } else { value })
        } else {
            match self.terms().get(literal) {
                TermData::Not(inner) => (*inner, !value),
                _ => (literal, value),
            }
        };
        let debug = self.debug_lra_assert;
        if debug {
            safe_eprintln!("[LRA] assert_literal: term={:?}, value={}", term, val);
        }
        // Only decrement unassigned count if this is a new assertion (not re-assertion).
        // Use entry API to avoid double HashMap lookup (#perf).
        #[cfg(not(kani))]
        use hashbrown::hash_map::Entry;
        #[cfg(kani)]
        use std::collections::btree_map::Entry;
        let is_new = match self.asserted.entry(term) {
            Entry::Vacant(e) => {
                e.insert(val);
                true
            }
            Entry::Occupied(mut e) => {
                // #8255: Track whether the value actually changed.
                // When the same atom is re-asserted with the same value
                // (common during BCP when the SAT solver propagates the
                // same literal multiple times), skip setting dirty to
                // avoid unnecessary check_during_propagate work.
                let old_val = *e.get();
                if old_val != val {
                    e.insert(val);
                }
                false
            }
        };
        // STAGE B: a newly-asserted atom leaves the unasserted decision-candidate
        // index (removes are O(1) no-ops if the term is not a candidate). Only on
        // is_new: re-assertions of an already-asserted term were removed already.
        if is_new {
            self.decision_index.eq.remove(term);
            self.decision_index.ineq.remove(term);
        }
        self.asserted_trail.push(term);
        // #8255: Only set dirty on genuinely new assertions or value
        // changes. Re-assertions of the same (term, value) pair don't
        // change theory state: the bound is already in bound_atoms and
        // process_check_atoms will skip it. Setting dirty unconditionally
        // caused 84% of runtime to be spent in BCP theory checks that
        // were effectively no-ops.
        //
        // For new assertions: always dirty (new bound to process).
        // For re-assertions with value change: always dirty (bound
        // was popped and new bound_atoms entry needed).
        // For re-assertions with same value: only set dirty if it
        // hasn't been set yet by another assertion in this batch
        // (dirty may already be true from pop_inner or a prior new
        // assertion in this batch).
        if is_new {
            self.dirty = true;
        } else if !self.bound_atoms.contains(&(term, val)) {
            // Value changed or bound was popped — need to reprocess.
            self.dirty = true;
        }
        // Note: when !is_new && bound_atoms.contains((term, val)),
        // dirty is NOT set. This is the fast path for same-value
        // re-assertions that are already fully processed.
        if !is_new && self.bound_atoms.contains(&(term, val)) {
            self.stats.assert_dirty_skips += 1;
        }
        // Decrement unassigned atom count for ALL variables in this atom (#4919 Phase D).
        // Matches the register_atom increment which counts all atoms (single + compound).
        if is_new {
            // Borrow atom_cache without cloning — we only read the info (#perf).
            if let Some(Some(info)) = self.atom_cache.get(&term) {
                if !info.is_eq && !info.is_distinct {
                    for &(v, _) in &info.expr.coeffs {
                        let vi = v as usize;
                        if vi < self.unassigned_atom_count.len()
                            && self.unassigned_atom_count[vi] > 0
                        {
                            self.unassigned_atom_count[vi] -= 1;
                        }
                    }
                    // Also decrement slack's count for compound atoms (#4919).
                    // Precomputed compound_slack avoids per-assertion Vec alloc + sort.
                    if let Some(slack) = info.compound_slack {
                        let si = slack as usize;
                        if si < self.unassigned_atom_count.len()
                            && self.unassigned_atom_count[si] > 0
                        {
                            self.unassigned_atom_count[si] -= 1;
                        }
                    }
                }
            }
        }
    }
}
