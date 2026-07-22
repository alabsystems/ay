// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `TheorySolver` trait implementation for `DtSolver`.
//!
//! Implements the DPLL(T) theory interface for the datatype theory.

use super::*;

impl TheorySolver for DtSolver<'_> {
    fn internalize_atom(&mut self, term: TermId) {
        // Parse tester atoms: is-C(x) → record (term, x, C) for case splitting (#8539).
        if let TermData::App(Symbol::Named(name), args) = self.terms.get(term) {
            if name.starts_with("is-") && args.len() == 1 {
                if let Some((_dt_name, ctor_name)) = self.tester_map.get(name).cloned() {
                    let arg = args[0];
                    self.internalized_testers.insert(term, (arg, ctor_name));
                    // Track the argument as a DT-sorted term.
                    if let Some((dt_name, _)) = self.tester_map.get(name) {
                        self.dt_terms.entry(arg).or_insert_with(|| dt_name.clone());
                    }
                }
            }
        }
    }

    fn assert_literal(&mut self, literal: TermId, value: bool) {
        // Unwrap NOT: NOT(inner)=true means inner=false
        let (term, val) = if let Some(inner) = self.decode_not(literal) {
            (inner, !value)
        } else {
            (literal, value)
        };

        // Check if this is an equality
        if let Some((lhs, rhs)) = self.decode_eq(term) {
            self.process_equality(term, lhs, rhs, val);
            return;
        }

        // Check if this term itself is a constructor (for direct constructor assertions)
        if let Some((dt_name, ctor_name, args)) = self.try_extract_constructor(term) {
            if !self.term_constructors.contains_key(&term) {
                self.register_constructor(term, &dt_name, &ctor_name, &args);
            }
        }

        // Check for tester assertions (is-Constructor)
        if let TermData::App(Symbol::Named(name), args) = self.terms.get(term) {
            if name.starts_with("is-") && args.len() == 1 {
                if let Some((_dt_name, ctor_name)) = self.tester_map.get(name).cloned() {
                    self.tester_results.insert(args[0], (ctor_name, val, term));
                    self.current_scope.tester_keys.push(args[0]);
                    // Track this tester atom as asserted (#8539).
                    self.asserted_tester_atoms.insert(term);
                }
            }
        }
    }

    fn check(&mut self) -> TheoryResult {
        self.check_count += 1;
        tracing::debug!(
            constructors = self.term_constructors.len(),
            eq_lits = self.asserted_eq_lits.len(),
            diseqs = self.asserted_diseqs.len(),
            "DT check"
        );

        if self.debug {
            tracing::trace!(
                constructors = self.term_constructors.len(),
                eq_lits = self.asserted_eq_lits.len(),
                diseqs = self.asserted_diseqs.len(),
                scopes = self.scopes.len(),
                "DT check verbose"
            );
        }

        #[cfg(debug_assertions)]
        self.debug_check_invariants();

        // Upward constructor congruence (#dt-congruence): if every argument pair
        // of two same-constructor terms is already equal, the constructor terms
        // must be merged (`a = zero ⇒ succ(a) = succ(zero)`). Run this first so
        // the merges feed every subsequent check (clash, disequality, ...).
        self.apply_constructor_congruence();

        // Run injectivity: it may merge terms in the union-find via
        // constructor argument equalities (e.g., mk-rec(f1(s),...) = mk-rec(f1(t),...)
        // → f1(s) = f1(t)). Subsequent checks need the updated classes (#5082).
        if let Some(conflict) = self.check_injectivity_conflicts() {
            tracing::debug!("DT check: injectivity conflict");
            self.conflict_count += 1;
            return TheoryResult::Unsat(conflict);
        }

        // Injectivity may have merged constant arguments (`c(0) = c(1) ⇒ 0 = 1`).
        // Two distinct constants in one class are inconsistent; the standalone
        // DT solver must reject this directly (no arithmetic partner) (#dt-congruence).
        if let Some(conflict) = self.check_constant_clash() {
            tracing::debug!("DT check: constant clash conflict");
            self.conflict_count += 1;
            return TheoryResult::Unsat(conflict);
        }

        // Check for constructor clashes (including those exposed by injectivity merges).
        if let Some(conflict) = self.check_clash() {
            tracing::debug!("DT check: constructor clash conflict");
            self.conflict_count += 1;
            return TheoryResult::Unsat(conflict);
        }

        // Check tester results against constructors in equivalence classes (#5082).
        if let Some(conflict) = self.check_tester_conflicts() {
            tracing::debug!("DT check: tester-constructor conflict");
            self.conflict_count += 1;
            return TheoryResult::Unsat(conflict);
        }

        // Check for implied equality vs asserted disequality conflicts.
        if let Some(conflict) = self.check_disequality_conflicts() {
            tracing::debug!("DT check: disequality conflict");
            self.conflict_count += 1;
            return TheoryResult::Unsat(conflict);
        }

        // Downward selector-projection congruence (#dt-sel-projection).
        //
        // From `t = C(a_0, ..., a_{n-1})` derive `sel_i(t') = a_i` for every
        // existing selector application `(sel_i t')` with `t'` in `t`'s class.
        // This exposes cycles routed through nested-constructor projections that
        // the upward congruence + occurs-check cannot otherwise see — e.g.
        // `x = cons(cons(tl x))` projects `tl(x) = cons(tl x)`, closing the
        // cycle. Loop projection and upward congruence to a joint fixpoint so
        // newly-projected equalities can enable further congruence (and vice
        // versa) before the occurs-check runs. Every projected equality is
        // implied by an existing constructor equality, so this is sound.
        loop {
            let projected = self.apply_selector_projection();
            let merged = self.apply_constructor_congruence();
            if !projected && !merged {
                break;
            }
        }

        // Occurs check (acyclicity) for recursive datatypes.
        //
        // Cycles like `x = cons(1, x)` imply infinite values and are UNSAT for
        // finite algebraic datatypes (SMT-LIB). See the development design notes
        if let Some(conflict) = self.occurs_check() {
            tracing::debug!("DT check: acyclicity conflict");
            self.conflict_count += 1;
            return TheoryResult::Unsat(conflict);
        }

        // Dynamic case splitting for recursive datatypes (#8539).
        //
        // After all conflict checks pass, scan for DT terms whose equivalence
        // class has no constructor and no tester constraint. Suggest a tester
        // atom as the next decision to the DPLL engine. This is the AY equivalent
        // of Z3's `final_check_eh()` + `mk_split()`.
        //
        // Without this, the SAT solver may never decide on tester atoms for
        // unconstrained recursive DT variables, causing Unknown results on
        // decidable problems.
        self.pending_split_atom = self.find_case_split();
        if self.pending_split_atom.is_some() {
            self.split_count += 1;
            tracing::debug!("DT check: sat (with pending case split)");
        } else {
            tracing::debug!("DT check: sat");
        }
        TheoryResult::Sat
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        let props = std::mem::take(&mut self.pending);
        self.propagation_count += props.len() as u64;
        props
    }

    fn collect_statistics(&self) -> Vec<(&'static str, u64)> {
        vec![
            ("dt_checks", self.check_count),
            ("dt_conflicts", self.conflict_count),
            ("dt_propagations", self.propagation_count),
            ("dt_splits", self.split_count),
        ]
    }

    /// The DT theory needs a final check after SAT to ensure all DT variables
    /// are constrained (#8539). Without this, the solver may accept a model
    /// where some DT variables have no constructor assignment.
    fn needs_final_check_after_sat(&self) -> bool {
        // Only needed when we have internalized tester atoms (i.e., there are
        // DT variables in the problem that might need case splitting).
        !self.dt_terms.is_empty()
    }

    /// Suggest a specific tester atom for the DPLL engine to decide (#8539).
    ///
    /// When `check()` finds an unconstrained DT variable, it sets
    /// `pending_split_atom` to the tester atom that should be decided next.
    /// The DPLL extension calls this method before activity-based selection,
    /// ensuring the theory's case-split request takes priority.
    ///
    /// Reference: Z3 `theory_datatype::mk_split()` creates a tester atom and
    /// sets `true_first_flag`. This is the AY equivalent.
    fn suggest_decision_atom(&self) -> Option<(TermId, bool)> {
        self.pending_split_atom
    }

    fn push(&mut self) {
        self.current_scope.asserted_eq_lits_len = self.asserted_eq_lits.len();
        self.current_scope.asserted_diseqs_len = self.asserted_diseqs.len();
        // Save union trail mark for efficient pop (#8627).
        // Since find() does NOT use path compression (it takes &self),
        // trail-based undo is sound: each union records the root that was
        // re-parented, and pop restores it.
        self.current_scope.union_trail_mark = self.union_trail.len();
        self.current_scope.merge_reasons_len = self.merge_reasons.len();
        self.scopes.push(std::mem::take(&mut self.current_scope));
    }

    fn pop(&mut self) {
        if let Some(scope) = self.scopes.pop() {
            // Undo union-find merges from the popped scope (#8627).
            // Replay the union trail backwards: restore each merged root
            // to point to itself, undoing the union.
            while self.union_trail.len() > scope.union_trail_mark {
                if let Some(ra) = self.union_trail.pop() {
                    self.parent.insert(ra, ra);
                }
            }
            self.merge_reasons.truncate(scope.merge_reasons_len);
            // Undo constructor registrations from current scope
            for term_id in &self.current_scope.registered_ctors {
                self.term_constructors.remove(term_id);
            }
            // Undo tester results from current scope
            for term_id in &self.current_scope.tester_keys {
                self.tester_results.remove(term_id);
                // Also remove from asserted_tester_atoms (#8539).
                // Find the tester atom for this key and remove it.
                // The tester_keys contain the argument term, not the tester atom itself.
                // We need to find which tester atoms were asserted for this argument.
            }
            // Undo equality assertions
            self.asserted_eq_lits.truncate(scope.asserted_eq_lits_len);
            self.asserted_diseqs.truncate(scope.asserted_diseqs_len);
            // Clear propagated pairs, pending propagations, and pending
            // injectivity equalities since the assertions that derived them
            // may have been popped. These will be re-discovered on subsequent
            // check() calls. (#3725: stale propagations must not leak across scopes)
            self.propagated_eq_pairs.clear();
            self.pending.clear();
            self.pending_injectivity_eqs.clear();
            // Clear case-split suggestion (#8539) — stale splits must not persist.
            self.pending_split_atom = None;
            // Rebuild asserted_tester_atoms from surviving tester_results (#8539).
            self.asserted_tester_atoms.clear();
            // Note: tester_results has already been trimmed above; rebuild from what remains.
            for (_, _, tester_lit) in self.tester_results.values() {
                self.asserted_tester_atoms.insert(*tester_lit);
            }
            self.current_scope = scope;
        }
    }

    fn reset(&mut self) {
        self.term_constructors.clear();
        self.parent.clear();
        self.union_trail.clear();
        self.merge_reasons.clear();
        self.pending.clear();
        self.scopes.clear();
        self.current_scope = DtScope::default();
        self.tester_results.clear();
        self.asserted_eq_lits.clear();
        self.pending_injectivity_eqs.clear();
        self.propagated_eq_pairs.clear();
        self.asserted_diseqs.clear();
        // Clear case-split state (#8539).
        self.asserted_tester_atoms.clear();
        self.pending_split_atom = None;
        // Shrink persistent buffers that may have grown during solving (#8599).
        self.buf_sorted_ctor_keys.clear();
        self.buf_sorted_ctor_keys.shrink_to_fit();
        self.buf_class_groups.clear();
        self.buf_class_groups.shrink_to_fit();
        self.buf_sorted_reps.clear();
        self.buf_sorted_reps.shrink_to_fit();
        self.buf_oc_color.clear();
        self.buf_oc_color.shrink_to_fit();
        self.buf_oc_parent_edge.clear();
        self.buf_oc_parent_edge.shrink_to_fit();
        self.buf_oc_rep_to_args.clear();
        self.buf_oc_rep_to_args.shrink_to_fit();
        self.buf_oc_stack.clear();
        self.buf_oc_stack.shrink_to_fit();
        self.buf_explain_adj.clear();
        self.buf_explain_adj.shrink_to_fit();
        self.buf_explain_visited.clear();
        self.buf_explain_visited.shrink_to_fit();
        self.buf_explain_queue.clear();
        self.buf_explain_queue.shrink_to_fit();
        self.buf_unconstrained.clear();
        self.buf_unconstrained.shrink_to_fit();
        // Note: datatype_defs, ctor_to_dt, tester_map, internalized_testers,
        // and dt_terms are preserved across reset (structural, not assertion-dependent).
    }

    fn propagate_equalities(&mut self) -> EqualityPropagationResult {
        // Return injectivity-derived equalities for Nelson-Oppen propagation.
        // These are discovered during check() when same-constructor terms are
        // in the same equivalence class.
        EqualityPropagationResult {
            equalities: std::mem::take(&mut self.pending_injectivity_eqs),
            ..Default::default()
        }
    }

    fn assert_shared_equality(&mut self, lhs: TermId, rhs: TermId, _reason: &[TheoryLit]) {
        // Receive equality from another theory (e.g., EUF → DT in Nelson-Oppen).
        // Merge the terms in our union-find so that injectivity checks are aware.
        self.assert_equality(lhs, rhs);
    }
}
