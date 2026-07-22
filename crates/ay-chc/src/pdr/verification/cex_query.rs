// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Query-clause verification for PDR counterexample checking.

use super::*;
use crate::pdr::counterexample::DerivationWitness;

impl PdrSolver {
    pub(super) fn verify_counterexample_query_clause(
        &mut self,
        witness: &DerivationWitness,
        saw_unknown: &mut bool,
    ) -> Option<CexVerificationResult> {
        let root_pred = witness.entries[witness.root].predicate;

        // Trusted path: the recorded query clause index addresses a clause
        // that structurally matches the violated query (False head whose body
        // references the root predicate). Witnesses produced on this exact
        // problem replay through it with unchanged semantics.
        if let Some(query_clause) = witness
            .query_clause
            .and_then(|idx| self.problem.clauses().get(idx))
            .cloned()
        {
            if Self::query_clause_matches_root(&query_clause, root_pred) {
                return self.verify_query_clause_candidate(
                    witness,
                    &query_clause,
                    false,
                    saw_unknown,
                );
            }
        }

        // Transform-tolerant path (FM2b): the witness came from a transformed
        // problem (e.g. ClauseInliner), so its clause index does not address
        // the original clause list (or is unset). Re-resolve the violated
        // query by content: direct False-head clauses over the root predicate
        // or two-hop compositions through an inlined intermediate predicate
        // (INV → END_QUERY → false). The counterexample is accepted only if
        // it replays against some original query path; otherwise fail closed
        // as Unknown — index mismatch is not evidence of spuriousness.
        let candidates = self.resolve_query_clauses_for_root(root_pred);
        if candidates.is_empty() {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Counterexample verification: no original query clause matches \
                    root predicate {:?}, marking as unknown",
                    root_pred
                );
            }
            *saw_unknown = true;
            return None;
        }
        for candidate in &candidates {
            let mut local_unknown = false;
            if self
                .verify_query_clause_candidate(witness, candidate, true, &mut local_unknown)
                .is_none()
                && !local_unknown
            {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Counterexample verification: query re-resolved by content \
                        against original clauses (transform-space witness)"
                    );
                }
                return None;
            }
        }
        if self.config.verbose {
            safe_eprintln!(
                "PDR: Counterexample verification: no re-resolved query candidate \
                replayed, marking as unknown"
            );
        }
        *saw_unknown = true;
        None
    }

    /// Structural trust check for a recorded query-clause index: the clause
    /// must be a query (False head) whose body references the root predicate.
    fn query_clause_matches_root(clause: &crate::HornClause, root_pred: PredicateId) -> bool {
        matches!(clause.head, crate::ClauseHead::False)
            && clause
                .body
                .predicates
                .iter()
                .any(|(pred, _)| *pred == root_pred)
    }

    /// Re-resolve candidate query clauses for a root predicate by content.
    ///
    /// Direct candidates: original False-head clauses whose body references
    /// the root predicate. When none exist (the query path was inlined),
    /// two-hop compositions `root →(C1) Q →(C2) false` are synthesized with
    /// the composed constraint `C1.constraint ∧ C2.constraint[C2 args ↦ C1
    /// head args]`, which is exactly the clause the inliner produced.
    fn resolve_query_clauses_for_root(&self, root_pred: PredicateId) -> Vec<crate::HornClause> {
        let clauses = self.problem.clauses();
        let direct: Vec<crate::HornClause> = clauses
            .iter()
            .filter(|clause| Self::query_clause_matches_root(clause, root_pred))
            .cloned()
            .collect();
        if !direct.is_empty() {
            return direct;
        }

        let mut composed = Vec::new();
        for c1 in clauses {
            let crate::ClauseHead::Predicate(intermediate, head_args) = &c1.head else {
                continue;
            };
            if !c1
                .body
                .predicates
                .iter()
                .any(|(pred, _)| *pred == root_pred)
            {
                continue;
            }
            for c2 in clauses {
                if !matches!(c2.head, crate::ClauseHead::False) {
                    continue;
                }
                let [(c2_pred, c2_args)] = c2.body.predicates.as_slice() else {
                    continue;
                };
                if c2_pred != intermediate || c2_args.len() != head_args.len() {
                    continue;
                }
                // Link C2's constraint through its predicate args onto C1's
                // head args. Require plain variable args and a constraint
                // closed over them so substitution cannot capture C1 vars.
                let mut link: Vec<(ChcVar, ChcExpr)> = Vec::new();
                let mut linkable = true;
                for (arg, head_arg) in c2_args.iter().zip(head_args.iter()) {
                    match arg {
                        ChcExpr::Var(var) => link.push((var.clone(), head_arg.clone())),
                        _ => {
                            linkable = false;
                            break;
                        }
                    }
                }
                if !linkable {
                    continue;
                }
                let c2_constraint = c2.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
                let linked: std::collections::BTreeSet<String> =
                    link.iter().map(|(var, _)| var.name.clone()).collect();
                if !c2_constraint
                    .vars()
                    .into_iter()
                    .all(|var| linked.contains(&var.name))
                {
                    continue;
                }
                let composed_constraint = ChcExpr::and(
                    c1.body.constraint.clone().unwrap_or(ChcExpr::Bool(true)),
                    c2_constraint.substitute(&link),
                );
                composed.push(crate::HornClause::new(
                    crate::ClauseBody::new(c1.body.predicates.clone(), Some(composed_constraint)),
                    crate::ClauseHead::False,
                ));
            }
        }
        composed
    }

    /// Replay the root entry against one (possibly synthesized) query clause.
    ///
    /// Extracted from `verify_counterexample_query_clause` so transform-space
    /// witnesses can try several re-resolved candidates.
    fn verify_query_clause_candidate(
        &mut self,
        witness: &DerivationWitness,
        query_clause: &crate::HornClause,
        restrict_subst_to_canonical: bool,
        saw_unknown: &mut bool,
    ) -> Option<CexVerificationResult> {
        let Some(query_constraint) = query_clause.body.constraint.clone() else {
            return None;
        };

        let root_entry = &witness.entries[witness.root];
        let query_sort_map = self.counterexample_query_sort_map(witness, root_entry);
        let mut subst = self.counterexample_query_subst(
            witness,
            query_clause,
            root_entry,
            &query_sort_map,
            saw_unknown,
        );
        if restrict_subst_to_canonical {
            // FM2b: engine models leak clause-local variable names into the
            // instances; on a re-resolved ORIGINAL clause those names collide
            // with unrelated clause variables. Keep only canonical
            // (positional) names and let `extend_query_arg_subst` map them
            // onto this clause's argument variables.
            subst.retain(|(var, _)| is_canonical_arg_name(&var.name));
        }
        self.extend_query_arg_subst(query_clause, witness, root_entry, &mut subst, saw_unknown);

        let root_state_in_clause_vars =
            self.counterexample_root_state_in_clause_vars(query_clause, root_entry);
        let mut missing_query_vars: Vec<String> = query_constraint
            .vars()
            .into_iter()
            .map(|v| v.name)
            .filter(|name| !subst.iter().any(|(var, _)| var.name == *name))
            .collect();
        missing_query_vars.sort();
        missing_query_vars.dedup();

        if !missing_query_vars.is_empty() {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Counterexample verification: query instances missing vars {:?}; \
                    using root-state ∧ constraint satisfiability check",
                    missing_query_vars
                );
            }
            // The unpinned variables are the query clause's own
            // existentially-quantified variables (e.g. a single-body
            // output-equality query `pred(…A…) ∧ (= A C1) ∧ … → false` whose
            // `C1 …` occur ONLY here). For such queries deriving `false`
            // requires the reached root state to SATISFY the constraint for SOME
            // choice of them — `root_state ∧ constraint` SAT — not the strictly
            // stronger state-IMPLIES-constraint condition, which wrongly rejects
            // genuine refutations. (For a multi-body hyperedge query the root
            // pins only one premise, so the fallback stays the conservative
            // implication test.)
            return self.verify_counterexample_query_fallback(
                query_clause,
                &root_state_in_clause_vars,
                &query_constraint,
                saw_unknown,
            );
        }

        let query = self.bound_int_vars(query_constraint.substitute(&subst));
        self.smt.reset();
        match self
            .smt
            .check_sat_with_timeout(&query, VERIFY_RETRY_TIMEOUT)
        {
            SmtResult::Sat(_) => self.verify_counterexample_query_violation(
                &root_state_in_clause_vars,
                &query_constraint,
                saw_unknown,
            ),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                // FM2b: cross-check array-bearing UNSATs by concrete witness
                // evaluation before falling back to the implication check.
                if query.contains_array_ops() && ground_query_witness_evaluates_true(&query) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: CEX query constraint: backend UNSAT overridden by \
                            concrete ground witness evaluation (array replay)"
                        );
                    }
                    return self.verify_counterexample_query_violation(
                        &root_state_in_clause_vars,
                        &query_constraint,
                        saw_unknown,
                    );
                }
                // The ground constraint under the witness instances is UNSAT.
                // That can be a GENUINELY spurious query, but for a single-body
                // query it also fires when the root predicate's instance map
                // carries clause-local variables whose names collide with the
                // query clause's own (SMT-LIB reuses `A`,`B`,…,`C1` across
                // clauses), so wrong values were substituted. The fallback
                // decides by the exact reachability condition on the canonical
                // root state (single-body: `root_state ∧ constraint` SAT ⇒
                // fires; multi-body: the conservative implication test).
                let result = self.verify_counterexample_query_fallback(
                    query_clause,
                    &root_state_in_clause_vars,
                    &query_constraint,
                    saw_unknown,
                );
                if result.is_none() && self.config.verbose {
                    safe_eprintln!(
                        "PDR: CEX query constraint: instance check failed, \
                        but root state satisfies query constraint (valid)"
                    );
                }
                result
            }
            SmtResult::Unknown => {
                *saw_unknown = true;
                None
            }
        }
    }

    fn verify_counterexample_query_violation(
        &mut self,
        root_state_in_clause_vars: &ChcExpr,
        query_constraint: &ChcExpr,
        saw_unknown: &mut bool,
    ) -> Option<CexVerificationResult> {
        let root_and_query =
            ChcExpr::and(root_state_in_clause_vars.clone(), query_constraint.clone());
        let check = self.bound_int_vars(root_and_query);
        self.smt.reset();
        match self
            .smt
            .check_sat_with_timeout(&check, VERIFY_RETRY_TIMEOUT)
        {
            SmtResult::Sat(_) => array_sat_cross_check_result(
                &mut self.smt,
                &check,
                self.config.verbose,
                "query violation",
            ),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                // FM2b: cross-check array-bearing UNSATs by concrete witness
                // evaluation — the array extensionality fragment can produce
                // false UNSATs on ground const-array/store disequalities.
                if check.contains_array_ops() && ground_query_witness_evaluates_true(&check) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: CEX query violation: backend UNSAT overridden by \
                            concrete ground witness evaluation (array replay)"
                        );
                    }
                    return None;
                }
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Counterexample verification failed: \
                        root state is inconsistent with query violation"
                    );
                }
                Some(CexVerificationResult::Spurious)
            }
            SmtResult::Unknown => {
                *saw_unknown = true;
                None
            }
        }
    }

    fn counterexample_query_sort_map(
        &self,
        witness: &DerivationWitness,
        root_entry: &crate::pdr::counterexample::DerivationWitnessEntry,
    ) -> FxHashMap<String, ChcSort> {
        let mut sort_map: FxHashMap<String, ChcSort> = FxHashMap::default();
        if let Some(cvars) = self.canonical_vars(root_entry.predicate) {
            for cv in cvars {
                sort_map.insert(cv.name.clone(), cv.sort.clone());
            }
        }
        for &premise_idx in &root_entry.premises {
            if let Some(entry) = witness.entries.get(premise_idx) {
                if let Some(cvars) = self.canonical_vars(entry.predicate) {
                    for cv in cvars {
                        sort_map
                            .entry(cv.name.clone())
                            .or_insert_with(|| cv.sort.clone());
                    }
                }
            }
        }
        sort_map
    }

    fn counterexample_query_subst(
        &self,
        witness: &DerivationWitness,
        query_clause: &crate::HornClause,
        root_entry: &crate::pdr::counterexample::DerivationWitnessEntry,
        query_sort_map: &FxHashMap<String, ChcSort>,
        saw_unknown: &mut bool,
    ) -> Vec<(ChcVar, ChcExpr)> {
        let mut subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
        for (name, value) in &root_entry.instances {
            subst.push(instance_subst_var_and_value(
                name,
                value,
                query_sort_map.get(name.as_str()),
                self.config.verbose,
                saw_unknown,
            ));
        }

        if query_clause.body.predicates.len() > 1 {
            for &premise_idx in &root_entry.premises {
                if let Some(premise_entry) = witness.entries.get(premise_idx) {
                    for (name, value) in &premise_entry.instances {
                        if let Some((_, existing_expr)) =
                            subst.iter().find(|(var, _)| var.name == *name)
                        {
                            let (_, new_expr) = instance_subst_var_and_value(
                                name,
                                value,
                                query_sort_map.get(name.as_str()),
                                false,
                                saw_unknown,
                            );
                            if existing_expr != &new_expr {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: Counterexample verification: variable {} has \
                                        conflicting values across premise entries ({:?} vs {:?})",
                                        name,
                                        existing_expr,
                                        new_expr
                                    );
                                }
                                *saw_unknown = true;
                            }
                        } else {
                            subst.push(instance_subst_var_and_value(
                                name,
                                value,
                                query_sort_map.get(name.as_str()),
                                self.config.verbose,
                                saw_unknown,
                            ));
                        }
                    }
                }
            }
        }

        subst
    }

    fn extend_query_arg_subst(
        &self,
        query_clause: &crate::HornClause,
        witness: &DerivationWitness,
        root_entry: &crate::pdr::counterexample::DerivationWitnessEntry,
        subst: &mut Vec<(ChcVar, ChcExpr)>,
        saw_unknown: &mut bool,
    ) {
        for (body_pred, body_args) in &query_clause.body.predicates {
            let matching_entry = if root_entry.predicate == *body_pred {
                Some(root_entry)
            } else {
                root_entry
                    .premises
                    .iter()
                    .filter_map(|&idx| witness.entries.get(idx))
                    .find(|entry| entry.predicate == *body_pred)
            };

            if let Some(entry) = matching_entry {
                if let Some(canon_vars) = self.canonical_vars(*body_pred) {
                    for (arg, canon_var) in body_args.iter().zip(canon_vars.iter()) {
                        if let ChcExpr::Var(arg_var) = arg {
                            if let Some(val) = entry.instances.get(&canon_var.name) {
                                if !subst.iter().any(|(var, _)| var.name == arg_var.name) {
                                    subst.push(instance_subst_var_and_value(
                                        &arg_var.name,
                                        val,
                                        Some(&canon_var.sort),
                                        self.config.verbose,
                                        saw_unknown,
                                    ));
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    fn counterexample_root_state_in_clause_vars(
        &self,
        query_clause: &crate::HornClause,
        root_entry: &crate::pdr::counterexample::DerivationWitnessEntry,
    ) -> ChcExpr {
        let mut state_subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
        for (body_pred, body_args) in &query_clause.body.predicates {
            if let Some(canon_vars) = self.canonical_vars(*body_pred) {
                for (arg, canon_var) in body_args.iter().zip(canon_vars.iter()) {
                    if let ChcExpr::Var(arg_var) = arg {
                        state_subst.push((canon_var.clone(), ChcExpr::var(arg_var.clone())));
                    }
                }
            }
        }
        root_entry.state.substitute(&state_subst)
    }

    /// Fallback query check when the witness instances cannot ground the query
    /// constraint (a query variable is unpinned, or the ground constraint under
    /// the instances is UNSAT because clause-local variable names collided).
    ///
    /// For a SINGLE-body-predicate query the reached root state pins that one
    /// body predicate, and any remaining query-constraint variables are the
    /// query's own existentials; `false` is derivable iff `root_state ∧
    /// constraint` is SATISFIABLE (query_violation). For a MULTI-body
    /// (hyperedge) query the root state pins only ONE premise, so the
    /// satisfiability check would under-constrain the others — there we keep the
    /// conservative state-IMPLIES-constraint test.
    fn verify_counterexample_query_fallback(
        &mut self,
        query_clause: &crate::HornClause,
        root_state_in_clause_vars: &ChcExpr,
        query_constraint: &ChcExpr,
        saw_unknown: &mut bool,
    ) -> Option<CexVerificationResult> {
        if query_clause.body.predicates.len() == 1 {
            self.verify_counterexample_query_violation(
                root_state_in_clause_vars,
                query_constraint,
                saw_unknown,
            )
        } else {
            self.verify_counterexample_query_implication(
                root_state_in_clause_vars,
                query_constraint,
                saw_unknown,
            )
        }
    }

    fn verify_counterexample_query_implication(
        &mut self,
        root_state_in_clause_vars: &ChcExpr,
        query_constraint: &ChcExpr,
        saw_unknown: &mut bool,
    ) -> Option<CexVerificationResult> {
        let implies_query = ChcExpr::and(
            root_state_in_clause_vars.clone(),
            ChcExpr::not(query_constraint.clone()),
        );
        let implies_check = self.bound_int_vars(implies_query);
        self.smt.reset();
        match self
            .smt
            .check_sat_with_timeout(&implies_check, VERIFY_RETRY_TIMEOUT)
        {
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => None,
            SmtResult::Sat(_) => {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Counterexample verification failed: \
                        query constraint UNSAT with witness instances \
                        and root state does not imply query constraint"
                    );
                }
                Some(CexVerificationResult::Spurious)
            }
            SmtResult::Unknown => {
                *saw_unknown = true;
                None
            }
        }
    }
}
