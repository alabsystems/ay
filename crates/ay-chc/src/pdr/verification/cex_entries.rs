// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Witness-entry verification for PDR counterexample checking.

use super::*;
use crate::pdr::counterexample::DerivationWitness;

impl PdrSolver {
    pub(super) fn verify_counterexample_witness_entries(
        &mut self,
        witness: &DerivationWitness,
        saw_unknown: &mut bool,
    ) -> Option<CexVerificationResult> {
        // Adversarial-witness defense (inc-9 review): an honest derivation
        // witness is a DAG over `entries`. A cycle in the entry→premise graph
        // (e.g. an entry premising ITSELF through an identity rule
        // `P(x) => P(x)`) lets an unreachable state "justify" itself, so the
        // whole witness is marked Unknown. Fail closed: the bounded-BMC
        // replay, which independently re-derives false on this problem's
        // clauses, remains the only upgrade path to Valid.
        if Self::witness_premise_graph_ill_founded(witness) {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Counterexample verification: witness premise graph has a \
                    cycle or dangling premise index, marking as unknown"
                );
            }
            *saw_unknown = true;
        }

        for (entry_idx, entry) in witness.entries.iter().enumerate() {
            if self.is_cancelled() {
                return Some(CexVerificationResult::Unknown);
            }
            let clause_idx = match entry.incoming_clause {
                Some(idx) => idx,
                None => {
                    // Adversarial-witness defense (inc-9 review): axiom
                    // entries (`incoming_clause: None`) were previously
                    // skipped outright, so a fabricated witness whose only
                    // entry claims an UNREACHABLE state passed entry
                    // verification vacuously. An axiom entry is now justified
                    // only if it replays as a FACT of the problem; anything
                    // else marks the witness Unknown (fail closed; the
                    // bounded-BMC replay decides).
                    self.verify_axiom_entry_as_fact(entry_idx, entry, saw_unknown);
                    continue;
                }
            };

            // Trusted path: the recorded clause index addresses a clause that
            // structurally matches this entry (same head predicate, premise
            // predicates align). Witnesses produced on this exact problem
            // replay through it with unchanged semantics.
            let indexed = self.problem.clauses().get(clause_idx).cloned();
            if let Some(clause) = indexed {
                if Self::entry_clause_matches(witness, entry, &clause) {
                    if let Some(result) = self.verify_entry_against_clause(
                        witness,
                        entry_idx,
                        entry,
                        &clause,
                        false,
                        saw_unknown,
                    ) {
                        return Some(result);
                    }
                    continue;
                }
            }

            // Transform-tolerant path (FM2b): the witness came from a
            // transformed problem (e.g. ClauseInliner) whose clause indices do
            // not address the original clause list. Re-resolve by content:
            // the entry is justified iff SOME original clause with matching
            // head/premise structure replays it. If none does, fail closed as
            // Unknown — index mismatch is not evidence of spuriousness.
            let candidates: Vec<crate::HornClause> = self
                .problem
                .clauses()
                .iter()
                .filter(|clause| Self::entry_clause_matches(witness, entry, clause))
                .cloned()
                .collect();
            if candidates.is_empty() {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Counterexample verification: entry {} has no structurally \
                        matching original clause (transform-space index {}), marking as unknown",
                        entry_idx,
                        clause_idx
                    );
                }
                *saw_unknown = true;
                continue;
            }
            let mut entry_justified = false;
            for clause in &candidates {
                let mut local_unknown = false;
                if self
                    .verify_entry_against_clause(
                        witness,
                        entry_idx,
                        entry,
                        clause,
                        true,
                        &mut local_unknown,
                    )
                    .is_none()
                    && !local_unknown
                {
                    entry_justified = true;
                    break;
                }
            }
            if !entry_justified {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Counterexample verification: entry {} not justified by any \
                        re-resolved original clause, marking as unknown",
                        entry_idx
                    );
                }
                *saw_unknown = true;
            }
        }

        None
    }

    /// Well-foundedness pre-check for the witness premise graph (inc-9
    /// adversarial review).
    ///
    /// Honest in-tree producers emit DAGs: BMC's derivation builders pop
    /// incomplete entries and recurse with strictly decreasing levels, and
    /// PDR reach-fact chains only reference previously inserted facts. A
    /// cycle (including a self-loop) means some entry is justified by itself,
    /// which is never a derivation; a premise index outside `entries` is
    /// structurally meaningless. Both make the witness untrustworthy.
    fn witness_premise_graph_ill_founded(witness: &DerivationWitness) -> bool {
        const WHITE: u8 = 0;
        const GRAY: u8 = 1;
        const BLACK: u8 = 2;
        let num_entries = witness.entries.len();
        let mut color = vec![WHITE; num_entries];
        for start in 0..num_entries {
            if color[start] != WHITE {
                continue;
            }
            color[start] = GRAY;
            // Iterative three-color DFS: (node, next premise position).
            let mut stack: Vec<(usize, usize)> = vec![(start, 0)];
            while let Some((node, next_premise)) = stack.last_mut() {
                let premises = &witness.entries[*node].premises;
                if let Some(&child) = premises.get(*next_premise) {
                    *next_premise += 1;
                    if child >= num_entries {
                        return true; // dangling premise index
                    }
                    match color[child] {
                        GRAY => return true, // cycle (incl. self-loop)
                        WHITE => {
                            color[child] = GRAY;
                            stack.push((child, 0));
                        }
                        _ => {}
                    }
                } else {
                    color[*node] = BLACK;
                    stack.pop();
                }
            }
        }
        false
    }

    /// Replay an axiom entry (`incoming_clause: None`) as a fact of the
    /// problem (inc-9 adversarial review).
    ///
    /// The entry is justified iff some fact clause (no body predicates) whose
    /// head predicate matches admits the claimed argument values: the clause
    /// constraint, conjoined with positional `head_arg = claimed value`
    /// bindings (canonical instances) and the claimed state applied to the
    /// head arguments, must be satisfiable. Entries that claim nothing
    /// concrete (trivial state, no canonical instances) cannot be exactly
    /// checked and fail closed. No justification sets `saw_unknown` — never
    /// Valid from here; the bounded-BMC replay is the only upgrade path.
    fn verify_axiom_entry_as_fact(
        &mut self,
        entry_idx: usize,
        entry: &crate::pdr::counterexample::DerivationWitnessEntry,
        saw_unknown: &mut bool,
    ) {
        let canon_vars: Vec<ChcVar> = self
            .canonical_vars(entry.predicate)
            .map(<[ChcVar]>::to_vec)
            .unwrap_or_default();
        let fact_clauses: Vec<crate::HornClause> = self
            .problem
            .clauses()
            .iter()
            .filter(|clause| {
                clause.body.predicates.is_empty()
                    && clause.head.predicate_id() == Some(entry.predicate)
            })
            .cloned()
            .collect();
        if fact_clauses.is_empty() {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Counterexample verification: axiom entry {} has no fact \
                    clause for its predicate, marking as unknown",
                    entry_idx
                );
            }
            *saw_unknown = true;
            return;
        }

        for clause in &fact_clauses {
            let crate::ClauseHead::Predicate(_, head_args) = &clause.head else {
                continue;
            };
            let mut local_unknown = false;
            let mut conjuncts = vec![clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true))];
            // Positional claims: canonical instance values pinned onto this
            // clause's head argument expressions.
            let mut concrete_claims = 0usize;
            for (canon_var, head_arg) in canon_vars.iter().zip(head_args.iter()) {
                if let Some(value) = entry.instances.get(&canon_var.name) {
                    let (_, value_expr) = instance_subst_var_and_value(
                        &canon_var.name,
                        value,
                        Some(&canon_var.sort),
                        self.config.verbose,
                        &mut local_unknown,
                    );
                    conjuncts.push(ChcExpr::eq(head_arg.clone(), value_expr));
                    concrete_claims += 1;
                }
            }
            // Claimed state applied to the head arguments (covers producers
            // whose instances use non-canonical names but whose state pins
            // the canonical arguments, e.g. hyperedge init facts).
            let Some(state_on_head) = self.apply_to_args(entry.predicate, &entry.state, head_args)
            else {
                continue;
            };
            if !matches!(state_on_head, ChcExpr::Bool(true)) {
                concrete_claims += 1;
            }
            conjuncts.push(state_on_head);
            if concrete_claims == 0 || local_unknown {
                // Nothing concrete claimed (or opaque values): this clause
                // cannot exactly justify the entry. Fail closed.
                continue;
            }
            let query = self.bound_int_vars(ChcExpr::and_all(conjuncts));
            self.smt.reset();
            match self
                .smt
                .check_sat_with_timeout(&query, VERIFY_RETRY_TIMEOUT)
            {
                SmtResult::Sat(_) => {
                    if array_sat_cross_check_result(
                        &mut self.smt,
                        &query,
                        self.config.verbose,
                        "axiom fact entry",
                    )
                    .is_none()
                    {
                        return; // justified by this fact clause
                    }
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    // FM2b parity: cross-check array-bearing UNSATs by
                    // concrete witness evaluation (false UNSATs on ground
                    // array disequalities).
                    if query.contains_array_ops() && ground_query_witness_evaluates_true(&query) {
                        return;
                    }
                }
                SmtResult::Unknown => {}
            }
        }
        if self.config.verbose {
            safe_eprintln!(
                "PDR: Counterexample verification: axiom entry {} not justified by \
                any fact clause, marking as unknown",
                entry_idx
            );
        }
        *saw_unknown = true;
    }

    /// Structural match between a witness entry and a clause: head predicate
    /// equals the entry predicate and body predicates align positionally with
    /// the entry's premise predicates.
    fn entry_clause_matches(
        witness: &DerivationWitness,
        entry: &crate::pdr::counterexample::DerivationWitnessEntry,
        clause: &crate::HornClause,
    ) -> bool {
        if clause.head.predicate_id() != Some(entry.predicate) {
            return false;
        }
        if clause.body.predicates.is_empty() {
            return true;
        }
        if entry.premises.len() < clause.body.predicates.len() {
            return false;
        }
        clause
            .body
            .predicates
            .iter()
            .enumerate()
            .all(|(i, (body_pred, _))| {
                entry
                    .premises
                    .get(i)
                    .and_then(|&premise_idx| witness.entries.get(premise_idx))
                    .is_some_and(|premise| premise.predicate == *body_pred)
            })
    }

    /// Replay one witness entry against one candidate clause.
    ///
    /// Extracted from the `verify_counterexample_witness_entries` loop body so
    /// transform-space witnesses can try several re-resolved candidates.
    fn verify_entry_against_clause(
        &mut self,
        witness: &DerivationWitness,
        entry_idx: usize,
        entry: &crate::pdr::counterexample::DerivationWitnessEntry,
        clause: &crate::HornClause,
        restrict_subst_to_canonical: bool,
        saw_unknown: &mut bool,
    ) -> Option<CexVerificationResult> {
        {
            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, head_args) => head_args.as_slice(),
                crate::ClauseHead::False => return None,
            };

            let sort_map = self.counterexample_entry_sort_map_with_clause(witness, entry, clause);
            let mut subst = self.counterexample_entry_subst(witness, entry, &sort_map, saw_unknown);
            if restrict_subst_to_canonical {
                // FM2b: engine models leak clause-local variable names into
                // the instances; on a re-resolved ORIGINAL clause those names
                // collide with unrelated clause variables. Keep only the
                // canonical (positional) names.
                subst.retain(|(var, _)| super::is_canonical_arg_name(&var.name));
            }
            let subst = subst;
            let clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));
            let constraint_instantiated = clause_constraint.substitute(&subst);
            let Some(entry_state_on_head) =
                self.apply_to_args(entry.predicate, &entry.state, head_args)
            else {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Counterexample verification failed at entry {}: \
                        could not apply entry state to clause head",
                        entry_idx
                    );
                }
                return Some(CexVerificationResult::Spurious);
            };
            let entry_state_instantiated = entry_state_on_head.substitute(&subst);

            if clause.body.predicates.is_empty() {
                let fact_query = ChcExpr::and(constraint_instantiated, entry_state_instantiated);
                if let Some(result) = self.verify_counterexample_fact_entry(
                    entry_idx,
                    &subst,
                    fact_query,
                    saw_unknown,
                ) {
                    return Some(result);
                }
                return None;
            }

            if entry.premises.len() < clause.body.predicates.len() {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Counterexample verification failed at entry {}: \
                        clause requires {} premises but only {} provided",
                        entry_idx,
                        clause.body.predicates.len(),
                        entry.premises.len()
                    );
                }
                return Some(CexVerificationResult::Spurious);
            }

            let mut conjuncts = vec![constraint_instantiated, entry_state_instantiated];
            for (i, (body_pred, body_args)) in clause.body.predicates.iter().enumerate() {
                if let Some(&premise_idx) = entry.premises.get(i) {
                    if let Some(premise_entry) = witness.entries.get(premise_idx) {
                        if premise_entry.predicate != *body_pred {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Counterexample verification failed: \
                                    premise predicate mismatch"
                                );
                            }
                            return Some(CexVerificationResult::Spurious);
                        }

                        if let Some(result) = self.verify_counterexample_premise_head_alignment(
                            witness,
                            entry_idx,
                            premise_entry,
                            *body_pred,
                            body_args,
                            &sort_map,
                            &subst,
                            saw_unknown,
                        ) {
                            return Some(result);
                        }

                        if let Some(state_on_body) =
                            self.apply_to_args(*body_pred, &premise_entry.state, body_args)
                        {
                            conjuncts.push(state_on_body.substitute(&subst));
                        }
                    }
                }
            }

            if let Some(result) = self.verify_counterexample_transition_entry(
                entry_idx,
                &subst,
                conjuncts,
                saw_unknown,
            ) {
                return Some(result);
            }
        }

        None
    }

    fn counterexample_entry_sort_map(
        &self,
        witness: &DerivationWitness,
        entry: &crate::pdr::counterexample::DerivationWitnessEntry,
    ) -> FxHashMap<String, ChcSort> {
        let indexed = entry
            .incoming_clause
            .and_then(|clause_idx| self.problem.clauses().get(clause_idx));
        self.counterexample_entry_sort_map_with_clause_opt(witness, entry, indexed)
    }

    /// Like [`counterexample_entry_sort_map`], but sources clause-variable
    /// sorts from an explicitly resolved clause. Required for transform-space
    /// witnesses whose `incoming_clause` index does not address this problem's
    /// clause list (FM2b re-resolution).
    fn counterexample_entry_sort_map_with_clause(
        &self,
        witness: &DerivationWitness,
        entry: &crate::pdr::counterexample::DerivationWitnessEntry,
        clause: &crate::HornClause,
    ) -> FxHashMap<String, ChcSort> {
        self.counterexample_entry_sort_map_with_clause_opt(witness, entry, Some(clause))
    }

    fn counterexample_entry_sort_map_with_clause_opt(
        &self,
        witness: &DerivationWitness,
        entry: &crate::pdr::counterexample::DerivationWitnessEntry,
        clause: Option<&crate::HornClause>,
    ) -> FxHashMap<String, ChcSort> {
        let mut sort_map: FxHashMap<String, ChcSort> = FxHashMap::default();
        if let Some(cvars) = self.canonical_vars(entry.predicate) {
            for cv in cvars {
                sort_map.insert(cv.name.clone(), cv.sort.clone());
            }
        }
        if let Some(clause) = clause {
            for var in clause.vars() {
                sort_map.entry(var.name.clone()).or_insert(var.sort);
            }
        }
        for &premise_idx in &entry.premises {
            if let Some(premise_entry) = witness.entries.get(premise_idx) {
                if let Some(cvars) = self.canonical_vars(premise_entry.predicate) {
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

    fn counterexample_entry_subst(
        &self,
        witness: &DerivationWitness,
        entry: &crate::pdr::counterexample::DerivationWitnessEntry,
        sort_map: &FxHashMap<String, ChcSort>,
        saw_unknown: &mut bool,
    ) -> Vec<(ChcVar, ChcExpr)> {
        let mut subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
        for (name, value) in &entry.instances {
            subst.push(instance_subst_var_and_value(
                name,
                value,
                sort_map.get(name.as_str()),
                self.config.verbose,
                saw_unknown,
            ));
        }

        for &premise_idx in &entry.premises {
            if let Some(premise_entry) = witness.entries.get(premise_idx) {
                for (name, value) in &premise_entry.instances {
                    let (var, expr) = instance_subst_var_and_value(
                        name,
                        value,
                        sort_map.get(name.as_str()),
                        self.config.verbose,
                        saw_unknown,
                    );
                    if !subst.iter().any(|(existing, _)| existing.name == *name) {
                        subst.push((var, expr));
                    }
                }
            }
        }

        subst
    }

    fn verify_counterexample_fact_entry(
        &mut self,
        entry_idx: usize,
        subst: &[(ChcVar, ChcExpr)],
        constraint_instantiated: ChcExpr,
        saw_unknown: &mut bool,
    ) -> Option<CexVerificationResult> {
        let fact_vars: Vec<String> = constraint_instantiated
            .vars()
            .into_iter()
            .map(|v| v.name)
            .filter(|name| !subst.iter().any(|(var, _)| var.name == *name))
            .collect();

        if !fact_vars.is_empty() && subst.is_empty() {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Counterexample verification inconclusive at entry {}: \
                    fact clause has empty instances, {} uncovered variables",
                    entry_idx,
                    fact_vars.len()
                );
            }
            *saw_unknown = true;
            return None;
        }

        let query = self.bound_int_vars(constraint_instantiated);
        self.smt.reset();
        match self
            .smt
            .check_sat_with_timeout(&query, VERIFY_RETRY_TIMEOUT)
        {
            SmtResult::Sat(_) => array_sat_cross_check_result(
                &mut self.smt,
                &query,
                self.config.verbose,
                "fact entry",
            ),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                // FM2b: cross-check array-bearing UNSATs by concrete witness
                // evaluation (false UNSATs on ground array disequalities).
                if query.contains_array_ops() && ground_query_witness_evaluates_true(&query) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: CEX fact entry {}: backend UNSAT overridden by \
                            concrete ground witness evaluation (array replay)",
                            entry_idx
                        );
                    }
                    return None;
                }
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Counterexample verification failed at entry {}: \
                        fact clause constraint UNSAT with instances",
                        entry_idx
                    );
                }
                Some(CexVerificationResult::Spurious)
            }
            SmtResult::Unknown => {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Counterexample verification unknown at entry {}",
                        entry_idx
                    );
                }
                *saw_unknown = true;
                None
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn verify_counterexample_premise_head_alignment(
        &mut self,
        witness: &DerivationWitness,
        entry_idx: usize,
        premise_entry: &crate::pdr::counterexample::DerivationWitnessEntry,
        body_pred: PredicateId,
        body_args: &[ChcExpr],
        _sort_map: &FxHashMap<String, ChcSort>,
        subst: &[(ChcVar, ChcExpr)],
        saw_unknown: &mut bool,
    ) -> Option<CexVerificationResult> {
        let Some(premise_clause_idx) = premise_entry.incoming_clause else {
            return None;
        };
        let Some(premise_clause) = self.problem.clauses().get(premise_clause_idx) else {
            return None;
        };
        let crate::ClauseHead::Predicate(_, head_args) = &premise_clause.head else {
            return None;
        };
        let premise_sort_map = self.counterexample_entry_sort_map(witness, premise_entry);

        let mut full_subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
        for (name, value) in &premise_entry.instances {
            full_subst.push(instance_subst_var_and_value(
                name,
                value,
                premise_sort_map.get(name.as_str()),
                self.config.verbose,
                saw_unknown,
            ));
        }

        for (bp_idx, (bp_pred, bp_args)) in premise_clause.body.predicates.iter().enumerate() {
            let pp_entry = premise_entry
                .premises
                .get(bp_idx)
                .and_then(|&idx| witness.entries.get(idx));
            if let (Some(pp), Some(canon_vars)) = (pp_entry, self.canonical_vars(*bp_pred)) {
                for (arg, cv) in bp_args.iter().zip(canon_vars.iter()) {
                    if let ChcExpr::Var(arg_var) = arg {
                        if let Some(val) = pp.instances.get(&cv.name) {
                            if !full_subst.iter().any(|(var, _)| var.name == arg_var.name) {
                                full_subst.push(instance_subst_var_and_value(
                                    &arg_var.name,
                                    val,
                                    Some(&cv.sort),
                                    self.config.verbose,
                                    saw_unknown,
                                ));
                            }
                        }
                    }
                }
            }
        }

        // Pin the premise clause's head arguments to this premise entry's
        // RECORDED derivation values (its canonical instances). Without this,
        // an under-determined clause constraint — e.g. a base fact
        // `A = 0 ∧ B = C - 1` with `C` unconstrained — lets the SMT solver
        // pick an arbitrary head (`B = -1`, `C = 0`) that then spuriously
        // mismatches the parent clause's body arguments (`B = 2`), even though
        // the recorded derivation (`REC_f_(0, 2, 3)`) is genuine. Pinning the
        // head to the values the reconstructor already committed to keeps the
        // re-solve faithful to the actual derivation. It is soundness-safe:
        // it only ever CONSTRAINS the solve toward the claimed head, so an
        // unachievable head still comes back UNSAT ⇒ Spurious, and the parent
        // transition check plus each premise's own entry verification remain
        // the independent gates.
        let head_pin_vars: Vec<ChcVar> = self
            .canonical_vars(premise_entry.predicate)
            .map(<[ChcVar]>::to_vec)
            .unwrap_or_default();
        for (head_arg, cv) in head_args.iter().zip(head_pin_vars.iter()) {
            if let ChcExpr::Var(head_var) = head_arg {
                if let Some(val) = premise_entry.instances.get(&cv.name) {
                    if !full_subst.iter().any(|(var, _)| var.name == head_var.name) {
                        full_subst.push(instance_subst_var_and_value(
                            &head_var.name,
                            val,
                            Some(&cv.sort),
                            self.config.verbose,
                            saw_unknown,
                        ));
                    }
                }
            }
        }

        let clause_constraint = premise_clause
            .body
            .constraint
            .clone()
            .unwrap_or(ChcExpr::Bool(true));
        let query = self.bound_int_vars(clause_constraint.substitute(&full_subst));
        self.smt.reset();
        match self
            .smt
            .check_sat_with_timeout(&query, VERIFY_RETRY_TIMEOUT)
        {
            SmtResult::Sat(model) => {
                if let Some(result) = array_sat_cross_check_result(
                    &mut self.smt,
                    &query,
                    self.config.verbose,
                    "premise clause",
                ) {
                    return Some(result);
                }
                for (name, value) in model {
                    if !full_subst.iter().any(|(var, _)| var.name == name) {
                        let (var, expr) = instance_subst_var_and_value(
                            &name,
                            &value,
                            None,
                            self.config.verbose,
                            saw_unknown,
                        );
                        full_subst.push((var, expr));
                    }
                }
            }
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                // FM2b: cross-check array-bearing UNSATs by concrete witness
                // evaluation. On override, continue without model-derived
                // substitutions — the witness instances already pin the
                // variables that the head/body alignment below compares.
                if query.contains_array_ops() && ground_query_witness_evaluates_true(&query) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: CEX premise entry {}: backend UNSAT overridden by \
                            concrete ground witness evaluation (array replay)",
                            entry_idx
                        );
                    }
                } else {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Counterexample verification failed at entry {}: \
                             premise clause constraint UNSAT",
                            entry_idx
                        );
                    }
                    return Some(CexVerificationResult::Spurious);
                }
            }
            SmtResult::Unknown => {
                *saw_unknown = true;
            }
        }

        let concrete_head: Vec<ChcExpr> = head_args
            .iter()
            .map(|arg| arg.substitute(&full_subst).simplify_constants())
            .collect();

        let mut body_subst = subst.to_vec();
        if let Some(canon_vars) = self.canonical_vars(body_pred) {
            for (arg, cv) in body_args.iter().zip(canon_vars.iter()) {
                if let ChcExpr::Var(arg_var) = arg {
                    if !body_subst.iter().any(|(var, _)| var.name == arg_var.name) {
                        if let Some(val) = premise_entry.instances.get(&cv.name) {
                            body_subst.push(instance_subst_var_and_value(
                                &arg_var.name,
                                val,
                                Some(&cv.sort),
                                self.config.verbose,
                                saw_unknown,
                            ));
                        }
                    }
                }
            }
        }
        let body_values: Vec<ChcExpr> = body_args
            .iter()
            .map(|arg| arg.substitute(&body_subst).simplify_constants())
            .collect();

        for (pos, (head_val, body_val)) in concrete_head.iter().zip(body_values.iter()).enumerate()
        {
            let values_match = head_val == body_val
                || matches!(
                    ground_exprs_semantically_equal(head_val, body_val),
                    Some(true)
                );
            if !values_match {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Counterexample verification failed at entry {}: \
                         position {} mismatch",
                        entry_idx,
                        pos
                    );
                    safe_eprintln!("  premise head[{}] = {:?}", pos, head_val);
                    safe_eprintln!("  expected body[{}] = {:?}", pos, body_val);
                }
                return Some(CexVerificationResult::Spurious);
            }
        }

        None
    }

    fn verify_counterexample_transition_entry(
        &mut self,
        entry_idx: usize,
        subst: &[(ChcVar, ChcExpr)],
        conjuncts: Vec<ChcExpr>,
        saw_unknown: &mut bool,
    ) -> Option<CexVerificationResult> {
        let combined = ChcExpr::and_all(conjuncts);
        let combined_vars: Vec<String> = combined
            .vars()
            .into_iter()
            .map(|v| v.name)
            .filter(|name| !subst.iter().any(|(var, _)| var.name == *name))
            .collect();

        if !combined_vars.is_empty() && subst.is_empty() {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Counterexample verification inconclusive at entry {}: \
                    transition step has empty instances, {} uncovered variables",
                    entry_idx,
                    combined_vars.len()
                );
            }
            *saw_unknown = true;
            return None;
        }

        let query = self.bound_int_vars(combined);
        self.smt.reset();
        match self
            .smt
            .check_sat_with_timeout(&query, VERIFY_RETRY_TIMEOUT)
        {
            SmtResult::Sat(_) => array_sat_cross_check_result(
                &mut self.smt,
                &query,
                self.config.verbose,
                "transition entry",
            ),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                // FM2b: cross-check array-bearing UNSATs by concrete witness
                // evaluation — guards against false UNSATs on ground
                // const-array/store disequalities in transition replays.
                if query.contains_array_ops() && ground_query_witness_evaluates_true(&query) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: CEX transition entry {}: backend UNSAT overridden by \
                            concrete ground witness evaluation (array replay)",
                            entry_idx
                        );
                    }
                    return None;
                }
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Counterexample verification failed at entry {}: \
                        derivation UNSAT",
                        entry_idx
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
