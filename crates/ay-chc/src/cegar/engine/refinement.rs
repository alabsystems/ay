// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Refinement: template predicate generation, equality resolution, and ARG restart.

use super::*;

impl CegarEngine {
    pub(super) fn generate_template_predicates(
        &self,
        trace: &[usize],
    ) -> Vec<(PredicateId, ChcExpr)> {
        const MIN_TEMPLATE_PREDICATES: usize = 12;
        const MAX_TEMPLATE_PREDICATES: usize = 24;

        let mut predicates = Vec::new();
        let trace_relations = self.trace_relations(trace);
        let mut known_by_relation: FxHashMap<PredicateId, FxHashSet<ChcExpr>> =
            FxHashMap::default();

        for relation in &trace_relations {
            let known = known_by_relation.entry(*relation).or_default();
            for existing in self.predicates.get_formulas(*relation) {
                known.insert((*existing).clone());
            }
        }

        for &edge_idx in trace {
            let edge = &self.edges[edge_idx];
            let clause = &self.problem.clauses()[edge.clause_index];

            let (relation, head_args) = match &clause.head {
                ClauseHead::Predicate(pid, args) => (*pid, args.clone()),
                ClauseHead::False => continue,
            };
            let canonical_vars = self.canonical_vars(relation);

            // #2660: Build substitution only for Var head args. Collect
            // expression head arg vars so we can skip atoms that reference
            // them (they can't be meaningfully canonicalized).
            let mut subst = Vec::new();
            let mut expr_arg_vars: FxHashSet<String> = FxHashSet::default();
            for (arg, canonical) in head_args.iter().zip(canonical_vars.iter()) {
                match arg {
                    ChcExpr::Var(v) => {
                        subst.push((v.clone(), ChcExpr::var(canonical.clone())));
                    }
                    expr => {
                        for v in expr.vars() {
                            expr_arg_vars.insert(v.name.clone());
                        }
                    }
                }
            }

            if let Some(ref constraint) = clause.body.constraint {
                let atoms = Self::extract_comparison_atoms(constraint);
                let head_vars: FxHashSet<_> = head_args.iter().flat_map(ChcExpr::vars).collect();

                for atom in atoms {
                    let atom_vars: FxHashSet<_> = atom.vars().into_iter().collect();
                    if atom_vars.is_subset(&head_vars) {
                        // #2660: Skip atoms that use expression head arg vars —
                        // they can't be canonicalized to predicate-positional form.
                        if atom_vars.iter().any(|v| expr_arg_vars.contains(&v.name)) {
                            continue;
                        }
                        let pred = atom.substitute(&subst);
                        if !matches!(pred, ChcExpr::Bool(_)) {
                            let known = known_by_relation.entry(relation).or_default();
                            if known.insert(pred.clone()) {
                                predicates.push((relation, pred));
                            }
                        }
                    }
                }
            }
        }

        if predicates.len() < MIN_TEMPLATE_PREDICATES {
            let mut added = 0usize;
            for &relation in &trace_relations {
                let canonical_vars = self.canonical_vars(relation);
                if canonical_vars.is_empty() {
                    continue;
                }

                for candidate in self.qualifiers.instantiate(&canonical_vars) {
                    if matches!(candidate, ChcExpr::Bool(_)) {
                        continue;
                    }

                    let known = known_by_relation.entry(relation).or_default();
                    if !known.insert(candidate.clone()) {
                        continue;
                    }

                    predicates.push((relation, candidate));
                    added += 1;

                    if predicates.len() >= MIN_TEMPLATE_PREDICATES
                        || predicates.len() >= MAX_TEMPLATE_PREDICATES
                    {
                        break;
                    }
                }

                if predicates.len() >= MIN_TEMPLATE_PREDICATES
                    || predicates.len() >= MAX_TEMPLATE_PREDICATES
                {
                    break;
                }
            }

            if self.config.base.verbose && added > 0 {
                safe_eprintln!(
                    "CEGAR: qualifier fallback added {} template predicates",
                    added
                );
            }
        }

        // Always inject product/quadratic predicates regardless of MIN/MAX caps.
        // Product invariants (v1*v2 = v3, v*v+v = 2*w, v1+v2 = v3) are critical
        // for s_multipl benchmarks. When linear comparison atoms fill the template
        // budget, the qualifier fallback never reaches these nonlinear patterns.
        let mut prod_added = 0usize;
        for &relation in &trace_relations {
            let canonical_vars = self.canonical_vars(relation);
            let known = known_by_relation.entry(relation).or_default();
            for candidate in self
                .qualifiers
                .instantiate_product_predicates(&canonical_vars)
            {
                if known.insert(candidate.clone()) {
                    predicates.push((relation, candidate));
                    prod_added += 1;
                }
            }
        }
        if self.config.base.verbose && prod_added > 0 {
            safe_eprintln!(
                "CEGAR: injected {} product/quadratic template predicates",
                prod_added
            );
        }

        // Always inject modular predicates regardless of MIN/MAX caps.
        // Modular invariants (= (mod v k) c) are critical for benchmarks like
        // dillig02_m, half_true_modif_m, and s_multipl_09-17. When comparison
        // atoms already fill the template budget, the normal qualifier fallback
        // is skipped; this keeps the full problem-derived modular family alive.
        let mut mod_added = 0usize;
        for &relation in &trace_relations {
            let canonical_vars = self.canonical_vars(relation);
            let known = known_by_relation.entry(relation).or_default();
            for candidate in self
                .qualifiers
                .instantiate_modular_predicates(&canonical_vars)
            {
                if known.insert(candidate.clone()) {
                    predicates.push((relation, candidate));
                    mod_added += 1;
                }
            }
        }
        if self.config.base.verbose && mod_added > 0 {
            safe_eprintln!("CEGAR: injected {} modular template predicates", mod_added);
        }

        predicates
    }

    /// Build linking equalities between consecutive trace steps.
    ///
    /// For each step after the first, finds the previous step whose head predicate
    /// matches a body predicate of the current step, and creates equality constraints
    /// between the renamed head args and renamed body args.
    pub(super) fn build_trace_links(
        &self,
        trace: &[usize],
        step_substs: &[Vec<(ChcVar, ChcExpr)>],
    ) -> Vec<TraceLink> {
        let mut links = Vec::new();
        for step in 1..trace.len() {
            let edge = &self.edges[trace[step]];
            let clause = &self.problem.clauses()[edge.clause_index];
            for (body_pred_id, body_args) in &clause.body.predicates {
                for prev_step in (0..step).rev() {
                    let prev_edge = &self.edges[trace[prev_step]];
                    let prev_clause = &self.problem.clauses()[prev_edge.clause_index];
                    if let ClauseHead::Predicate(ref head_pred_id, ref head_args) = prev_clause.head
                    {
                        if head_pred_id == body_pred_id && head_args.len() == body_args.len() {
                            let eqs: Vec<_> = head_args
                                .iter()
                                .zip(body_args.iter())
                                .map(|(h, b)| {
                                    ChcExpr::eq(
                                        h.substitute(&step_substs[prev_step]),
                                        b.substitute(&step_substs[step]),
                                    )
                                })
                                .collect();
                            links.push(TraceLink {
                                from_step: prev_step,
                                to_step: step,
                                equalities: eqs,
                            });
                            break;
                        }
                    }
                }
            }
        }
        links
    }

    /// Resolve var=var and var=const equalities by substitution.
    ///
    /// Given a set of constraints containing equalities like `_ref_0_A = _iface_0`
    /// and `_ref_0_A = 1`, builds a substitution to eliminate non-shared variables.
    /// The result expresses the constraints purely in terms of shared (interface)
    /// variables plus any irreducible non-equality constraints.
    ///
    /// This enables the Farkas-based interpolation methods to work, since they
    /// require constraints expressed over the shared variables.
    pub(super) fn resolve_equalities(
        parts: &[ChcExpr],
        shared_vars: &FxHashSet<String>,
    ) -> Vec<ChcExpr> {
        let mut subst_map: FxHashMap<String, ChcExpr> = FxHashMap::default();
        let mut remaining: Vec<ChcExpr> = Vec::new();

        // Initial extraction of equalities from all parts.
        for part in parts {
            Self::collect_equalities_for_resolution(
                part,
                shared_vars,
                &mut subst_map,
                &mut remaining,
            );
        }

        // Iteratively: (1) resolve chains in subst_map, (2) apply substitution
        // to remaining, (3) re-extract any new equalities that appear.
        // This handles conflict-generated equalities like eq(_ref_2_A, _iface_0)
        // that need further resolution.
        for _ in 0..20 {
            // Resolve transitive chains in subst_map.
            let mut chain_changed = true;
            while chain_changed {
                chain_changed = false;
                let keys: Vec<String> = subst_map.keys().cloned().collect();
                for key in keys {
                    let val = subst_map[&key].clone();
                    let resolved = Self::apply_subst_expr(&val, &subst_map);
                    if resolved != val {
                        subst_map.insert(key, resolved);
                        chain_changed = true;
                    }
                }
            }

            // Build substitution pairs for application.
            let subst_pairs = Self::build_subst_pairs(&subst_map);

            // Apply substitution to remaining, and re-extract equalities.
            let prev_remaining = std::mem::take(&mut remaining);
            let prev_map_size = subst_map.len();

            for expr in &prev_remaining {
                let substituted = expr.substitute(&subst_pairs);
                let simplified = substituted.simplify_constants();
                Self::collect_equalities_for_resolution(
                    &simplified,
                    shared_vars,
                    &mut subst_map,
                    &mut remaining,
                );
            }

            // If no new mappings were added, we've converged.
            if subst_map.len() == prev_map_size {
                break;
            }
        }

        // Final substitution application.
        let subst_pairs = Self::build_subst_pairs(&subst_map);

        let mut result: Vec<ChcExpr> = Vec::new();
        for expr in &remaining {
            let substituted = expr.substitute(&subst_pairs);
            let simplified = substituted.simplify_constants();
            match &simplified {
                ChcExpr::Bool(true) => {}
                ChcExpr::Bool(false) => {
                    return vec![ChcExpr::Bool(false)];
                }
                _ => result.push(simplified),
            }
        }

        if result.is_empty() {
            result.push(ChcExpr::Bool(true));
        }

        result
    }

    /// Build substitution pairs from a name→expr map, inferring sorts from values.
    fn build_subst_pairs(subst_map: &FxHashMap<String, ChcExpr>) -> Vec<(ChcVar, ChcExpr)> {
        subst_map
            .iter()
            .map(|(name, expr)| {
                let sort = match expr {
                    ChcExpr::Int(_) => ChcSort::Int,
                    ChcExpr::Bool(_) => ChcSort::Bool,
                    ChcExpr::Var(v) => v.sort.clone(),
                    _ => ChcSort::Int,
                };
                (ChcVar::new(name, sort), expr.clone())
            })
            .collect()
    }

    /// Extract equalities from an expression and classify them for resolution.
    fn collect_equalities_for_resolution(
        expr: &ChcExpr,
        shared_vars: &FxHashSet<String>,
        subst_map: &mut FxHashMap<String, ChcExpr>,
        remaining: &mut Vec<ChcExpr>,
    ) {
        match expr {
            ChcExpr::Op(ChcOp::And, args) => {
                for arg in args {
                    Self::collect_equalities_for_resolution(arg, shared_vars, subst_map, remaining);
                }
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                let (lhs, rhs) = (args[0].as_ref(), args[1].as_ref());
                match (lhs, rhs) {
                    // var = expr: substitute the non-shared var
                    (ChcExpr::Var(v), rhs_expr) if !shared_vars.contains(&v.name) => {
                        if let Some(existing) = subst_map.get(&v.name) {
                            // var already mapped: add implied equality between existing and new
                            remaining.push(ChcExpr::eq(existing.clone(), rhs_expr.clone()));
                        } else {
                            subst_map.insert(v.name.clone(), rhs_expr.clone());
                        }
                    }
                    (lhs_expr, ChcExpr::Var(v)) if !shared_vars.contains(&v.name) => {
                        if let Some(existing) = subst_map.get(&v.name) {
                            remaining.push(ChcExpr::eq(existing.clone(), lhs_expr.clone()));
                        } else {
                            subst_map.insert(v.name.clone(), lhs_expr.clone());
                        }
                    }
                    // Both shared or both non-var: keep as constraint
                    _ => remaining.push(expr.clone()),
                }
            }
            _ => remaining.push(expr.clone()),
        }
    }

    /// Apply a substitution map to a single expression.
    fn apply_subst_expr(expr: &ChcExpr, map: &FxHashMap<String, ChcExpr>) -> ChcExpr {
        expr.substitute_name_map(map)
    }

    fn trace_relations(&self, trace: &[usize]) -> Vec<PredicateId> {
        let mut seen = FxHashSet::default();
        let mut relations = Vec::new();

        for &edge_idx in trace {
            let edge = &self.edges[edge_idx];
            let clause = &self.problem.clauses()[edge.clause_index];
            if let ClauseHead::Predicate(pred_id, _) = clause.head {
                if seen.insert(pred_id) {
                    relations.push(pred_id);
                }
            }
        }

        relations
    }

    pub(super) fn extract_comparison_atoms(expr: &ChcExpr) -> Vec<ChcExpr> {
        let mut atoms = Vec::new();
        Self::collect_atoms(expr, &mut atoms);
        atoms
    }

    fn collect_atoms(expr: &ChcExpr, atoms: &mut Vec<ChcExpr>) {
        crate::expr::maybe_grow_expr_stack(|| {
            if let ChcExpr::Op(op, args) = expr {
                match op {
                    ChcOp::Le | ChcOp::Lt | ChcOp::Ge | ChcOp::Gt | ChcOp::Eq | ChcOp::Ne => {
                        atoms.push(expr.clone());
                    }
                    ChcOp::And | ChcOp::Or => {
                        for arg in args {
                            Self::collect_atoms(arg, atoms);
                        }
                    }
                    ChcOp::Not => {
                        if let Some(inner) = args.first() {
                            Self::collect_atoms(inner, atoms);
                        }
                    }
                    _ => {}
                }
            }
        });
    }

    pub(super) fn refine(&mut self, new_predicates: Vec<(PredicateId, ChcExpr)>) -> bool {
        // Deduplicate: skip predicates already in the store (structural equality
        // after constant simplification). Keep conjunctive predicates intact —
        // splitting them into atomic components causes CEGAR to lose relational
        // invariant strength needed for multi-predicate problems like s_multipl_12
        // (#2735).
        let mut actually_new: Vec<(PredicateId, ChcExpr)> = Vec::new();
        for (rel, formula) in &new_predicates {
            // Skip trivial predicates
            if let ChcExpr::Bool(_) = formula {
                continue;
            }
            let simplified = formula.simplify_constants();
            if matches!(simplified, ChcExpr::Bool(_)) {
                continue;
            }

            // Structural dedup against existing store
            let existing = self.predicates.get_formulas(*rel);
            let is_structural_dup = existing
                .iter()
                .any(|f| f.simplify_constants() == simplified);
            if is_structural_dup {
                continue;
            }

            // Structural dedup against other candidates in this batch
            let is_batch_dup = actually_new
                .iter()
                .any(|(r, f)| *r == *rel && f.simplify_constants() == simplified);
            if is_batch_dup {
                continue;
            }

            actually_new.push((*rel, formula.clone()));
        }

        if self.config.base.verbose {
            safe_eprintln!(
                "CEGAR: adding {} new predicates ({} duplicates skipped)",
                actually_new.len(),
                new_predicates.len() - actually_new.len()
            );
        }

        if actually_new.is_empty() {
            return false;
        }

        // Add new predicates to the store
        for (rel, formula) in &actually_new {
            self.predicates.add_predicate(*rel, formula.clone());
        }

        // State preservation (#3762): invalidate the implication cache because
        // new predicates change abstract state computation (different conclusions
        // in implication checks). The feasibility cache is preserved — expansion
        // constraints with new predicates will have structurally different keys.
        self.cache.invalidate_implications();

        // Publish discovered predicates to the cooperative blackboard (#7910).
        // PDR engines consume these as lemma hints, accelerating convergence
        // when CEGAR discovers predicates that PDR's generalization misses.
        if let Some(ref bb) = self.config.blackboard {
            let lemmas = actually_new
                .iter()
                .map(|(rel, formula)| (*rel, formula.clone(), 0usize));
            bb.publish(self.config.engine_idx, lemmas);
            if self.config.base.verbose {
                safe_eprintln!(
                    "CEGAR: published {} predicates to blackboard",
                    actually_new.len()
                );
            }
        }

        // Restart the ARG with the enriched predicate set.
        // The new predicates will produce more refined abstract states during
        // re-exploration, changing the subsumption structure and potentially
        // leading to different counterexample traces.
        self.restart_arg();
        true
    }

    /// Clear the ARG and re-seed facts, preserving the predicate store.
    pub(super) fn restart_arg(&mut self) {
        self.edges.clear();
        self.active_states
            .values_mut()
            .for_each(|states| states.clear());
        self.max_states
            .values_mut()
            .for_each(|states| states.clear());
        self.forward_subsumed.clear();
        self.backward_subsumed.clear();
        self.queue = StateQueue::new();
        self.seed_facts();
    }
}
