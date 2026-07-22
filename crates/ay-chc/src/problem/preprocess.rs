// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl ChcProblem {
    /// (#7048) Pre-expand `(mod p k)` and `(div p k)` (constant positive k) into fresh
    /// variables with Euclidean division axioms in all clause expressions.
    ///
    /// Replaces each `(mod p k)` with a fresh `r` and `(div p k)` with a fresh `q`, adding
    /// axioms `p = k * q + r ∧ 0 ≤ r < k` as body constraint conjuncts. This eliminates
    /// mod/div from the clause surface, making the problem classifiable as pure LIA.
    ///
    /// Fresh variables are per-clause (each clause has its own universally quantified scope).
    pub fn expand_mod_div_in_clauses(&mut self, verbose: bool) {
        let has_any = self.clauses.iter().any(|c| {
            c.body
                .constraint
                .as_ref()
                .is_some_and(ChcExpr::contains_mod_or_div)
                || c.body
                    .predicates
                    .iter()
                    .any(|(_, args)| args.iter().any(ChcExpr::contains_mod_or_div))
                || match &c.head {
                    ClauseHead::Predicate(_, args) => args.iter().any(ChcExpr::contains_mod_or_div),
                    ClauseHead::False => false,
                }
        });
        if !has_any {
            return;
        }

        let mut total_expansions = 0usize;
        for clause in &mut self.clauses {
            let mut counter = 0usize;
            let mut axioms: Vec<ChcExpr> = Vec::new();
            // Cache: (dividend_debug_string, divisor) → (quotient_expr, remainder_expr).
            // Ensures identical mod/div sub-expressions share the same fresh variables
            // (soundness fix: const_mod_3 has two `(mod B 2)` in the query).
            let mut cache: Vec<(String, i128, ChcExpr, ChcExpr)> = Vec::new();

            // Expand in body constraint.
            if let Some(ref constraint) = clause.body.constraint {
                if constraint.contains_mod_or_div() {
                    clause.body.constraint = Some(Self::expand_mod_div_expr(
                        constraint,
                        &mut counter,
                        &mut axioms,
                        &mut cache,
                    ));
                }
            }

            // Expand in body predicate arguments.
            for (_pred_id, args) in &mut clause.body.predicates {
                for arg in args.iter_mut() {
                    if arg.contains_mod_or_div() {
                        *arg =
                            Self::expand_mod_div_expr(arg, &mut counter, &mut axioms, &mut cache);
                    }
                }
            }

            // Expand in head arguments.
            if let ClauseHead::Predicate(_, ref mut args) = clause.head {
                for arg in args.iter_mut() {
                    if arg.contains_mod_or_div() {
                        *arg =
                            Self::expand_mod_div_expr(arg, &mut counter, &mut axioms, &mut cache);
                    }
                }
            }

            // Conjoin axioms into the body constraint.
            if !axioms.is_empty() {
                total_expansions += axioms.len() / 3; // 3 axioms per expansion
                let axiom_conj = ChcExpr::and_all(axioms);
                clause.body.constraint = Some(match clause.body.constraint.take() {
                    Some(existing) => ChcExpr::and(existing, axiom_conj),
                    None => axiom_conj,
                });
            }
        }

        if verbose && total_expansions > 0 {
            safe_eprintln!(
                "CHC: mod/div expansion: {} expansions across clauses (#7048)",
                total_expansions
            );
        }
    }

    /// Recursively expand mod/div in a single expression, generating fresh variables.
    ///
    /// The `cache` ensures identical `(mod p k)` / `(div p k)` sub-expressions within
    /// the same clause share a single pair of fresh quotient/remainder variables.
    /// Without this, two occurrences of `(mod B 2)` would get independent fresh vars,
    /// breaking soundness (e.g., `const_mod_3` would return unsat instead of sat).
    fn expand_mod_div_expr(
        expr: &ChcExpr,
        counter: &mut usize,
        axioms: &mut Vec<ChcExpr>,
        cache: &mut Vec<(String, i128, ChcExpr, ChcExpr)>,
    ) -> ChcExpr {
        match expr {
            ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::Real(_, _)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::Var(_)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_) => expr.clone(),

            ChcExpr::Op(op, args) => {
                // Bottom-up: expand children first
                let new_args: Vec<Arc<ChcExpr>> = args
                    .iter()
                    .map(|a| Arc::new(Self::expand_mod_div_expr(a, counter, axioms, cache)))
                    .collect();
                match op {
                    ChcOp::Mod if new_args.len() == 2 => {
                        if let ChcExpr::Int(k) = new_args[1].as_ref() {
                            if *k > 0 {
                                let dividend = new_args[0].as_ref().clone();
                                let key = format!("{dividend:?}");
                                if let Some((_, _, _q_e, r_e)) =
                                    cache.iter().find(|(dk, dv, _, _)| dk == &key && *dv == *k)
                                {
                                    return r_e.clone();
                                }
                                let idx = *counter;
                                *counter += 1;
                                let q = ChcVar::new(format!("__moddiv_q_{idx}"), ChcSort::Int);
                                let r = ChcVar::new(format!("__moddiv_r_{idx}"), ChcSort::Int);
                                let q_e = ChcExpr::var(q);
                                let r_e = ChcExpr::var(r);
                                let k_e = ChcExpr::Int(*k);
                                axioms.push(ChcExpr::eq(
                                    dividend,
                                    ChcExpr::add(
                                        ChcExpr::mul(k_e.clone(), q_e.clone()),
                                        r_e.clone(),
                                    ),
                                ));
                                axioms.push(ChcExpr::ge(r_e.clone(), ChcExpr::Int(0)));
                                axioms.push(ChcExpr::lt(r_e.clone(), k_e));
                                cache.push((key, *k, q_e, r_e.clone()));
                                return r_e;
                            }
                        }
                        ChcExpr::Op(*op, new_args)
                    }
                    ChcOp::Div if new_args.len() == 2 => {
                        if let ChcExpr::Int(k) = new_args[1].as_ref() {
                            if *k > 0 {
                                let dividend = new_args[0].as_ref().clone();
                                let key = format!("{dividend:?}");
                                if let Some((_, _, q_e, _r_e)) =
                                    cache.iter().find(|(dk, dv, _, _)| dk == &key && *dv == *k)
                                {
                                    return q_e.clone();
                                }
                                let idx = *counter;
                                *counter += 1;
                                let q = ChcVar::new(format!("__moddiv_q_{idx}"), ChcSort::Int);
                                let r = ChcVar::new(format!("__moddiv_r_{idx}"), ChcSort::Int);
                                let q_e = ChcExpr::var(q);
                                let r_e = ChcExpr::var(r);
                                let k_e = ChcExpr::Int(*k);
                                axioms.push(ChcExpr::eq(
                                    dividend,
                                    ChcExpr::add(
                                        ChcExpr::mul(k_e.clone(), q_e.clone()),
                                        r_e.clone(),
                                    ),
                                ));
                                axioms.push(ChcExpr::ge(r_e.clone(), ChcExpr::Int(0)));
                                axioms.push(ChcExpr::lt(r_e.clone(), k_e));
                                cache.push((key, *k, q_e.clone(), r_e));
                                return q_e;
                            }
                        }
                        ChcExpr::Op(*op, new_args)
                    }
                    _ => ChcExpr::Op(*op, new_args),
                }
            }

            ChcExpr::PredicateApp(name, id, args) => {
                let new_args: Vec<Arc<ChcExpr>> = args
                    .iter()
                    .map(|a| Arc::new(Self::expand_mod_div_expr(a, counter, axioms, cache)))
                    .collect();
                ChcExpr::PredicateApp(name.clone(), *id, new_args)
            }

            ChcExpr::FuncApp(name, sort, args) => {
                let new_args: Vec<Arc<ChcExpr>> = args
                    .iter()
                    .map(|a| Arc::new(Self::expand_mod_div_expr(a, counter, axioms, cache)))
                    .collect();
                ChcExpr::FuncApp(name.clone(), sort.clone(), new_args)
            }

            ChcExpr::ConstArray(ks, val) => ChcExpr::ConstArray(
                ks.clone(),
                Arc::new(Self::expand_mod_div_expr(val, counter, axioms, cache)),
            ),
        }
    }

    /// Pre-eliminate mod/div in clause body constraints (#7048, #5970).
    ///
    /// For each `(mod x k)` with constant k, introduces fresh q, r with:
    ///   x = k*q + r, r >= 0, r < |k|
    ///
    /// Fresh variables are clause-local (existentially quantified in the
    /// clause body). They do NOT appear in predicate argument lists.
    ///
    /// **Exception (#1362):** Clauses where ALL mod/div terms have constant
    /// (literal integer) divisors are preserved. The SMT solver's LIA theory
    /// handles `(mod x k)` natively for constant k, and preserving the modular
    /// structure lets PDR synthesize invariants like `A mod 6 = 0` that would
    /// be lost after Euclidean decomposition.
    pub fn eliminate_mod_in_constraints(&mut self, verbose: bool) {
        let mut eliminated = 0;
        let mut preserved = 0;
        for clause in &mut self.clauses {
            if let Some(ref c) = clause.body.constraint {
                if c.contains_mod_or_div() {
                    if c.all_mod_div_have_constant_divisors() {
                        // #1362: Keep mod/div with constant divisors for PDR
                        preserved += 1;
                    } else {
                        clause.body.constraint = Some(c.eliminate_mod());
                        eliminated += 1;
                    }
                }
            }
        }
        if verbose && (eliminated > 0 || preserved > 0) {
            safe_eprintln!(
                "CHC: mod/div preprocessing: eliminated {} clauses, preserved {} with constant divisors (#7048/#1362)",
                eliminated, preserved
            );
        }
    }

    /// Expand nullary "fail" predicate queries into direct queries.
    ///
    /// CHC-COMP benchmarks often use a pattern with a nullary `fail` predicate:
    /// 1. `inv(...) AND bad_condition => fail`
    /// 2. `fail => false`
    ///
    /// This transformation replaces `fail => false` queries with expanded queries
    /// that directly reference the original predicates:
    /// - For each clause `body => fail`, create a query `body => false`
    /// - Remove the original `fail => false` query
    /// - Remove clauses that have `fail` in their head
    ///
    /// This enables the PDR solver to work with the actual state predicates
    /// instead of the intermediate nullary fail predicate.
    ///
    /// Returns true if any transformation was performed.
    pub fn expand_nullary_fail_queries(&mut self, verbose: bool) -> bool {
        // Find query clauses with nullary predicates in body
        let mut nullary_fail_preds: Vec<PredicateId> = Vec::new();

        for query in self.queries() {
            if query.body.predicates.len() == 1 {
                let (pred_id, args) = &query.body.predicates[0];
                if args.is_empty() {
                    // This is a query with a nullary predicate (like `fail => false`)
                    nullary_fail_preds.push(*pred_id);
                }
            }
        }

        if nullary_fail_preds.is_empty() {
            return false;
        }

        if verbose {
            let pred_names: Vec<_> = nullary_fail_preds
                .iter()
                .filter_map(|id| self.get_predicate(*id).map(|p| p.name.clone()))
                .collect();
            safe_eprintln!(
                "CHC: expanding {} nullary fail predicates: {:?}",
                nullary_fail_preds.len(),
                pred_names
            );
        }

        // For each nullary fail predicate, find clauses that transition to it
        let mut new_queries: Vec<HornClause> = Vec::new();

        for fail_pred in &nullary_fail_preds {
            // Find all clauses `body => fail_pred`
            for clause in &self.clauses {
                if let ClauseHead::Predicate(head_pred, _) = &clause.head {
                    if head_pred == fail_pred {
                        // Convert `body => fail_pred` to `body => false`
                        let new_query = HornClause::query(clause.body.clone());
                        new_queries.push(new_query);
                    }
                }
            }
        }

        if new_queries.is_empty() {
            return false;
        }

        const MAX_EXPANDED_NULLARY_FAIL_QUERIES: usize = 512;
        if new_queries.len() > MAX_EXPANDED_NULLARY_FAIL_QUERIES {
            if verbose {
                safe_eprintln!(
                    "CHC: keeping nullary fail predicates unexpanded ({} candidate queries exceeds threshold {})",
                    new_queries.len(),
                    MAX_EXPANDED_NULLARY_FAIL_QUERIES
                );
            }
            return false;
        }

        if verbose {
            safe_eprintln!("CHC: created {} expanded queries", new_queries.len());
        }

        // Remove:
        // 1. Original queries with nullary predicates (`fail => false`)
        // 2. Clauses that have a nullary fail predicate in their head
        // Keep all other clauses (facts, transitions, and any queries not using nullary predicates)
        let nullary_set: FxHashSet<PredicateId> = nullary_fail_preds.iter().copied().collect();

        self.clauses.retain(|clause| {
            // Remove `fail => false` queries
            if clause.is_query() && clause.body.predicates.len() == 1 {
                let (pred_id, args) = &clause.body.predicates[0];
                if args.is_empty() && nullary_set.contains(pred_id) {
                    return false;
                }
            }
            // Remove clauses with nullary fail predicate in head
            if let ClauseHead::Predicate(head_pred, _) = &clause.head {
                if nullary_set.contains(head_pred) {
                    return false;
                }
            }
            true
        });

        // Add the expanded queries
        self.clauses.extend(new_queries);

        true
    }
}
