// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Helper methods for verification.
//!
//! Shared utilities used by both model and counterexample verification:
//! clause body/head evaluation under a model, state extraction from SMT models,
//! formula application to predicate arguments, and constraint canonicalization.

use super::*;

impl PdrSolver {
    pub(super) fn has_verification_case_split_surface(expr: &ChcExpr) -> bool {
        let mut stack = vec![(expr, 0usize)];
        while let Some((expr, depth)) = stack.pop() {
            if depth >= 128 {
                return false;
            }

            match expr {
                ChcExpr::Op(ChcOp::Ite | ChcOp::Or, _) => return true,
                ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                    if matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::Eq, eq) if eq.len() == 2) {
                        return true;
                    }
                    stack.push((args[0].as_ref(), depth + 1));
                }
                ChcExpr::Op(_, args)
                | ChcExpr::PredicateApp(_, _, args)
                | ChcExpr::FuncApp(_, _, args) => {
                    for arg in args {
                        stack.push((arg.as_ref(), depth + 1));
                    }
                }
                ChcExpr::ConstArray(_, value) => {
                    stack.push((value.as_ref(), depth + 1));
                }
                ChcExpr::Bool(_)
                | ChcExpr::Int(_)
                | ChcExpr::Real(_, _)
                | ChcExpr::BitVec(_, _)
                | ChcExpr::Var(_)
                | ChcExpr::ConstArrayMarker(_)
                | ChcExpr::IsTesterMarker(_) => {}
            }
        }
        false
    }

    pub(super) fn try_verification_case_split(
        smt: &mut SmtContext,
        verbose: bool,
        query: &ChcExpr,
        timeout: std::time::Duration,
    ) -> SmtResult {
        if timeout.is_zero() {
            return SmtResult::Unknown;
        }

        let simplified = query.propagate_equalities();
        if matches!(simplified, ChcExpr::Bool(false)) {
            return SmtResult::Unsat;
        }

        // `timeout` bounds the WHOLE split, not one check of it.
        //
        // `scoped_check_timeout` is a PER-CHECK bound and
        // `check_sat_with_ite_case_split` issues one check per LEAF (ITE
        // pre-split to `MAX_ITE_SPLIT_DEPTH`, the OR/disequality fallbacks,
        // and `decide_bool_mod_unsat`'s exhaustive split over up to
        // `MAX_BOOL_SPLIT_VARS` Booleans), so the bound multiplied. Every
        // caller derives `timeout` from the remainder of the enclosing
        // per-clause verification budget (`current_verify_step_timeout`,
        // `VERIFY_CASE_SPLIT_TIMEOUT.min(remaining)`), so the multiplier is
        // exactly how that budget gets exceeded. Measured at a 20s adaptive
        // budget over the extra-small-lia corpus: 7 of 250 calls ran past
        // their `timeout`, worst 680ms against 200ms (3.40x) on
        // `count_by_2_m_nest_000` and 618ms (3.09x) twice on `dillig12_m_000`.
        //
        // The recursion already consults the thread SMT deadline
        // (`smt_deadline_expired()` at its entry; `check_sat` clamps every
        // per-check timeout through `clamp_timeout_to_smt_deadline`) — it was
        // simply never armed on this path. `ScopedSmtDeadline` only ever
        // TIGHTENS, so an enclosing engine deadline still wins, and the guard
        // is released when this call returns.
        //
        // Verdict-safe by construction: an expired deadline yields `Unknown`
        // for that leaf, `any_unknown` then suppresses the all-branches-UNSAT
        // conclusion, and every caller treats `Unknown` as "not decided" and
        // falls through. It can lose an UNSAT, never fabricate one.
        let _split_deadline = crate::smt::ScopedSmtDeadline::install(timeout);
        let _timeout = smt.scoped_check_timeout(Some(timeout));
        let (result, _) = Self::check_sat_with_ite_case_split(smt, verbose, &simplified);
        result
    }

    pub(in crate::pdr) fn clause_body_under_model(
        &self,
        body: &crate::ClauseBody,
        model: &InvariantModel,
    ) -> Option<ChcExpr> {
        let mut parts: Vec<ChcExpr> = Vec::new();

        if let Some(c) = &body.constraint {
            parts.push(c.clone());
        }

        for (pred, args) in &body.predicates {
            let interp = model.get(pred)?;
            let applied = self.apply_interp_to_args(interp, args)?;
            parts.push(applied);
        }

        Some(ChcExpr::and_all(parts))
    }

    /// Extract only the invariant parts from a clause body (predicate interpretations).
    /// Unlike `clause_body_under_model`, this EXCLUDES the constraint.
    /// Used by #74 fix to filter invariant separately from bad state constraint.
    pub(in crate::pdr) fn extract_invariant_only_from_body(
        &self,
        body: &crate::ClauseBody,
        model: &InvariantModel,
    ) -> Option<ChcExpr> {
        let mut parts: Vec<ChcExpr> = Vec::new();
        // Only add predicate interpretations, NOT the constraint
        for (pred, args) in &body.predicates {
            let interp = model.get(pred)?;
            let applied = self.apply_interp_to_args(interp, args)?;
            parts.push(applied);
        }
        if parts.is_empty() {
            return Some(ChcExpr::Bool(true));
        }
        Some(ChcExpr::and_all(parts))
    }

    pub(in crate::pdr) fn clause_head_under_model(
        &self,
        head: &crate::ClauseHead,
        model: &InvariantModel,
    ) -> Option<ChcExpr> {
        match head {
            crate::ClauseHead::Predicate(pred, args) => {
                let interp = model.get(pred)?;
                self.apply_interp_to_args(interp, args)
            }
            crate::ClauseHead::False => Some(ChcExpr::Bool(false)),
        }
    }

    /// Extract a state formula from a model given predicate arguments.
    /// Maps argument expressions (which may be clause-local variables) to canonical variables.
    pub(in crate::pdr) fn extract_state_from_args(
        &self,
        pred: PredicateId,
        args: &[ChcExpr],
        smt_model: &FxHashMap<String, SmtValue>,
    ) -> Option<ChcExpr> {
        let canonical_vars = self.canonical_vars(pred)?;
        if canonical_vars.len() != args.len() {
            return None;
        }

        let mut conjuncts = Vec::new();
        for (canon_var, arg) in canonical_vars.iter().zip(args.iter()) {
            // Get the value of this argument from the SMT model
            let value = match arg {
                ChcExpr::Var(v) => smt_model.get(&v.name).cloned(),
                ChcExpr::Int(n) => Some(SmtValue::Int(*n)),
                ChcExpr::Bool(b) => Some(SmtValue::Bool(*b)),
                // Evaluate complex expressions using the SMT model
                _ => crate::expr::evaluate_expr(arg, smt_model),
            };
            // Best-effort fallback: some verification queries use canonical variable names
            // in the SMT model rather than clause-local argument variable names.
            let value = value.or_else(|| smt_model.get(&canon_var.name).cloned());
            let value = match value {
                Some(v) => v,
                None => continue, // Skip if evaluation fails
            };

            // A transformed BV-to-Int model may carry this predicate argument
            // as Int/BigInt. Reconstruct it modulo the declared BV width before
            // the generic scalar match below; never emit an Int-sorted literal
            // on the right-hand side of a BV equality.
            if let ChcSort::BitVec(expected_width) = &canon_var.sort {
                let literal = match &value {
                    SmtValue::Int(n) => SmtValue::bitvec_from_bigint((*n).into(), *expected_width)
                        .bitvec_to_chc_expr(),
                    SmtValue::BigInt(n) => {
                        SmtValue::bitvec_from_bigint(n.as_ref().clone(), *expected_width)
                            .bitvec_to_chc_expr()
                    }
                    value @ (SmtValue::BitVec(_, actual_width)
                    | SmtValue::BigBitVec(_, actual_width))
                        if actual_width == expected_width =>
                    {
                        value.bitvec_to_chc_expr()
                    }
                    _ => None,
                };
                if let Some(literal) = literal {
                    conjuncts.push(ChcExpr::eq(ChcExpr::var(canon_var.clone()), literal));
                }
                continue;
            }
            match value {
                SmtValue::Int(n) => {
                    conjuncts.push(ChcExpr::eq(
                        ChcExpr::var(canon_var.clone()),
                        ChcExpr::int(n),
                    ));
                }
                // Beyond-i128 witness: exact Horner encoding keeps the
                // re-verification constraint precise (never weakened).
                SmtValue::BigInt(ref b) => {
                    conjuncts.push(ChcExpr::eq(
                        ChcExpr::var(canon_var.clone()),
                        ChcExpr::from_bigint(b.as_ref().clone()),
                    ));
                }
                SmtValue::Bool(b) => {
                    conjuncts.push(ChcExpr::eq(
                        ChcExpr::var(canon_var.clone()),
                        ChcExpr::Bool(b),
                    ));
                }
                SmtValue::Real(r) => {
                    use num_traits::ToPrimitive;
                    let n = r.numer().to_i64()?;
                    let d = r.denom().to_i64()?;
                    conjuncts.push(ChcExpr::eq(
                        ChcExpr::var(canon_var.clone()),
                        ChcExpr::Real(n, d),
                    ));
                }
                SmtValue::BitVec(..) | SmtValue::BigBitVec(..) => {}
                // #6047: For array values, generate select-based constraints from the model.
                SmtValue::ConstArray(_) | SmtValue::ArrayMap { .. } => {
                    if let Some(select_conjuncts) =
                        Self::array_select_constraints_from_model(canon_var, Some(&value))
                    {
                        conjuncts.extend(select_conjuncts);
                    }
                }
                // Opaque/DT values have no representation — skip.
                SmtValue::Opaque(_) | SmtValue::Datatype(..) => {}
            }
        }

        if conjuncts.is_empty() {
            None
        } else {
            Some(ChcExpr::and_all(conjuncts))
        }
    }

    /// Apply a formula over canonical vars to a concrete predicate application `pred(args)`.
    pub(in crate::pdr) fn apply_to_args(
        &self,
        pred: PredicateId,
        formula: &ChcExpr,
        args: &[ChcExpr],
    ) -> Option<ChcExpr> {
        let vars = self.canonical_vars(pred)?;
        if vars.len() != args.len() {
            return None;
        }
        let subst: Vec<(ChcVar, ChcExpr)> =
            vars.iter().cloned().zip(args.iter().cloned()).collect();
        Some(formula.substitute(&subst))
    }

    /// Apply a model's predicate interpretation to a concrete predicate application `pred(args)`.
    ///
    /// Unlike `apply_to_args`, this uses the binder vars stored in the model
    /// (`PredicateInterpretation.vars`). This makes `verify_model` work for:
    /// - PDR-produced models,
    /// - synthesis-produced models, and
    /// - parsed SMT-LIB models (`InvariantModel::parse_smtlib`),
    ///   without requiring a hidden solver-specific naming convention.
    pub(in crate::pdr) fn apply_interp_to_args(
        &self,
        interp: &PredicateInterpretation,
        args: &[ChcExpr],
    ) -> Option<ChcExpr> {
        if interp.vars.len() != args.len() {
            return None;
        }
        let subst: Vec<(ChcVar, ChcExpr)> = interp
            .vars
            .iter()
            .cloned()
            .zip(args.iter().cloned())
            .collect();
        Some(interp.formula.substitute(&subst))
    }

    /// Rewrite a constraint expressed over the clause variables into canonical vars for `pred(args)`.
    ///
    /// For variable args: substitutes `x -> __p_arg0`, etc.
    /// For expression head args (#2660): adds equality `__p_argK = expr(substituted)` and maps
    /// constituent vars to themselves so they survive substitution.
    pub(in crate::pdr) fn constraint_to_canonical_state(
        &self,
        pred: PredicateId,
        args: &[ChcExpr],
        constraint: &ChcExpr,
    ) -> Option<ChcExpr> {
        let vars = self.canonical_vars(pred)?;
        if vars.len() != args.len() {
            return None;
        }
        // Two-pass processing to avoid first-match shadowing.
        //
        // Bug scenario with single-pass: P(x+1, x) — expression arg0's constituent
        // var `x` gets identity mapping `(x, x)` first, then variable arg1 adds
        // `(x, __p_arg1)`. Since substitute() is first-match, `x` always resolves
        // to `x` (identity) instead of `__p_arg1`.
        //
        // Fix: Pass 1 collects variable arg mappings (canonical). Pass 2 adds
        // identity mappings for expression-arg constituent vars only when not
        // already mapped by a variable arg.
        let mut subst = Vec::with_capacity(args.len());
        let mut expr_equalities: Vec<ChcExpr> = Vec::new();
        // Pass 1: Map all variable args to their canonical vars.
        for (arg, canon) in args.iter().zip(vars.iter()) {
            if let ChcExpr::Var(v) = arg {
                subst.push((v.clone(), ChcExpr::var(canon.clone())));
            }
        }
        // Pass 2: Process expression head args — add identity mappings for
        // constituent vars not already mapped, and record equality constraints.
        for (arg, canon) in args.iter().zip(vars.iter()) {
            if !matches!(arg, ChcExpr::Var(_)) {
                // #2660: Expression head arg — map constituent vars to themselves (identity)
                // only if not already mapped by a variable arg in pass 1.
                for v in arg.vars() {
                    if !subst.iter().any(|(sv, _)| sv.name == v.name) {
                        subst.push((v.clone(), ChcExpr::var(v.clone())));
                    }
                }
                expr_equalities.push(ChcExpr::eq(ChcExpr::var(canon.clone()), arg.clone()));
            }
        }
        // Flatten constraint + expression equalities into a single and_all
        // to avoid deep right-skewed binary And trees (#2508).
        let base = constraint.substitute(&subst);
        let substituted_eqs: Vec<_> = expr_equalities
            .into_iter()
            .map(|eq| eq.substitute(&subst))
            .collect();
        let result = if substituted_eqs.is_empty() {
            base
        } else {
            let mut all = vec![base];
            all.extend(substituted_eqs);
            ChcExpr::and_all(all)
        };
        Some(result)
    }

    /// Try to prove a query body UNSAT by splitting disjunctions.
    ///
    /// When the body is And(Or(d1,d2,...), rest...), split into cases
    /// And(d1, rest...), And(d2, rest...) and check each separately.
    /// Returns Some(true) if all disjuncts UNSAT, Some(false) if any SAT, None if Unknown.
    pub(in crate::pdr) fn try_disjunction_split_verification(
        smt: &mut SmtContext,
        body: &ChcExpr,
        timeout: std::time::Duration,
    ) -> Option<bool> {
        let conjuncts = match body {
            ChcExpr::Op(ChcOp::And, args) => args,
            _ => return None,
        };
        let mut or_idx = None;
        for (i, c) in conjuncts.iter().enumerate() {
            if matches!(c.as_ref(), ChcExpr::Op(ChcOp::Or, _)) {
                or_idx = Some(i);
                break;
            }
        }
        let or_idx = or_idx?;
        let disjuncts = match conjuncts[or_idx].as_ref() {
            ChcExpr::Op(ChcOp::Or, ds) => ds,
            _ => return None,
        };
        let rest: Vec<Arc<ChcExpr>> = conjuncts
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != or_idx)
            .map(|(_, c)| c.clone())
            .collect();
        for disjunct in disjuncts {
            let mut case_parts: Vec<Arc<ChcExpr>> = Vec::with_capacity(rest.len() + 1);
            case_parts.push(disjunct.clone());
            case_parts.extend(rest.iter().cloned());
            let case_formula = ChcExpr::Op(ChcOp::And, case_parts);
            smt.reset();
            let result = smt.check_sat_with_timeout(&case_formula, timeout);
            match result {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
                SmtResult::Sat(_) => return Some(false),
                SmtResult::Unknown => {
                    if Self::contains_mod_or_div(&case_formula) {
                        if let Some(subst_body) =
                            mod_div::substitute_mod_equalities_in_body(&case_formula)
                        {
                            if matches!(subst_body, ChcExpr::Bool(false)) {
                                continue;
                            }
                            smt.reset();
                            match smt.check_sat_with_timeout(&subst_body, timeout) {
                                SmtResult::Unsat
                                | SmtResult::UnsatWithCore(_)
                                | SmtResult::UnsatWithFarkas(_) => continue,
                                _ => {}
                            }
                        }
                    }
                    return None;
                }
            }
        }
        Some(true)
    }
}
