// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CHC problem extraction: convert a linear CHC problem into a transition system.

use super::{
    DeterministicBvBoolTransitionMetadata, DeterministicBvBoolTransitionSystem,
    NextStateAssignment, TransitionSystem,
};
use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseHead, HornClause, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

#[allow(dead_code)]
fn is_bool_or_bv_sort(sort: &ChcSort) -> bool {
    matches!(sort, ChcSort::Bool | ChcSort::BitVec(_))
}

#[allow(dead_code)]
fn conjuncts(expr: &ChcExpr) -> Option<Vec<&ChcExpr>> {
    match expr {
        ChcExpr::Bool(true) => Some(Vec::new()),
        ChcExpr::Op(ChcOp::And, args) => Some(args.iter().map(AsRef::as_ref).collect()),
        ChcExpr::Op(ChcOp::Or, _) => None,
        other => Some(vec![other]),
    }
}

#[allow(dead_code)]
fn next_assignment<'a>(
    expr: &'a ChcExpr,
    next_vars: &'a [ChcVar],
) -> Option<(&'a ChcVar, &'a ChcExpr)> {
    let ChcExpr::Op(ChcOp::Eq, args) = expr else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }

    let lhs_next = next_var(args[0].as_ref(), next_vars);
    let rhs_next = next_var(args[1].as_ref(), next_vars);
    match (lhs_next, rhs_next) {
        (Some(next), None) => Some((next, args[1].as_ref())),
        (None, Some(next)) => Some((next, args[0].as_ref())),
        _ => None,
    }
}

#[allow(dead_code)]
fn next_var<'a>(expr: &ChcExpr, next_vars: &'a [ChcVar]) -> Option<&'a ChcVar> {
    let ChcExpr::Var(var) = expr else {
        return None;
    };
    next_vars.iter().find(|next| *next == var)
}

#[allow(dead_code)]
fn bitvec_width(sort: &ChcSort) -> Option<u32> {
    match sort {
        ChcSort::BitVec(width) => Some(*width),
        _ => None,
    }
}

#[allow(dead_code)]
fn supported_bool_bv_sort(expr: &ChcExpr, allowed_vars: &FxHashSet<ChcVar>) -> Option<ChcSort> {
    match expr {
        ChcExpr::Bool(_) => Some(ChcSort::Bool),
        ChcExpr::BitVec(_, width) => Some(ChcSort::BitVec(*width)),
        ChcExpr::Var(var) => {
            if is_bool_or_bv_sort(&var.sort) && allowed_vars.contains(var) {
                Some(var.sort.clone())
            } else {
                None
            }
        }
        ChcExpr::Op(op, args) => match op {
            ChcOp::Not => (args.len() == 1
                && supported_bool_bv_sort(args[0].as_ref(), allowed_vars)? == ChcSort::Bool)
                .then_some(ChcSort::Bool),
            ChcOp::And | ChcOp::Or => {
                for arg in args {
                    if supported_bool_bv_sort(arg.as_ref(), allowed_vars)? != ChcSort::Bool {
                        return None;
                    }
                }
                Some(ChcSort::Bool)
            }
            ChcOp::Implies | ChcOp::Iff => {
                if args.len() != 2 {
                    return None;
                }
                let lhs = supported_bool_bv_sort(args[0].as_ref(), allowed_vars)?;
                let rhs = supported_bool_bv_sort(args[1].as_ref(), allowed_vars)?;
                (lhs == ChcSort::Bool && rhs == ChcSort::Bool).then_some(ChcSort::Bool)
            }
            ChcOp::Eq | ChcOp::Ne => {
                if args.len() != 2 {
                    return None;
                }
                let lhs = supported_bool_bv_sort(args[0].as_ref(), allowed_vars)?;
                let rhs = supported_bool_bv_sort(args[1].as_ref(), allowed_vars)?;
                (lhs == rhs).then_some(ChcSort::Bool)
            }
            ChcOp::Ite => {
                if args.len() != 3 {
                    return None;
                }
                if supported_bool_bv_sort(args[0].as_ref(), allowed_vars)? != ChcSort::Bool {
                    return None;
                }
                let then_sort = supported_bool_bv_sort(args[1].as_ref(), allowed_vars)?;
                let else_sort = supported_bool_bv_sort(args[2].as_ref(), allowed_vars)?;
                (then_sort == else_sort).then_some(then_sort)
            }
            ChcOp::BvAdd
            | ChcOp::BvSub
            | ChcOp::BvMul
            | ChcOp::BvUDiv
            | ChcOp::BvURem
            | ChcOp::BvSDiv
            | ChcOp::BvSRem
            | ChcOp::BvSMod
            | ChcOp::BvAnd
            | ChcOp::BvOr
            | ChcOp::BvXor
            | ChcOp::BvNand
            | ChcOp::BvNor
            | ChcOp::BvXnor
            | ChcOp::BvShl
            | ChcOp::BvLShr
            | ChcOp::BvAShr => {
                if args.len() != 2 {
                    return None;
                }
                let lhs = supported_bool_bv_sort(args[0].as_ref(), allowed_vars)?;
                let rhs = supported_bool_bv_sort(args[1].as_ref(), allowed_vars)?;
                if lhs == rhs && matches!(lhs, ChcSort::BitVec(_)) {
                    Some(lhs)
                } else {
                    None
                }
            }
            ChcOp::BvNot | ChcOp::BvNeg => {
                if args.len() != 1 {
                    return None;
                }
                let sort = supported_bool_bv_sort(args[0].as_ref(), allowed_vars)?;
                matches!(sort, ChcSort::BitVec(_)).then_some(sort)
            }
            ChcOp::BvULt
            | ChcOp::BvULe
            | ChcOp::BvUGt
            | ChcOp::BvUGe
            | ChcOp::BvSLt
            | ChcOp::BvSLe
            | ChcOp::BvSGt
            | ChcOp::BvSGe => {
                if args.len() != 2 {
                    return None;
                }
                let lhs = supported_bool_bv_sort(args[0].as_ref(), allowed_vars)?;
                let rhs = supported_bool_bv_sort(args[1].as_ref(), allowed_vars)?;
                (lhs == rhs && matches!(lhs, ChcSort::BitVec(_))).then_some(ChcSort::Bool)
            }
            ChcOp::BvComp => {
                if args.len() != 2 {
                    return None;
                }
                let lhs = supported_bool_bv_sort(args[0].as_ref(), allowed_vars)?;
                let rhs = supported_bool_bv_sort(args[1].as_ref(), allowed_vars)?;
                (lhs == rhs && matches!(lhs, ChcSort::BitVec(_))).then_some(ChcSort::BitVec(1))
            }
            ChcOp::BvConcat => {
                if args.len() < 2 {
                    return None;
                }
                let mut width = 0_u32;
                for arg in args {
                    let sort = supported_bool_bv_sort(arg.as_ref(), allowed_vars)?;
                    width = width.checked_add(bitvec_width(&sort)?)?;
                }
                Some(ChcSort::BitVec(width))
            }
            ChcOp::BvExtract(high, low) => {
                if args.len() != 1 || high < low {
                    return None;
                }
                let source = supported_bool_bv_sort(args[0].as_ref(), allowed_vars)?;
                let source_width = bitvec_width(&source)?;
                if *high >= source_width {
                    return None;
                }
                Some(ChcSort::BitVec(high - low + 1))
            }
            ChcOp::BvZeroExtend(extra) | ChcOp::BvSignExtend(extra) => {
                if args.len() != 1 {
                    return None;
                }
                let source = supported_bool_bv_sort(args[0].as_ref(), allowed_vars)?;
                Some(ChcSort::BitVec(bitvec_width(&source)?.checked_add(*extra)?))
            }
            ChcOp::BvRotateLeft(_) | ChcOp::BvRotateRight(_) => {
                if args.len() != 1 {
                    return None;
                }
                let source = supported_bool_bv_sort(args[0].as_ref(), allowed_vars)?;
                matches!(source, ChcSort::BitVec(_)).then_some(source)
            }
            ChcOp::BvRepeat(times) => {
                if args.len() != 1 || *times == 0 {
                    return None;
                }
                let source = supported_bool_bv_sort(args[0].as_ref(), allowed_vars)?;
                Some(ChcSort::BitVec(bitvec_width(&source)?.checked_mul(*times)?))
            }
            ChcOp::Add
            | ChcOp::Sub
            | ChcOp::Mul
            | ChcOp::Div
            | ChcOp::Mod
            | ChcOp::Neg
            | ChcOp::Lt
            | ChcOp::Le
            | ChcOp::Gt
            | ChcOp::Ge
            | ChcOp::Select
            | ChcOp::Store
            | ChcOp::Bv2Nat
            | ChcOp::Int2Bv(_) => None,
        },
        ChcExpr::Int(_)
        | ChcExpr::Real(_, _)
        | ChcExpr::PredicateApp(_, _, _)
        | ChcExpr::FuncApp(_, _, _)
        | ChcExpr::ConstArrayMarker(_)
        | ChcExpr::IsTesterMarker(_)
        | ChcExpr::ConstArray(_, _) => None,
    }
}

#[allow(dead_code)]
fn expr_is_bool_bv(expr: &ChcExpr, allowed_vars: &FxHashSet<ChcVar>) -> bool {
    supported_bool_bv_sort(expr, allowed_vars).is_some()
}

#[allow(dead_code)]
fn deterministic_bv_bool_metadata(
    vars: &[ChcVar],
    transition_conjuncts: usize,
    guard_conjuncts: usize,
) -> DeterministicBvBoolTransitionMetadata {
    let bool_state_vars = vars
        .iter()
        .filter(|var| matches!(&var.sort, ChcSort::Bool))
        .count();
    let bv_widths = vars.iter().filter_map(|var| bitvec_width(&var.sort));
    let mut bv_state_vars = 0;
    let mut total_bv_width = 0_u64;
    let mut max_bv_width = 0_u32;
    for width in bv_widths {
        bv_state_vars += 1;
        total_bv_width += u64::from(width);
        max_bv_width = max_bv_width.max(width);
    }

    DeterministicBvBoolTransitionMetadata {
        bool_state_vars,
        bv_state_vars,
        total_bv_width,
        total_state_bits: total_bv_width + bool_state_vars as u64,
        max_bv_width,
        transition_conjuncts,
        guard_conjuncts,
    }
}

impl TransitionSystem {
    /// Conservatively recognize deterministic Bool/BV transition systems.
    ///
    /// Acceptance is intentionally narrow:
    /// - every state variable is Bool or BitVec;
    /// - init/transition/query stay within Bool/BV syntax;
    /// - the transition is one conjunctive relation, not a disjunction of
    ///   alternative transitions;
    /// - every canonical `v_next` has exactly one equality assignment;
    /// - assignment RHS terms depend only on current-state variables.
    ///
    /// This is routing scaffolding only. It never returns a SAT/UNSAT answer.
    #[allow(dead_code)]
    pub(crate) fn recognize_deterministic_bv_bool(
        &self,
    ) -> Option<DeterministicBvBoolTransitionSystem> {
        if self.vars.is_empty() || !self.vars.iter().all(|v| is_bool_or_bv_sort(&v.sort)) {
            return None;
        }

        let next_vars: Vec<ChcVar> = self
            .vars
            .iter()
            .map(|v| ChcVar::new(format!("{}_next", v.name), v.sort.clone()))
            .collect();
        let current_by_name: FxHashSet<&str> = self.vars.iter().map(|v| v.name.as_str()).collect();
        let next_by_name: FxHashSet<&str> = next_vars.iter().map(|v| v.name.as_str()).collect();
        if current_by_name.len() != self.vars.len()
            || next_by_name.len() != next_vars.len()
            || current_by_name
                .iter()
                .any(|name| next_by_name.contains(name))
        {
            return None;
        }
        let current_vars: FxHashSet<ChcVar> = self.vars.iter().cloned().collect();
        let next_var_set: FxHashSet<ChcVar> = next_vars.iter().cloned().collect();
        let current_and_next: FxHashSet<ChcVar> = current_vars
            .iter()
            .cloned()
            .chain(next_var_set.iter().cloned())
            .collect();

        if !expr_is_bool_bv(&self.init, &current_vars)
            || !expr_is_bool_bv(&self.query, &current_vars)
            || !expr_is_bool_bv(&self.transition, &current_and_next)
        {
            return None;
        }

        let transition_conjuncts = conjuncts(&self.transition)?;
        let mut assignments_by_next: FxHashMap<&str, NextStateAssignment> = FxHashMap::default();
        let mut has_transition_guard = false;

        for &conjunct in &transition_conjuncts {
            if let Some((next, value)) = next_assignment(conjunct, &next_vars) {
                if supported_bool_bv_sort(value, &current_vars)? != next.sort {
                    return None;
                }
                let next_index = next_vars.iter().position(|candidate| candidate == next)?;
                let current = self.vars.get(next_index)?;
                let assignment = NextStateAssignment {
                    current: current.clone(),
                    next: next.clone(),
                    value: value.clone(),
                };
                if assignments_by_next
                    .insert(next.name.as_str(), assignment)
                    .is_some()
                {
                    return None;
                }
            } else {
                if conjunct.vars().iter().any(|v| next_var_set.contains(v)) {
                    return None;
                }
                has_transition_guard = true;
            }
        }

        if assignments_by_next.len() != self.vars.len() {
            return None;
        }

        let mut next_assignments = Vec::with_capacity(self.vars.len());
        for next in &next_vars {
            next_assignments.push(assignments_by_next.remove(next.name.as_str())?);
        }
        let guard_conjuncts = transition_conjuncts.len() - next_assignments.len();
        let metadata =
            deterministic_bv_bool_metadata(&self.vars, transition_conjuncts.len(), guard_conjuncts);

        Some(DeterministicBvBoolTransitionSystem {
            predicate: self.predicate,
            vars: self.vars.clone(),
            init: self.init.clone(),
            transition: self.transition.clone(),
            query: self.query.clone(),
            next_assignments,
            has_transition_guard,
            metadata,
        })
    }

    /// Extract a transition system from a CHC problem.
    ///
    /// The problem must be a single-predicate linear CHC problem:
    /// - Exactly one predicate
    /// - At most one predicate in each clause body
    /// - At least one fact clause (init), one transition clause, and one query clause
    ///
    /// Part of #1032 (TPA engine).
    pub(crate) fn from_chc_problem(problem: &ChcProblem) -> Result<Self, String> {
        // Check: exactly one USED predicate. Orphan declarations — e.g. a
        // 0-arity query marker `fail` unfolded away by
        // `eliminate_trivial_bool_markers` (#9078) — remain in `predicates()`
        // but appear in no clause; they must not block single-predicate
        // transition-system extraction. The real predicate may be at any index.
        let mut used: Vec<PredicateId> = Vec::new();
        for clause in problem.clauses() {
            if let Some(h) = clause.head.predicate_id() {
                if !used.contains(&h) {
                    used.push(h);
                }
            }
            for (pid, _) in &clause.body.predicates {
                if !used.contains(pid) {
                    used.push(*pid);
                }
            }
        }
        let [the_pred_id] = used.as_slice() else {
            return Err(format!("Expected 1 used predicate, found {}", used.len()));
        };
        let pred = problem
            .get_predicate(*the_pred_id)
            .ok_or_else(|| "used predicate lookup failed".to_string())?;
        let pred_id = pred.id;

        // Check: all clauses are linear (at most one predicate in body)
        for clause in problem.clauses() {
            if clause.body.predicates.len() > 1 {
                return Err("Non-linear clause: multiple predicates in body".to_string());
            }
        }

        // Create canonical variables
        let vars: Vec<ChcVar> = pred
            .arg_sorts
            .iter()
            .enumerate()
            .map(|(i, sort)| ChcVar::new(format!("v{i}"), sort.clone()))
            .collect();

        // Extract init constraint from fact clauses
        let init = Self::extract_init_constraint(problem, pred_id, &vars)
            .ok_or_else(|| "No fact clause found".to_string())?;

        // Extract transition constraint from transition clauses
        let transition = Self::extract_transition_constraint(problem, pred_id, &vars)
            .ok_or_else(|| "No transition clause found".to_string())?;

        // Extract query constraint from query clauses
        let query = Self::extract_query_constraint(problem, pred_id, &vars)
            .ok_or_else(|| "No query clause found".to_string())?;

        Ok(Self::new(pred_id, vars, init, transition, query))
    }

    /// Substitute clause arguments to canonical variables in a constraint.
    ///
    /// For each argument in `args`:
    /// - If it's a variable, substitute it in `constraint` with the canonical var.
    /// - If it's an expression, add an equality: `canonical_var = substituted_expr`.
    ///
    /// Returns the modified constraint, extra equalities, and the substitution map
    /// (needed by callers that do a second pass, e.g., transition head args).
    ///
    /// Uses the #2508 flatten pattern to avoid deep right-skewed binary And trees.
    pub(super) fn substitute_args_to_canonical_vars(
        constraint: ChcExpr,
        args: &[ChcExpr],
        canonical_vars: &[ChcVar],
    ) -> (ChcExpr, Vec<ChcExpr>, Vec<(ChcVar, ChcExpr)>) {
        let subst_map: Vec<(ChcVar, ChcExpr)> = args
            .iter()
            .enumerate()
            .filter_map(|(i, arg)| {
                if let ChcExpr::Var(v) = arg {
                    Some((v.clone(), ChcExpr::var(canonical_vars[i].clone())))
                } else {
                    None
                }
            })
            .collect();

        let mut result = constraint;
        let mut extra_eqs = Vec::new();
        for (i, arg) in args.iter().enumerate() {
            if let ChcExpr::Var(v) = arg {
                result = result.substitute(&[(v.clone(), ChcExpr::var(canonical_vars[i].clone()))]);
            } else {
                let substituted_arg = arg.substitute(&subst_map);
                extra_eqs.push(ChcExpr::eq(
                    ChcExpr::var(canonical_vars[i].clone()),
                    substituted_arg,
                ));
            }
        }

        (result, extra_eqs, subst_map)
    }

    /// Combine a constraint with extra equalities using and_all (#2508 flatten pattern).
    pub(super) fn finalize_constraint(constraint: ChcExpr, extra_eqs: Vec<ChcExpr>) -> ChcExpr {
        if extra_eqs.is_empty() {
            constraint
        } else {
            let mut all = extra_eqs;
            all.insert(0, constraint);
            ChcExpr::and_all(all)
        }
    }

    /// Rename local (non-canonical) variables in a constraint to avoid collisions.
    ///
    /// After substituting predicate arguments to canonical variables (v0..vN,
    /// v0_next..vN_next), any remaining free variables are clause-local
    /// existentials. Different clauses may reuse the same variable names for
    /// their locals. When init, transition, and query constraints are conjoined
    /// (e.g., `init ∧ Tr ∧ query`), these same-named locals accidentally merge,
    /// adding spurious constraints that make satisfiable formulas appear UNSAT.
    ///
    /// This function renames all non-canonical variables by prefixing them with
    /// a unique clause tag (e.g., `__init0_`, `__tr0_`, `__qry0_`).
    ///
    /// Fixes #6789: Kind engine false-Safe caused by local variable collision.
    pub(super) fn rename_local_vars(
        constraint: ChcExpr,
        canonical_vars: &[ChcVar],
        next_vars: Option<&[ChcVar]>,
        prefix: &str,
    ) -> ChcExpr {
        // Collect all variables in the constraint
        let all_vars = constraint.vars();

        // Build set of canonical var names to exclude from renaming
        let mut canonical_names: FxHashSet<String> =
            canonical_vars.iter().map(|v| v.name.clone()).collect();
        if let Some(nvars) = next_vars {
            for v in nvars {
                canonical_names.insert(v.name.clone());
            }
        }

        // Build substitution for local vars only
        let substitutions: Vec<(ChcVar, ChcExpr)> = all_vars
            .into_iter()
            .filter(|v| !canonical_names.contains(&v.name))
            .map(|v| {
                let renamed = ChcVar::new(format!("{}{}", prefix, v.name), v.sort.clone());
                (v, ChcExpr::var(renamed))
            })
            .collect();

        if substitutions.is_empty() {
            constraint
        } else {
            constraint.substitute(&substitutions)
        }
    }

    /// Extract init constraint: maps fact clauses to constraint on canonical vars.
    fn extract_init_constraint(
        problem: &ChcProblem,
        pred_id: PredicateId,
        vars: &[ChcVar],
    ) -> Option<ChcExpr> {
        let mut init_disjuncts = Vec::new();

        for (idx, fact) in problem.facts().enumerate() {
            if fact.head.predicate_id() != Some(pred_id) {
                continue;
            }

            // Get head arguments
            let head_args = match &fact.head {
                ClauseHead::Predicate(_, args) => args,
                _ => continue,
            };

            let constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
            let (constraint, extra_eqs, _) =
                Self::substitute_args_to_canonical_vars(constraint, head_args, vars);
            let combined = Self::finalize_constraint(constraint, extra_eqs);
            // Rename local variables to avoid collisions with transition/query locals (#6789)
            let prefix = format!("__init{idx}_");
            init_disjuncts.push(Self::rename_local_vars(combined, vars, None, &prefix));
        }

        if init_disjuncts.is_empty() {
            None
        } else {
            Some(ChcExpr::or_all(init_disjuncts))
        }
    }

    /// Extract transition constraint from transition clauses.
    fn extract_transition_constraint(
        problem: &ChcProblem,
        pred_id: PredicateId,
        vars: &[ChcVar],
    ) -> Option<ChcExpr> {
        let mut trans_disjuncts = Vec::new();

        for (idx, trans) in problem.transitions().enumerate() {
            if let Some(canonical) =
                Self::canonical_transition_clause_constraint(trans, pred_id, vars, idx)
            {
                trans_disjuncts.push(canonical);
            }
        }

        if trans_disjuncts.is_empty() {
            None
        } else {
            Some(ChcExpr::or_all(trans_disjuncts))
        }
    }

    /// Canonicalize one self-transition clause into the `vars`/`vars_next` form.
    pub(super) fn canonical_transition_clause_constraint(
        trans: &HornClause,
        pred_id: PredicateId,
        vars: &[ChcVar],
        transition_ordinal: usize,
    ) -> Option<ChcExpr> {
        let next_vars: Vec<ChcVar> = vars
            .iter()
            .map(|v| ChcVar::new(format!("{}_next", v.name), v.sort.clone()))
            .collect();

        // Body should have the predicate.
        let (body_pred, body_args) = trans.body.predicates.first()?;
        if *body_pred != pred_id {
            return None;
        }

        // Head should also be the predicate.
        let head_args = match &trans.head {
            ClauseHead::Predicate(p, args) if *p == pred_id => args,
            _ => return None,
        };

        // Substitute body args with current canonical vars.
        let constraint = trans.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
        let (mut constraint, mut extra_eqs, body_subst) =
            Self::substitute_args_to_canonical_vars(constraint, body_args, vars);

        // Substitute head args with next vars.
        for (i, head_arg) in head_args.iter().enumerate() {
            if let ChcExpr::Var(v) = head_arg {
                // When the same variable appears as a body and head arg, the body
                // substitution consumes it first; preserve the next-state equality.
                if let Some((_, canonical_expr)) = body_subst.iter().find(|(bv, _)| bv == v) {
                    extra_eqs.push(ChcExpr::eq(
                        ChcExpr::var(next_vars[i].clone()),
                        canonical_expr.clone(),
                    ));
                } else {
                    constraint =
                        constraint.substitute(&[(v.clone(), ChcExpr::var(next_vars[i].clone()))]);
                }
            } else {
                // Apply body substitution to head_arg before adding equality.
                let substituted_head_arg = head_arg.substitute(&body_subst);
                extra_eqs.push(ChcExpr::eq(
                    ChcExpr::var(next_vars[i].clone()),
                    substituted_head_arg,
                ));
            }
        }
        let combined = Self::finalize_constraint(constraint, extra_eqs);
        let prefix = format!("__tr{transition_ordinal}_");
        Some(Self::rename_local_vars(
            combined,
            vars,
            Some(&next_vars),
            &prefix,
        ))
    }

    /// Extract query constraint from query clauses.
    fn extract_query_constraint(
        problem: &ChcProblem,
        pred_id: PredicateId,
        vars: &[ChcVar],
    ) -> Option<ChcExpr> {
        let mut query_disjuncts = Vec::new();

        for (idx, query) in problem.queries().enumerate() {
            // Body should have the predicate
            let (body_pred, body_args) = query.body.predicates.first()?;
            if *body_pred != pred_id {
                continue;
            }

            let constraint = query.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
            let (constraint, extra_eqs, _) =
                Self::substitute_args_to_canonical_vars(constraint, body_args, vars);
            let combined = Self::finalize_constraint(constraint, extra_eqs);
            // Rename local variables to avoid collisions with init/transition locals (#6789)
            let prefix = format!("__qry{idx}_");
            query_disjuncts.push(Self::rename_local_vars(combined, vars, None, &prefix));
        }

        if query_disjuncts.is_empty() {
            None
        } else {
            Some(ChcExpr::or_all(query_disjuncts))
        }
    }
}
