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
        ChcExpr::ArrayLambda(_) => None,
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
        let (pred_id, vars, parts) = Self::extract_parts(problem)?;
        let init = parts
            .init_constraint()
            .ok_or_else(|| "No fact clause found".to_string())?;
        let transition = parts
            .transition_constraint()
            .ok_or_else(|| "No transition clause found".to_string())?;
        let query = parts
            .query_constraint()
            .ok_or_else(|| "No query clause found".to_string())?;
        Ok(Self::new(pred_id, vars, init, transition, query))
    }

    /// The per-clause disjuncts `from_chc_problem` folds into `init`,
    /// `transition` and `query`, each paired with the index of the clause it
    /// came from. Byte-identical canonicalization: `from_chc_problem` is built
    /// on this same extraction, so a disjunct here IS the corresponding term
    /// of the system's constraint (before `TransitionSystem::new`'s mod/div
    /// elimination, which touches neither variable names nor clause order).
    ///
    /// Consumers use it to attribute a model of the unrolled system back to
    /// the original clauses (`bmc::ts_witness`).
    pub(crate) fn clause_disjuncts(problem: &ChcProblem) -> Result<TsClauseDisjuncts, String> {
        Self::extract_parts(problem).map(|(_, _, parts)| parts)
    }

    /// Shared front half of `from_chc_problem`: the single used predicate, its
    /// canonical variables, and the per-clause canonical disjuncts.
    fn extract_parts(
        problem: &ChcProblem,
    ) -> Result<(PredicateId, Vec<ChcVar>, TsClauseDisjuncts), String> {
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

        let parts = TsClauseDisjuncts {
            facts: Self::extract_init_disjuncts(problem, pred_id, &vars),
            transitions: Self::extract_transition_disjuncts(problem, pred_id, &vars),
            queries: Self::extract_query_disjuncts(problem, pred_id, &vars),
        };
        Ok((pred_id, vars, parts))
    }

    /// Canonicalize one clause constraint onto predicate argument positions.
    ///
    /// `current` pairs the arguments of the predicate application read at
    /// the current state (a body atom, or a fact's head) with the canonical
    /// variables `v{i}`; `next`, for a transition clause, pairs the head
    /// arguments with `v{i}_next`. The result is the constraint conjoined
    /// with one equality per argument position the substitution cannot
    /// express:
    /// - a variable argument's first occurrence is renamed to its position's
    ///   canonical variable;
    /// - a repeated variable argument (`P(x, x)`, or a body variable that is
    ///   also a head argument) yields `canonical_i = canonical_j` of its first
    ///   occurrence;
    /// - an expression argument yields `canonical_i = arg`.
    ///
    /// Every other clause variable is a clause-local existential, renamed to
    /// `{local_prefix}{name}` (#6789: different clauses reuse local names).
    ///
    /// The renaming is ONE simultaneous substitution decided on the clause's
    /// own variables, so a clause variable whose name is a canonical name
    /// (`v1`, `v0_next`) is neither captured by a later argument's renaming
    /// nor mistaken for a state variable.
    pub(crate) fn canonicalize_clause_constraint(
        constraint: &ChcExpr,
        current: (&[ChcExpr], &[ChcVar]),
        next: Option<(&[ChcExpr], &[ChcVar])>,
        local_prefix: &str,
    ) -> ChcExpr {
        let positions: Vec<(&ChcExpr, &ChcVar)> = {
            let (args, vars) = current;
            let mut positions: Vec<_> = args.iter().zip(vars).collect();
            if let Some((args, vars)) = next {
                positions.extend(args.iter().zip(vars));
            }
            positions
        };

        // Argument variables, first occurrence wins.
        let mut renaming: FxHashMap<ChcVar, ChcExpr> = FxHashMap::default();
        for (arg, canonical) in &positions {
            if let ChcExpr::Var(v) = arg {
                renaming
                    .entry(v.clone())
                    .or_insert_with(|| ChcExpr::var((*canonical).clone()));
            }
        }
        // Clause locals: every other variable of the constraint or of an
        // expression argument.
        let mut clause_vars = constraint.vars();
        for (arg, _) in &positions {
            clause_vars.extend(arg.vars());
        }
        for v in clause_vars {
            if !renaming.contains_key(&v) {
                let local = ChcVar::new(format!("{local_prefix}{}", v.name), v.sort.clone());
                renaming.insert(v, ChcExpr::var(local));
            }
        }
        let rename =
            |expr: &ChcExpr| expr.substitute_with_lookup(&|v: &ChcVar| renaming.get(v).cloned());

        let mut conjuncts = vec![rename(constraint)];
        for (arg, canonical) in positions {
            let canonical_expr = ChcExpr::var(canonical.clone());
            let value = rename(arg);
            if value != canonical_expr {
                conjuncts.push(ChcExpr::eq(canonical_expr, value));
            }
        }
        if conjuncts.len() == 1 {
            conjuncts.pop().expect("one conjunct")
        } else {
            // #2508: one flat conjunction, not a right-skewed binary And tree.
            ChcExpr::and_all(conjuncts)
        }
    }

    /// Extract the per-fact-clause init disjuncts (canonical vars, prefixed
    /// locals). `idx` enumerates `problem.facts()` exactly as before, so the
    /// `__init{idx}_` local prefix is unchanged.
    fn extract_init_disjuncts(
        problem: &ChcProblem,
        pred_id: PredicateId,
        vars: &[ChcVar],
    ) -> Vec<TsClauseDisjunct> {
        let mut init_disjuncts = Vec::new();

        for (idx, (clause_idx, fact)) in problem
            .clauses()
            .iter()
            .enumerate()
            .filter(|(_, clause)| clause.is_fact() && !clause.is_query())
            .enumerate()
        {
            if fact.head.predicate_id() != Some(pred_id) {
                continue;
            }

            // Get head arguments
            let head_args = match &fact.head {
                ClauseHead::Predicate(_, args) => args,
                _ => continue,
            };

            let constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
            // Locals get a per-clause prefix (#6789).
            let prefix = format!("__init{idx}_");
            init_disjuncts.push(TsClauseDisjunct {
                clause_idx,
                constraint: Self::canonicalize_clause_constraint(
                    &constraint,
                    (head_args, vars),
                    None,
                    &prefix,
                ),
                local_prefix: prefix,
            });
        }

        init_disjuncts
    }

    /// Extract the per-transition-clause disjuncts. `idx` enumerates
    /// `problem.transitions()` exactly as before (`__tr{idx}_` local prefix).
    fn extract_transition_disjuncts(
        problem: &ChcProblem,
        pred_id: PredicateId,
        vars: &[ChcVar],
    ) -> Vec<TsClauseDisjunct> {
        let mut trans_disjuncts = Vec::new();

        for (idx, (clause_idx, trans)) in problem
            .clauses()
            .iter()
            .enumerate()
            .filter(|(_, clause)| !clause.is_fact() && !clause.is_query())
            .enumerate()
        {
            if let Some(canonical) =
                Self::canonical_transition_clause_constraint(trans, pred_id, vars, idx)
            {
                trans_disjuncts.push(TsClauseDisjunct {
                    clause_idx,
                    constraint: canonical,
                    local_prefix: format!("__tr{idx}_"),
                });
            }
        }

        trans_disjuncts
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

        let constraint = trans.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
        Some(Self::canonicalize_clause_constraint(
            &constraint,
            (body_args, vars),
            Some((head_args, &next_vars)),
            &format!("__tr{transition_ordinal}_"),
        ))
    }

    /// Extract the per-query-clause disjuncts. `idx` enumerates
    /// `problem.queries()` exactly as before (`__qry{idx}_` local prefix).
    fn extract_query_disjuncts(
        problem: &ChcProblem,
        pred_id: PredicateId,
        vars: &[ChcVar],
    ) -> Vec<TsClauseDisjunct> {
        let mut query_disjuncts = Vec::new();

        for (idx, (clause_idx, query)) in problem
            .clauses()
            .iter()
            .enumerate()
            .filter(|(_, clause)| clause.is_query())
            .enumerate()
        {
            // Body should have the predicate
            let Some((body_pred, body_args)) = query.body.predicates.first() else {
                return query_disjuncts;
            };
            if *body_pred != pred_id {
                continue;
            }

            let constraint = query.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
            // Locals get a per-clause prefix (#6789).
            let prefix = format!("__qry{idx}_");
            query_disjuncts.push(TsClauseDisjunct {
                clause_idx,
                constraint: Self::canonicalize_clause_constraint(
                    &constraint,
                    (body_args, vars),
                    None,
                    &prefix,
                ),
                local_prefix: prefix,
            });
        }

        query_disjuncts
    }
}

/// One original clause as it enters the transition system: its canonical
/// constraint (over `v{i}` / `v{i}_next` and `local_prefix`-renamed locals,
/// before per-step versioning) and its index in `ChcProblem::clauses()`.
#[derive(Debug, Clone)]
pub(crate) struct TsClauseDisjunct {
    pub(crate) clause_idx: usize,
    pub(crate) constraint: ChcExpr,
    /// Prefix `canonicalize_clause_constraint` put on this clause's local
    /// variables.
    pub(crate) local_prefix: String,
}

/// The per-clause disjuncts behind a transition system's `init` (facts),
/// `transition` (self-transitions) and `query` (queries), in the order they
/// were folded.
#[derive(Debug, Clone)]
pub(crate) struct TsClauseDisjuncts {
    pub(crate) facts: Vec<TsClauseDisjunct>,
    pub(crate) transitions: Vec<TsClauseDisjunct>,
    pub(crate) queries: Vec<TsClauseDisjunct>,
}

impl TsClauseDisjuncts {
    fn fold(disjuncts: &[TsClauseDisjunct]) -> Option<ChcExpr> {
        if disjuncts.is_empty() {
            None
        } else {
            Some(ChcExpr::or_all(
                disjuncts.iter().map(|d| d.constraint.clone()),
            ))
        }
    }

    fn init_constraint(&self) -> Option<ChcExpr> {
        Self::fold(&self.facts)
    }

    fn transition_constraint(&self) -> Option<ChcExpr> {
        Self::fold(&self.transitions)
    }

    fn query_constraint(&self) -> Option<ChcExpr> {
        Self::fold(&self.queries)
    }
}
