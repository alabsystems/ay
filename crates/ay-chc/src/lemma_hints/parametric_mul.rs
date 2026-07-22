// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Parametric multiplication hint provider.
//!
//! Struct definitions and helper methods for parsing multiplication guard
//! patterns and propagating hints to predecessor predicates. The
//! `LemmaHintProvider` impl is in `parametric_mul_collect.rs`.

use super::*;

pub(crate) struct ParametricMultiplicationProvider;

#[derive(Debug, Clone)]
pub(super) struct MulGuard {
    pub(super) op: ChcOp,
    /// True if the multiplication term is the LHS of the comparison.
    pub(super) mul_on_lhs: bool,
    /// The non-multiplication variable being compared.
    pub(super) other_var: ChcVar,
    /// The variable inside the multiplication term.
    pub(super) mul_var: ChcVar,
    /// The constant coefficient in the multiplication term.
    pub(super) k: i128,
}

#[derive(Debug, Clone)]
pub(super) struct MulGuardOccurrence {
    pub(super) guard: MulGuard,
    /// Whether the hint formula should be negated (i.e. we saw an unnegated
    /// comparison in the query guard).
    pub(super) negate_for_hint: bool,
}

impl ParametricMultiplicationProvider {
    pub(super) const SOURCE: &'static str = "parametric-mul-v1";
    pub(super) const PRIORITY: u16 = 150;
    pub(super) const MAX_HINTS_PER_PRED: usize = 64;

    pub(super) fn collect_mul_guard_occurrences(
        expr: &ChcExpr,
        negated_context: bool,
        out: &mut Vec<MulGuardOccurrence>,
    ) {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            // bad guard: (not (cmp ...)) -> hint: (cmp ...)
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                if !negated_context {
                    if let Some(guard) = Self::parse_mul_guard(args[0].as_ref()) {
                        out.push(MulGuardOccurrence {
                            guard,
                            negate_for_hint: false,
                        });
                    }
                }
                Self::collect_mul_guard_occurrences(args[0].as_ref(), !negated_context, out);
            }

            // bad guard: (cmp ...) -> hint: (not (cmp ...))
            _ => {
                if !negated_context {
                    if let Some(guard) = Self::parse_mul_guard(expr) {
                        out.push(MulGuardOccurrence {
                            guard,
                            negate_for_hint: true,
                        });
                    }
                }

                match expr {
                    ChcExpr::Op(_, args) => {
                        for arg in args {
                            Self::collect_mul_guard_occurrences(arg.as_ref(), negated_context, out);
                        }
                    }
                    ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
                        for arg in args {
                            Self::collect_mul_guard_occurrences(arg.as_ref(), negated_context, out);
                        }
                    }
                    _ => {}
                }
            }
        });
    }

    pub(super) fn parse_mul_guard(expr: &ChcExpr) -> Option<MulGuard> {
        let ChcExpr::Op(op, args) = expr else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }
        if !matches!(
            op,
            ChcOp::Eq | ChcOp::Ne | ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge
        ) {
            return None;
        }

        // (eq/neq B C) treated as (eq/neq B (* 1 C))
        if matches!(op, ChcOp::Eq | ChcOp::Ne) {
            if let (ChcExpr::Var(lhs_var), ChcExpr::Var(rhs_var)) =
                (args[0].as_ref(), args[1].as_ref())
            {
                if lhs_var != rhs_var {
                    return Some(MulGuard {
                        op: *op,
                        mul_on_lhs: false,
                        other_var: lhs_var.clone(),
                        mul_var: rhs_var.clone(),
                        k: 1,
                    });
                }
            }
        }

        // (cmp (* k C) B)
        if let Some((k, mul_var)) = Self::const_mul_var(args[0].as_ref()) {
            if let ChcExpr::Var(other_var) = args[1].as_ref() {
                if other_var == &mul_var {
                    return None;
                }
                return Some(MulGuard {
                    op: *op,
                    mul_on_lhs: true,
                    other_var: other_var.clone(),
                    mul_var,
                    k,
                });
            }
        }

        // (cmp B (* k C))
        if let Some((k, mul_var)) = Self::const_mul_var(args[1].as_ref()) {
            if let ChcExpr::Var(other_var) = args[0].as_ref() {
                if other_var == &mul_var {
                    return None;
                }
                return Some(MulGuard {
                    op: *op,
                    mul_on_lhs: false,
                    other_var: other_var.clone(),
                    mul_var,
                    k,
                });
            }
        }

        None
    }

    pub(super) fn const_mul_var(expr: &ChcExpr) -> Option<(i128, ChcVar)> {
        let ChcExpr::Op(ChcOp::Mul, args) = expr else {
            return None;
        };
        if args.is_empty() {
            return None;
        }

        let mut coeff: i128 = 1;
        let mut var: Option<ChcVar> = None;

        for arg in args {
            match arg.as_ref() {
                ChcExpr::Int(k) => {
                    coeff = coeff.checked_mul(*k)?;
                }
                ChcExpr::Var(v) => {
                    if var.is_some() {
                        return None;
                    }
                    var = Some(v.clone());
                }
                _ => return None,
            }
        }

        let var = var?;
        if coeff <= 0 {
            return None;
        }
        Some((coeff, var))
    }

    pub(super) fn mul_term(k: i128, var: ChcVar) -> ChcExpr {
        if k == 0 {
            return ChcExpr::int(0);
        }
        if k == 1 {
            return ChcExpr::var(var);
        }
        ChcExpr::mul(ChcExpr::int(k), ChcExpr::var(var))
    }

    /// Extract guards of the form `A >= C` (variable >= variable) from an expression.
    /// Returns pairs of (greater_var, lesser_var) for each found guard.
    pub(super) fn collect_ge_var_var_guards(
        expr: &ChcExpr,
        negated_context: bool,
        out: &mut Vec<(ChcVar, ChcVar)>,
    ) {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                Self::collect_ge_var_var_guards(args[0].as_ref(), !negated_context, out);
            }
            ChcExpr::Op(op, args) if args.len() == 2 => {
                if let (ChcExpr::Var(v0), ChcExpr::Var(v1)) = (args[0].as_ref(), args[1].as_ref()) {
                    match (negated_context, op) {
                        // (>= A C) => A >= C
                        (false, ChcOp::Ge) => out.push((v0.clone(), v1.clone())),
                        // (<= C A) => A >= C
                        (false, ChcOp::Le) => out.push((v1.clone(), v0.clone())),
                        // (not (< A C)) => A >= C
                        (true, ChcOp::Lt) => out.push((v0.clone(), v1.clone())),
                        // (not (> C A)) => A >= C
                        (true, ChcOp::Gt) => out.push((v1.clone(), v0.clone())),
                        _ => {}
                    }
                }
                // Recurse even for binary ops so we don't miss guards under `(and ...)`.
                for arg in args {
                    Self::collect_ge_var_var_guards(arg.as_ref(), negated_context, out);
                }
            }
            ChcExpr::Op(_, args) => {
                for arg in args {
                    Self::collect_ge_var_var_guards(arg.as_ref(), negated_context, out);
                }
            }
            ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
                for arg in args {
                    Self::collect_ge_var_var_guards(arg.as_ref(), negated_context, out);
                }
            }
            _ => {}
        });
    }

    /// Propagate parametric multiplication hints to predecessor predicates.
    ///
    /// For multi-phase loops like s_multipl_09 (FUN -> SAD -> WEE) where the query
    /// predicate WEE requires `B >= A + 2*C`, this method emits hints for the
    /// intermediate predicate SAD with the pattern `B >= A + C`.
    ///
    /// Algorithm:
    /// 1. Find query predicates with parametric multiplication patterns
    /// 2. Build predecessor graph from transition clauses
    /// 3. BFS backward through the phase chain, emitting hints with decremented k
    pub(super) fn propagate_hints_to_predecessors(req: &HintRequest<'_>, out: &mut Vec<LemmaHint>) {
        use crate::clause::ClauseHead;
        use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

        // Find query predicates with parametric multiplication patterns
        // Tuple: (pred_id, k, b_pos, a_pos, c_pos)
        let mut query_patterns: Vec<(PredicateId, i128, usize, usize, usize)> = Vec::new();

        for query in req.problem.queries() {
            let Some(constraint) = &query.body.constraint else {
                continue;
            };

            let mut occurrences = Vec::new();
            Self::collect_mul_guard_occurrences(constraint, false, &mut occurrences);
            if occurrences.is_empty() {
                continue;
            }

            // Collect A >= C guards to find the "A" variable position
            let mut ge_guards = Vec::new();
            Self::collect_ge_var_var_guards(constraint, false, &mut ge_guards);

            if query.body.predicates.len() != 1 {
                continue;
            }

            let (pred_id, body_args) = &query.body.predicates[0];

            // Find positions of B, A, C in the predicate arguments.
            // Accept both inequality (B >= k*C) and equality (B = k*C) patterns.
            for occ in &occurrences {
                let guard = &occ.guard;

                // Match inequality patterns: B >= k*C (from negated query guards)
                let matches_ineq = matches!(
                    (occ.negate_for_hint, &guard.op, guard.mul_on_lhs),
                    (false, ChcOp::Ge, false)
                        | (false, ChcOp::Le, true)
                        | (true, ChcOp::Lt, false)
                        | (true, ChcOp::Gt, true)
                );

                // Match equality patterns: B = k*C (from `not (= B (* k C))`)
                let matches_eq = !occ.negate_for_hint && matches!(&guard.op, ChcOp::Eq);

                if !matches_ineq && !matches_eq {
                    continue;
                }

                // Find positions of other_var (B) and mul_var (C)
                // #2492: Also search inside expression body args
                let mut b_pos = None;
                let mut c_pos = None;
                for (i, arg) in body_args.iter().enumerate() {
                    let arg_vars: Vec<_> = match arg {
                        ChcExpr::Var(v) => vec![v.clone()],
                        expr => expr.vars(),
                    };
                    for v in &arg_vars {
                        if v == &guard.other_var && b_pos.is_none() {
                            b_pos = Some(i);
                        }
                        if v == &guard.mul_var && c_pos.is_none() {
                            c_pos = Some(i);
                        }
                    }
                }

                let (Some(b_pos), Some(c_pos)) = (b_pos, c_pos) else {
                    continue;
                };

                // Find position of A (the phase-exit guard variable).
                // Check both var >= var guards and var >= k*var guards from
                // the multiplication occurrences (e.g., `(>= A (* 5 C))`).
                let mut found_a = false;
                for (ge_greater, ge_lesser) in &ge_guards {
                    if ge_lesser != &guard.mul_var || ge_greater == &guard.other_var {
                        continue;
                    }

                    // #2492: Also search inside expression body args
                    for (i, arg) in body_args.iter().enumerate() {
                        let contains = match arg {
                            ChcExpr::Var(v) => v == ge_greater,
                            expr => expr.vars().iter().any(|v| v == ge_greater),
                        };
                        if contains {
                            query_patterns.push((*pred_id, guard.k, b_pos, i, c_pos));
                            found_a = true;
                            break;
                        }
                    }
                }

                // Also check multiplication occurrences for A >= k*C patterns
                // (e.g., gj2007_m_1: `(>= A (* 5 C))` is a mul guard, not var-var)
                if !found_a {
                    for other_occ in &occurrences {
                        let og = &other_occ.guard;
                        // Looking for non-negated (>= A (* k C)) where A != B
                        let is_ge_mul = matches!(
                            (other_occ.negate_for_hint, &og.op, og.mul_on_lhs),
                            (true | false, ChcOp::Ge, false) | (true | false, ChcOp::Le, true)
                        );
                        if !is_ge_mul || og.mul_var != guard.mul_var {
                            continue;
                        }
                        if og.other_var == guard.other_var {
                            continue; // A must be different from B
                        }

                        // #2492: Also search inside expression body args
                        for (i, arg) in body_args.iter().enumerate() {
                            let contains = match arg {
                                ChcExpr::Var(v) => v == &og.other_var,
                                expr => expr.vars().iter().any(|v| v == &og.other_var),
                            };
                            if contains {
                                query_patterns.push((*pred_id, guard.k, b_pos, i, c_pos));
                                found_a = true;
                                break;
                            }
                        }
                        if found_a {
                            break;
                        }
                    }
                }

                // If no A position found, use b_pos as a_pos fallback
                // (the predecessor propagation will still emit B >= (k-1)*C)
                if !found_a {
                    query_patterns.push((*pred_id, guard.k, b_pos, b_pos, c_pos));
                }
            }
        }

        if query_patterns.is_empty() {
            return;
        }

        // Build predecessor map: pred -> [(body_pred, clause_idx)]
        let mut predecessors: FxHashMap<PredicateId, Vec<(PredicateId, usize)>> =
            FxHashMap::default();

        for (clause_idx, clause) in req.problem.clauses().iter().enumerate() {
            let ClauseHead::Predicate(head_pred, _) = &clause.head else {
                continue;
            };

            if clause.body.predicates.len() != 1 {
                continue;
            }

            let (body_pred, _) = &clause.body.predicates[0];
            if body_pred != head_pred {
                predecessors
                    .entry(*head_pred)
                    .or_default()
                    .push((*body_pred, clause_idx));
            }
        }

        // BFS to propagate hints backward through the phase chain.
        //
        // For each predecessor transition body_pred -> head_pred, we check if
        // the B and C variable positions are preserved (same args passed through).
        // If so, we emit direct `B >= (k-1)*C` for the predecessor, plus the
        // normalized difference hint `B >= A + (k-2)*C` when applicable.
        //
        // gj2007_m_1 pattern: inter-predicate transitions have vacuous guards
        // (guard variable is not in predicate args), so we must not require
        // a specific `A >= C` guard -- just positional arg matching.
        let mut visited: FxHashSet<(PredicateId, i128)> = FxHashSet::default();
        let mut worklist = query_patterns;

        while let Some((pred_id, k, b_pos, a_pos, c_pos)) = worklist.pop() {
            if !visited.insert((pred_id, k)) {
                continue;
            }

            let Some(preds) = predecessors.get(&pred_id) else {
                continue;
            };

            for (body_pred, clause_idx) in preds {
                let clause = &req.problem.clauses()[*clause_idx];
                let ClauseHead::Predicate(_, head_args) = &clause.head else {
                    continue;
                };

                // Verify the positions exist in both body and head args.
                // We trust positional indices: multi-phase chain predicates share
                // the same arity and semantic positions for B and C variables.
                // The constraint may rename variables (e.g., C = B), but the
                // positional correspondence is maintained by the chain structure.
                let body_args = &clause.body.predicates[0].1;
                if body_args.len() <= b_pos.max(c_pos) || head_args.len() <= b_pos.max(c_pos) {
                    continue;
                }

                // Get canonical vars for body predicate
                let Some(canonical_vars) = req.canonical_vars(*body_pred) else {
                    continue;
                };

                let (Some(canonical_b), Some(canonical_c)) =
                    (canonical_vars.get(b_pos), canonical_vars.get(c_pos))
                else {
                    continue;
                };

                if canonical_b.sort != crate::ChcSort::Int
                    || canonical_c.sort != crate::ChcSort::Int
                {
                    continue;
                }

                // Emit direct hint: B >= (k-1)*C for predecessor
                // i128-lockstep: checked sub; skip these hints on overflow.
                let Some(pred_k) = k.checked_sub(1) else {
                    continue;
                };
                if pred_k >= 1 {
                    let rhs = Self::mul_term(pred_k, canonical_c.clone());
                    let formula = ChcExpr::ge(ChcExpr::var(canonical_b.clone()), rhs);
                    out.push(LemmaHint::new(
                        *body_pred,
                        formula,
                        Self::PRIORITY.saturating_sub(10),
                        "parametric-mul-pred-direct-v1",
                    ));
                }

                // Also emit equality hint: B = (k-1)*C for predecessor
                if pred_k >= 1 {
                    let rhs = Self::mul_term(pred_k, canonical_c.clone());
                    let formula = ChcExpr::eq(ChcExpr::var(canonical_b.clone()), rhs);
                    out.push(LemmaHint::new(
                        *body_pred,
                        formula,
                        Self::PRIORITY.saturating_sub(15),
                        "parametric-mul-pred-eq-v1",
                    ));
                }

                // Also emit difference-form predecessor hint in normalized form:
                // B >= A + (k-2)*C when a distinct A position exists.
                let Some(diff_k) = k.checked_sub(2) else {
                    continue;
                };
                if diff_k >= 0 && a_pos != b_pos {
                    if let Some(canonical_a) = canonical_vars.get(a_pos) {
                        if canonical_a.sort == crate::ChcSort::Int {
                            let rhs = ChcExpr::add(
                                ChcExpr::var(canonical_a.clone()),
                                Self::mul_term(diff_k, canonical_c.clone()),
                            )
                            .simplify_constants();
                            let formula = ChcExpr::ge(ChcExpr::var(canonical_b.clone()), rhs);
                            out.push(LemmaHint::new(
                                *body_pred,
                                formula,
                                Self::PRIORITY.saturating_sub(20),
                                "parametric-mul-pred-v1",
                            ));
                        }
                    }
                }

                // Add to worklist with decremented k.
                // Stop when k <= 1: at k=0, pred_k would be -1 and no hints are
                // emitted (all require pred_k >= 1 or diff_k >= 0). Without this
                // guard, cyclic SCCs cause k to decrement to -infinity (#3121).
                if k - 1 > 0 {
                    worklist.push((*body_pred, k - 1, b_pos, a_pos, c_pos));
                }
            }
        }
    }
}
