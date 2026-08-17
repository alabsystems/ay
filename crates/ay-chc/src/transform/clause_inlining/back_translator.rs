// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Back-translation for clause inlining.
//!
//! Synthesizes interpretations for predicates that were removed by inlining,
//! reconstructing their definitions from the original clause bodies.

use crate::{
    mbp::Mbp,
    pdr::counterexample::{DerivationWitness, DerivationWitnessEntry},
    smt::{SmtContext, SmtResult, SmtValue},
    ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseHead, HornClause, PredicateId,
    PredicateInterpretation,
};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use std::sync::Arc;

use super::{deriv_expansion_enabled, ClauseTrace, CompositionStep};

use super::super::{
    BackTranslator, InvalidityWitness, TransformMemoryReport, TransformObligation, ValidityWitness,
};

/// Cap AllSAT+MBP existential projection during back-translation.
///
/// If the cap is hit before the exact projection is covered, synthesis fails
/// closed and portfolio validation rejects the Safe result.
const MAX_EXISTENTIAL_QE_ITERS: usize = 100;

/// Per-check SMT timeout inside the AllSAT+MBP projection loop.
///
/// The QE SmtContext previously ran UNBOUNDED: the internal DPLL loop's
/// known incompleteness could spin forever on a 53-node LIA conjunction
/// (HOLA 16.c acceptance hang leg 2), never reaching the executor fallback
/// that decides the same query in milliseconds. With a bounded check, the
/// internal loop gets min(2s, t/4) and the executor fallback the rest.
/// Unknown results keep their existing fail-closed handling.
const EXISTENTIAL_QE_CHECK_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(3);

/// Overall wall-clock deadline for one AllSAT+MBP projection loop.
///
/// On expiry with no projections, synthesis fails closed (portfolio keeps
/// the verdict at Unknown). On expiry with partial projections, the
/// candidate is still subject to the exactness check below and—like every
/// synthesized interpretation—to mandatory full validation against the
/// ORIGINAL clauses before any Safe is reported.
const EXISTENTIAL_QE_LOOP_DEADLINE: std::time::Duration = std::time::Duration::from_secs(6);

/// Acceptance-pipeline profiling (--chc-accept-profile): per-leg timing of
/// back-translation synthesis. Diagnostics only — no behavioral effect.
pub(crate) fn accept_profile_enabled() -> bool {
    static FLAG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *FLAG.get_or_init(|| ay_core::misc_cli_flags().chc_accept_profile)
}

/// Back-translator that synthesizes interpretations for predicates removed by inlining.
///
/// When ClauseInliner eliminates a predicate P with defining clause
/// `P(x1,...,xn) ⇐ C(x1,...,xn) ∧ Q1(a1) ∧ ...`, the solver's model
/// will not contain an interpretation for P. This translator reconstructs
/// P's interpretation from its defining clause body so that the model
/// validates against the original (pre-inlining) problem.
pub(super) struct InliningBackTranslator {
    /// Defining clauses for each inlined predicate, in inlining order.
    /// Later entries may have body predicates already substituted from earlier rounds.
    /// PredicateIds are from the **original** (pre-compaction) problem.
    pub(super) inlined_defs: Vec<(PredicateId, HornClause)>,
    /// Mapping from compacted (engine) predicate IDs to original predicate IDs.
    /// Empty if no compaction was performed.
    pub(super) new_to_old: FxHashMap<PredicateId, PredicateId>,
    /// Per-surviving-clause composition traces, keyed by FINAL (compacted)
    /// clause index. Used to EXPAND a collapsed (composite) derivation entry
    /// into the chain of original-clause entries so bounded refutations found
    /// on the inlined problem replay on the input clauses
    /// (#chc25-deriv-expansion). Only a hint — every reconstructed entry is
    /// re-validated by the SMT counterexample kernel.
    pub(super) composition_traces: FxHashMap<usize, ClauseTrace>,
    /// Output clause index -> INPUT clause index, when the trace alignment
    /// survived multi-def expansion. `None` disables ground back-translation.
    pub(super) output_to_input: Option<Vec<usize>>,
    /// The INPUT problem, retained so ground back-translation can rebuild and
    /// self-validate an expanded derivation against it. `None` when the
    /// ground-back-translation feature is off.
    pub(super) input_problem: Option<std::sync::Arc<ChcProblem>>,
}

impl InliningBackTranslator {
    fn vars_are_closed(formula: &ChcExpr, allowed: &FxHashSet<ChcVar>) -> bool {
        formula.vars().into_iter().all(|var| allowed.contains(&var))
    }

    /// Substitute Int variables pinned by matching lower/upper constant bounds.
    ///
    /// This is especially important for inlined loop-exit clauses where a guard
    /// like `B >= 16` combines with the body invariant `B <= 16`, making the
    /// existential witness effectively constant before projection.
    fn propagate_tight_bound_constants(formula: &ChcExpr) -> ChcExpr {
        let conjuncts = formula.collect_conjuncts();
        let mut lower: FxHashMap<String, i128> = FxHashMap::default();
        let mut upper: FxHashMap<String, i128> = FxHashMap::default();

        for conj in &conjuncts {
            if let ChcExpr::Op(ChcOp::Ge, args) = conj {
                if args.len() == 2 {
                    if let (ChcExpr::Var(v), ChcExpr::Int(c)) = (args[0].as_ref(), args[1].as_ref())
                    {
                        if matches!(v.sort, ChcSort::Int) {
                            lower
                                .entry(v.name.clone())
                                .and_modify(|old| *old = (*old).max(*c))
                                .or_insert(*c);
                        }
                    }
                }
            }
            if let ChcExpr::Op(ChcOp::Le, args) = conj {
                if args.len() == 2 {
                    if let (ChcExpr::Var(v), ChcExpr::Int(c)) = (args[0].as_ref(), args[1].as_ref())
                    {
                        if matches!(v.sort, ChcSort::Int) {
                            upper
                                .entry(v.name.clone())
                                .and_modify(|old| *old = (*old).min(*c))
                                .or_insert(*c);
                        }
                    }
                }
            }
        }

        let subst: Vec<(ChcVar, ChcExpr)> = lower
            .iter()
            .filter_map(|(name, lb)| {
                (upper.get(name) == Some(lb))
                    .then(|| (ChcVar::new(name.clone(), ChcSort::Int), ChcExpr::Int(*lb)))
            })
            .collect();

        if subst.is_empty() {
            return formula.clone();
        }

        let mut equalities: Vec<ChcExpr> = subst
            .iter()
            .map(|(var, val)| ChcExpr::eq(ChcExpr::var(var.clone()), val.clone()))
            .collect();
        let simplified = formula.substitute(&subst).simplify_constants();
        if matches!(simplified, ChcExpr::Bool(true)) {
            ChcExpr::and_all(equalities)
        } else {
            equalities.push(simplified);
            ChcExpr::and_all(equalities)
        }
    }

    fn solve_local_from_head_equality(
        equality: &ChcExpr,
        keep_names: &FxHashSet<&str>,
    ) -> Option<(ChcVar, ChcExpr)> {
        fn local_affine_rhs(expr: &ChcExpr) -> Option<(ChcVar, i128, bool)> {
            match expr {
                ChcExpr::Var(v) if matches!(v.sort, ChcSort::Int) => Some((v.clone(), 0, true)),
                ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
                    match (args[0].as_ref(), args[1].as_ref()) {
                        (ChcExpr::Var(v), ChcExpr::Int(c)) if matches!(v.sort, ChcSort::Int) => {
                            Some((v.clone(), *c, true))
                        }
                        (ChcExpr::Int(c), ChcExpr::Var(v)) if matches!(v.sort, ChcSort::Int) => {
                            Some((v.clone(), *c, true))
                        }
                        _ => None,
                    }
                }
                ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
                    match (args[0].as_ref(), args[1].as_ref()) {
                        (ChcExpr::Var(v), ChcExpr::Int(c)) if matches!(v.sort, ChcSort::Int) => {
                            Some((v.clone(), *c, true))
                        }
                        (ChcExpr::Int(c), ChcExpr::Var(v)) if matches!(v.sort, ChcSort::Int) => {
                            Some((v.clone(), *c, false))
                        }
                        _ => None,
                    }
                }
                _ => None,
            }
        }

        let ChcExpr::Op(ChcOp::Eq, args) = equality else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }

        // Try both orientations: either side can be a keep var or expression.
        // First check: one side is a plain keep var.
        let simple_result = match (args[0].as_ref(), args[1].as_ref()) {
            (ChcExpr::Var(v), rhs) if keep_names.contains(v.name.as_str()) => {
                if let Some((local_var, constant, positive_local)) = local_affine_rhs(rhs) {
                    if !keep_names.contains(local_var.name.as_str()) {
                        let rhs_expr = if positive_local {
                            if constant == 0 {
                                ChcExpr::var(v.clone())
                            } else if matches!(rhs, ChcExpr::Op(ChcOp::Sub, _)) {
                                ChcExpr::add(ChcExpr::var(v.clone()), ChcExpr::int(constant))
                            } else {
                                ChcExpr::sub(ChcExpr::var(v.clone()), ChcExpr::int(constant))
                            }
                        } else {
                            ChcExpr::sub(ChcExpr::int(constant), ChcExpr::var(v.clone()))
                        };
                        Some((local_var, rhs_expr))
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            (lhs, ChcExpr::Var(v)) if keep_names.contains(v.name.as_str()) => {
                if let Some((local_var, constant, positive_local)) = local_affine_rhs(lhs) {
                    if !keep_names.contains(local_var.name.as_str()) {
                        let rhs_expr = if positive_local {
                            if constant == 0 {
                                ChcExpr::var(v.clone())
                            } else if matches!(lhs, ChcExpr::Op(ChcOp::Sub, _)) {
                                ChcExpr::add(ChcExpr::var(v.clone()), ChcExpr::int(constant))
                            } else {
                                ChcExpr::sub(ChcExpr::var(v.clone()), ChcExpr::int(constant))
                            }
                        } else {
                            ChcExpr::sub(ChcExpr::int(constant), ChcExpr::var(v.clone()))
                        };
                        Some((local_var, rhs_expr))
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            _ => None,
        };

        if simple_result.is_some() {
            return simple_result;
        }

        // Generalized linear solver: handle expressions containing exactly one
        // local (non-keep) Int variable in a linear (Add/Sub) position.
        // This handles patterns from signed triple-sum invariants and
        // multi-variable equalities like `C = A + B` or `(A + B) - C = D`.
        Self::solve_local_from_linear_equality(args[0].as_ref(), args[1].as_ref(), keep_names)
    }

    /// Solve for a single local variable in a linear equality between two expressions.
    ///
    /// Given `lhs = rhs`, find any non-keep (local) variable in an Add/Sub position
    /// and express it in terms of the remaining variables. The solved expression
    /// may still contain other locals — the caller iterates until convergence.
    ///
    /// Handles patterns such as:
    /// - `keep1 = Add(local, keep2)` -> `local = keep1 - keep2`
    /// - `keep1 = Sub(Add(local, keep2), keep3)` -> `local = keep1 + keep3 - keep2`
    /// - `Sub(Add(keep1, keep2), local) = keep3` -> `local = keep1 + keep2 - keep3`
    /// - `keep1 = Add(local1, local2)` -> `local1 = keep1 - local2` (multi-local)
    fn solve_local_from_linear_equality(
        lhs: &ChcExpr,
        rhs: &ChcExpr,
        keep_names: &FxHashSet<&str>,
    ) -> Option<(ChcVar, ChcExpr)> {
        // TERMINATION FIX (HOLA 16.c acceptance hang): operate on the
        // difference `lhs - rhs = 0` so a local that appears on BOTH sides is
        // combined (or cancelled) by extract_local_from_linear instead of
        // being re-introduced through the untouched other side. Solving from
        // one side only produced self-referential replacements
        // (`A := A + C - B`), which made substitute_head_affine_locals
        // diverge with exponential formula growth (53 -> 201 -> 2289 ->
        // 238809 -> >1e6 nodes in 5 iterations).
        //
        // The remainder returned by extract_local_from_linear is local-free
        // by construction, so each accepted substitution removes the solved
        // local from the whole formula and the caller's loop terminates in
        // at most #locals iterations.
        let diff = ChcExpr::sub(lhs.clone(), rhs.clone()).simplify_constants();
        let locals: Vec<ChcVar> = diff
            .vars()
            .into_iter()
            .filter(|v| matches!(v.sort, ChcSort::Int) && !keep_names.contains(v.name.as_str()))
            .collect();
        if locals.is_empty() {
            return None;
        }

        // Try each local until one has a unit coefficient. The solved
        // expression may still contain OTHER locals — that is OK because
        // substitute_head_affine_locals iterates until no more substitutions
        // are possible. For the signed triple-sum pattern `C = A + B - D`
        // where C is keep and A, B, D are locals, this picks (say) A and
        // produces `A = C - B + D`, eliminating one local per iteration.
        for local in locals {
            let Some((sign, remainder)) = Self::extract_local_from_linear(&diff, &local.name)
            else {
                continue;
            };
            // diff = sign * local + remainder = 0  =>  local = -remainder / sign.
            // For integers, we can only solve exactly with unit coefficients;
            // non-unit coefficients are left for try_integer_projection (#7997).
            let result = match sign {
                1 => ChcExpr::sub(ChcExpr::int(0), remainder).simplify_constants(),
                -1 => remainder.simplify_constants(),
                _ => continue,
            };
            // Defense in depth: never emit a self-referential substitution.
            if Self::expr_contains_var(&result, &local.name) {
                continue;
            }
            return Some((local, result));
        }
        None
    }

    /// Extract a local variable from a linear Add/Sub expression tree.
    ///
    /// Returns `(sign, remainder)` where:
    /// - `sign` is +1 if the local appears positively, -1 if negated
    /// - `remainder` is the expression with the local removed
    ///
    /// So `expr = sign * Var(local_name) + remainder`.
    ///
    /// Handles nested Add/Sub trees (sufficient for signed triple-sum
    /// patterns like `Sub(Add(a, b), c)`).
    fn extract_local_from_linear(expr: &ChcExpr, local_name: &str) -> Option<(i128, ChcExpr)> {
        match expr {
            ChcExpr::Var(v) if v.name == local_name => {
                // expr = 1 * local + 0
                Some((1, ChcExpr::int(0)))
            }
            // Mul(const, local) or Mul(local, const) — the local has an integer
            // coefficient. Common after simplify_constants flattens Add trees
            // containing scaled variables (e.g., `A + (-3)*B`).
            ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Int(n), ChcExpr::Var(v)) if v.name == local_name && *n != 0 => {
                        // expr = n * local + 0
                        Some((*n, ChcExpr::int(0)))
                    }
                    (ChcExpr::Var(v), ChcExpr::Int(n)) if v.name == local_name && *n != 0 => {
                        // expr = n * local + 0
                        Some((*n, ChcExpr::int(0)))
                    }
                    _ => None,
                }
            }
            // Neg(local) = -1 * local
            ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
                if let ChcExpr::Var(v) = args[0].as_ref() {
                    if v.name == local_name {
                        return Some((-1, ChcExpr::int(0)));
                    }
                }
                // Neg(Mul(n, local)) = -n * local
                if let ChcExpr::Op(ChcOp::Mul, mul_args) = args[0].as_ref() {
                    if mul_args.len() == 2 {
                        match (mul_args[0].as_ref(), mul_args[1].as_ref()) {
                            (ChcExpr::Int(n), ChcExpr::Var(v))
                                if v.name == local_name && *n != 0 =>
                            {
                                return Some((n.checked_neg()?, ChcExpr::int(0)));
                            }
                            (ChcExpr::Var(v), ChcExpr::Int(n))
                                if v.name == local_name && *n != 0 =>
                            {
                                return Some((n.checked_neg()?, ChcExpr::int(0)));
                            }
                            _ => {}
                        }
                    }
                }
                None
            }
            ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
                // expr = lhs + rhs
                let (lhs, rhs) = (args[0].as_ref(), args[1].as_ref());
                let lhs_has = Self::expr_contains_var(lhs, local_name);
                let rhs_has = Self::expr_contains_var(rhs, local_name);

                if lhs_has && rhs_has {
                    // Local appears in both sides. Try extracting from both
                    // and combining coefficients. This handles `Mul(2, B) + B`
                    // -> coefficient 2 + 1 = 3. (#7997)
                    let (sign_l, rem_l) = Self::extract_local_from_linear(lhs, local_name)?;
                    let (sign_r, rem_r) = Self::extract_local_from_linear(rhs, local_name)?;
                    let combined_sign = sign_l.checked_add(sign_r)?;
                    if combined_sign == 0 {
                        return None; // Local cancels out
                    }
                    Some((combined_sign, ChcExpr::add(rem_l, rem_r)))
                } else if lhs_has {
                    let (sign, remainder) = Self::extract_local_from_linear(lhs, local_name)?;
                    // expr = (sign * local + remainder) + rhs
                    // expr = sign * local + (remainder + rhs)
                    Some((sign, ChcExpr::add(remainder, rhs.clone())))
                } else if rhs_has {
                    let (sign, remainder) = Self::extract_local_from_linear(rhs, local_name)?;
                    // expr = lhs + (sign * local + remainder)
                    // expr = sign * local + (lhs + remainder)
                    Some((sign, ChcExpr::add(lhs.clone(), remainder)))
                } else {
                    None // Local not found
                }
            }
            // N-ary Add: simplify_constants can produce Add with >2 args from
            // flattening nested additions. Extract the local from all args that
            // contain it, combining coefficients, and accumulate the rest as remainder.
            ChcExpr::Op(ChcOp::Add, args) if args.len() > 2 => {
                let mut total_sign: i128 = 0;
                let mut remainder_terms: Vec<std::sync::Arc<ChcExpr>> = Vec::new();

                for arg in args {
                    if Self::expr_contains_var(arg, local_name) {
                        let (sign, inner_rem) = Self::extract_local_from_linear(arg, local_name)?;
                        total_sign = total_sign.checked_add(sign)?;
                        if !matches!(inner_rem, ChcExpr::Int(0)) {
                            remainder_terms.push(std::sync::Arc::new(inner_rem));
                        }
                    } else {
                        remainder_terms.push(arg.clone());
                    }
                }

                if total_sign == 0 {
                    return None;
                }

                let remainder = if remainder_terms.is_empty() {
                    ChcExpr::int(0)
                } else if remainder_terms.len() == 1 {
                    remainder_terms[0].as_ref().clone()
                } else {
                    ChcExpr::Op(ChcOp::Add, remainder_terms)
                };
                Some((total_sign, remainder))
            }
            ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
                // expr = lhs - rhs
                let (lhs, rhs) = (args[0].as_ref(), args[1].as_ref());
                let lhs_has = Self::expr_contains_var(lhs, local_name);
                let rhs_has = Self::expr_contains_var(rhs, local_name);

                if lhs_has && rhs_has {
                    // Local in both sides of subtraction. Extract and combine.
                    let (sign_l, rem_l) = Self::extract_local_from_linear(lhs, local_name)?;
                    let (sign_r, rem_r) = Self::extract_local_from_linear(rhs, local_name)?;
                    // expr = (sign_l * local + rem_l) - (sign_r * local + rem_r)
                    // expr = (sign_l - sign_r) * local + (rem_l - rem_r)
                    let combined_sign = sign_l.checked_sub(sign_r)?;
                    if combined_sign == 0 {
                        return None;
                    }
                    Some((combined_sign, ChcExpr::sub(rem_l, rem_r)))
                } else if lhs_has {
                    let (sign, remainder) = Self::extract_local_from_linear(lhs, local_name)?;
                    // expr = (sign * local + remainder) - rhs
                    // expr = sign * local + (remainder - rhs)
                    Some((sign, ChcExpr::sub(remainder, rhs.clone())))
                } else if rhs_has {
                    let (sign, remainder) = Self::extract_local_from_linear(rhs, local_name)?;
                    // expr = lhs - (sign * local + remainder)
                    // expr = -sign * local + (lhs - remainder)
                    Some((sign.checked_neg()?, ChcExpr::sub(lhs.clone(), remainder)))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Check if an expression contains a variable with the given name.
    fn expr_contains_var(expr: &ChcExpr, var_name: &str) -> bool {
        expr.vars().iter().any(|v| v.name == var_name)
    }

    /// Propagate equalities between local (non-keep) variables.
    ///
    /// Before doing the keep-oriented algebraic elimination, reduce the number of
    /// distinct local variables by substituting equalities like `A = 2*B` or
    /// `A = B + C`. This prevents expression bloat: substituting `A = 2*B` into
    /// `bt_arg0 = A + B` yields `bt_arg0 = 3*B` (one local) instead of keeping
    /// both A and B around.
    ///
    /// Pattern from #7997: PDR produces `A = 2*B` in Inner's invariant. Without
    /// this pre-pass, algebraic elimination picks `A = bt_arg0 - B` (from `bt_arg0 = A + B`),
    /// leaving `B` plus bloated nested expressions. With the pre-pass, `A` is replaced
    /// by `2*B` first, so the defining equality becomes `bt_arg0 = 3*B` and only `B` remains.
    fn propagate_local_equalities(formula: &ChcExpr, keep_vars: &[ChcVar]) -> ChcExpr {
        let keep_names: FxHashSet<&str> = keep_vars.iter().map(|v| v.name.as_str()).collect();
        let mut current = formula.clone();

        // Iterate: each round finds one local=expr(locals_only) equality and substitutes.
        // Converges when no more local-only equalities remain.
        // Prefer direct `Var = expr` substitutions over linear extractions to
        // avoid introducing unnecessary negation/subtraction. (#7997)
        let mut max_rounds = 20;
        loop {
            if max_rounds == 0 {
                break;
            }
            max_rounds -= 1;

            let conjuncts = current.collect_conjuncts();

            // Pass 1: look for direct `Var = expr` (no linear extraction needed)
            let subst = conjuncts
                .iter()
                .find_map(|conj| {
                    let ChcExpr::Op(ChcOp::Eq, args) = conj else {
                        return None;
                    };
                    if args.len() != 2 {
                        return None;
                    }
                    Self::find_direct_local_substitution(
                        args[0].as_ref(),
                        args[1].as_ref(),
                        &keep_names,
                    )
                })
                .or_else(|| {
                    // Pass 2: try linear extraction (handles `A + (-2)*B = 0` etc.)
                    conjuncts.iter().find_map(|conj| {
                        let ChcExpr::Op(ChcOp::Eq, args) = conj else {
                            return None;
                        };
                        if args.len() != 2 {
                            return None;
                        }
                        Self::find_linear_local_substitution(
                            args[0].as_ref(),
                            args[1].as_ref(),
                            &keep_names,
                        )
                    })
                });

            let Some((local, replacement)) = subst else {
                break;
            };
            current = current
                .substitute(&[(local, replacement)])
                .simplify_constants();
        }

        current
    }

    /// Check that both sides of an equality are free of keep variables.
    fn both_sides_local(lhs: &ChcExpr, rhs: &ChcExpr, keep_names: &FxHashSet<&str>) -> bool {
        !lhs.vars()
            .iter()
            .any(|v| keep_names.contains(v.name.as_str()))
            && !rhs
                .vars()
                .iter()
                .any(|v| keep_names.contains(v.name.as_str()))
    }

    /// Find a DIRECT substitution `Var(local) = expr` from an equality.
    /// This is the cleanest form: one side is a plain local variable.
    /// Preferred over linear extraction to avoid introducing negation/subtraction.
    fn find_direct_local_substitution(
        lhs: &ChcExpr,
        rhs: &ChcExpr,
        keep_names: &FxHashSet<&str>,
    ) -> Option<(ChcVar, ChcExpr)> {
        if !Self::both_sides_local(lhs, rhs, keep_names) {
            return None;
        }

        // Try lhs = Var(local), rhs = expr
        if let ChcExpr::Var(v) = lhs {
            if matches!(v.sort, ChcSort::Int) && !keep_names.contains(v.name.as_str()) {
                if !Self::expr_contains_var(rhs, &v.name) {
                    return Some((v.clone(), rhs.clone()));
                }
            }
        }

        // Try rhs = Var(local), lhs = expr
        if let ChcExpr::Var(v) = rhs {
            if matches!(v.sort, ChcSort::Int) && !keep_names.contains(v.name.as_str()) {
                if !Self::expr_contains_var(lhs, &v.name) {
                    return Some((v.clone(), lhs.clone()));
                }
            }
        }

        None
    }

    /// Find a substitution by linear extraction from an equality like `A + (-2)*B = 0`.
    /// Only extracts when the coefficient is unit (+1 or -1).
    fn find_linear_local_substitution(
        lhs: &ChcExpr,
        rhs: &ChcExpr,
        keep_names: &FxHashSet<&str>,
    ) -> Option<(ChcVar, ChcExpr)> {
        if !Self::both_sides_local(lhs, rhs, keep_names) {
            return None;
        }

        for (expr_side, other_side) in [(lhs, rhs), (rhs, lhs)] {
            let vars_in_expr = expr_side.vars();
            let local_vars: Vec<&ChcVar> = vars_in_expr
                .iter()
                .filter(|v| matches!(v.sort, ChcSort::Int) && !keep_names.contains(v.name.as_str()))
                .collect();
            for local in local_vars {
                if let Some((sign, remainder)) =
                    Self::extract_local_from_linear(expr_side, &local.name)
                {
                    if sign == 1 || sign == -1 {
                        let diff = ChcExpr::sub(other_side.clone(), remainder).simplify_constants();
                        let result = if sign == 1 {
                            diff
                        } else {
                            ChcExpr::sub(ChcExpr::int(0), diff).simplify_constants()
                        };
                        if !Self::expr_contains_var(&result, &local.name) {
                            return Some(((*local).clone(), result));
                        }
                    }
                }
            }
        }

        None
    }

    /// Try to eliminate remaining non-keep variables via integer projection
    /// with divisibility constraints.
    ///
    /// Handles the case where algebraic elimination reduced the formula to a
    /// single non-keep variable `B` with a linear equation to keep vars:
    /// `keep = c * B + d` (where c is a non-unit integer coefficient).
    ///
    /// The existential projection of `exists B. keep = c*B + d /\ bounds(B)` is:
    /// `(keep - d) mod c = 0 /\ bounds_on_keep_from_B_bounds`
    ///
    /// Example from #7997: `bt_arg0 = 3*B /\ 2*B >= 20 /\ B >= 0`
    /// -> `bt_arg0 mod 3 = 0 /\ bt_arg0 >= 30`.
    fn try_integer_projection(
        formula: &ChcExpr,
        _keep_vars: &[ChcVar],
        keep_set: &FxHashSet<ChcVar>,
    ) -> Option<ChcExpr> {
        let non_keep: Vec<ChcVar> = formula
            .vars()
            .into_iter()
            .filter(|v| !keep_set.contains(v))
            .collect();

        // Only handle single remaining non-keep variable
        if non_keep.len() != 1 {
            return None;
        }
        let local = &non_keep[0];
        if !matches!(local.sort, ChcSort::Int) {
            return None;
        }

        let conjuncts = formula.collect_conjuncts();

        // Find an equality that relates keep vars to the local var.
        // We need: `expr(keep) = c * local + d` or equivalently
        // `expr(keep) = expr(local)` that we can extract via linear algebra.
        let mut found_solution: Option<(i128, ChcExpr)> = None; // (coefficient, keep_expr) s.t. keep_expr = coeff * local

        for conj in &conjuncts {
            let ChcExpr::Op(ChcOp::Eq, args) = conj else {
                continue;
            };
            if args.len() != 2 {
                continue;
            }

            // Use the same linear extraction on both sides, but now we want
            // to find `side1 - side2 = 0` written as `coeff * local + remainder(keep) = 0`
            let combined = ChcExpr::sub(args[0].as_ref().clone(), args[1].as_ref().clone())
                .simplify_constants();

            if let Some((sign, remainder)) = Self::extract_local_from_linear(&combined, &local.name)
            {
                // combined = sign * local + remainder = 0
                // => sign * local = -remainder
                // => local = -remainder / sign
                //
                // The remainder should only contain keep vars.
                let remainder_vars = remainder.vars();
                if remainder_vars.iter().all(|v| keep_set.contains(v)) {
                    // local = -remainder / sign
                    // keep_expr = -remainder, coefficient = sign
                    // So: sign * local + remainder = 0 => local = (-remainder) / sign
                    let neg_remainder =
                        ChcExpr::sub(ChcExpr::int(0), remainder.clone()).simplify_constants();
                    found_solution = Some((sign, neg_remainder));
                    break;
                }
            }
        }

        let (coeff, keep_expr) = found_solution?;
        let abs_coeff = coeff.checked_abs()?;

        // Build the projected formula by substituting local = keep_expr / coeff
        // in each conjunct, converting to keep-only constraints.
        let mut result_conjuncts = Vec::new();

        // Add divisibility constraint: keep_expr mod abs_coeff = 0
        if abs_coeff > 1 {
            result_conjuncts.push(ChcExpr::eq(
                ChcExpr::mod_op(keep_expr.clone(), ChcExpr::int(abs_coeff)),
                ChcExpr::int(0),
            ));
        }

        // Process each conjunct, substituting local and converting bounds
        for conj in &conjuncts {
            match conj {
                ChcExpr::Op(ChcOp::Eq, _) => {
                    // Equalities involving local are satisfied by the substitution
                    // (the equality we found defines local, and local-only equalities
                    // like `2*B - 2*B = 0` are tautologies). Skip them.
                    // But equalities that are purely keep-vars should be kept.
                    let conj_vars = conj.vars();
                    if conj_vars.iter().all(|v| keep_set.contains(v)) {
                        result_conjuncts.push(conj.clone());
                    }
                    // Otherwise skip (handled by substitution + divisibility)
                }
                ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
                    // Convert bound: `expr(local) >= k` -> bound on keep_expr
                    if let Some(keep_bound) = Self::convert_bound_to_keep(
                        args[0].as_ref(),
                        args[1].as_ref(),
                        coeff,
                        &keep_expr,
                        &local.name,
                    ) {
                        result_conjuncts.push(keep_bound);
                    }
                    // If conversion fails, the bound doesn't contribute to the projection
                }
                ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
                    // `expr(local) <= k` can be rewritten as `-(expr(local)) >= -k`
                    // i.e., `-expr >= -k`, but it's easier to negate and convert
                    if let Some(keep_bound) = Self::convert_le_bound_to_keep(
                        args[0].as_ref(),
                        args[1].as_ref(),
                        coeff,
                        &keep_expr,
                        &local.name,
                    ) {
                        result_conjuncts.push(keep_bound);
                    }
                }
                _ => {
                    // Other constraints: if they're keep-only, keep them
                    let conj_vars = conj.vars();
                    if conj_vars.iter().all(|v| keep_set.contains(v)) {
                        result_conjuncts.push(conj.clone());
                    }
                    // Otherwise drop (covered by the projection)
                }
            }
        }

        if result_conjuncts.is_empty() {
            return Some(ChcExpr::Bool(true));
        }

        let result = ChcExpr::and_all(result_conjuncts).simplify_constants();
        if Self::vars_are_closed(&result, keep_set) {
            Some(result)
        } else {
            None
        }
    }

    /// Convert a >= bound on expressions involving `local` to a bound on `keep_expr`.
    ///
    /// Given `local = keep_expr / coeff`, and a bound `lhs >= rhs` where lhs
    /// may contain `local`, produce an equivalent bound on `keep_expr`.
    ///
    /// Handles patterns like:
    /// - `c * local >= k` => `keep_expr >= k * abs_coeff / c` (with appropriate sign)
    /// - `local >= k` => `keep_expr >= k * coeff` (if coeff > 0) or `keep_expr <= k * coeff` (if coeff < 0)
    fn convert_bound_to_keep(
        lhs: &ChcExpr,
        rhs: &ChcExpr,
        coeff: i128,
        keep_expr: &ChcExpr,
        local_name: &str,
    ) -> Option<ChcExpr> {
        // Simple case: `local >= k` where k is a constant
        if let (ChcExpr::Var(v), ChcExpr::Int(k)) = (lhs, rhs) {
            if v.name == local_name {
                // local >= k => keep_expr / coeff >= k => keep_expr >= k * coeff (if coeff > 0)
                // or keep_expr <= k * coeff (if coeff < 0)
                let bound = k.checked_mul(coeff)?;
                if coeff > 0 {
                    return Some(ChcExpr::ge(keep_expr.clone(), ChcExpr::int(bound)));
                } else {
                    return Some(ChcExpr::le(keep_expr.clone(), ChcExpr::int(bound)));
                }
            }
        }

        // `c * local >= k` where c is a constant multiplier
        if let ChcExpr::Op(ChcOp::Mul, mul_args) = lhs {
            if mul_args.len() == 2 {
                if let Some((c, local_in_mul)) = match (mul_args[0].as_ref(), mul_args[1].as_ref())
                {
                    (ChcExpr::Int(c), ChcExpr::Var(v)) if v.name == local_name => Some((*c, true)),
                    (ChcExpr::Var(v), ChcExpr::Int(c)) if v.name == local_name => Some((*c, true)),
                    _ => None,
                } {
                    if local_in_mul {
                        if let ChcExpr::Int(k) = rhs {
                            // c * local >= k => c * (keep_expr / coeff) >= k
                            // => (c / coeff) * keep_expr >= k
                            // If c and coeff have the same sign: keep_expr >= k * coeff / c
                            // This simplifies when c divides k*coeff evenly.
                            let numerator = k.checked_mul(coeff)?;
                            if numerator.checked_rem(c)? == 0 {
                                let bound = numerator.checked_div(c)?;
                                if (c > 0) == (coeff > 0) {
                                    // Same sign: inequality direction preserved
                                    return Some(ChcExpr::ge(
                                        keep_expr.clone(),
                                        ChcExpr::int(bound),
                                    ));
                                } else {
                                    return Some(ChcExpr::le(
                                        keep_expr.clone(),
                                        ChcExpr::int(bound),
                                    ));
                                }
                            } else {
                                // Use ceiling division for >=
                                let bound = if (c > 0) == (coeff > 0) {
                                    // Same sign: keep_expr >= ceil(k*coeff/c)
                                    numerator.checked_add(c)?.checked_sub(1)?.checked_div(c)?
                                // ceiling division
                                } else {
                                    numerator.checked_div(c)?
                                };
                                if (c > 0) == (coeff > 0) {
                                    return Some(ChcExpr::ge(
                                        keep_expr.clone(),
                                        ChcExpr::int(bound),
                                    ));
                                } else {
                                    return Some(ChcExpr::le(
                                        keep_expr.clone(),
                                        ChcExpr::int(bound),
                                    ));
                                }
                            }
                        }
                    }
                }
            }
        }

        // Subtraction: `expr - c*local >= k` or `local - expr >= k`
        // These arise from constraints like `A - B >= 0` after substituting A.
        // Try to handle by extracting the local coefficient.
        if Self::expr_contains_var(lhs, local_name) {
            if let Some((sign, remainder)) = Self::extract_local_from_linear(lhs, local_name) {
                if let ChcExpr::Int(k) = rhs {
                    // lhs = sign * local + remainder >= k
                    // sign * local >= k - remainder
                    // sign * (keep_expr / coeff) >= k - remainder
                    let remainder_vars = remainder.vars();
                    if remainder_vars.iter().all(|v| v.name != local_name) {
                        // If remainder is keep-only or constant, we can convert
                        if let ChcExpr::Int(r) = &remainder {
                            let rhs_val = k.checked_sub(*r)?;
                            // sign * (keep_expr / coeff) >= rhs_val
                            // If sign and coeff have the same sign: keep_expr >= rhs_val * coeff / sign
                            let numerator = rhs_val.checked_mul(coeff)?;
                            if sign != 0 && numerator.checked_rem(sign)? == 0 {
                                let bound = numerator.checked_div(sign)?;
                                if (sign > 0) == (coeff > 0) {
                                    return Some(ChcExpr::ge(
                                        keep_expr.clone(),
                                        ChcExpr::int(bound),
                                    ));
                                } else {
                                    return Some(ChcExpr::le(
                                        keep_expr.clone(),
                                        ChcExpr::int(bound),
                                    ));
                                }
                            }
                        }
                    }
                }
            }
        }

        None
    }

    /// Convert a <= bound to a keep-only bound. Delegates to `convert_bound_to_keep`
    /// with flipped signs: `lhs <= rhs` is equivalent to `-lhs >= -rhs`.
    fn convert_le_bound_to_keep(
        lhs: &ChcExpr,
        rhs: &ChcExpr,
        coeff: i128,
        keep_expr: &ChcExpr,
        local_name: &str,
    ) -> Option<ChcExpr> {
        // `local <= k` => `-local >= -k` which is the same as `local >= -k` with sign flip
        if let (ChcExpr::Var(v), ChcExpr::Int(k)) = (lhs, rhs) {
            if v.name == local_name {
                // local <= k => keep_expr / coeff <= k => keep_expr <= k * coeff (if coeff > 0)
                let bound = k.checked_mul(coeff)?;
                if coeff > 0 {
                    return Some(ChcExpr::le(keep_expr.clone(), ChcExpr::int(bound)));
                } else {
                    return Some(ChcExpr::ge(keep_expr.clone(), ChcExpr::int(bound)));
                }
            }
        }

        // For more complex patterns, try extract_local_from_linear
        if Self::expr_contains_var(lhs, local_name) {
            if let Some((sign, remainder)) = Self::extract_local_from_linear(lhs, local_name) {
                if let ChcExpr::Int(k) = rhs {
                    let remainder_vars = remainder.vars();
                    if remainder_vars.iter().all(|v| v.name != local_name) {
                        if let ChcExpr::Int(r) = &remainder {
                            let rhs_val = k.checked_sub(*r)?;
                            // sign * (keep_expr / coeff) <= rhs_val
                            let numerator = rhs_val.checked_mul(coeff)?;
                            if sign != 0 && numerator.checked_rem(sign)? == 0 {
                                let bound = numerator.checked_div(sign)?;
                                if (sign > 0) == (coeff > 0) {
                                    return Some(ChcExpr::le(
                                        keep_expr.clone(),
                                        ChcExpr::int(bound),
                                    ));
                                } else {
                                    return Some(ChcExpr::ge(
                                        keep_expr.clone(),
                                        ChcExpr::int(bound),
                                    ));
                                }
                            }
                        }
                    }
                }
            }
        }

        None
    }

    fn substitute_head_affine_locals(formula: &ChcExpr, keep_vars: &[ChcVar]) -> ChcExpr {
        let keep_names: FxHashSet<&str> = keep_vars.iter().map(|v| v.name.as_str()).collect();

        // Pre-pass: reduce the number of distinct local variables by propagating
        // equalities between locals (e.g., A = 2*B). This prevents expression
        // bloat in the main algebraic elimination pass. (#7997)
        let profile = accept_profile_enabled();
        let t_start = ay_core::time::Instant::now();
        let mut current = Self::propagate_local_equalities(formula, keep_vars).simplify_constants();
        if profile {
            safe_eprintln!(
                "[ACCEPT-PROF] qe phase=prop-local-eq dt={:.3}s nodes={}",
                t_start.elapsed().as_secs_f64(),
                current.node_count(1_000_000)
            );
        }
        current = Self::propagate_tight_bound_constants(&current).simplify_constants();
        if profile {
            safe_eprintln!(
                "[ACCEPT-PROF] qe phase=tight-bounds dt={:.3}s nodes={}",
                t_start.elapsed().as_secs_f64(),
                current.node_count(1_000_000)
            );
        }

        // Each accepted substitution removes its local from the whole formula
        // (replacements are never self-referential), so this terminates in at
        // most #locals iterations. The cap and growth guard are defense in
        // depth: on bail, residual locals flow to try_integer_projection /
        // AllSAT+MBP, and if those fail too, synthesis fails closed (the
        // portfolio rejects the Safe result).
        const MAX_AFFINE_ITERS: usize = 64;
        const MAX_AFFINE_GROWTH_NODES: usize = 200_000;
        let mut affine_iters = 0usize;
        loop {
            if affine_iters >= MAX_AFFINE_ITERS {
                break;
            }
            affine_iters += 1;
            if profile {
                safe_eprintln!(
                    "[ACCEPT-PROF] qe phase=affine-loop iter={} dt={:.3}s nodes={}",
                    affine_iters,
                    t_start.elapsed().as_secs_f64(),
                    current.node_count(1_000_000)
                );
            }
            let subst = current
                .collect_conjuncts()
                .into_iter()
                .find_map(|conj| Self::solve_local_from_head_equality(&conj, &keep_names));
            let Some((local, replacement)) = subst else {
                break;
            };
            let next = current
                .substitute(&[(local, replacement)])
                .simplify_constants();
            if next.node_count(MAX_AFFINE_GROWTH_NODES) >= MAX_AFFINE_GROWTH_NODES {
                // Substitution exploded the term — not progress toward a
                // closed form. Keep the smaller formula and bail.
                break;
            }
            current = next;
        }

        current
    }

    fn propagate_non_keep_constants(formula: &ChcExpr, keep_vars: &[ChcVar]) -> ChcExpr {
        let keep_names: FxHashSet<&str> = keep_vars.iter().map(|v| v.name.as_str()).collect();
        let subst: Vec<(ChcVar, ChcExpr)> = formula
            .collect_conjuncts()
            .into_iter()
            .filter_map(|conj| {
                let ChcExpr::Op(ChcOp::Eq, ref args) = conj else {
                    return None;
                };
                if args.len() != 2 {
                    return None;
                }
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Var(v), ChcExpr::Int(c)) | (ChcExpr::Int(c), ChcExpr::Var(v))
                        if !keep_names.contains(v.name.as_str())
                            && matches!(v.sort, ChcSort::Int) =>
                    {
                        Some((v.clone(), ChcExpr::Int(*c)))
                    }
                    _ => None,
                }
            })
            .collect();

        if subst.is_empty() {
            formula.clone()
        } else {
            formula.substitute(&subst).simplify_constants()
        }
    }

    fn normalize_shifted_keep_constraints(formula: &ChcExpr, keep_vars: &[ChcVar]) -> ChcExpr {
        let keep_names: FxHashSet<&str> = keep_vars.iter().map(|v| v.name.as_str()).collect();
        let rewrite = |conj: &ChcExpr| -> ChcExpr {
            match conj {
                ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
                    match (args[0].as_ref(), args[1].as_ref()) {
                        (ChcExpr::Op(ChcOp::Sub, sub_args), ChcExpr::Int(k))
                            if sub_args.len() == 2 =>
                        {
                            if let (ChcExpr::Var(v), ChcExpr::Int(c)) =
                                (sub_args[0].as_ref(), sub_args[1].as_ref())
                            {
                                if keep_names.contains(v.name.as_str()) {
                                    return ChcExpr::le(
                                        ChcExpr::var(v.clone()),
                                        ChcExpr::int(k.saturating_add(*c)),
                                    );
                                }
                            }
                        }
                        _ => {}
                    }
                    conj.clone()
                }
                ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
                    match (args[0].as_ref(), args[1].as_ref()) {
                        (ChcExpr::Op(ChcOp::Sub, sub_args), ChcExpr::Int(k))
                            if sub_args.len() == 2 =>
                        {
                            if let (ChcExpr::Var(v), ChcExpr::Int(c)) =
                                (sub_args[0].as_ref(), sub_args[1].as_ref())
                            {
                                if keep_names.contains(v.name.as_str()) {
                                    return ChcExpr::ge(
                                        ChcExpr::var(v.clone()),
                                        ChcExpr::int(k.saturating_add(*c)),
                                    );
                                }
                            }
                        }
                        _ => {}
                    }
                    conj.clone()
                }
                ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                    if let ChcExpr::Op(ChcOp::Le, inner) = args[0].as_ref() {
                        if inner.len() == 2 {
                            match (inner[0].as_ref(), inner[1].as_ref()) {
                                (ChcExpr::Int(k), ChcExpr::Op(ChcOp::Sub, sub_args))
                                    if sub_args.len() == 2 =>
                                {
                                    if let (ChcExpr::Var(v), ChcExpr::Int(c)) =
                                        (sub_args[0].as_ref(), sub_args[1].as_ref())
                                    {
                                        if keep_names.contains(v.name.as_str()) {
                                            return ChcExpr::le(
                                                ChcExpr::var(v.clone()),
                                                ChcExpr::int(
                                                    k.saturating_add(*c).saturating_sub(1),
                                                ),
                                            );
                                        }
                                    }
                                }
                                (ChcExpr::Int(k), ChcExpr::Var(v))
                                    if keep_names.contains(v.name.as_str()) =>
                                {
                                    return ChcExpr::le(
                                        ChcExpr::var(v.clone()),
                                        ChcExpr::int(k.saturating_sub(1)),
                                    );
                                }
                                _ => {}
                            }
                        }
                    }
                    conj.clone()
                }
                ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                    let rewrite_mod = |expr: &ChcExpr| -> Option<ChcExpr> {
                        let ChcExpr::Op(ChcOp::Mod, mod_args) = expr else {
                            return None;
                        };
                        if mod_args.len() != 2 {
                            return None;
                        }
                        let ChcExpr::Int(modulus) = mod_args[1].as_ref() else {
                            return None;
                        };
                        match mod_args[0].as_ref() {
                            ChcExpr::Op(ChcOp::Sub, sub_args) if sub_args.len() == 2 => {
                                if let (ChcExpr::Var(v), ChcExpr::Int(c)) =
                                    (sub_args[0].as_ref(), sub_args[1].as_ref())
                                {
                                    if keep_names.contains(v.name.as_str())
                                        && c.rem_euclid(*modulus) == 0
                                    {
                                        return Some(ChcExpr::mod_op(
                                            ChcExpr::var(v.clone()),
                                            ChcExpr::int(*modulus),
                                        ));
                                    }
                                }
                                None
                            }
                            _ => None,
                        }
                    };

                    match (rewrite_mod(args[0].as_ref()), rewrite_mod(args[1].as_ref())) {
                        (Some(lhs), _) => ChcExpr::eq(lhs, args[1].as_ref().clone()),
                        (_, Some(rhs)) => ChcExpr::eq(args[0].as_ref().clone(), rhs),
                        _ => conj.clone(),
                    }
                }
                _ => conj.clone(),
            }
        };

        if let ChcExpr::Op(ChcOp::And, _) = formula {
            ChcExpr::and_all(
                formula
                    .collect_conjuncts()
                    .into_iter()
                    .map(|conj| rewrite(&conj)),
            )
            .simplify_constants()
        } else {
            rewrite(formula).simplify_constants()
        }
    }

    fn compress_closed_keep_constraints(formula: &ChcExpr, keep_vars: &[ChcVar]) -> ChcExpr {
        let [keep] = keep_vars else {
            return formula.clone();
        };
        if !matches!(keep.sort, ChcSort::Int) {
            return formula.clone();
        }

        let mut lower: Option<i128> = None;
        let mut upper: Option<i128> = None;
        let mut best_mod_zero: Option<i128> = None;
        let mut rest = Vec::new();

        for conj in formula.collect_conjuncts() {
            match &conj {
                ChcExpr::Op(ChcOp::Ge, args)
                    if args.len() == 2
                        && matches!(args[0].as_ref(), ChcExpr::Var(v) if v == keep)
                        && matches!(args[1].as_ref(), ChcExpr::Int(_)) =>
                {
                    if let ChcExpr::Int(c) = args[1].as_ref() {
                        lower = Some(lower.map_or(*c, |old| old.max(*c)));
                    }
                }
                ChcExpr::Op(ChcOp::Le, args)
                    if args.len() == 2
                        && matches!(args[0].as_ref(), ChcExpr::Var(v) if v == keep)
                        && matches!(args[1].as_ref(), ChcExpr::Int(_)) =>
                {
                    if let ChcExpr::Int(c) = args[1].as_ref() {
                        upper = Some(upper.map_or(*c, |old| old.min(*c)));
                    }
                }
                ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                    let matches_mod_zero = |lhs: &ChcExpr, rhs: &ChcExpr| -> Option<i128> {
                        let ChcExpr::Op(ChcOp::Mod, mod_args) = lhs else {
                            return None;
                        };
                        if mod_args.len() != 2 {
                            return None;
                        }
                        match (mod_args[0].as_ref(), mod_args[1].as_ref(), rhs) {
                            (ChcExpr::Var(v), ChcExpr::Int(m), ChcExpr::Int(0)) if v == keep => {
                                Some(*m)
                            }
                            _ => None,
                        }
                    };
                    if let Some(m) = matches_mod_zero(args[0].as_ref(), args[1].as_ref())
                        .or_else(|| matches_mod_zero(args[1].as_ref(), args[0].as_ref()))
                    {
                        best_mod_zero = Some(best_mod_zero.map_or(m, |old| old.max(m)));
                    } else {
                        rest.push(conj);
                    }
                }
                _ => rest.push(conj),
            }
        }

        if let Some(lb) = lower {
            rest.push(ChcExpr::ge(ChcExpr::var(keep.clone()), ChcExpr::int(lb)));
        }
        if let Some(ub) = upper {
            rest.push(ChcExpr::le(ChcExpr::var(keep.clone()), ChcExpr::int(ub)));
        }
        if let Some(m) = best_mod_zero {
            rest.push(ChcExpr::eq(
                ChcExpr::mod_op(ChcExpr::var(keep.clone()), ChcExpr::int(m)),
                ChcExpr::int(0),
            ));
        }

        ChcExpr::and_all(rest).simplify_constants()
    }

    /// Existentially eliminate clause-local variables from a synthesized
    /// interpretation, keeping only the predicate's formal parameters.
    ///
    /// Uses AllSAT+MBP enumeration to build a candidate projection and then
    /// validates completeness with `formula ∧ ¬projection`. If any models remain,
    /// the projection is incomplete and we fail closed.
    fn existentially_project_to_head_vars(
        formula: &ChcExpr,
        keep_vars: &[ChcVar],
    ) -> Option<ChcExpr> {
        let profile = accept_profile_enabled();
        let t_start = ay_core::time::Instant::now();
        let keep_set: FxHashSet<ChcVar> = keep_vars.iter().cloned().collect();
        if profile {
            safe_eprintln!(
                "[ACCEPT-PROF] qe phase=enter in_nodes={}",
                formula.node_count(1_000_000)
            );
        }
        let pre_simplified = formula.simplify_array_ops().simplify_constants();
        if profile {
            safe_eprintln!(
                "[ACCEPT-PROF] qe phase=pre-simplify dt={:.3}s nodes={}",
                t_start.elapsed().as_secs_f64(),
                pre_simplified.node_count(1_000_000)
            );
        }
        let simplified = Self::substitute_non_keep_equalities(&pre_simplified, &keep_set);
        if profile {
            safe_eprintln!(
                "[ACCEPT-PROF] qe phase=subst-non-keep-eq dt={:.3}s nodes={}",
                t_start.elapsed().as_secs_f64(),
                simplified.node_count(1_000_000)
            );
        }
        if Self::has_syntactic_contradiction(&simplified) {
            return Some(ChcExpr::Bool(false));
        }

        // Try algebraic elimination first. This handles simple cases like
        // `bt_arg0 = A + B` where A can be expressed as `bt_arg0 - B`.
        // The propagate_local_equalities pre-pass (inside substitute_head_affine_locals)
        // reduces the number of distinct locals first, preventing expression bloat. (#7997)
        let affine = Self::substitute_head_affine_locals(&simplified, keep_vars);
        if profile {
            safe_eprintln!(
                "[ACCEPT-PROF] qe phase=affine-locals dt={:.3}s nodes={}",
                t_start.elapsed().as_secs_f64(),
                affine.node_count(1_000_000)
            );
        }
        let algebraic = Self::propagate_non_keep_constants(&affine, keep_vars);
        let algebraic = Self::normalize_shifted_keep_constraints(&algebraic, keep_vars);
        let algebraic = Self::compress_closed_keep_constraints(&algebraic, keep_vars);
        let algebraic = algebraic.simplify_array_ops().simplify_constants();
        if Self::has_syntactic_contradiction(&algebraic) {
            return Some(ChcExpr::Bool(false));
        }
        if Self::vars_are_closed(&algebraic, &keep_set) {
            if profile {
                safe_eprintln!(
                    "[ACCEPT-PROF] qe-algebraic ok dt={:.3}s in_nodes={} out_nodes={}",
                    t_start.elapsed().as_secs_f64(),
                    formula.node_count(1_000_000),
                    algebraic.node_count(1_000_000)
                );
            }
            return Some(algebraic);
        }

        // Algebraic elimination was partial — some non-keep vars remain.
        // Try integer projection with divisibility constraints before
        // falling through to the expensive AllSAT+MBP loop. (#7997)
        let formula = algebraic;

        // Fast path: if there's a single remaining non-keep variable with an
        // equality to keep expressions, eliminate it with integer division +
        // divisibility constraint. This handles the common pattern from #7997:
        // `bt_arg0 = 3*B /\ 2*B >= 20 /\ B >= 0` -> `bt_arg0 mod 3 = 0 /\ bt_arg0 >= 30`.
        if let Some(projected) = Self::try_integer_projection(&formula, keep_vars, &keep_set) {
            return Some(projected);
        }

        if profile {
            safe_eprintln!(
                "[ACCEPT-PROF] qe-mbp-loop start dt={:.3}s formula_nodes={} keep={} locals={}",
                t_start.elapsed().as_secs_f64(),
                formula.node_count(1_000_000),
                keep_vars.len(),
                formula
                    .vars()
                    .into_iter()
                    .filter(|v| !keep_set.contains(v))
                    .count()
            );
        }
        let mbp = Mbp::new();
        let mut smt = SmtContext::new();
        let mut projections = Vec::new();
        let mut blocking = formula.clone();
        let mut mbp_iters = 0usize;
        let t_loop = ay_core::time::Instant::now();

        for _iter_idx in 0..MAX_EXISTENTIAL_QE_ITERS {
            // Shared wall deadline for the whole enumeration: a pathological
            // model count must not consume the portfolio's remaining budget.
            // Empty projections fail closed below (same as Unknown).
            if t_loop.elapsed() >= EXISTENTIAL_QE_LOOP_DEADLINE {
                if profile {
                    safe_eprintln!(
                        "[ACCEPT-PROF] qe-mbp-loop deadline iters={} dt={:.3}s",
                        mbp_iters,
                        t_start.elapsed().as_secs_f64()
                    );
                }
                if projections.is_empty() {
                    return None;
                }
                break;
            }
            mbp_iters += 1;
            if profile {
                safe_eprintln!(
                    "[ACCEPT-PROF] qe-mbp-loop iter={} dt={:.3}s blocking_nodes={}",
                    mbp_iters,
                    t_start.elapsed().as_secs_f64(),
                    blocking.node_count(1_000_000)
                );
            }
            match smt
                .check_sat_with_executor_fallback_timeout(&blocking, EXISTENTIAL_QE_CHECK_TIMEOUT)
            {
                SmtResult::Sat(model) => {
                    let projection = mbp
                        .keep_only(&formula, keep_vars, &model)
                        .simplify_constants();
                    if !Self::vars_are_closed(&projection, &keep_set) {
                        return None;
                    }
                    projections.push(projection.clone());
                    blocking =
                        ChcExpr::and(blocking, ChcExpr::not(projection)).simplify_constants();
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    break;
                }
                SmtResult::Unknown => {
                    if projections.is_empty() {
                        return None;
                    }
                    break;
                }
            }
        }

        let projected = if projections.is_empty() {
            ChcExpr::Bool(false)
        } else {
            ChcExpr::or_all(projections).simplify_constants()
        };

        if !Self::vars_are_closed(&projected, &keep_set) {
            return None;
        }

        let mut exactness = SmtContext::new();
        let missing_region =
            ChcExpr::and(formula.clone(), ChcExpr::not(projected.clone())).simplify_constants();
        match exactness
            .check_sat_with_executor_fallback_timeout(&missing_region, EXISTENTIAL_QE_CHECK_TIMEOUT)
        {
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
            SmtResult::Sat(_) => return None,
            SmtResult::Unknown => {}
        }

        if profile {
            safe_eprintln!(
                "[ACCEPT-PROF] qe-mbp-loop done iters={} dt={:.3}s out_nodes={}",
                mbp_iters,
                t_start.elapsed().as_secs_f64(),
                projected.node_count(1_000_000)
            );
        }
        Some(projected)
    }

    fn close_synthesized_interpretation(
        interp: PredicateInterpretation,
    ) -> Option<PredicateInterpretation> {
        if let Some(formula) =
            Self::existentially_project_to_head_vars(&interp.formula, &interp.vars)
        {
            return Some(PredicateInterpretation::new(interp.vars, formula));
        }

        let formula = Self::project_ground_array_store_facts(&interp.formula, &interp.vars)?;
        Some(PredicateInterpretation::new(interp.vars, formula))
    }

    fn has_syntactic_contradiction(formula: &ChcExpr) -> bool {
        let conjuncts = formula.collect_conjuncts();
        let mut positive = FxHashSet::default();
        let mut negative = FxHashSet::default();

        for conjunct in conjuncts {
            if matches!(conjunct, ChcExpr::Bool(false)) {
                return true;
            }

            match &conjunct {
                ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                    let inner = args[0].as_ref().clone();
                    if positive.contains(&inner) {
                        return true;
                    }
                    negative.insert(inner);
                }
                _ => {
                    if negative.contains(&conjunct) {
                        return true;
                    }
                    positive.insert(conjunct);
                }
            }
        }

        false
    }

    fn substitute_non_keep_equalities(formula: &ChcExpr, keep_set: &FxHashSet<ChcVar>) -> ChcExpr {
        let mut current = formula.clone();

        for _ in 0..8 {
            let Some((var, value)) = current
                .collect_conjuncts()
                .into_iter()
                .find_map(|conjunct| Self::non_keep_equality_substitution(&conjunct, keep_set))
            else {
                break;
            };

            let next = current
                .substitute(&[(var, value)])
                .simplify_array_ops()
                .simplify_constants();
            if next == current {
                break;
            }
            current = next;
        }

        current
    }

    fn non_keep_equality_substitution(
        conjunct: &ChcExpr,
        keep_set: &FxHashSet<ChcVar>,
    ) -> Option<(ChcVar, ChcExpr)> {
        let ChcExpr::Op(ChcOp::Eq, args) = conjunct else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }

        Self::non_keep_var_eq(args[0].as_ref(), args[1].as_ref(), keep_set)
            .or_else(|| Self::non_keep_var_eq(args[1].as_ref(), args[0].as_ref(), keep_set))
    }

    fn non_keep_var_eq(
        lhs: &ChcExpr,
        rhs: &ChcExpr,
        keep_set: &FxHashSet<ChcVar>,
    ) -> Option<(ChcVar, ChcExpr)> {
        let ChcExpr::Var(var) = lhs else {
            return None;
        };
        if keep_set.contains(var) || rhs.vars().iter().any(|rhs_var| rhs_var == var) {
            return None;
        }
        Some((var.clone(), rhs.clone()))
    }

    /// Project array equalities conservatively by keeping ground read facts.
    ///
    /// Some inlined model-checker-consumer-style clauses define an array argument as a concrete
    /// store chain over an unconstrained default element. Exact projection would
    /// require an existential array/default value, which this back-translator
    /// cannot express. For safety proofs we can still retain facts such as
    /// `select(head, k) = v` that are syntactically entailed by the store chain.
    /// The portfolio's original-problem verifier checks the resulting model
    /// before any Safe result is accepted.
    fn project_ground_array_store_facts(
        formula: &ChcExpr,
        keep_vars: &[ChcVar],
    ) -> Option<ChcExpr> {
        let keep_set: FxHashSet<ChcVar> = keep_vars.iter().cloned().collect();
        let mut facts = Vec::new();

        for conjunct in formula.collect_conjuncts() {
            if Self::vars_are_closed(&conjunct, &keep_set) {
                facts.push(conjunct);
                continue;
            }

            let ChcExpr::Op(ChcOp::Eq, args) = &conjunct else {
                continue;
            };
            if args.len() != 2 {
                continue;
            }

            Self::collect_array_store_facts_from_equality(
                args[0].as_ref(),
                args[1].as_ref(),
                &keep_set,
                &mut facts,
            );
            Self::collect_array_store_facts_from_equality(
                args[1].as_ref(),
                args[0].as_ref(),
                &keep_set,
                &mut facts,
            );
        }

        facts.retain(|fact| {
            !matches!(fact, ChcExpr::Bool(true)) && Self::vars_are_closed(fact, &keep_set)
        });
        if facts.is_empty() {
            return None;
        }

        let projected = ChcExpr::and_all(facts)
            .simplify_array_ops()
            .simplify_constants();
        if Self::vars_are_closed(&projected, &keep_set) {
            Some(projected)
        } else {
            None
        }
    }

    fn collect_array_store_facts_from_equality(
        lhs: &ChcExpr,
        rhs: &ChcExpr,
        keep_set: &FxHashSet<ChcVar>,
        facts: &mut Vec<ChcExpr>,
    ) {
        let ChcExpr::Var(var) = lhs else {
            return;
        };
        if !keep_set.contains(var) || !matches!(var.sort, ChcSort::Array(_, _)) {
            return;
        }

        let mut seen_stores = FxHashSet::default();
        Self::collect_array_store_select_facts(
            ChcExpr::var(var.clone()),
            rhs,
            keep_set,
            facts,
            &mut seen_stores,
        );
    }

    fn collect_array_store_select_facts(
        array_expr: ChcExpr,
        rhs: &ChcExpr,
        keep_set: &FxHashSet<ChcVar>,
        facts: &mut Vec<ChcExpr>,
        seen_stores: &mut FxHashSet<(ChcExpr, ChcExpr)>,
    ) {
        let ChcExpr::Op(ChcOp::Store, args) = rhs else {
            return;
        };
        if args.len() != 3 {
            return;
        }

        let base = args[0].as_ref();
        let index = args[1].as_ref().clone();
        let value = args[2].as_ref().clone();
        let select_expr = ChcExpr::select(array_expr.clone(), index.clone());

        // Visit outer stores before their base so repeated writes keep the
        // newest value and older writes at the same select path are ignored.
        if seen_stores.insert((array_expr.clone(), index)) {
            match value.sort() {
                ChcSort::Array(_, _) => Self::collect_array_store_select_facts(
                    select_expr,
                    &value,
                    keep_set,
                    facts,
                    seen_stores,
                ),
                _ => {
                    let fact = ChcExpr::eq(select_expr, value)
                        .simplify_array_ops()
                        .simplify_constants();
                    if !matches!(fact, ChcExpr::Bool(true))
                        && Self::vars_are_closed(&fact, keep_set)
                    {
                        facts.push(fact);
                    }
                }
            }
        }

        Self::collect_array_store_select_facts(array_expr, base, keep_set, facts, seen_stores);
    }

    /// Synthesize interpretation for an inlined predicate from its defining clause.
    ///
    /// For a fact clause `P(x1,...,xn) ⇐ C`: P's interpretation is C with
    /// the head variables as formal parameters.
    ///
    /// For a clause with body predicates `P(x1,...,xn) ⇐ C ∧ Q(a1,...,am)`:
    /// P's interpretation is C ∧ Q_interp(a1,...,am) where Q_interp substitutes
    /// Q's model interpretation applied to the body predicate's arguments.
    fn synthesize_interpretation(
        clause: &HornClause,
        model: &ValidityWitness,
    ) -> Option<PredicateInterpretation> {
        // Extract formal parameter variables from the head
        let head_vars = match &clause.head {
            ClauseHead::Predicate(_, args) => {
                let mut vars = Vec::new();
                for arg in args {
                    if let ChcExpr::Var(v) = arg {
                        vars.push(v.clone());
                    } else {
                        // After normalize_head_for_back_translation (#5295), all
                        // head args should be plain variables. This is a safety net.
                        debug_assert!(
                            false,
                            "BUG #5295: defining clause should be normalized before \
                             storing in inlined_defs — got complex head arg: {arg:?}"
                        );
                        return None;
                    }
                }
                vars
            }
            ClauseHead::False => return None,
        };

        // A repeated variable in the head — `P(x, y, x)`, which is legal CHC —
        // gives two FORMAL PARAMETERS THE SAME NAME. `PredicateInterpretation`
        // is applied by zipping `vars` against the call's actual arguments and
        // running a FIRST-MATCH substitution, so a duplicated name makes the
        // interpretation bind to the wrong argument position: the invariant
        // silently constrains argument #2 when it should constrain #0. A
        // tautological clause then reports "implication failed", and the
        // already-proved SAFE verdict is demoted to `unknown`
        // (tools/ay-ask/repro_refcell.smt2 in the model-checker-consumer tree).
        //
        // The meaning of a repeated head variable is that those positions are
        // EQUAL, so make each repeat a FRESH parameter and carry that equality
        // explicitly. Parameter names become distinct and no constraint is lost.
        let mut seen_names: Vec<String> = Vec::with_capacity(head_vars.len());
        let mut dedup_equalities: Vec<ChcExpr> = Vec::new();
        let mut head_vars_deduped: Vec<ChcVar> = Vec::with_capacity(head_vars.len());
        for (idx, v) in head_vars.iter().enumerate() {
            if seen_names.iter().any(|n| n == &v.name) {
                let fresh = ChcVar::new(format!("__dedup_a{idx}_{}", v.name), v.sort.clone());
                dedup_equalities.push(ChcExpr::eq(
                    ChcExpr::var(fresh.clone()),
                    ChcExpr::var(v.clone()),
                ));
                head_vars_deduped.push(fresh);
            } else {
                seen_names.push(v.name.clone());
                head_vars_deduped.push(v.clone());
            }
        }
        let head_vars = head_vars_deduped;

        // Start with the body constraint
        let constraint = clause
            .body
            .constraint
            .clone()
            .unwrap_or(ChcExpr::Bool(true));

        if clause.body.predicates.is_empty() {
            // Fact clause: interpretation is just the body constraint
            let constraint = if dedup_equalities.is_empty() {
                constraint
            } else {
                let mut parts = vec![constraint];
                parts.extend(dedup_equalities.iter().cloned());
                ChcExpr::and_all(parts)
            };
            return Self::close_synthesized_interpretation(PredicateInterpretation::new(
                head_vars, constraint,
            ));
        }

        // Clause has body predicates — substitute each with its model interpretation
        let mut conjuncts = vec![Arc::new(constraint)];
        for (body_pred_id, body_args) in &clause.body.predicates {
            let Some(body_interp) = model.get(body_pred_id) else {
                // Body predicate has no interpretation — can't synthesize
                return None;
            };
            // Build substitution: body_interp.vars[i] → body_args[i]
            let subst: Vec<(ChcVar, ChcExpr)> = body_interp
                .vars
                .iter()
                .zip(body_args.iter())
                .map(|(formal, actual)| (formal.clone(), actual.clone()))
                .collect();
            let applied = body_interp.formula.substitute(&subst);
            conjuncts.push(Arc::new(applied));
        }

        conjuncts.extend(dedup_equalities.into_iter().map(Arc::new));
        let formula = if conjuncts.len() == 1 {
            Arc::unwrap_or_clone(conjuncts.pop().unwrap())
        } else {
            ChcExpr::Op(ChcOp::And, conjuncts)
        };
        if accept_profile_enabled() {
            safe_eprintln!(
                "[ACCEPT-PROF] synth-built body_preds={} formula_nodes={}",
                clause.body.predicates.len(),
                formula.node_count(10_000_000)
            );
        }
        Self::close_synthesized_interpretation(PredicateInterpretation::new(head_vars, formula))
    }

    /// Group inlined definitions by predicate ID, preserving insertion order.
    fn group_defs_by_predicate(
        inlined_defs: &[(PredicateId, HornClause)],
    ) -> Vec<(PredicateId, Vec<&HornClause>)> {
        let mut grouped: Vec<(PredicateId, Vec<&HornClause>)> = Vec::new();
        let mut group_idx: FxHashMap<PredicateId, usize> = FxHashMap::default();
        for (pred_id, defining_clause) in inlined_defs {
            if let Some(&idx) = group_idx.get(pred_id) {
                grouped[idx].1.push(defining_clause);
            } else {
                let idx = grouped.len();
                group_idx.insert(*pred_id, idx);
                grouped.push((*pred_id, vec![defining_clause]));
            }
        }
        grouped
    }

    /// Synthesize a disjunctive interpretation for a multi-definition predicate.
    ///
    /// Returns `OR(body1, body2, ...)` where each body_i comes from one defining
    /// clause. All definitions share the same formal parameters; we rename vars
    /// to match the first definition's variable names.
    fn synthesize_disjunctive(
        clauses: &[&HornClause],
        model: &ValidityWitness,
    ) -> Option<PredicateInterpretation> {
        let mut disjuncts: Vec<Arc<ChcExpr>> = Vec::new();
        let mut shared_vars: Option<Vec<ChcVar>> = None;
        for (def_idx, clause) in clauses.iter().enumerate() {
            let interp = Self::synthesize_interpretation(clause, model)?;
            if shared_vars.is_none() {
                shared_vars = Some(interp.vars.clone());
            }
            // Rename interp vars to match the first definition's vars.
            let formula = if let Some(ref sv) = shared_vars {
                let head_subst: Vec<(ChcVar, ChcExpr)> = interp
                    .vars
                    .iter()
                    .zip(sv.iter())
                    .filter(|(a, b)| a.name != b.name)
                    .map(|(from, to)| (from.clone(), ChcExpr::var(to.clone())))
                    .collect();
                if head_subst.is_empty() {
                    interp.formula
                } else {
                    // Alpha-rename free body vars that collide with target
                    // shared_vars names before renaming head vars.
                    let head_var_names: FxHashSet<&str> =
                        interp.vars.iter().map(|v| v.name.as_str()).collect();
                    let target_names: FxHashSet<&str> =
                        sv.iter().map(|v| v.name.as_str()).collect();
                    let mut alpha_subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
                    for fv in interp.formula.vars() {
                        if head_var_names.contains(fv.name.as_str()) {
                            continue;
                        }
                        if target_names.contains(fv.name.as_str()) {
                            let fresh =
                                ChcVar::new(format!("_bt{}_{}", def_idx, fv.name), fv.sort.clone());
                            alpha_subst.push((fv, ChcExpr::var(fresh)));
                        }
                    }
                    let formula = if alpha_subst.is_empty() {
                        interp.formula
                    } else {
                        interp.formula.substitute(&alpha_subst)
                    };
                    formula.substitute(&head_subst)
                }
            } else {
                interp.formula
            };
            disjuncts.push(Arc::new(formula));
        }
        let vars = shared_vars?;
        let formula = if disjuncts.len() == 1 {
            Arc::unwrap_or_clone(disjuncts.pop().unwrap())
        } else {
            ChcExpr::Op(ChcOp::Or, disjuncts)
        };
        let allowed: FxHashSet<ChcVar> = vars.iter().cloned().collect();
        if !Self::vars_are_closed(&formula, &allowed) {
            return None;
        }
        Some(PredicateInterpretation::new(vars, formula))
    }

    /// Remap witness PredicateIds from compacted space to original space.
    fn remap_witness(
        witness: ValidityWitness,
        new_to_old: &FxHashMap<PredicateId, PredicateId>,
    ) -> ValidityWitness {
        let mut remapped = ValidityWitness::new();
        remapped.verification_method = witness.verification_method;
        for (new_id, interp) in witness.iter() {
            let old_id = new_to_old.get(new_id).copied().unwrap_or(*new_id);
            remapped.set(old_id, interp.clone());
        }
        remapped
    }

    // ======================================================================
    // Derivation-chain expansion (#chc25-deriv-expansion).
    //
    // A surviving *composite* clause is one built by `apply_defs_tracked` inlining a
    // chain of INPUT clauses into a single clause. When the engine refutes with
    // it, the derivation witness has ONE entry per composite step; to replay on
    // the input clauses, that entry must expand into the chain of input-clause
    // applications with the intermediate predicate states. The recorded
    // `ClauseTrace` supplies exactly what is needed; the intermediate values
    // are read from the composite entry's fresh-variable `instances` (the
    // engine SAT model already pinned them). Every reconstructed entry is
    // re-validated by `PdrSolver::verify_counterexample` against the ORIGINAL
    // clauses — a wrong/stale reconstruction can only produce Spurious/Unknown,
    // never a wrong `unsat`.
    // ======================================================================

    /// Expand every composite derivation entry in place.
    fn expand_composite_entries(
        &self,
        derivation: &mut DerivationWitness,
        engine_incoming: &[Option<usize>],
    ) {
        let original_len = derivation.entries.len();
        // Collect (entry index, engine clause index) for expandable entries
        // up front to avoid aliasing the entries vec while we push to it.
        let mut todo: Vec<(usize, usize)> = Vec::new();
        for (entry_idx, incoming) in engine_incoming.iter().enumerate().take(original_len) {
            if let Some(clause_idx) = incoming {
                if let Some(trace) = self.composition_traces.get(clause_idx) {
                    if trace.is_composite() {
                        todo.push((entry_idx, *clause_idx));
                    }
                }
            }
        }

        for (entry_idx, clause_idx) in todo {
            let Some(trace) = self.composition_traces.get(&clause_idx) else {
                continue;
            };
            Self::expand_one_entry(derivation, entry_idx, trace);
        }
    }

    /// Reconstruct the derivation chain for one composite entry.
    ///
    /// Builds the intermediate entries in a scratch buffer; on any uncertainty
    /// (unevaluable argument, missing stable clause index, ambiguous surviving
    /// premise) it FAILS CLOSED, leaving the entry untouched so content
    /// re-resolution / fail-closed Unknown handles it.
    fn expand_one_entry(derivation: &mut DerivationWitness, entry_idx: usize, trace: &ClauseTrace) {
        let Some(original_clause) = trace.original_clause.as_ref() else {
            return;
        };
        // The composite entry must be the head of C₀ (both in input space now).
        if original_clause.head.predicate_id() != Some(derivation.entries[entry_idx].predicate) {
            return;
        }

        // Value environment for the intermediate predicates. The engine model
        // does NOT reliably retain the collapsed fresh-variable assignments in
        // the composite entry's `instances` (a fact-collapse keeps only the
        // head canonical value), so we RECOVER them by SMT-solving the
        // composite clause's constraint with the surviving endpoint pinned to
        // the engine's head value. The constraint transitively determines every
        // intermediate, and any satisfying assignment is a genuine derivation
        // that the kernel re-validates — fail closed if unrecoverable.
        let Some(env) = Self::recover_composite_env(trace, &derivation.entries[entry_idx]) else {
            return;
        };

        // Surviving (non-inlined) body predicates draw their premise from the
        // composite entry's existing premises, consumed in traversal order.
        let mut leaf_queue: std::collections::VecDeque<usize> = derivation.entries[entry_idx]
            .premises
            .iter()
            .copied()
            .collect();

        let mut scratch: Vec<ScratchEntry> = Vec::new();
        let Some(new_premises) = Self::reconstruct_body(
            &original_clause.body.predicates,
            &env,
            trace,
            &mut scratch,
            &mut leaf_queue,
        ) else {
            return; // fail closed — leave the entry unchanged
        };

        // Commit: splice the scratch entries into the witness, converting local
        // premise references to absolute indices.
        let offset = derivation.entries.len();
        let resolve = |r: &PremiseRef| -> usize {
            match r {
                PremiseRef::Existing(i) => *i,
                PremiseRef::Local(k) => offset + k,
            }
        };
        for se in &scratch {
            let premises: Vec<usize> = se.premises.iter().map(resolve).collect();
            derivation.entries.push(DerivationWitnessEntry {
                predicate: se.predicate,
                level: se.level,
                state: se.state.clone(),
                incoming_clause: se.incoming_clause,
                premises,
                instances: se.instances.clone(),
            });
        }

        let comp = &mut derivation.entries[entry_idx];
        comp.premises = new_premises.iter().map(resolve).collect();
        // Re-point the composite head at C₀ (input-space index; downstream
        // condense/pc_split back-translators carry it to an original clause).
        comp.incoming_clause = Some(trace.c0_input_index);
    }

    /// Reconstruct the premise list for a clause body, recursing into inlined
    /// predicates and drawing surviving ones from `leaf_queue`.
    fn reconstruct_body(
        body_preds: &[(PredicateId, Vec<ChcExpr>)],
        env: &FxHashMap<String, SmtValue>,
        trace: &ClauseTrace,
        scratch: &mut Vec<ScratchEntry>,
        leaf_queue: &mut std::collections::VecDeque<usize>,
    ) -> Option<Vec<PremiseRef>> {
        let mut refs = Vec::with_capacity(body_preds.len());
        for (bp, _args) in body_preds {
            if let Some(step) = trace.steps.get(bp) {
                refs.push(Self::build_reconstructed_entry(
                    *bp, step, env, trace, scratch, leaf_queue,
                )?);
            } else {
                // Surviving body predicate: take the composite entry's next
                // existing premise. Fail closed if none remain.
                refs.push(PremiseRef::Existing(leaf_queue.pop_front()?));
            }
        }
        Some(refs)
    }

    /// Build one reconstructed intermediate entry for `bp`, recursing into its
    /// defining clause body. Returns a scratch-local premise reference.
    fn build_reconstructed_entry(
        bp: PredicateId,
        step: &CompositionStep,
        env: &FxHashMap<String, SmtValue>,
        trace: &ClauseTrace,
        scratch: &mut Vec<ScratchEntry>,
        leaf_queue: &mut std::collections::VecDeque<usize>,
    ) -> Option<PremiseRef> {
        let head_args = match &step.def_clause.head {
            ClauseHead::Predicate(_, args) => args,
            ClauseHead::False => return None,
        };
        if head_args.len() != step.call_args.len() {
            return None;
        }

        // Read this predicate's argument values from the composite model and
        // build its canonical state + instances.
        let mut state_conj: Vec<ChcExpr> = Vec::with_capacity(head_args.len());
        let mut instances: FxHashMap<String, SmtValue> = FxHashMap::default();
        for (k, (call_arg, head_arg)) in step.call_args.iter().zip(head_args.iter()).enumerate() {
            let value = Self::eval_arg(call_arg, env)?;
            let sort = head_arg.sort();
            let value_expr = Self::value_to_expr(&value, &sort)?;
            let cname = format!("__p{}_a{}", bp.index(), k);
            state_conj.push(ChcExpr::eq(
                ChcExpr::var(ChcVar::new(cname.clone(), sort.clone())),
                value_expr,
            ));
            instances.insert(cname, value);
        }
        let state = ChcExpr::and_all(state_conj);

        // Recurse into the defining clause body BEFORE pushing this entry so
        // deeper entries get lower scratch indices (any order is acyclic).
        let premises = Self::reconstruct_body(
            &step.def_clause.body.predicates,
            env,
            trace,
            scratch,
            leaf_queue,
        )?;

        // Incoming clause: a transition entry MUST have a stable input index so
        // it routes through the transition-replay path; a fact entry may fall
        // back to axiom-as-fact (None) when no stable index was recorded.
        let incoming_clause = if step.def_clause.body.predicates.is_empty() {
            step.def_input_index
        } else {
            Some(step.def_input_index?)
        };

        let local_idx = scratch.len();
        scratch.push(ScratchEntry {
            predicate: bp,
            level: 0,
            state,
            incoming_clause,
            premises,
            instances,
        });
        Some(PremiseRef::Local(local_idx))
    }

    /// Recover the composite clause's full variable assignment (including the
    /// collapsed fresh intermediates) by SMT-solving its constraint with the
    /// surviving endpoint pinned to the engine's head value.
    ///
    /// Soundness: this only PROPOSES intermediate values; the reconstructed
    /// chain is re-validated per-entry by the counterexample kernel. Any
    /// satisfying assignment corresponds to a genuine derivation of the head.
    fn recover_composite_env(
        trace: &ClauseTrace,
        entry: &DerivationWitnessEntry,
    ) -> Option<FxHashMap<String, SmtValue>> {
        let composite = trace.composite_clause.as_ref()?;
        let head_args = match &composite.head {
            ClauseHead::Predicate(_, args) => args,
            ClauseHead::False => return None,
        };
        let mut conjuncts: Vec<ChcExpr> = Vec::new();
        if let Some(c) = &composite.body.constraint {
            conjuncts.push(c.clone());
        }
        // Pin the surviving head arguments to the engine's canonical values.
        let mut pinned_any = false;
        for (k, head_arg) in head_args.iter().enumerate() {
            let cname = format!("__p{}_a{}", entry.predicate.index(), k);
            if let Some(value) = entry.instances.get(&cname) {
                let sort = head_arg.sort();
                let value_expr = Self::value_to_expr(value, &sort)?;
                conjuncts.push(ChcExpr::eq(head_arg.clone(), value_expr));
                pinned_any = true;
            }
        }
        // Without any endpoint pin the recovered chain would be unanchored.
        if !pinned_any {
            return None;
        }
        let formula = ChcExpr::and_all(conjuncts);
        let mut smt = SmtContext::new();
        smt.get_model(&formula)
    }

    /// Evaluate an argument expression (in composite-clause variable space)
    /// against the composite entry's model instances. Only plain variables and
    /// literals are supported; anything else fails closed (kernel-safe).
    fn eval_arg(expr: &ChcExpr, env: &FxHashMap<String, SmtValue>) -> Option<SmtValue> {
        match expr {
            ChcExpr::Var(v) => env.get(&v.name).cloned(),
            ChcExpr::Int(i) => Some(SmtValue::Int(*i)),
            ChcExpr::Bool(b) => Some(SmtValue::Bool(*b)),
            ChcExpr::BitVec(v, w) => Some(SmtValue::BitVec(*v, *w)),
            _ => None,
        }
    }

    /// Convert a concrete model value to a typed literal expression.
    fn value_to_expr(value: &SmtValue, sort: &ChcSort) -> Option<ChcExpr> {
        match (sort, value) {
            (ChcSort::Int, SmtValue::Int(i)) => Some(ChcExpr::int(*i)),
            (ChcSort::Bool, SmtValue::Bool(b)) => Some(ChcExpr::Bool(*b)),
            (ChcSort::Bool, SmtValue::Int(i)) => Some(ChcExpr::Bool(*i != 0)),
            (ChcSort::BitVec(w), SmtValue::BitVec(v, vw)) if w == vw => {
                Some(ChcExpr::BitVec(*v, *w))
            }
            _ => None,
        }
    }
}

/// A reconstructed derivation entry awaiting commit into the witness. Premise
/// references are kept symbolic (local vs. pre-existing) until splice time.
struct ScratchEntry {
    predicate: PredicateId,
    level: usize,
    state: ChcExpr,
    incoming_clause: Option<usize>,
    premises: Vec<PremiseRef>,
    instances: FxHashMap<String, SmtValue>,
}

/// Premise reference used while reconstructing, before absolute indices are known.
enum PremiseRef {
    /// Index into the existing `derivation.entries` (a surviving leaf premise).
    Existing(usize),
    /// Index into the scratch buffer (a freshly reconstructed entry).
    Local(usize),
}

impl BackTranslator for InliningBackTranslator {
    fn translate_ground_derivation(
        &self,
        derivation: &crate::ground_derivation::GroundDerivation,
    ) -> Option<crate::ground_derivation::GroundDerivation> {
        self.translate_ground(derivation)
    }

    fn ground_translation_name(&self) -> &'static str {
        "clause-inliner"
    }

    fn translate_validity(&self, mut witness: ValidityWitness) -> ValidityWitness {
        // Step 1: Remap engine witness from compacted IDs to original IDs.
        // The engine produced interpretations keyed by new (compacted) PredicateIds;
        // we need them keyed by original IDs for back-translation to work.
        if !self.new_to_old.is_empty() {
            witness = Self::remap_witness(witness, &self.new_to_old);
        }

        // Step 2: Synthesize interpretations for inlined predicates.
        // inlined_defs uses original PredicateIds, so after remapping the
        // engine witness, all IDs are in the original space.
        let profile = accept_profile_enabled();
        let t_total = ay_core::time::Instant::now();
        let grouped = Self::group_defs_by_predicate(&self.inlined_defs);
        let mut changed = true;
        while changed {
            changed = false;
            for (pred_id, clauses) in &grouped {
                if witness.get(pred_id).is_some() {
                    continue;
                }

                let t_pred = ay_core::time::Instant::now();
                let synthesized = if clauses.len() == 1 {
                    Self::synthesize_interpretation(clauses[0], &witness)
                } else {
                    Self::synthesize_disjunctive(clauses, &witness)
                };
                if profile {
                    safe_eprintln!(
                        "[ACCEPT-PROF] synth pred=P{} defs={} dt={:.3}s ok={} out_nodes={}",
                        pred_id.index(),
                        clauses.len(),
                        t_pred.elapsed().as_secs_f64(),
                        synthesized.is_some(),
                        synthesized
                            .as_ref()
                            .map(|i| i.formula.node_count(1_000_000))
                            .unwrap_or(0)
                    );
                }

                if let Some(interp) = synthesized {
                    witness.set(*pred_id, interp);
                    changed = true;
                }
            }
        }
        if profile {
            safe_eprintln!(
                "[ACCEPT-PROF] translate_validity(inlining) done defs={} dt={:.3}s",
                self.inlined_defs.len(),
                t_total.elapsed().as_secs_f64()
            );
        }
        witness
    }

    fn translate_invalidity(&self, mut witness: InvalidityWitness) -> InvalidityWitness {
        // Counterexamples don't need predicate interpretation synthesis, but
        // derivation witnesses carry engine-space metadata that must be
        // remapped to the original problem before original-clause replay
        // (FM2b: heap__swaparray-class rejections):
        //
        // 1. Predicate IDs: compaction renumbers surviving predicates.
        //    `new_to_old` maps engine IDs back to original IDs.
        // 2. Canonical variable names: `__p{idx}_a{k}` embeds the predicate
        //    index, so instance keys and state vars are renamed alongside.
        // 3. Clause indices: inlining changes the clause list, so engine
        //    clause indices do not address the original clause list. They are
        //    left in place; `PdrSolver::verify_counterexample` re-resolves
        //    clauses by content when the indexed clause does not match the
        //    entry structurally.
        if self.new_to_old.is_empty() && self.composition_traces.is_empty() {
            return witness;
        }

        let remap = |pred: PredicateId| -> PredicateId {
            self.new_to_old.get(&pred).copied().unwrap_or(pred)
        };
        let rename = |name: &str| -> Option<String> {
            // Canonical names look like `__p{idx}_a{k}`.
            let rest = name.strip_prefix("__p")?;
            let (idx_str, suffix) = rest.split_once("_a")?;
            let idx: u32 = idx_str.parse().ok()?;
            let old = self.new_to_old.get(&PredicateId::new(idx))?;
            Some(format!("__p{}_a{}", old.index(), suffix))
        };

        for step in &mut witness.steps {
            step.predicate = remap(step.predicate);
            // Engine-space clause index; meaningless on the original list.
            step.clause_index = None;
            let assignments = std::mem::take(&mut step.assignments);
            step.assignments = assignments
                .into_iter()
                .map(|(name, value)| (rename(&name).unwrap_or(name), value))
                .collect();
        }

        if let Some(derivation) = &mut witness.witness {
            // Capture engine-space (compacted) incoming clause indices BEFORE
            // nulling — used to look up the per-clause composition trace for
            // derivation-chain expansion (#chc25-deriv-expansion).
            let engine_incoming: Vec<Option<usize>> = derivation
                .entries
                .iter()
                .map(|e| e.incoming_clause)
                .collect();

            for entry in &mut derivation.entries {
                entry.predicate = remap(entry.predicate);

                // Engine-space derivation clause index; like `step.clause_index`
                // above it does NOT address the original clause list once
                // inlining has renumbered/composed clauses. Null it so the
                // premise-head-alignment helper skips (returns None on a `None`
                // incoming_clause, `cex_entries.rs`) and downstream index-
                // remapping back-translators (condense, pc_split) do not remap a
                // wrong-space index — forcing the content-re-resolution path
                // (FM2b `entry_clause_matches`) that this translator's contract
                // documents. Leaving it populated made the premise-alignment
                // path dereference an unrelated original clause and reject a
                // genuine counterexample as Spurious (SLayerCF towers). Sound:
                // this can only turn a false-Spurious into a correct verify or
                // a fail-closed Unknown, never a wrong verdict.
                //
                // Composite entries are re-pointed by the expansion pass below;
                // for non-composite entries this nulling is the retained co-fix.
                entry.incoming_clause = None;

                let instances = std::mem::take(&mut entry.instances);
                entry.instances = instances
                    .into_iter()
                    .map(|(name, value)| (rename(&name).unwrap_or(name), value))
                    .collect();

                let state_subst: Vec<(ChcVar, ChcExpr)> = entry
                    .state
                    .vars()
                    .into_iter()
                    .filter_map(|var| {
                        let renamed = rename(&var.name)?;
                        let new_var = ChcVar::new(renamed, var.sort.clone());
                        Some((var, ChcExpr::Var(new_var)))
                    })
                    .collect();
                if !state_subst.is_empty() {
                    entry.state = entry.state.substitute(&state_subst);
                }
            }

            // Derivation-chain expansion: replace each collapsed composite entry
            // with the reconstructed chain of input-clause entries so the
            // bounded refutation replays on the original clauses. Only OFFERS a
            // chain; the SMT counterexample kernel re-validates every entry.
            if deriv_expansion_enabled() && !self.composition_traces.is_empty() {
                self.expand_composite_entries(derivation, &engine_incoming);
            }
        }

        witness
    }

    fn transform_memory(&self) -> TransformMemoryReport {
        TransformMemoryReport::with_original_validation_obligations(
            "clause_inlining",
            [
                TransformObligation::named("synthesized-predicate-interpretations"),
                TransformObligation::named("existential-qe-cap-fail-closed"),
                TransformObligation::named("original-validation-on-safe"),
                TransformObligation::named("original-replay-on-unsafe"),
            ],
        )
    }
}

// ==========================================================================
// Ground derivation back-translation (#item4-ground-witness-backtranslation)
//
// The invalidity path above reconstructs the collapsed chain and then relies
// on the SMT counterexample kernel to re-validate it — including an SMT solve
// (`recover_composite_env`) to recover the intermediate values the engine
// model did not retain. A GROUND derivation needs neither: its step already
// carries a total assignment for the composite clause, which is exactly the
// environment that solve was reaching for, and the reconstructed chain is
// checked by evaluation rather than by search.
// ==========================================================================

/// A reconstructed step before premise indices are made absolute.
struct GroundScratchStep {
    clause_index: usize,
    env: FxHashMap<String, SmtValue>,
    /// Premise references: `Ok(index into the already-emitted output)` for a
    /// surviving premise, `Err(scratch index)` for a reconstructed one.
    premises: Vec<Result<usize, usize>>,
    /// Values the level-BMC model assigned to this defining clause's OWN
    /// variables, read back through the rename the inliner applied and keyed by
    /// the DEF-CLAUSE name. Consulted by environment completion only where it
    /// would otherwise fabricate a sort default, so a variable the original
    /// clause constrains solely through an ITE or a tester still gets the value
    /// the search actually used. Synthesis, never evidence — see
    /// `CompositionStep::var_renames`.
    witness_seed: FxHashMap<String, SmtValue>,
}

impl InliningBackTranslator {
    /// Expand a ground derivation over the INLINED problem into one over the
    /// INPUT problem.
    ///
    /// Each output step either maps 1:1 onto its input clause (nothing was
    /// composed into it) or expands into the chain of input-clause applications
    /// the inliner collapsed. Fails closed on a poisoned trace, a lost clause
    /// alignment, an argument that does not evaluate, or a defining clause with
    /// no stable input index.
    pub(super) fn translate_ground(
        &self,
        derivation: &crate::ground_derivation::GroundDerivation,
    ) -> Option<crate::ground_derivation::GroundDerivation> {
        use crate::ground_derivation::{
            complete::complete_env_for_clause, log_ground_translation_detail,
            validate_ground_derivation, GroundDerivation, GroundDerivationStep,
        };

        let Some(input_problem) = self.input_problem.as_ref() else {
            log_ground_translation_detail(format_args!(
                "clause-inliner: no input problem retained; fail closed"
            ));
            return None;
        };
        let output_to_input = self.output_to_input.as_ref().or_else(|| {
            log_ground_translation_detail(format_args!(
                "clause-inliner: clause alignment was lost (multi-def expansion); fail closed"
            ));
            None
        })?;
        let input_clauses = input_problem.clauses();

        let mut steps: Vec<GroundDerivationStep> = Vec::new();
        // Old step index -> new step index of the step that DERIVES the same
        // fact (the C₀ application, for an expanded step).
        let mut mapped: Vec<usize> = Vec::with_capacity(derivation.steps.len());
        let mut query_step = None;

        for (old_index, step) in derivation.steps.iter().enumerate() {
            let Some(premise_targets) = step
                .premises
                .iter()
                .map(|premise| mapped.get(*premise).copied())
                .collect::<Option<Vec<_>>>()
            else {
                log_ground_translation_detail(format_args!(
                    "clause-inliner: premise of step {old_index} was not mapped; fail closed"
                ));
                return None;
            };

            let trace = self
                .composition_traces
                .get(&step.clause_index)
                .filter(|trace| trace.is_composite());

            let emitted = match trace {
                Some(trace) => {
                    let expanded = Self::expand_ground_step(
                        trace,
                        step,
                        &premise_targets,
                        input_clauses,
                        &mut steps,
                    );
                    let Some(expanded) = expanded else {
                        log_ground_translation_detail(format_args!(
                            "clause-inliner: composite expansion failed for output clause {} \
                             (step {old_index})",
                            step.clause_index
                        ));
                        return None;
                    };
                    expanded
                }
                None => {
                    let Some(input_index) = output_to_input.get(step.clause_index).copied() else {
                        log_ground_translation_detail(format_args!(
                            "clause-inliner: output clause {} has no input index (step {old_index})",
                            step.clause_index
                        ));
                        return None;
                    };
                    let Some(clause) = input_clauses.get(input_index) else {
                        log_ground_translation_detail(format_args!(
                            "clause-inliner: input clause {input_index} out of range"
                        ));
                        return None;
                    };
                    let Some(ordered_premises) = Self::order_surviving_premises(
                        &clause.body.predicates,
                        &premise_targets,
                        &steps,
                        input_clauses,
                    ) else {
                        log_ground_translation_detail(format_args!(
                            "clause-inliner: could not align premises for uncomposed input \
                             clause {input_index} (output step {old_index})"
                        ));
                        return None;
                    };
                    let mut env = step.env.clone();
                    crate::ground_derivation::complete::seed_env_from_premises(
                        clause,
                        &ordered_premises,
                        &steps,
                        input_clauses,
                        &mut env,
                    );
                    if !complete_env_for_clause(clause, &mut env) {
                        log_ground_translation_detail(format_args!(
                            "clause-inliner: could not complete the environment for input \
                             clause {input_index} (output step {old_index})"
                        ));
                        return None;
                    }
                    let emitted = steps.len();
                    steps.push(GroundDerivationStep {
                        clause_index: input_index,
                        env,
                        premises: ordered_premises,
                    });
                    emitted
                }
            };
            if old_index == derivation.query_step {
                query_step = Some(emitted);
            }
            mapped.push(emitted);
        }

        let translated = GroundDerivation {
            steps,
            query_step: query_step?,
        };
        if let Err(err) = validate_ground_derivation(input_problem, &translated) {
            log_ground_translation_detail(format_args!(
                "clause-inliner: expanded derivation does not validate on the input problem ({err})"
            ));
            if crate::ground_derivation::ground_backtranslation_debug() {
                for (step_index, step) in translated.steps.iter().enumerate() {
                    let Some(clause) = input_clauses.get(step.clause_index) else {
                        continue;
                    };
                    let expected: Vec<String> = clause
                        .body
                        .predicates
                        .iter()
                        .map(|(pred, _)| format!("P{}", pred.0))
                        .collect();
                    let actual: Vec<String> = step
                        .premises
                        .iter()
                        .map(|premise| {
                            translated
                                .steps
                                .get(*premise)
                                .and_then(|premise_step| {
                                    input_clauses.get(premise_step.clause_index)
                                })
                                .and_then(|premise_clause| premise_clause.head.predicate_id())
                                .map_or_else(|| "false".to_string(), |pred| format!("P{}", pred.0))
                        })
                        .collect();
                    log_ground_translation_detail(format_args!(
                        "clause-inliner: translated step {step_index} clause={} \
                         expected={expected:?} premises={:?} actual={actual:?}",
                        step.clause_index, step.premises
                    ));
                }
            }
            return None;
        }
        Some(translated)
    }

    /// Expand one composite step into the chain of input-clause steps, pushing
    /// them onto `steps` in topological order. Returns the index of the step
    /// that derives the composite's head (the C₀ application).
    fn expand_ground_step(
        trace: &ClauseTrace,
        step: &crate::ground_derivation::GroundDerivationStep,
        premise_targets: &[usize],
        input_clauses: &[HornClause],
        steps: &mut Vec<crate::ground_derivation::GroundDerivationStep>,
    ) -> Option<usize> {
        use crate::ground_derivation::{
            complete::complete_env_for_clause, log_ground_translation_detail, GroundDerivationStep,
        };

        if trace.poisoned {
            log_ground_translation_detail(format_args!(
                "clause-inliner: trace for output clause is poisoned; fail closed"
            ));
            return None;
        }
        let Some(c0) = trace.original_clause.as_ref() else {
            log_ground_translation_detail(format_args!(
                "clause-inliner: composite trace has no C0 clause; fail closed"
            ));
            return None;
        };
        let Some(c0_clause) = input_clauses.get(trace.c0_input_index) else {
            log_ground_translation_detail(format_args!(
                "clause-inliner: C0 input index {} out of range",
                trace.c0_input_index
            ));
            return None;
        };

        // The composite step's environment covers the SURVIVING clause, but
        // inlining existentially projects the fresh linking variables out of
        // it — those are exactly the values `recover_composite_env` reaches for
        // with an SMT solve on the invalidity path. Recover them by ground
        // propagation over the RETAINED composite clause instead: its linking
        // equalities determine every intermediate from the surviving endpoints.
        // No defaults are filled in here; an intermediate that propagation
        // cannot determine fails the expansion closed rather than naming a
        // different derivation.
        let mut env = step.env.clone();
        if let Some(composite) = trace.composite_clause.as_ref() {
            crate::ground_derivation::complete::propagate_env_for_clause(composite, &mut env);
            // Then rebuild the linking variables the composite clause no longer
            // mentions at all, from the definitions the inliner RECORDED for
            // them at substitution time. Still pure evaluation, no solving.
            Self::recover_linking_defs_ground(composite, trace, &mut env);
            // Finally, the call-site variables the composite dropped entirely:
            // unconstrained by construction, so a sort default is all the
            // expansion needs to stay total.
            Self::default_unconstrained_call_vars(composite, trace, &mut env);
            Self::log_unresolved_linking_defs(trace, &env);
            if !Self::composite_env_covers(composite, trace, &env) {
                if crate::ground_derivation::ground_backtranslation_debug() {
                    let unbound: Vec<String> = Self::composite_env_vars(composite, trace)
                        .into_iter()
                        .filter(|var| !env.contains_key(&var.name))
                        .map(|var| var.name)
                        .collect();
                    log_ground_translation_detail(format_args!(
                        "clause-inliner: {} composite vars still unbound after ground recovery: \
                         {:?}",
                        unbound.len(),
                        &unbound[..unbound.len().min(8)]
                    ));
                    for name in unbound.iter().take(2) {
                        let in_head = composite.head.vars().iter().any(|v| &v.name == name);
                        let in_body_pred: Vec<String> = composite
                            .body
                            .predicates
                            .iter()
                            .filter(|(_, args)| {
                                args.iter()
                                    .any(|a| a.vars().iter().any(|v| &v.name == name))
                            })
                            .map(|(pid, args)| format!("P{}/{}", pid.0, args.len()))
                            .collect();
                        let in_steps: Vec<String> = trace
                            .steps
                            .values()
                            .filter(|s| {
                                s.call_args
                                    .iter()
                                    .any(|a| a.vars().iter().any(|v| &v.name == name))
                            })
                            .map(|s| {
                                format!(
                                    "P{}(def_idx={:?}, defs={})",
                                    s.inlined_pred.0,
                                    s.def_input_index,
                                    s.linking_defs.len()
                                )
                            })
                            .collect();
                        log_ground_translation_detail(format_args!(
                            "clause-inliner:   {name}: in_head={in_head} \
                             body_preds={in_body_pred:?} call_args_of={in_steps:?}"
                        ));
                    }
                }
                // Propagation could not determine every intermediate (the
                // linking constraint routes them through ITEs / disjunctions,
                // not plain equalities). Fall back to a BOUNDED LOCAL solve of
                // this one clause with every known value pinned.
                //
                // This is value RECOVERY, not validation: the recovered values
                // are only a proposal, and the derivation built from them is
                // still decided by pure ground evaluation against the original
                // clauses. The distinction matters — the search this work item
                // removes is a whole-problem unrolling to depth 381; this is a
                // single clause with its endpoints pinned, and if it times out
                // the expansion fails closed.
                Self::recover_composite_env_ground(composite, trace, &mut env);
            }
        }
        let env = &env;
        let mut surviving = premise_targets.to_vec();

        let mut scratch: Vec<GroundScratchStep> = Vec::new();
        let premises = Self::reconstruct_ground_body(
            &c0.body.predicates,
            env,
            trace,
            input_clauses,
            steps,
            &mut scratch,
            &mut surviving,
        )?;
        if !surviving.is_empty() {
            log_ground_translation_detail(format_args!(
                "clause-inliner: {} surviving premises left unconsumed; fail closed",
                surviving.len()
            ));
            return None;
        }

        // Commit the scratch chain first (deepest premises already come first
        // because each entry is pushed after its own body was reconstructed).
        let offset = steps.len();
        for entry in &scratch {
            let clause = input_clauses.get(entry.clause_index)?;
            let mut entry_env = entry.env.clone();
            // Each scratch entry is pushed only after its own body was
            // reconstructed, so every premise it names is already committed and
            // can instantiate this clause's free body-argument variables.
            let entry_premises: Vec<usize> = entry
                .premises
                .iter()
                .map(|premise| match premise {
                    Ok(existing) => *existing,
                    Err(local) => offset + local,
                })
                .collect();
            crate::ground_derivation::complete::seed_env_from_premises(
                clause,
                &entry_premises,
                steps,
                input_clauses,
                &mut entry_env,
            );
            // The witness seed is consulted only where completion would
            // otherwise pick a sort default, and it runs AFTER premise seeding,
            // so a value the derivation's own links determined always wins over
            // a value carried down from the transformed search.
            if !crate::ground_derivation::complete::complete_env_for_clause_with_fallback(
                clause,
                &mut entry_env,
                &entry.witness_seed,
            ) {
                log_ground_translation_detail(format_args!(
                    "clause-inliner: could not complete the environment for reconstructed \
                     input clause {}",
                    entry.clause_index
                ));
                return None;
            }
            steps.push(GroundDerivationStep {
                clause_index: entry.clause_index,
                env: entry_env,
                premises: entry_premises,
            });
        }

        // Finally the C₀ application itself, consuming the reconstructed chain.
        let c0_premises: Vec<usize> = premises
            .iter()
            .map(|premise| match premise {
                Ok(existing) => *existing,
                Err(local) => offset + local,
            })
            .collect();
        let mut c0_env = env.clone();
        crate::ground_derivation::complete::seed_env_from_premises(
            c0_clause,
            &c0_premises,
            steps,
            input_clauses,
            &mut c0_env,
        );
        if !complete_env_for_clause(c0_clause, &mut c0_env) {
            log_ground_translation_detail(format_args!(
                "clause-inliner: could not complete the environment for C0 clause {}",
                trace.c0_input_index
            ));
            return None;
        }
        let emitted = steps.len();
        steps.push(GroundDerivationStep {
            clause_index: trace.c0_input_index,
            env: c0_env,
            premises: c0_premises,
        });
        Some(emitted)
    }

    /// Every variable the expansion needs a value for: the composite clause's
    /// own variables PLUS the call-argument variables of each inlined step.
    ///
    /// The latter matter because inlining can project a fresh linking variable
    /// out of the surviving constraint while the recorded call site still
    /// mentions it — that variable is exactly the one whose value the expansion
    /// needs and the surviving clause no longer determines.
    fn composite_env_vars(composite: &HornClause, trace: &ClauseTrace) -> Vec<ChcVar> {
        let mut vars = composite.body.vars();
        for var in composite.head.vars() {
            if !vars.contains(&var) {
                vars.push(var);
            }
        }
        for step in trace.steps.values() {
            for call_arg in &step.call_args {
                for var in call_arg.vars() {
                    if !vars.contains(&var) {
                        vars.push(var);
                    }
                }
            }
        }
        vars
    }

    /// The composite clause's endpoint variables: bare-variable positions in
    /// its head arguments and in its surviving body-predicate arguments.
    fn composite_endpoint_vars(composite: &HornClause) -> Vec<ChcVar> {
        let mut vars = Vec::new();
        let mut push = |expr: &ChcExpr| {
            if let ChcExpr::Var(var) = expr {
                if !vars.contains(var) {
                    vars.push(var.clone());
                }
            }
        };
        if let ClauseHead::Predicate(_, args) = &composite.head {
            for arg in args {
                push(arg);
            }
        }
        for (_, args) in &composite.body.predicates {
            for arg in args {
                push(arg);
            }
        }
        vars
    }

    /// Whether every variable the expansion needs has a value.
    fn composite_env_covers(
        composite: &HornClause,
        trace: &ClauseTrace,
        env: &FxHashMap<String, SmtValue>,
    ) -> bool {
        Self::composite_env_vars(composite, trace)
            .iter()
            .all(|var| env.contains_key(&var.name))
    }

    /// Rebuild the fresh linking variables inlining projected away, by
    /// EVALUATING the definitions the inliner recorded for them.
    ///
    /// When `apply_defs_tracked` substitutes a definition into a caller it replaces each
    /// head argument by a fresh variable and equates that variable to the call
    /// argument. The surviving clause then existentially projects the fresh
    /// variable away, so a ground derivation over the surviving clause carries
    /// no value for it — yet the recorded call site still names it, and the
    /// expansion needs its value to seed the reconstructed premise. Each such
    /// variable has an exact defining expression in call-site space, so its
    /// value is a matter of evaluation, not of search.
    ///
    /// Runs a FIXPOINT, interleaving the recorded definitions with ordinary
    /// propagation over the retained composite clause: a composition of depth
    /// `n` defines each step's fresh variables in terms of the previous step's,
    /// and either source can unlock the other. Definitions are evaluated in
    /// whatever order they resolve, which is exactly the topological order.
    ///
    /// SOUNDNESS: synthesis only, and never destructive — a variable the
    /// environment already binds is left alone, so a recorded definition can
    /// never displace a value the derivation committed to. Anything that does
    /// not evaluate is simply left unbound, and the caller fails the expansion
    /// closed. Every value produced here is re-checked by
    /// `validate_ground_derivation` against the ORIGINAL clauses.
    pub(super) fn recover_linking_defs_ground(
        composite: &HornClause,
        trace: &ClauseTrace,
        env: &mut FxHashMap<String, SmtValue>,
    ) {
        // A single composition step may introduce one definition per distinct
        // head argument, so the step count is not a sound fixpoint bound. In
        // the worst iteration order each round resolves only one recorded
        // definition; count those definitions directly. The cap is only a
        // completeness guard for pathological traces: unresolved values fail
        // closed (and may take the bounded recovery-solve path).
        let definition_count: usize = trace.steps.values().fold(0usize, |count, step| {
            count.saturating_add(step.linking_defs.len())
        });
        let max_rounds = definition_count.saturating_add(1).clamp(4, 64);
        for _ in 0..max_rounds {
            let mut progressed = false;
            for step in trace.steps.values() {
                for (var, definition) in &step.linking_defs {
                    if env.contains_key(&var.name) {
                        continue;
                    }
                    if let Some(value) = crate::ground_derivation::eval_ground_pub(definition, env)
                    {
                        env.insert(var.name.clone(), value);
                        progressed = true;
                    }
                }
            }
            if !progressed {
                return;
            }
            // A newly recovered linking value can unlock the composite's own
            // equalities, whose results feed the next definition sweep.
            crate::ground_derivation::complete::propagate_env_for_clause(composite, env);
        }
    }

    /// Bind the call-site variables the composite clause does not mention AT
    /// ALL, to their sort defaults.
    ///
    /// Not every linking variable has a defining expression. When a definition
    /// is substituted along the DIRECT path (all head arguments distinct plain
    /// variables, no body locals) the inliner introduces no fresh variable and
    /// adds no linking equality — it substitutes the call arguments straight
    /// into the definition's body. A parameter that definition never uses then
    /// disappears completely: the argument expression is a variable an earlier
    /// step freshened, and after substitution it occurs in NO conjunct, NO
    /// surviving body-predicate argument, and NO head argument of the composite
    /// clause. The recorded call site is the only place left that names it.
    ///
    /// Such a variable is by construction UNCONSTRAINED — the composite clause
    /// holds for every value of it — so there is nothing to recover and nothing
    /// to solve for; the expansion just needs SOME value to keep the
    /// reconstructed step total. A sort default is the same choice
    /// `complete_env_for_clause` already makes for a clause's own unconstrained
    /// variables, which is what makes the two sides AGREE: the consumer step
    /// defaults its unused body-local to the identical value, so the
    /// premise/consumer argument check sees one value, not two.
    ///
    /// The criterion is deliberately narrow — occurring nowhere in the
    /// composite clause is a syntactic proof that no constraint can pin the
    /// variable. A variable the composite DOES mention is never defaulted here;
    /// if propagation could not determine it, it falls through to the bounded
    /// solve and then fails closed, exactly as before.
    ///
    /// SOUNDNESS: unchanged. A default is a proposal like every other value the
    /// recovery synthesizes; if it is wrong for the original clauses, the
    /// constraint it violates evaluates to `false` and
    /// `validate_ground_derivation` REJECTS the whole expansion.
    pub(super) fn default_unconstrained_call_vars(
        composite: &HornClause,
        trace: &ClauseTrace,
        env: &mut FxHashMap<String, SmtValue>,
    ) {
        let mentioned = composite.vars();
        for var in Self::composite_env_vars(composite, trace) {
            if env.contains_key(&var.name) || mentioned.iter().any(|v| v.name == var.name) {
                continue;
            }
            let Some(default) = crate::ground_derivation::complete::sort_default(&var.sort) else {
                continue;
            };
            crate::ground_derivation::log_ground_translation_detail(format_args!(
                "clause-inliner: {} occurs nowhere in the composite clause (unconstrained); \
                 taking its sort default",
                var.name
            ));
            env.insert(var.name, default);
        }
    }

    /// Debug-only: report which linking definitions the fixpoint could not
    /// evaluate, and why (the variables their right-hand sides still need).
    fn log_unresolved_linking_defs(trace: &ClauseTrace, env: &FxHashMap<String, SmtValue>) {
        if !crate::ground_derivation::ground_backtranslation_debug() {
            return;
        }
        let mut recorded = 0usize;
        let mut unresolved: Vec<String> = Vec::new();
        for step in trace.steps.values() {
            for (var, definition) in &step.linking_defs {
                recorded += 1;
                if env.contains_key(&var.name) {
                    continue;
                }
                let missing: Vec<String> = definition
                    .vars()
                    .into_iter()
                    .filter(|v| !env.contains_key(&v.name))
                    .map(|v| v.name)
                    .collect();
                unresolved.push(format!("{} <- needs {:?}", var.name, missing));
            }
        }
        crate::ground_derivation::log_ground_translation_detail(format_args!(
            "clause-inliner: linking definitions recorded {recorded}, unresolved {}: {:?}",
            unresolved.len(),
            &unresolved[..unresolved.len().min(8)]
        ));
    }

    /// Fill the remaining composite-clause variables with a bounded local SMT
    /// solve, pinning every value already known.
    ///
    /// Merges only variables the environment does not already bind, so a
    /// recovered value can never displace one that came from the derivation.
    fn recover_composite_env_ground(
        composite: &HornClause,
        trace: &ClauseTrace,
        env: &mut FxHashMap<String, SmtValue>,
    ) {
        /// Wall-clock cap for the per-clause recovery solve.
        const RECOVERY_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(5);
        /// Per-polarity cap when completing a Boolean call argument omitted
        /// from a partial SMT model.
        const FORCED_BOOL_TIMEOUT: std::time::Duration = std::time::Duration::from_millis(250);

        let mut conjuncts: Vec<ChcExpr> = Vec::new();
        if let Some(constraint) = &composite.body.constraint {
            conjuncts.push(constraint.clone());
        }
        // Re-add each inlined definition's own constraint, with its head
        // arguments unified to the call arguments. This is the UNPROJECTED
        // composite: the inliner's existential projection is what erased the
        // linking variables, so restoring the definitions restores exactly the
        // equalities that determine them.
        for step in trace.steps.values() {
            if let ClauseHead::Predicate(_, head_args) = &step.def_clause.head {
                for (head_arg, call_arg) in head_args.iter().zip(step.call_args.iter()) {
                    conjuncts.push(ChcExpr::eq(head_arg.clone(), call_arg.clone()));
                }
            }
            if let Some(constraint) = &step.def_clause.body.constraint {
                conjuncts.push(constraint.clone());
            }
        }
        let needed = Self::composite_env_vars(composite, trace);
        // Pin only the ENDPOINTS — the composite's head and body-predicate
        // argument variables. Pinning every known variable over-constrains the
        // solve: the environment arriving here was itself reconstructed by the
        // downstream passes, so a value that is merely PLAUSIBLE for a sliced
        // or defaulted variable can contradict the composite's exact semantics
        // and make the recovery formula unsatisfiable. The endpoints are the
        // values the derivation actually commits to.
        let endpoints = Self::composite_endpoint_vars(composite);
        let mut pinned = 0usize;
        for var in endpoints.iter().cloned() {
            let Some(value) = env.get(&var.name) else {
                continue;
            };
            let Some(value_expr) = Self::value_to_expr(value, &var.sort) else {
                continue;
            };
            conjuncts.push(ChcExpr::eq(ChcExpr::var(var), value_expr));
            pinned += 1;
        }
        if pinned == 0 || conjuncts.is_empty() {
            return;
        }
        let formula = ChcExpr::and_all(conjuncts);
        let mut smt = SmtContext::new();
        let SmtResult::Sat(model) = smt.check_sat_with_timeout(&formula, RECOVERY_TIMEOUT) else {
            crate::ground_derivation::log_ground_translation_detail(format_args!(
                "clause-inliner: bounded composite-env recovery did not return a model"
            ));
            return;
        };
        for var in needed {
            if env.contains_key(&var.name) {
                continue;
            }
            if let Some(value) = model.get(&var.name) {
                env.insert(var.name, value.clone());
            }
        }

        // The SMT layer is allowed to return a PARTIAL model.  In particular,
        // a Boolean fixed only through a short implication chain may be absent
        // even though the restored composite formula forces its value.  Such a
        // variable can still occur in an inlined predicate's call arguments,
        // where reconstruction must evaluate it to seed the original head.
        //
        // Complete only missing Boolean CALL variables, and only when the two
        // polarities prove uniqueness: F /\ v SAT and F /\ !v UNSAT (or the
        // converse).  If both are possible, either is Unknown, or the sort is
        // not Boolean, leave the variable unbound so expansion fails closed.
        // The proposed value is additionally checked by the full translated
        // derivation validation below.
        let mut call_vars: Vec<ChcVar> = Vec::new();
        for step in trace.steps.values() {
            for call_arg in &step.call_args {
                for var in call_arg.vars() {
                    if !call_vars.contains(&var) {
                        call_vars.push(var);
                    }
                }
            }
        }
        call_vars.sort();
        for var in call_vars {
            if env.contains_key(&var.name) || var.sort != ChcSort::Bool {
                continue;
            }
            let Some(value) = Self::uniquely_forced_bool_value(&formula, &var, FORCED_BOOL_TIMEOUT)
            else {
                continue;
            };
            crate::ground_derivation::log_ground_translation_detail(format_args!(
                "clause-inliner: recovered uniquely forced Boolean call argument {}={value:?}",
                var.name
            ));
            env.insert(var.name, value);
        }
    }

    /// Return a Boolean value only when `formula` permits exactly one polarity.
    ///
    /// This is deliberately not model completion by convention: an omitted
    /// Boolean whose two polarities are both satisfiable remains absent.  Each
    /// query is bounded, and any Unknown fails closed.
    pub(super) fn uniquely_forced_bool_value(
        formula: &ChcExpr,
        var: &ChcVar,
        timeout: std::time::Duration,
    ) -> Option<SmtValue> {
        if var.sort != ChcSort::Bool {
            return None;
        }
        let atom = ChcExpr::var(var.clone());
        let mut positive_smt = SmtContext::new();
        let positive = positive_smt
            .check_sat_with_timeout(&ChcExpr::and(formula.clone(), atom.clone()), timeout);
        let mut negative_smt = SmtContext::new();
        let negative = negative_smt
            .check_sat_with_timeout(&ChcExpr::and(formula.clone(), ChcExpr::not(atom)), timeout);
        match (positive, negative) {
            (SmtResult::Sat(_), negative) if negative.is_unsat() => Some(SmtValue::Bool(true)),
            (positive, SmtResult::Sat(_)) if positive.is_unsat() => Some(SmtValue::Bool(false)),
            _ => None,
        }
    }

    /// Remove the unique available premise whose translated input clause
    /// derives `body_pred`.
    ///
    /// Predicate identity is only an ordering key. Multiple matches are
    /// ambiguous (the calls may carry different arguments), so they fail
    /// closed; the final full derivation validation checks all argument links.
    fn take_surviving_premise(
        body_pred: PredicateId,
        surviving: &mut Vec<usize>,
        emitted_steps: &[crate::ground_derivation::GroundDerivationStep],
        input_clauses: &[HornClause],
    ) -> Option<usize> {
        let matching: Vec<usize> = surviving
            .iter()
            .enumerate()
            .filter_map(|(position, premise)| {
                let premise_head = emitted_steps
                    .get(*premise)
                    .and_then(|premise_step| input_clauses.get(premise_step.clause_index))
                    .and_then(|premise_clause| premise_clause.head.predicate_id());
                (premise_head == Some(body_pred)).then_some(position)
            })
            .collect();
        if matching.len() != 1 {
            crate::ground_derivation::log_ground_translation_detail(format_args!(
                "clause-inliner: expected one surviving premise for body predicate \
                 {body_pred:?}, found {}; fail closed",
                matching.len()
            ));
            return None;
        }
        Some(surviving.remove(matching[0]))
    }

    /// Order translated premises exactly as an input clause's body.
    fn order_surviving_premises(
        body_preds: &[(PredicateId, Vec<ChcExpr>)],
        premises: &[usize],
        emitted_steps: &[crate::ground_derivation::GroundDerivationStep],
        input_clauses: &[HornClause],
    ) -> Option<Vec<usize>> {
        let mut surviving = premises.to_vec();
        let ordered = body_preds
            .iter()
            .map(|(body_pred, _)| {
                Self::take_surviving_premise(
                    *body_pred,
                    &mut surviving,
                    emitted_steps,
                    input_clauses,
                )
            })
            .collect::<Option<Vec<_>>>()?;
        if !surviving.is_empty() {
            crate::ground_derivation::log_ground_translation_detail(format_args!(
                "clause-inliner: {} translated premises were not consumed; fail closed",
                surviving.len()
            ));
            return None;
        }
        Some(ordered)
    }

    /// Reconstruct premise references for a clause body, recursing into inlined
    /// predicates and matching each surviving premise by its translated input
    /// head. The inliner's stack may reorder output body predicates, so output
    /// premise position is not an input-space correspondence.
    fn reconstruct_ground_body(
        body_preds: &[(PredicateId, Vec<ChcExpr>)],
        env: &FxHashMap<String, SmtValue>,
        trace: &ClauseTrace,
        input_clauses: &[HornClause],
        emitted_steps: &[crate::ground_derivation::GroundDerivationStep],
        scratch: &mut Vec<GroundScratchStep>,
        surviving: &mut Vec<usize>,
    ) -> Option<Vec<Result<usize, usize>>> {
        let mut refs = Vec::with_capacity(body_preds.len());
        for (body_pred, _) in body_preds {
            match trace.steps.get(body_pred) {
                Some(step) => refs.push(Err(Self::reconstruct_ground_step(
                    step,
                    env,
                    trace,
                    input_clauses,
                    emitted_steps,
                    scratch,
                    surviving,
                )?)),
                None => {
                    let existing = Self::take_surviving_premise(
                        *body_pred,
                        surviving,
                        emitted_steps,
                        input_clauses,
                    )?;
                    refs.push(Ok(existing));
                }
            }
        }
        Some(refs)
    }

    /// Build one reconstructed step for an inlined predicate application.
    fn reconstruct_ground_step(
        step: &CompositionStep,
        env: &FxHashMap<String, SmtValue>,
        trace: &ClauseTrace,
        input_clauses: &[HornClause],
        emitted_steps: &[crate::ground_derivation::GroundDerivationStep],
        scratch: &mut Vec<GroundScratchStep>,
        surviving: &mut Vec<usize>,
    ) -> Option<usize> {
        let Some(def_index) = step.def_input_index else {
            crate::ground_derivation::log_ground_translation_detail(format_args!(
                "clause-inliner: inlined definition has no stable input index; fail closed"
            ));
            return None;
        };
        let def_clause = input_clauses.get(def_index)?;
        let ClauseHead::Predicate(_, head_args) = &def_clause.head else {
            return None;
        };
        if head_args.len() != step.call_args.len() {
            crate::ground_derivation::log_ground_translation_detail(format_args!(
                "clause-inliner: call/head arity mismatch ({} vs {}) for input clause {def_index}",
                step.call_args.len(),
                head_args.len()
            ));
            return None;
        }

        // Seed the defining clause's environment from the call site: every head
        // argument that is a bare variable takes the value the composite clause
        // passed for it. The rest is recovered by ground propagation over the
        // defining clause's own constraint.
        let mut seed: FxHashMap<String, SmtValue> = FxHashMap::default();
        for (call_arg, head_arg) in step.call_args.iter().zip(head_args.iter()) {
            let Some(value) = crate::ground_derivation::eval_ground_pub(call_arg, env) else {
                let missing: Vec<String> = call_arg
                    .vars()
                    .into_iter()
                    .filter(|var| !env.contains_key(&var.name))
                    .map(|var| var.name)
                    .collect();
                crate::ground_derivation::log_ground_translation_detail(format_args!(
                    "clause-inliner: call argument for input clause {def_index} does not \
                     evaluate in the composite environment; unbound {missing:?}"
                ));
                return None;
            };
            if let ChcExpr::Var(var) = head_arg {
                seed.entry(var.name.clone()).or_insert(value);
            }
        }

        // Everything the call arguments do NOT pin — the definition's
        // BODY-LOCALS above all — is read back out of the composite environment
        // through the rename the inliner recorded. The composite step's
        // environment is TOTAL for the composite clause (the level model
        // assigns every clause variable, not just the argument positions), so a
        // variable the original clause constrains only through an ITE, a tester
        // or a disjunction still has the value the search used. Without this
        // the completion sort-defaults it and falsifies the very conjunct the
        // counterexample satisfied.
        //
        // Keyed by the DEF-CLAUSE name (the rename's left-hand side), because
        // that is the variable space the reconstructed step is evaluated in.
        let mut witness_seed: FxHashMap<String, SmtValue> = FxHashMap::default();
        for (def_name, composite_expr) in &step.var_renames {
            if seed.contains_key(def_name) {
                continue;
            }
            if let Some(value) = crate::ground_derivation::eval_ground_pub(composite_expr, env) {
                witness_seed.insert(def_name.clone(), value);
            }
        }

        let premises = Self::reconstruct_ground_body(
            &def_clause.body.predicates,
            env,
            trace,
            input_clauses,
            emitted_steps,
            scratch,
            surviving,
        )?;

        let local = scratch.len();
        scratch.push(GroundScratchStep {
            clause_index: def_index,
            env: seed,
            premises,
            witness_seed,
        });
        Some(local)
    }
}
