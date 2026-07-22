// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LemmaHintProvider implementation for parametric multiplication hints.
//!
//! Collects invariant hints from query guard patterns involving multiplication
//! by a constant (e.g., `B >= k*C`). Helper methods for pattern parsing and
//! predecessor propagation are in `parametric_mul.rs`.

use super::parametric_mul::ParametricMultiplicationProvider;
use super::*;

impl LemmaHintProvider for ParametricMultiplicationProvider {
    fn collect(&self, req: &HintRequest<'_>, out: &mut Vec<LemmaHint>) {
        // Query analysis is deterministic and cheap; validate via the usual inductiveness check.
        if req.stage != HintStage::Startup {
            return;
        }

        for query in req.problem.queries() {
            let Some(constraint) = &query.body.constraint else {
                continue;
            };

            let mut occurrences = Vec::new();
            Self::collect_mul_guard_occurrences(constraint, false, &mut occurrences);
            if occurrences.is_empty() {
                continue;
            }

            // Collect `A >= C` guards for phase-difference hints
            let mut ge_guards = Vec::new();
            Self::collect_ge_var_var_guards(constraint, false, &mut ge_guards);

            if query.body.predicates.len() != 1 {
                continue;
            }

            for (pred_id, body_args) in &query.body.predicates {
                let canonical_vars = match req.canonical_vars(*pred_id) {
                    Some(vars) => vars,
                    None => continue,
                };
                if body_args.len() != canonical_vars.len() {
                    continue;
                }

                // Map body arg vars -> canonical vars by position.
                // #2492: Also extract constituent vars from expression body args
                let mut var_to_canonical: ay_core::kani_compat::DetHashMap<ChcVar, ChcVar> =
                    ay_core::kani_compat::DetHashMap::default();
                for (i, arg) in body_args.iter().enumerate() {
                    let Some(canonical) = canonical_vars.get(i) else {
                        continue;
                    };
                    match arg {
                        ChcExpr::Var(v) => {
                            var_to_canonical.insert(v.clone(), canonical.clone());
                        }
                        expr => {
                            for v in expr.vars() {
                                var_to_canonical
                                    .entry(v.clone())
                                    .or_insert_with(|| canonical.clone());
                            }
                        }
                    }
                }

                let mut hint_count = 0usize;

                for occ in &occurrences {
                    if hint_count >= Self::MAX_HINTS_PER_PRED {
                        break;
                    }

                    let guard = &occ.guard;

                    // Match inequality patterns: B >= k*C (from negated query guards)
                    let matches_ge_pattern = matches!(
                        (occ.negate_for_hint, &guard.op, guard.mul_on_lhs),
                        (false, ChcOp::Ge, false)
                            | (false, ChcOp::Le, true)
                            | (true, ChcOp::Lt, false)
                            | (true, ChcOp::Gt, true)
                    );

                    // Match equality patterns: B = k*C (from negated `not (= B (* k C))`)
                    // gj2007_m_1/3: query has `not (= B (* 5 C))` -> hint B = 5*C
                    let matches_eq_pattern = !occ.negate_for_hint && matches!(&guard.op, ChcOp::Eq);

                    // Match positive >= guards: A >= k*C (non-negated exit condition in query)
                    // gj2007_m_1: `(>= A (* 5 C))` is exit condition -> loop invariant is A < 5*C
                    // Since negate_for_hint=true, the correct hint is the negation: A < k*C
                    let matches_positive_ge = occ.negate_for_hint
                        && matches!(
                            (&guard.op, guard.mul_on_lhs),
                            (ChcOp::Ge, false) | (ChcOp::Le, true)
                        );

                    if !matches_ge_pattern && !matches_eq_pattern && !matches_positive_ge {
                        continue;
                    }

                    let Some(canonical_other) = var_to_canonical.get(&guard.other_var) else {
                        continue;
                    };
                    let Some(canonical_mul_var) = var_to_canonical.get(&guard.mul_var) else {
                        continue;
                    };
                    if canonical_other.sort != crate::ChcSort::Int
                        || canonical_mul_var.sort != crate::ChcSort::Int
                    {
                        continue;
                    }

                    let rhs = Self::mul_term(guard.k, canonical_mul_var.clone());

                    if matches_eq_pattern {
                        // Equality hint: B = k*C
                        let eq_formula =
                            ChcExpr::eq(ChcExpr::var(canonical_other.clone()), rhs.clone());
                        out.push(LemmaHint::new(
                            *pred_id,
                            eq_formula,
                            Self::PRIORITY,
                            "parametric-mul-eq-v1",
                        ));
                        hint_count += 1;

                        // Also emit inequality hints B >= k*C and B <= k*C
                        // since the equality may not be directly inductive but
                        // the individual bounds might be.
                        if hint_count < Self::MAX_HINTS_PER_PRED {
                            let ge_formula =
                                ChcExpr::ge(ChcExpr::var(canonical_other.clone()), rhs.clone());
                            out.push(LemmaHint::new(
                                *pred_id,
                                ge_formula,
                                Self::PRIORITY.saturating_sub(5),
                                "parametric-mul-eq-ge-v1",
                            ));
                            hint_count += 1;
                        }
                        if hint_count < Self::MAX_HINTS_PER_PRED {
                            let le_formula =
                                ChcExpr::le(ChcExpr::var(canonical_other.clone()), rhs.clone());
                            out.push(LemmaHint::new(
                                *pred_id,
                                le_formula,
                                Self::PRIORITY.saturating_sub(5),
                                "parametric-mul-eq-le-v1",
                            ));
                            hint_count += 1;
                        }
                    } else if matches_positive_ge {
                        // Negated exit condition hint: A >= k*C in query -> A < k*C as invariant
                        // The exit condition holds when the loop terminates, so its negation
                        // holds during the loop body.
                        let formula =
                            ChcExpr::lt(ChcExpr::var(canonical_other.clone()), rhs.clone());
                        out.push(LemmaHint::new(
                            *pred_id,
                            formula,
                            Self::PRIORITY.saturating_sub(10),
                            "parametric-mul-exit-neg-v1",
                        ));
                        hint_count += 1;

                        // Also emit the positive guard itself: A >= k*C
                        // The guard may be directly part of the invariant (e.g., when
                        // the predicate maintains the bound throughout the loop).
                        if hint_count < Self::MAX_HINTS_PER_PRED {
                            let pos_formula =
                                ChcExpr::ge(ChcExpr::var(canonical_other.clone()), rhs);
                            out.push(LemmaHint::new(
                                *pred_id,
                                pos_formula,
                                Self::PRIORITY.saturating_sub(15),
                                "parametric-mul-exit-pos-v1",
                            ));
                            hint_count += 1;
                        }
                    } else {
                        // Inequality hint: B >= k*C
                        let formula = ChcExpr::ge(ChcExpr::var(canonical_other.clone()), rhs);
                        out.push(LemmaHint::new(
                            *pred_id,
                            formula,
                            Self::PRIORITY,
                            Self::SOURCE,
                        ));
                        hint_count += 1;
                    }

                    // Phase-difference hints: B >= A + (k-1)*C
                    // For each `A >= C` guard in the query where C matches mul_var,
                    // generate `B >= A + (k-1)*C` as an alternative invariant.
                    // This form is often entry-inductive when the direct form isn't.
                    for (ge_greater, ge_lesser) in &ge_guards {
                        if hint_count >= Self::MAX_HINTS_PER_PRED {
                            break;
                        }

                        // Check if the `ge_lesser` matches `mul_var` (both are C)
                        if ge_lesser != &guard.mul_var {
                            continue;
                        }
                        // Check if `ge_greater` (A) is different from `canonical_other` (B)
                        if ge_greater == &guard.other_var {
                            continue;
                        }

                        let Some(canonical_ge_greater) = var_to_canonical.get(ge_greater) else {
                            continue;
                        };
                        if canonical_ge_greater.sort != crate::ChcSort::Int {
                            continue;
                        }
                        // Expression body args can map multiple query vars to one canonical var.
                        // Skip self-difference forms like `X >= X + k*C`.
                        if canonical_ge_greater == canonical_other {
                            continue;
                        }

                        // Generate normalized phase-difference hint:
                        // B >= A + (k-1)*C
                        let diff_k = guard.k - 1;
                        if diff_k < 0 {
                            continue;
                        }

                        let rhs_diff = ChcExpr::add(
                            ChcExpr::var(canonical_ge_greater.clone()),
                            Self::mul_term(diff_k, canonical_mul_var.clone()),
                        )
                        .simplify_constants();
                        let diff_formula =
                            ChcExpr::ge(ChcExpr::var(canonical_other.clone()), rhs_diff);

                        out.push(LemmaHint::new(
                            *pred_id,
                            diff_formula.clone(),
                            Self::PRIORITY.saturating_sub(10),
                            "parametric-mul-diff-v1",
                        ));
                        hint_count += 1;

                        // NOTE: We intentionally do NOT generate the offset-equality variant
                        // `B = (k-1)*C + A` here. While this formula is self-inductive, it is
                        // often NOT entry-inductive for multi-phase problems. For example, in
                        // s_multipl_08, at entry to SAD we have B >= C but not B = C (since the
                        // FUN phase may exit with A > C). The inequality form is more general
                        // and works for both exact and overshoot cases.
                    }
                }
            }
        }

        // Phase 2: Propagate hints to predecessor predicates in the phase chain.
        // For multi-phase loops (e.g., s_multipl_09), emit hints for intermediate predicates.
        Self::propagate_hints_to_predecessors(req, out);
    }
}

pub(super) static PARAMETRIC_MULTIPLICATION_PROVIDER: ParametricMultiplicationProvider =
    ParametricMultiplicationProvider;
