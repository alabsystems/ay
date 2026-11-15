// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Theory-specific LIA and LRA variable projection.
//!
//! Implements Fourier-Motzkin variable elimination for LIA (integer) and LRA (real)
//! theories. Bound extraction and coefficient normalization live in `theory_bounds`.

use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, SmtValue};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::sync::Arc;

use super::{BoundKind, Literal, Mbp};

/// Above this many `lower_bounds.len() * upper_bounds.len()` resolvents,
/// [`Mbp::project_real_var`] substitutes the model's own value for the
/// variable instead of resolving every lower/upper pair (2026-09-24,
/// `LRA_memouts_2026-09-24.md`).
///
/// Unlike [`Mbp::project_integer_var`] (which the Omega-test-style tightest
/// lower bound reduces to one `upper_bounds.len()` pass, see below), the LRA
/// path resolves every lower bound against every upper bound: `L*U` new
/// `ChcExpr` literals per eliminated variable, none of them repeats of one
/// another (a genuine combinatorial expansion, not tree-vs-DAG redundancy, so
/// no `seen`-pointer dedup can bound it). `Mbp::project` eliminates its
/// `projectable_vars` in sequence, each one's output literals feeding the
/// next one's bound extraction, so the product compounds across variables.
/// Measured: PDKIND's `generalize -> Mbp::project` on the wide, ITE-heavy
/// transition relations of `om1_with_relays_general_{3,4,5}_9_*` (sally) and
/// `cav12/{toy,toy-bug,kundu-bug,simple_array_inversion,transmitter}` (dozens
/// of Real state variables, hundreds of derived bounds per clause) drove RSS
/// past a 16 GiB budget in 18-56 s with no single allocation ever large
/// enough, and no loop-head checkpoint inside this nested loop, to let the
/// per-lane `ay_sys::MemoryGroup`'s cooperative cancel or hard-unwind
/// intervene before the process-wide allocator ceiling finally aborted the
/// whole run past its own budget.
///
/// The fallback is sound by the same argument [`Mbp::project`] already uses
/// for its `subst_vars` (Bool) and `fallback_vars` (MBQI) substitutions: the
/// caller's `model` already satisfies every literal in `with_var` at the
/// variable's own model value, so substituting that value keeps the model a
/// witness for the projected formula (`model |= psi`), and it costs
/// `with_var.len()` literals — the size of the INPUT to this step — instead
/// of `lower_bounds.len() * upper_bounds.len()`. It activates only when the
/// full resolution would exceed the cap, so every instance whose per-variable
/// bound counts stay below it (the overwhelming majority measured so far,
/// including every currently-passing LRA-Lin/LIA-Lin/BV instance) takes the
/// exact same exact-resolution path as before, byte for byte.
const MAX_REAL_MBP_RESOLVENTS: usize = 4096;

impl Mbp {
    /// Project out a single variable from the implicant
    pub(super) fn project_single_var(
        &self,
        var: &ChcVar,
        implicant: Vec<Literal>,
        model: &FxHashMap<String, SmtValue>,
    ) -> Vec<Literal> {
        // Partition literals into those containing var and those not
        let (with_var, without_var): (Vec<_>, Vec<_>) = implicant
            .into_iter()
            .partition(|lit| lit.atom.contains_var_name(&var.name));

        if with_var.is_empty() {
            return without_var;
        }

        match var.sort {
            ChcSort::Int => self.project_integer_var(var, with_var, without_var, model),
            ChcSort::Real => self.project_real_var(var, with_var, without_var, model),
            ChcSort::BitVec(_) => self.project_bitvec_var(var, with_var, without_var, model),
            // Array: model-based Ackermannization (#6047).
            ChcSort::Array(_, _) => self.project_array_var(var, with_var, without_var, model),
            // DT: constructor unfolding (Z3 mbp_datatypes.cpp:68, project_nonrec).
            ChcSort::Datatype { .. } => {
                self.project_datatype_var(var, with_var, without_var, model)
            }
            // Bool is handled via model-value substitution before reaching here
            // (see project.rs). Uninterpreted sorts drop constraints.
            _ => without_var,
        }
    }

    /// Project out an integer variable (LIA)
    fn project_integer_var(
        &self,
        var: &ChcVar,
        with_var: Vec<Literal>,
        mut without_var: Vec<Literal>,
        model: &FxHashMap<String, SmtValue>,
    ) -> Vec<Literal> {
        // Collect bounds: lower (ax >= t), upper (ax <= t), and equalities
        let mut lower_bounds: Vec<(i128, ChcExpr, bool)> = Vec::new(); // (coeff, term, strict)
        let mut upper_bounds: Vec<(i128, ChcExpr, bool)> = Vec::new();
        let mut equalities: Vec<(i128, ChcExpr, usize)> = Vec::new(); // (coeff, term, lit_index)

        for (i, lit) in with_var.iter().enumerate() {
            if let Some(bound) = self.extract_bound(&lit.atom, var, lit.positive) {
                match bound {
                    BoundKind::Lower(coeff, term, strict) => {
                        lower_bounds.push((coeff, term, strict));
                    }
                    BoundKind::Upper(coeff, term, strict) => {
                        upper_bounds.push((coeff, term, strict));
                    }
                    BoundKind::Equality(coeff, term) => {
                        equalities.push((coeff, term, i));
                    }
                }
            }
        }

        // If we have an equality, use it to substitute
        if let Some((coeff, term, eq_idx)) = equalities.first() {
            if *coeff == 1 || *coeff == -1 {
                // Can directly substitute: var = term or var = -term
                let subst_term = if *coeff == 1 {
                    term.clone()
                } else {
                    ChcExpr::neg(term.clone())
                };
                // Substitute in remaining literals, skipping the defining equality
                // (it becomes a tautology after substitution, e.g. eq(neg(neg(t)), t))
                for (i, lit) in with_var.iter().enumerate() {
                    if i == *eq_idx {
                        continue;
                    }
                    let new_atom = lit.atom.substitute(&[(var.clone(), subst_term.clone())]);
                    // Simplify and check if non-trivial
                    let simplified = new_atom.simplify_constants();
                    if simplified != ChcExpr::Bool(true) {
                        without_var.push(Literal::new(simplified, lit.positive));
                    }
                }
                return without_var;
            } else {
                // Non-unit coefficient: coeff * var = term.
                // Substitute var = term / coeff (integer division is exact when
                // the divisibility constraint holds).
                let abs_coeff = coeff.saturating_abs();

                // Add divisibility constraint: term mod |coeff| = 0
                if abs_coeff > 1 {
                    let div_check = ChcExpr::eq(
                        ChcExpr::Op(
                            ChcOp::Mod,
                            vec![Arc::new(term.clone()), Arc::new(ChcExpr::Int(abs_coeff))],
                        ),
                        ChcExpr::Int(0),
                    );
                    without_var.push(Literal::new(div_check, true));
                }

                // Compute substitution: var = term / |coeff|, with sign adjustment.
                let sign_adjusted = if *coeff < 0 {
                    ChcExpr::neg(term.clone())
                } else {
                    term.clone()
                };
                let subst_term = if abs_coeff != 1 {
                    ChcExpr::Op(
                        ChcOp::Div,
                        vec![Arc::new(sign_adjusted), Arc::new(ChcExpr::Int(abs_coeff))],
                    )
                } else {
                    sign_adjusted
                };

                // Substitute in remaining literals, skipping the defining equality.
                for (i, lit) in with_var.iter().enumerate() {
                    if i == *eq_idx {
                        continue;
                    }
                    let new_atom = lit.atom.substitute(&[(var.clone(), subst_term.clone())]);
                    let simplified = new_atom.simplify_constants();
                    if simplified != ChcExpr::Bool(true) {
                        without_var.push(Literal::new(simplified, lit.positive));
                    }
                }
                return without_var;
            }
        }

        // No equality - use bounds to eliminate variable
        if lower_bounds.is_empty() || upper_bounds.is_empty() {
            // Missing one side of bounds - variable is unconstrained
            return without_var;
        }

        // Find the tightest lower bound according to model
        let _var_val = model
            .get(&var.name)
            .and_then(|v| match v {
                SmtValue::Int(n) => Some(*n),
                _ => None,
            })
            .unwrap_or(0);

        // Select the tightest lower bound via cross-multiplication.
        // For bounds c1*x >= t1 and c2*x >= t2 (c1, c2 > 0), the tighter bound
        // has the higher t/c value. Compare t1/c1 vs t2/c2 as t1*c2 vs t2*c1
        // to avoid integer division imprecision (truncation or floor can both
        // give wrong orderings for negative values with non-unit coefficients).
        //
        // The products of two i128 operands need up to 255 bits, so they are
        // formed exactly as big integers. In i128 they overflowed — an
        // unevaluable bound reads as i128::MIN, and any coefficient above 1
        // then panicked "attempt to multiply with overflow" (measured: PDKIND
        // on examples/model_checker_consumer_looping_id_bv64.smt2, caught by the portfolio
        // and reported as `unknown`).
        let cross = |value: i128, coefficient: i128| {
            num_bigint::BigInt::from(value) * num_bigint::BigInt::from(coefficient.saturating_abs())
        };
        let best_lower = lower_bounds.iter().max_by(|(c1, t1, _), (c2, t2, _)| {
            let ev1 = self.eval_arith(t1, model).unwrap_or(i128::MIN);
            let ev2 = self.eval_arith(t2, model).unwrap_or(i128::MIN);
            // Compare t1/c1 vs t2/c2 as t1*c2 vs t2*c1 (cross-multiply)
            cross(ev1, *c2).cmp(&cross(ev2, *c1))
        });

        // Generate resolved constraints
        if let Some((lb_coeff, lb_term, lb_strict)) = best_lower {
            for (ub_coeff, ub_term, ub_strict) in &upper_bounds {
                // Resolve lower and upper: lb_coeff * x >= lb_term, ub_coeff * x <= ub_term
                // => lb_coeff * ub_term >= ub_coeff * lb_term (with adjustments for integers)

                // Scale terms appropriately
                let lb_coeff_abs = lb_coeff.saturating_abs();
                let ub_coeff_abs = ub_coeff.saturating_abs();

                let scaled_lb = if ub_coeff_abs == 1 {
                    lb_term.clone()
                } else {
                    ChcExpr::mul(ChcExpr::Int(ub_coeff_abs), lb_term.clone())
                };
                let scaled_ub = if lb_coeff_abs == 1 {
                    ub_term.clone()
                } else {
                    ChcExpr::mul(ChcExpr::Int(lb_coeff_abs), ub_term.clone())
                };

                // Add slack for strict integer inequality.
                // For lb_strict: c1*x > t1 → c1*x >= t1+1, scaled by c2: c2*t1 + c2 <= c1*t2
                // For ub_strict: c2*x < t2 → c2*x <= t2-1, scaled by c1: c2*t1 <= c1*t2 - c1
                let slack = if var.sort == ChcSort::Int {
                    let lb_slack = if *lb_strict { ub_coeff_abs } else { 0 };
                    let ub_slack = if *ub_strict { lb_coeff_abs } else { 0 };
                    lb_slack + ub_slack
                } else {
                    0
                };
                let final_lb = if slack > 0 {
                    ChcExpr::add(scaled_lb.clone(), ChcExpr::Int(slack))
                } else {
                    scaled_lb
                };

                // lb <= ub
                let resolved = ChcExpr::le(final_lb, scaled_ub);
                let simplified = resolved.simplify_constants();
                if simplified != ChcExpr::Bool(true) {
                    without_var.push(Literal::new(simplified, true));
                }
            }
        }

        without_var
    }

    /// Project out a real variable (LRA)
    fn project_real_var(
        &self,
        var: &ChcVar,
        with_var: Vec<Literal>,
        mut without_var: Vec<Literal>,
        model: &FxHashMap<String, SmtValue>,
    ) -> Vec<Literal> {
        // Similar to integer but without divisibility concerns.
        // Keep coefficients so bound resolution can cross-multiply correctly
        // when non-unit coefficients appear (e.g. 2*x >= t1, 3*x <= t2).
        let mut lower_bounds: Vec<(i128, ChcExpr, bool)> = Vec::new(); // (coeff, term, strict)
        let mut upper_bounds: Vec<(i128, ChcExpr, bool)> = Vec::new();

        for lit in &with_var {
            if let Some(bound) = self.extract_bound(&lit.atom, var, lit.positive) {
                match bound {
                    BoundKind::Lower(coeff, term, strict) => {
                        lower_bounds.push((coeff, term, strict));
                    }
                    BoundKind::Upper(coeff, term, strict) => {
                        upper_bounds.push((coeff, term, strict));
                    }
                    BoundKind::Equality(coeff, term) => {
                        // For equality: coeff * var = term → var = term / coeff
                        // For reals, division is exact (no divisibility concerns).
                        // 1. Flip term sign when coefficient is negative.
                        // 2. Divide by |coeff| when |coeff| != 1.
                        let abs_coeff = coeff.saturating_abs();
                        let sign_adjusted = if coeff < 0 { ChcExpr::neg(term) } else { term };
                        let subst_term = if abs_coeff != 1 {
                            ChcExpr::Op(
                                ChcOp::Div,
                                vec![Arc::new(sign_adjusted), Arc::new(ChcExpr::Int(abs_coeff))],
                            )
                        } else {
                            sign_adjusted
                        };
                        let empty_model = FxHashMap::default();
                        for other_lit in &with_var {
                            // Do not substitute into the defining equality itself:
                            // it becomes a tautology (e.g. -2*Div(-6,2)=6) and can
                            // block eval_bool on Real Eq in model checks.
                            if std::ptr::eq(other_lit, lit) {
                                continue;
                            }
                            let new_atom = other_lit
                                .atom
                                .substitute(&[(var.clone(), subst_term.clone())]);
                            let simplified = new_atom.simplify_constants();
                            if simplified == ChcExpr::Bool(true) {
                                continue;
                            }

                            // Drop ground tautologies that the simplifier does not
                            // currently reduce (e.g. duplicate substituted equalities).
                            if simplified.vars().is_empty()
                                && self.eval_bool(&simplified, &empty_model) == Some(true)
                            {
                                continue;
                            }

                            without_var.push(Literal::new(simplified, other_lit.positive));
                        }
                        return without_var;
                    }
                }
            }
        }

        if lower_bounds.is_empty() || upper_bounds.is_empty() {
            return without_var;
        }

        // Cap the Fourier-Motzkin cross product (see `MAX_REAL_MBP_RESOLVENTS`).
        // Above the cap, substitute the model's own value for `var` into every
        // literal that mentions it: `with_var.len()` new literals instead of
        // `lower_bounds.len() * upper_bounds.len()`, sound by the same model-
        // witness argument as the equality branch above.
        if lower_bounds.len().saturating_mul(upper_bounds.len()) > MAX_REAL_MBP_RESOLVENTS {
            if let Some(value) = Self::model_value_expr(var, model) {
                for lit in &with_var {
                    let new_atom = lit.atom.substitute(&[(var.clone(), value.clone())]);
                    let simplified = new_atom.simplify_constants();
                    if simplified != ChcExpr::Bool(true) {
                        without_var.push(Literal::new(simplified, lit.positive));
                    }
                }
                return without_var;
            }
            // No model value for `var` (should not happen: `project()` is only
            // ever invoked under a model that satisfies `formula`, including
            // this variable) — fall through to the exact resolution below
            // rather than silently dropping soundness-relevant constraints.
        }

        // Resolve each lower bound with each upper bound.
        // For lb_coeff * x >= lb_term, ub_coeff * x <= ub_term:
        // => lb_coeff * ub_term >= ub_coeff * lb_term (cross-multiply, coefficients positive).
        for (lb_coeff, lb_term, lb_strict) in &lower_bounds {
            for (ub_coeff, ub_term, ub_strict) in &upper_bounds {
                let new_strict = *lb_strict || *ub_strict;
                let lb_coeff_abs = lb_coeff.saturating_abs();
                let ub_coeff_abs = ub_coeff.saturating_abs();

                let scaled_lb = if ub_coeff_abs == 1 {
                    lb_term.clone()
                } else {
                    ChcExpr::mul(ChcExpr::Int(ub_coeff_abs), lb_term.clone())
                };
                let scaled_ub = if lb_coeff_abs == 1 {
                    ub_term.clone()
                } else {
                    ChcExpr::mul(ChcExpr::Int(lb_coeff_abs), ub_term.clone())
                };

                let cmp = if new_strict {
                    ChcExpr::lt(scaled_lb, scaled_ub)
                } else {
                    ChcExpr::le(scaled_lb, scaled_ub)
                };
                let simplified = cmp.simplify_constants();
                if simplified != ChcExpr::Bool(true) {
                    without_var.push(Literal::new(simplified, true));
                }
            }
        }

        without_var
    }
}
