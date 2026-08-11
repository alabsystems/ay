// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Objective and objective-certificate output.

use ay_core::{Sort, TermId};

use crate::executor_format::format_rational;
use crate::executor_types::SolveResult;

use super::{EvalValue, Executor};

impl Executor {
    /// Generate objective output for get-objectives command.
    pub(crate) fn get_objectives(&self) -> String {
        // MaxSMT path: when the last solve came from `(assert-soft ...)`, the
        // soft-cost objective was materialized and popped inside a scope, so it
        // is no longer in `ctx.objectives()`. Report the minimized total
        // violated weight recorded by the MaxSMT solve.
        if self.ctx.objectives().is_empty() {
            if let Some(cost) = self.last_soft_cost {
                // `:approximate` marks a feasible-but-unproven bound
                // (resource-limited or weight-incomplete search); consumers
                // must not treat it as the optimum.
                if !self.last_soft_cost_optimal {
                    return format!("(objectives\n (__ay_soft_cost {cost} :approximate)\n)\n");
                }
                return format!("(objectives\n (__ay_soft_cost {cost})\n)\n");
            }
            // z3 parity: with no objectives and no soft cost, `(get-objectives)`
            // prints an empty objectives list (exit 0), even before any
            // `(check-sat)` — it does not error here.
            return "(objectives\n)\n".to_string();
        }

        // PARETO terminal-`unsat` path: Z3 keeps reporting the LAST emitted Pareto
        // point's objectives after the front is exhausted (the terminal
        // `(check-sat)` returns `unsat`, but `(get-objectives)` still shows the
        // last point). `finite_objective_values` was cleared by the unsat path, so we
        // render directly from the persisted `pareto_state.last_point`.
        if matches!(self.last_result, Some(SolveResult::Unsat(_))) {
            if let Some(state) = &self.pareto_state {
                if let Some(point) = &state.last_point {
                    let objs = self.ctx.objectives();
                    if objs.len() == point.len() {
                        let mut out = String::from("(objectives\n");
                        for (obj, val) in objs.iter().zip(point.iter()) {
                            let term_str = self.format_term(obj.term);
                            let value_str =
                                if matches!(self.ctx.terms.sort(obj.term), Sort::BitVec(_)) {
                                    val.numer().to_string()
                                } else {
                                    self.format_objective_rational(val, obj.term)
                                };
                            out.push_str(&format!(" ({term_str} {value_str})\n"));
                        }
                        out.push_str(")\n");
                        return out;
                    }
                }
            }
        }

        if !matches!(self.last_result, Some(SolveResult::Sat)) {
            return "(error \"objectives are not available\")".to_string();
        }

        let mut out = String::from("(objectives\n");
        for (objective_index, obj) in self.ctx.objectives().iter().enumerate() {
            if self.unavailable_objectives.contains(&objective_index) {
                // A lex predecessor with no attainable optimum — unbounded
                // (`oo`) or unattained (infinitesimal, #opt-epsilon) — leaves
                // no scalar to optimize under. z3 prints an interval for the
                // predecessor and a demonstrably FALSE scalar for the suffix
                // (measured 4.15.4: `(y (- 1))` where max y = 5); AY refuses
                // to fabricate one. Documented deviation.
                return format!(
                    "(error \"objective {objective_index} is unavailable after a lexicographic predecessor with no attainable optimum\")"
                );
            }
            let term_str = self.format_term(obj.term);
            // An objective with no finite optimum is reported as infinity per
            // SMT-LIB OMT conventions (matches z3): `oo` for an unbounded
            // maximize, `(- oo)` for an unbounded minimize. Reporting the
            // arbitrary finite value from the iterative fallback would be wrong.
            let value_str = match self.unbounded_objectives.get(&objective_index) {
                Some(ay_frontend::ObjectiveDirection::Maximize) => "oo".to_string(),
                Some(ay_frontend::ObjectiveDirection::Minimize) => "(* (- 1) oo)".to_string(),
                None => {
                    // A BitVector objective is reported by Z3 as a DECIMAL
                    // numeral in `(get-objectives)` (e.g. `(x 7)`), NOT the
                    // `#x7` bitvector literal that `format_eval_value` would emit
                    // (the bitvector literal is only used by `(get-value)`). The
                    // optimum is the unsigned value, stored as a whole rational,
                    // so we render its numerator (the integer) directly.
                    let is_bv = matches!(self.ctx.terms.sort(obj.term), Sort::BitVec(_));
                    if let Some((value, eps_coeff)) =
                        self.infinitesimal_objectives.get(&objective_index)
                    {
                        // Unattained optimum (#opt-epsilon): render the z3
                        // epsilon grammar. Checked BEFORE the finite map,
                        // matching `objective_optimum`'s resolution order.
                        self.format_epsilon_objective(value, eps_coeff, obj.term)
                    } else if let Some(recorded) =
                        self.finite_objective_values.get(&objective_index)
                    {
                        // Every finite outcome is explicitly recorded only after
                        // an optimizing query is admitted. Lex/Pareto values are
                        // bound to the final model; BOX values are independently
                        // authenticated and intentionally model-free.
                        if is_bv {
                            recorded.numer().to_string()
                        } else {
                            self.format_objective_rational(recorded, obj.term)
                        }
                    } else {
                        return format!(
                            "(error \"objective {objective_index} has no admitted optimization outcome\")"
                        );
                    }
                }
            };
            out.push_str(&format!(" ({term_str} {value_str})\n"));
        }
        out.push_str(")\n");
        out
    }

    /// Format a recorded BOX objective optimum (a `BigRational`) exactly as
    /// the lex path formats an objective value: sort-aware at the stdout
    /// boundary (#real-fmt) — a Real objective prints `2.0` / `(/ 7.0 2.0)`,
    /// an Int one a bare integer. Routed through
    /// [`Self::try_format_eval_value_user`] so box and lex objective output
    /// (and the certificate `bound`/`entails` strings) use one shared
    /// formatter (no divergence).
    fn format_objective_rational(
        &self,
        value: &num_rational::BigRational,
        term_id: TermId,
    ) -> String {
        self.try_format_eval_value_user(&EvalValue::Rational(value.clone()), term_id)
            .expect("a rational value always formats")
    }

    /// Render an UNATTAINED Real optimum `value + eps_coeff·ε` in z3 4.15.4's
    /// exact `(get-objectives)` epsilon grammar (#opt-epsilon, all shapes
    /// measured and pinned byte-exact in the opt-epsilon battery):
    ///
    /// * minimize (k > 0): k=1 elides the coefficient (`(+ (/ 3.0 2.0)
    ///   epsilon)`; v=0 → bare `epsilon`); k≠1 → `(* 2.0 epsilon)` /
    ///   `(+ v (* k epsilon))`.
    /// * maximize (k < 0): the coefficient is never elided:
    ///   `(* (- 1.0) epsilon)`; v≠0 → `(+ v (* (- |k|) epsilon))`.
    ///
    /// `eps_coeff` is nonzero by construction (a zero ε-part is exactly an
    /// attained `Optimal` and never lands in `infinitesimal_objectives`).
    fn format_epsilon_objective(
        &self,
        value: &num_rational::BigRational,
        eps_coeff: &num_rational::BigRational,
        term_id: TermId,
    ) -> String {
        use num_traits::{One, Signed, Zero};
        let value_str = self.format_objective_rational(value, term_id);
        if eps_coeff.is_positive() {
            if eps_coeff.is_one() {
                if value.is_zero() {
                    "epsilon".to_string()
                } else {
                    format!("(+ {value_str} epsilon)")
                }
            } else {
                let k_str = self.format_objective_rational(eps_coeff, term_id);
                if value.is_zero() {
                    format!("(* {k_str} epsilon)")
                } else {
                    format!("(+ {value_str} (* {k_str} epsilon))")
                }
            }
        } else {
            let k_abs = -eps_coeff.clone();
            let k_str = self.format_objective_rational(&k_abs, term_id);
            let inner = format!("(* (- {k_str}) epsilon)");
            if value.is_zero() {
                inner
            } else {
                format!("(+ {value_str} {inner})")
            }
        }
    }

    /// Generate output for the `(get-objective-certificates)` command
    /// (#lra-opt-cert, AY extension).
    ///
    /// For each objective whose last optimizing `(check-sat)` produced a dual
    /// (Farkas) optimality certificate, prints
    ///
    /// ```text
    /// (objective-certificates
    ///  ((objective <term>)
    ///   (sense minimize|maximize)
    ///   (bound <value>)
    ///   (entails (>=|<= <term> <value>))
    ///   (strict true|false)
    ///   (farkas
    ///    (<coeff> <literal>)
    ///    ...))
    /// )
    /// ```
    ///
    /// where each `<literal>` is the asserted atom (wrapped in `(not ...)`
    /// when it was asserted false) and `<coeff>` its positive Farkas
    /// multiplier: summing `coeff * literal` (each literal oriented as a
    /// `>= 0` fact) yields exactly the `entails` inequality, checkable without
    /// trusting AY.
    pub(crate) fn get_objective_certificates(&self) -> String {
        if self.ctx.objectives().is_empty() {
            return "(error \"no objectives\")".to_string();
        }
        let mut certified = 0usize;
        let mut out = String::from("(objective-certificates\n");
        for (objective_index, obj) in self.ctx.objectives().iter().enumerate() {
            let Some(cert) = self.objective_certificates.get(&objective_index) else {
                continue;
            };
            certified += 1;
            let term_str = self.format_term(obj.term);
            // Same formatter as `(get-objectives)` so the two never diverge.
            let bound_str = self.format_objective_rational(&cert.bound, obj.term);
            let (sense_str, rel) = match cert.sense {
                ay_lra::OptimizationSense::Minimize => ("minimize", ">="),
                ay_lra::OptimizationSense::Maximize => ("maximize", "<="),
            };
            out.push_str(&format!(
                " ((objective {term_str})\n  (sense {sense_str})\n  (bound {bound_str})\n  (entails ({rel} {term_str} {bound_str}))\n  (strict {strict})\n  (farkas\n",
                strict = cert.strict
            ));
            for atom in &cert.atoms {
                let atom_str = self.format_term(atom.atom);
                let literal_str = if atom.value {
                    atom_str
                } else {
                    format!("(not {atom_str})")
                };
                out.push_str(&format!(
                    "   ({} {literal_str})\n",
                    format_rational(&atom.coeff)
                ));
            }
            out.push_str("  ))\n");
        }
        out.push_str(")\n");
        if certified == 0 {
            return "(error \"no objective certificates available\")".to_string();
        }
        out
    }
}
