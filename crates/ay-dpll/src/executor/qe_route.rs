// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #qe-alternation-route — recognise the quantified problems that iterated
//! quantifier elimination DECIDES, and route them to QE up front rather than
//! through instantiation.
//!
//! # Why a route at all
//!
//! A quantified formula whose only theory is linear arithmetic over `Int` /
//! `Real`, with no uninterpreted function of arity >= 1 and no arrays / BV /
//! nonlinear terms, is decidable by iterated QE: eliminate the innermost
//! binder, work outward, using ∀-duality (`∀v.ψ ≡ ¬∃v.¬ψ`) for universal
//! blocks. [`crate::executor::qe_prepass`] already implements exactly that
//! descent over [`crate::qe::eliminate_exists`] (Cooper, `Int`) and
//! [`crate::qe::eliminate_exists_real`] (Loos-Weispfenning, `Real`).
//!
//! Instantiation is REFUTED for this class by measurement, not by argument:
//! across the 1,666-file SMT-COMP `SQ Arith` selection ZERO files declare a
//! function of arity >= 1 and ZERO carry a `:pattern`, because `{LIA, LRA,
//! NIA, NRA}` have no uninterpreted functions at all. E-matching has nothing to
//! match on; a build that inferred triggers moved instances 0 -> 84 and left
//! the solved count at 1/40.
//!
//! # What this module does and does not decide
//!
//! It is a RECOGNIZER plus an adopter. It owns no verdict:
//!
//! * [`Executor::pure_arithmetic_quantified_problem`] answers whether the WHOLE
//!   assertion set is in the fragment. Whole-problem, not per-assertion: one
//!   out-of-fragment sibling declines the route and the problem stays on
//!   today's path byte-for-byte.
//! * [`Executor::adopt_qe_alternation_route`] runs `deep_qe` on the live
//!   assertions and reports whether the residue is FULLY quantifier-free. A
//!   partial elimination is refused (`deep_qe` is itself all-or-nothing per
//!   assertion, and a mixed residue would hand the quantifier lanes a shape
//!   they did not author).
//!
//! The residue is a SOLVING candidate, never publication authority — the
//! eliminators screen their output by bounded differential sampling, not by
//! proof. The caller sets `quantified_proof_translation_incomplete`, so an
//! `unsat` reached from the residue must still present an independently strict
//! authored-scope proof, and a `sat` must still clear the mandatory independent
//! model gate against the AUTHORED quantified window.
//!
//! # Why this is DEFAULT OFF
//!
//! Because the authority gap above is the binding constraint, and the route
//! cannot close it. Measured end to end:
//!
//! * The route WORKS. On `LRA/scholl-smt08/RND/RND_3_13.smt2` all four `Real`
//!   binders peel and the whole assertion reduces to the constant `true`.
//!   Across 138 SQ Arith files stratified over the 1,666-file selection it
//!   fully grounds 21 — LIA 8/30, LRA 13/51, NIA 0/32, NRA 0/25.
//! * Its answers are RIGHT. Of those 21, the 15 that fold to a constant were
//!   cross-checked against z3 4.16.0 and cvc5 1.3.0: 15/15 agreement with both
//!   solvers and with the declared `:status`, zero disagreements. Two
//!   (`mjollnir6/formula_160`, `formula_240`) are files z3 cannot answer in
//!   60 s and QE answers in under 3 s.
//! * It still moves ZERO published verdicts, because
//!   `model::independent_gate::quantified_gate_general_check` runs `deep_qe`
//!   itself, obtains the same residue, and declines it —
//!   "quantifier-free QE candidate lacks exact equivalence authority". Using a
//!   sampling-screened rewriter to CONFIRM a model is circular, and the gate is
//!   right to refuse.
//! * And it costs wall time: +11 s on `RND_3_13.smt2`, which fails closed in
//!   under a second without it. (Roughly neutral on the `mjollnir` families;
//!   30 s -> 19 s on `RNDPRE_4_11.smt2`.)
//!
//! Zero rows for seconds of budget is a regression, so the route is compiled
//! parked and can be armed only through its test seam. What lands is the route,
//! reachability counters, and barrier tests. Production activation requires a
//! certified equivalence authority and a deliberate typed caller; there is no
//! hidden environment switch for a measured-negative lane.
//!
//! # Budget
//!
//! The route adds no budget of its own: `deep_qe` fails closed on its DNF
//! caps, its per-apply elimination budget, `cooper::COOPER_INSTANCE_CAP` (the
//! bound on a single uninterruptible Cooper call after the measured 8.5 s /
//! 3.07 GB blowup), and the executor's solve-interrupt flag, which is threaded
//! through unchanged. Every one of those degrades to "keep the original
//! quantified assertion", which is the status quo — an `unknown`, never a hang.

use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId};
use std::collections::HashSet;

use super::Executor;
use crate::ematching::contains_quantifier;

/// Per-executor state for quantified routes that are retained for measurement
/// but have no production arming authority.
#[derive(Default)]
pub(super) struct MeasuredNegativeRoutes {
    qe_alternation: bool,
    #[cfg(test)]
    closed_universal_precheck_in_proof_mode: bool,
}

/// Eliminator-invocation budget for the EAGER route. Below
/// `qe_prepass::MAX_ELIMINATIONS_PER_APPLY` (8192), which is sized for the
/// `Unknown` fallback where the work is already sunk and there is no verdict to
/// lose. Exhaustion refuses the variable, restoring the original quantifier —
/// an `unknown`, never a hang.
///
/// # This constant is a MEASURED NULL. Do not turn it down again.
///
/// It was added to bound a real cost: on the `2010-Monniaux-QE/mjollnir4`
/// family a single `deep_qe` call runs past 20 s on SIX of six sampled files
/// and grounds NONE of them, while every file the route does ground finishes
/// inside 3 s. The hypothesis was that the cost is invocation-COUNT driven —
/// a several-hundred-disjunct DNF paying one self-checked LW/Cooper call per
/// disjunct per binder.
///
/// **Refuted.** Sweeping 64 / 256 / 1024 on `mjollnir4/formula_204` moved the
/// wall clock not at all: 42 s / 40 s / 42 s. The cost lives somewhere else —
/// DNF materialisation in `qe_prepass::dnf`, or the residue's own ground solve.
/// The constant is kept only because it cannot hurt, NOT because it was shown
/// to help; anyone attacking the eager-route cost should profile those two
/// first rather than shrink this number.
///
/// Per-CALL work stays bounded by construction regardless
/// (`qe::cooper::COOPER_INSTANCE_CAP`, LW's `MAX_LITERALS`), because the
/// solve-deadline flag is polled only BETWEEN invocations and cannot land
/// inside one.
const ROUTE_ELIMINATION_BUDGET: usize = 1024;

impl Executor {
    /// Arm or disarm the #qe-alternation-route for this executor.
    ///
    /// The in-process arming knob, so a test never has to mutate the process
    /// environment (which is shared across the test harness's threads).
    ///
    /// `#[cfg(test)]` because the measured-negative route has no production
    /// caller. Drop the gate only when a certified route earns published rows.
    #[cfg(test)]
    pub(crate) fn set_qe_alternation_route(&mut self, armed: bool) {
        self.measured_negative_quantifier_routes.qe_alternation = armed;
    }

    /// Is the route armed for this executor?
    pub(crate) const fn qe_alternation_route_armed(&self) -> bool {
        self.measured_negative_quantifier_routes.qe_alternation
    }

    /// Arm the measured-negative closed-universal proof route for a test.
    #[cfg(test)]
    pub(crate) fn set_closed_universal_precheck_in_proof_mode(&mut self, armed: bool) {
        self.measured_negative_quantifier_routes
            .closed_universal_precheck_in_proof_mode = armed;
    }

    /// Whether the closed-universal validity precheck may run for this solve.
    pub(crate) fn closed_universal_precheck_armed(&self) -> bool {
        if !self.is_producing_proofs() {
            return true;
        }

        #[cfg(test)]
        {
            self.measured_negative_quantifier_routes
                .closed_universal_precheck_in_proof_mode
        }
        #[cfg(not(test))]
        {
            false
        }
    }

    /// Apply the measured QE route before ordinary quantifier processing.
    ///
    /// Recognition is whole-problem and fail-closed. The route never clears
    /// the authored-quantifier marker: downstream publication still requires
    /// independently strict proof/model authority over the authored problem.
    pub(crate) fn maybe_adopt_qe_alternation_route(&mut self, has_quantifiers: bool) {
        if has_quantifiers
            && !self.deep_qe_retry_armed
            && self.qe_alternation_route_armed()
            && self.pure_arithmetic_quantified_problem()
        {
            self.prepass_reachability.qe_route_applicable += 1;
            if self.adopt_qe_alternation_route() {
                self.prepass_reachability.qe_route_grounded += 1;
                self.quantified_proof_translation_incomplete = true;
            }
        }
    }

    /// Is EVERY assertion a boolean combination of linear `Int` / `Real` atoms,
    /// with quantifiers binding only `Int` / `Real` variables?
    ///
    /// This is the decidable-by-QE class. It deliberately mirrors
    /// `qe_prepass::fragment_screen` — the screen the eliminators apply to a
    /// single matrix — but descends THROUGH binders, because the route has to
    /// answer a question about the whole problem before any elimination runs.
    ///
    /// Refuses (returns `false`) on anything else: uninterpreted functions of
    /// arity >= 1, arrays, bit-vectors, strings, algebraic datatypes,
    /// uninterpreted sorts, `ite`, `let`, `div`, `distinct`, `xor`, nonlinear
    /// multiplication (two non-constant factors — this is what keeps NIA / NRA
    /// out, where QE by these methods does not apply), a non-constant divisor,
    /// and any future `TermData` kind (`#[non_exhaustive]`).
    ///
    /// Arity-0 applications ARE admitted: an SMT-LIB `(declare-fun x () Real)`
    /// is a declared constant, not an uninterpreted function, and the whole
    /// target class is built from them.
    pub(crate) fn pure_arithmetic_quantified_problem(&self) -> bool {
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut seen: HashSet<TermId> = HashSet::new();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::Const(Constant::Bool(_) | Constant::Int(_) | Constant::Rational(_)) => {}
                TermData::Const(_) => return false,
                TermData::Var(_, _) => {
                    if !matches!(self.ctx.terms.sort(t), Sort::Bool | Sort::Int | Sort::Real) {
                        return false;
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Forall(vars, body, _) | TermData::Exists(vars, body, _) => {
                    // Cooper eliminates `Int` binders and Loos-Weispfenning
                    // `Real` ones; there is no eliminator for any other sort,
                    // so a binder over one is out of the decidable class.
                    if !vars
                        .iter()
                        .all(|(_, s)| matches!(s, Sort::Int | Sort::Real))
                    {
                        return false;
                    }
                    stack.push(*body);
                }
                TermData::App(Symbol::Named(name), args) => {
                    match name.as_str() {
                        "and" | "or" | "not" | "=" | "<" | "<=" | ">" | ">=" | "+" | "-" => {}
                        "*" => {
                            // Linear only: at most one non-constant factor.
                            // Two makes the problem NIA / NRA, where neither
                            // Cooper nor Loos-Weispfenning applies.
                            let nonconst = args
                                .iter()
                                .filter(|&&a| !matches!(self.ctx.terms.get(a), TermData::Const(_)))
                                .count();
                            if nonconst > 1 {
                                return false;
                            }
                        }
                        // Cooper accepts `mod` only in the divisibility form
                        // with a constant divisor; `/` is linear only with a
                        // constant divisor.
                        "mod" | "/" => {
                            if args.len() != 2
                                || !matches!(self.ctx.terms.get(args[1]), TermData::Const(_))
                            {
                                return false;
                            }
                        }
                        "to_real" => {
                            // The `Int -> Real` bridge Loos-Weispfenning
                            // purifies. Refused when the builtin is shadowed by
                            // a user declaration: rewriting an uninterpreted
                            // symbol would fabricate semantics.
                            if self.ctx.terms.to_real_is_shadowed() || args.len() != 1 {
                                return false;
                            }
                        }
                        // A declared constant is an arity-0 application and is
                        // in the class; an uninterpreted FUNCTION is not.
                        _ => {
                            if !args.is_empty() {
                                return false;
                            }
                            if !matches!(
                                self.ctx.terms.sort(t),
                                Sort::Bool | Sort::Int | Sort::Real
                            ) {
                                return false;
                            }
                        }
                    }
                    stack.extend(args.iter().copied());
                }
                // `ite` / `let` / any future node kind: out of class.
                _ => return false,
            }
        }
        true
    }

    /// Run `deep_qe` on the live assertions and report whether the residue is
    /// FULLY quantifier-free.
    ///
    /// `deep_qe` is already all-or-nothing PER ASSERTION (it keeps the original
    /// `TermId` verbatim unless the rewrite eliminates every binder of that
    /// assertion), so the only extra thing this adds is the WHOLE-PROBLEM
    /// check: a residue where one assertion grounded and another did not is
    /// refused, because the quantifier lanes downstream match on authored
    /// shape and a half-rewritten set is a shape nobody authored.
    ///
    /// Note the asymmetry with the refusal: `deep_qe` rewrites IN PLACE, and a
    /// refused variable already leaves its assertion untouched, so a `false`
    /// return here can still have adopted a per-assertion rewrite. That is
    /// exactly the pre-existing `deep_qe_retry_armed` site's behaviour and is
    /// equivalence-preserving either way; what changes on the `false` path is
    /// only that `has_quantified_assertions` stays true and the quantifier
    /// lanes run as they do today.
    pub(crate) fn adopt_qe_alternation_route(&mut self) -> bool {
        let before = self.ctx.assertions.clone();
        let progress = crate::executor::qe_prepass::deep_qe_with_budget(
            &mut self.ctx.terms,
            &mut self.ctx.assertions,
            self.solve_interrupt.as_deref(),
            ROUTE_ELIMINATION_BUDGET,
        );
        let grounded = self
            .ctx
            .assertions
            .iter()
            .all(|&a| !contains_quantifier(&self.ctx.terms, a));
        if progress && grounded {
            return true;
        }
        // Restore verbatim on refusal. `deep_qe` may have grounded SOME
        // assertions; keeping a mixed set would hand the quantifier lanes a
        // shape they did not author, which is the regression surface the
        // pre-pass's own "all-or-nothing per assertion" rule exists to avoid.
        self.ctx.assertions = before;
        false
    }
}

#[cfg(test)]
mod arming_policy_tests {
    use super::*;

    #[test]
    fn closed_universal_proof_route_is_parked_behind_typed_test_seam() {
        let mut executor = Executor::new();
        assert!(executor.closed_universal_precheck_armed());

        executor.set_produce_proofs(true);
        assert!(!executor.closed_universal_precheck_armed());

        executor.set_closed_universal_precheck_in_proof_mode(true);
        assert!(executor.closed_universal_precheck_armed());
    }
}
