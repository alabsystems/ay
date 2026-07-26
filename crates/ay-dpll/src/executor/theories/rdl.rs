// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `QF_RDL` route: drive the incremental difference-logic engine
//! ([`crate::executor::dl_theory::DiffLogicTheory`]) through the standard
//! eager DPLL(T) split-loop pipeline, with a fail-closed fall-through to the
//! general simplex lane (`solve_lra`).
//!
//! Lives beside the other `solve_*` routes (rather than next to the theory
//! solver) because the pipeline macro expands against
//! `crate::executor::theories` internals.

use crate::executor::dl_theory::{atom_is_routable, DiffLogicTheory};
use crate::executor::Executor;
use crate::executor_types::{Result, SolveResult};

/// Kill switch for the QF_RDL difference-logic lane (`AY_RDL_ENGINE=0`).
///
/// Default ON. Follows the repo convention for solver-lane switches
/// (`AY_LRA_INC_ENGINE`, `AY_LRA_INC_WARM`, ...): cached in a `OnceLock`, and
/// only the literal `0` disables, so the whole route can be turned off without
/// a rebuild.
fn rdl_engine_enabled() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| !std::env::var("AY_RDL_ENGINE").is_ok_and(|v| v == "0"))
}

/// Opt-in escape hatch to take the lane in a PROOF-PRODUCING session
/// (`AY_RDL_ENGINE_PROOFS=1`).
///
/// Default OFF. The difference-logic theory reports plain
/// `TheoryResult::Unsat` conflicts with no Farkas annotation, so a proof built
/// on top of them cannot carry an arithmetic certificate for the theory lemmas.
/// The verdict would still be sound (the conflict gate re-verifies every
/// conflict), but the proof ARTIFACT would be weaker than the simplex lane's,
/// so proof sessions stay on `solve_lra` unless explicitly opted in. Same
/// posture as `solve_lra_inc_engine`, which also excludes proof sessions from
/// its new lane.
fn rdl_engine_proofs_allowed() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| {
        std::env::var("AY_RDL_ENGINE_PROOFS").is_ok_and(|v| v != "0" && !v.is_empty())
    })
}

/// Restart schedule for the QF_RDL lane: `AY_RDL_RESTART=initial,factor,randfreq`.
fn restart_tuning() -> (f64, f64, f64) {
    static V: std::sync::OnceLock<(f64, f64, f64)> = std::sync::OnceLock::new();
    *V.get_or_init(|| {
        let Ok(raw) = std::env::var("AY_RDL_RESTART") else {
            return (100.0, 1.5, 0.01);
        };
        let p: Vec<f64> = raw
            .split(',')
            .filter_map(|x| x.trim().parse().ok())
            .collect();
        match p.as_slice() {
            [i, f, v] => (*i, *f, *v),
            _ => (100.0, 1.5, 0.01),
        }
    })
}

/// Optional one-line routing trace (`AY_RDL_ENGINE_DEBUG=1`).
fn rdl_engine_debug() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| std::env::var("AY_RDL_ENGINE_DEBUG").is_ok_and(|v| v != "0" && !v.is_empty()))
}

/// Rewrite every ARITHMETIC equality into a conjunction of two inequalities.
///
/// `a = b` over the reals is exactly `a <= b  ∧  a >= b`. The rewrite is
/// therefore semantics-preserving in both directions, but it moves the hard
/// case out of the theory and into the Boolean structure the SAT solver already
/// handles:
///
/// ```text
///     not (a = b)   ==>   not (a <= b  ∧  a >= b)   ==   (a > b) ∨ (a < b)
/// ```
///
/// A negated equality is a DISJUNCTION, which a conjunctive difference-constraint
/// graph cannot represent — it is the single reason the `sal` and `skdmxa2`
/// families (92 of 255 instances) could not use this lane at all. After the
/// rewrite there are no equality atoms left: every atom is an inequality, and
/// every inequality is a difference constraint in BOTH polarities, so the
/// theory models all of them exactly and the SAT layer picks the disjunct.
///
/// Only equalities whose operands are arithmetic are touched. A Boolean
/// equality is a biconditional, not an ordering, and is left for the Tseitin
/// encoder.
fn eliminate_arith_equalities(
    terms: &mut ay_core::term::TermStore,
    root: ay_core::TermId,
    memo: &mut ay_core::kani_compat::DetHashMap<ay_core::TermId, ay_core::TermId>,
) -> ay_core::TermId {
    use ay_core::term::{Symbol, TermData};
    use ay_core::Sort;

    if let Some(&hit) = memo.get(&root) {
        return hit;
    }
    let rewritten = match terms.get(root).clone() {
        TermData::App(Symbol::Named(name), args)
            if name == "="
                && args.len() == 2
                && matches!(terms.sort(args[0]), Sort::Int | Sort::Real) =>
        {
            let a = eliminate_arith_equalities(terms, args[0], memo);
            let b = eliminate_arith_equalities(terms, args[1], memo);
            let le = terms.mk_le(a, b);
            let ge = terms.mk_ge(a, b);
            terms.mk_and(vec![le, ge])
        }
        TermData::Not(inner) => {
            let r = eliminate_arith_equalities(terms, inner, memo);
            if r == inner {
                root
            } else {
                terms.mk_not(r)
            }
        }
        TermData::Ite(c, t, e) => {
            let rc = eliminate_arith_equalities(terms, c, memo);
            let rt = eliminate_arith_equalities(terms, t, memo);
            let re = eliminate_arith_equalities(terms, e, memo);
            if (rc, rt, re) == (c, t, e) {
                root
            } else {
                terms.mk_ite(rc, rt, re)
            }
        }
        TermData::App(sym, args) => {
            let new_args: Vec<_> = args
                .iter()
                .map(|&a| eliminate_arith_equalities(terms, a, memo))
                .collect();
            if new_args == args {
                root
            } else {
                let sort = terms.sort(root).clone();
                terms.mk_app(sym, &new_args, sort)
            }
        }
        // Constants, variables, quantifiers, and residual lets carry no
        // rewritable equality in a quantifier-free QF_RDL problem.
        _ => root,
    };
    memo.insert(root, rewritten);
    rewritten
}

impl Executor {
    /// QF_RDL route: decide the instance with [`DiffLogicTheory`] when every
    /// theory atom is a pure difference-logic atom, else fall straight through
    /// to the existing [`Executor::solve_lra`] simplex path.
    ///
    /// # Fall-through conditions (each hands the problem to `solve_lra`)
    ///
    /// * `AY_RDL_ENGINE=0`;
    /// * push/pop incremental mode, or a proof-producing session (the DL engine
    ///   emits no Farkas/proof artifacts);
    /// * ANY reachable theory atom that is not a pure Real difference-logic
    ///   atom (fail closed — the engine is never fed an approximation);
    /// * an `Unknown` verdict from the DL lane (today only reachable by
    ///   asserting a *negated* arithmetic equality, which is a disjunction).
    ///
    /// # Soundness
    ///
    /// `Sat` clears `last_model_validated`, so `check_sat` re-evaluates every
    /// ORIGINAL assertion against the extracted model and degrades a spurious
    /// model to `Unknown`. `Unsat` rests on the theory's conflicts, each a
    /// genuine negative cycle re-verified by the DPLL conflict gate.
    pub(in crate::executor) fn solve_rdl(&mut self) -> Result<SolveResult> {
        if !rdl_engine_enabled()
            || self.incremental_mode
            || (self.produce_proofs_enabled() && !rdl_engine_proofs_allowed())
        {
            return self.solve_lra();
        }
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }

        let mut lifted = self.preprocess_lra_assertions();
        // Remove arithmetic equalities BEFORE deciding routability: their
        // negation is the one shape this theory cannot model, and after the
        // rewrite every atom is an inequality (see
        // `eliminate_arith_equalities`). This is what lets the equality-bearing
        // `sal` / `skdmxa2` families use the lane at all.
        {
            let mut memo = ay_core::kani_compat::DetHashMap::default();
            for a in lifted.iter_mut() {
                *a = eliminate_arith_equalities(&mut self.ctx.terms, *a, &mut memo);
            }
        }
        let reachable =
            crate::incremental_state::collect_reachable_theory_atoms(&self.ctx.terms, &lifted);
        let pure = reachable
            .iter()
            .all(|&atom| atom_is_routable(&self.ctx.terms, atom));
        if !pure {
            if rdl_engine_debug() {
                ay_core::safe_eprintln!(
                    "[RDL] not pure difference logic ({} theory atoms); using solve_lra",
                    reachable.len()
                );
            }
            return self.solve_lra();
        }
        if rdl_engine_debug() {
            ay_core::safe_eprintln!(
                "[RDL] pure difference logic ({} theory atoms); using the DL engine",
                reachable.len()
            );
        }

        // WEIGHT-LANE SELECTION. `IStar` keeps the engine's inner loop in
        // registers; `RStar` pays a BigRational allocation on every slack
        // computation. Every SMT-LIB QF_RDL constant is a small integer, so the
        // fast lane is taken essentially always — but the choice is made from
        // the ACTUAL constants, and any atom that does not fit exactly sends the
        // whole problem to the exact lane rather than being rounded.
        let fast = reachable.iter().all(|&atom| {
            crate::executor::diff_logic::collect_comparison(&self.ctx.terms, atom)
                .is_none_or(|a| ay_diff_logic::IStar::fits_fast_lane(&a.c).is_some())
        });
        if rdl_engine_debug() {
            ay_core::safe_eprintln!(
                "[RDL] weight lane: {}",
                if fast {
                    "IStar (i128)"
                } else {
                    "RStar (exact rationals)"
                }
            );
        }
        if fast {
            self.solve_rdl_with::<ay_diff_logic::IStar>(lifted)
        } else {
            self.solve_rdl_with::<ay_diff_logic::RStar>(lifted)
        }
    }

    /// The QF_RDL split-loop pipeline, monomorphized per weight representation.
    fn solve_rdl_with<W: ay_diff_logic::DlWeight + 'static>(
        &mut self,
        lifted: Vec<ay_core::TermId>,
    ) -> Result<SolveResult> {
        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline.clone();
        let result = self.with_isolated_incremental_state(Some(lifted), |this| {
            // Restart schedule. The QF_LRA lane's Z3-style geometric restarts
            // (100, 1.5) are the default, but they are tunable without a
            // rebuild because the right schedule differs sharply by answer:
            // frequent restarts help REFUTATION (they escape bad subtrees),
            // while MODEL FINDING wants long dives that can complete an
            // assignment. This division splits that way — the `.base` (unsat)
            // instances solve in seconds while their structurally identical
            // `.induction` (sat) siblings do not terminate at all.
            let (ri, rf, rv) = restart_tuning();
            this.configure_sat_search_tuning(ri, rf, rv);
            solve_incremental_split_loop_pipeline!(this,
                tag: "RDL",
                persistent_sat_field: persistent_sat,
                create_theory: DiffLogicTheory::<W>::new(&this.ctx.terms),
                extract_models: |theory| {
                    use crate::executor::theories::solve_harness::TheoryModels;
                    TheoryModels {
                        lra: Some(theory.extract_model()),
                        ..TheoryModels::default()
                    }
                },
                max_splits: crate::executor::theories::MAX_SPLITS_LRA,
                pre_theory_import: |_theory, _lc, _hc, _ds| {
                    // Difference logic has no learned state to import.
                },
                post_theory_export: |_theory| {
                    (vec![], Default::default(), Default::default())
                },
                // Eager theory-SAT interleaving: the whole point of the lane is
                // that an assert costs almost nothing, so check on every BCP.
                eager_extension: true,
                pre_iter_check: |_s| {
                    solve_interrupt
                        .as_ref()
                        .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                        || solve_deadline.expired()
                }
            )
        });

        match result {
            Ok(SolveResult::Sat) => {
                // The solve ran against the PREPROCESSED assertions; force
                // `check_sat` to re-validate the model against the originals.
                self.last_model_validated = false;
                Ok(SolveResult::Sat)
            }
            Ok(SolveResult::Unsat(cert)) => Ok(SolveResult::Unsat(cert)),
            // Non-definite (or errored): hand the problem to the trusted simplex
            // lane, which owns the verdict. Nothing the DL lane computed is kept.
            other => {
                if self.solve_deadline.expired()
                    || self
                        .solve_interrupt
                        .as_ref()
                        .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                {
                    return other;
                }
                if rdl_engine_debug() {
                    ay_core::safe_eprintln!(
                        "[RDL] non-definite verdict ({:?}, reason {:?}); retrying with solve_lra",
                        other.as_ref().map(|r| std::mem::discriminant(r)),
                        self.last_unknown_reason
                    );
                }
                self.last_result = None;
                self.last_model = None;
                self.last_model_validated = false;
                self.last_unknown_reason = None;
                self.solve_lra()
            }
        }
    }
}
