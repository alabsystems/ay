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
use crate::executor::guard_nodes::ShareOf;
use crate::executor::Executor;
use crate::executor_types::{Result, SolveResult};

/// Kill switch for the QF_RDL difference-logic lane (`--dpll-no-rdl-engine`).
///
/// Default ON. Follows the repo convention for solver-lane switches
/// (`--dpll-no-lra-inc-engine`, `--dpll-no-lra-inc-warm`, ...): cached in a `OnceLock`, and
/// only the literal `0` disables, so the whole route can be turned off without
/// a rebuild.
fn rdl_engine_enabled() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| !ay_core::theory_disable_flags().no_rdl_engine)
}

/// What the route may do with an UNSAT verdict from the difference-logic lane.
///
/// The DL theory reports plain `TheoryResult::Unsat` conflicts with no Farkas
/// annotation, so a proof built on top of them carries no arithmetic
/// certificate for its theory lemmas. That never made the VERDICT unsound (the
/// DPLL conflict gate re-verifies every negative cycle), but it means the lane
/// cannot back an `unsat` with the checked certificate the mandatory-certificate
/// policy (`configure_public_solve_proof_posture`) requires on every public
/// solve that is not competition-shed.
///
/// The old answer was to keep the lane closed whenever the tracker was armed —
/// which, since the certificate became mandatory, is EVERY default-mode solve,
/// so the lane only ever ran under `--rigor fast`. That threw away the lane's
/// SAT answers too, although a SAT needs no proof at all: it publishes through
/// the fail-closed model validation gate (`last_model_validated = false` forces
/// `check_sat` to re-evaluate every ORIGINAL assertion against the model).
///
/// So the lane now runs under every posture and only its REFUTATION is
/// disposed of by this policy:
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DlUnsatDisposition {
    /// No certificate is demanded (competition shedding: the tracker is off).
    /// The lane's refutation publishes through the existing B3 raw admission
    /// lane, byte-identical to the pre-existing `--rigor fast` behaviour.
    PublishRaw,
    /// A checked certificate is demanded (tracker armed / `--self-check` /
    /// `:produce-proofs` / `--proof`). The lane's refutation is DISCARDED and
    /// the certified simplex lane re-derives the verdict with its Farkas-backed
    /// proof — exactly the lane that owned the verdict before, so nothing is
    /// lost relative to the old routing; the DL attempt only costs the time it
    /// spent. The proof tracker is disarmed for the attempt (its steps could
    /// never be published) and re-armed before the fallback.
    Discard,
}

impl Executor {
    /// The certificate policy for this solve: whether an UNSAT from the DL lane
    /// may publish raw or must be re-derived by the certified lane.
    ///
    /// `produce_proofs_enabled()` is the recording predicate — the tracker is
    /// armed, or `:produce-proofs` is set. It is the right question here (not
    /// `is_producing_proofs()`, the explicit artifact demand): the mandatory
    /// certificate is keyed to the tracker, and a raw UNSAT may only be
    /// published when publication itself will not require one.
    fn dl_unsat_disposition(&self) -> DlUnsatDisposition {
        if self.produce_proofs_enabled() {
            DlUnsatDisposition::Discard
        } else {
            DlUnsatDisposition::PublishRaw
        }
    }

    /// Run one difference-logic attempt with the proof tracker DISARMED and
    /// on a share of the solve deadline when its refutation could never be
    /// published, re-arming the tracker afterwards. Without a share the
    /// deadline it found is put back after it (`end_sliced_attempt`).
    ///
    /// Disarming is state-preserving (`ProofTracker::enable`/`disable` flip a
    /// flag; the ledger is untouched) and is pure cost hygiene: under
    /// [`DlUnsatDisposition::Discard`] every step the attempt would record is
    /// thrown away with the attempt, so recording them — and the search-time
    /// bookkeeping budget they consume — buys nothing. Under
    /// [`DlUnsatDisposition::PublishRaw`] the tracker is already off.
    ///
    /// The deadline cap is the other half of the same fact. A discarded
    /// attempt can contribute exactly one thing: a SAT answer. On an UNSAT
    /// instance every second it spends is a second the certified lane — the
    /// only lane that can publish that verdict — no longer has, so an
    /// uncapped attempt turns "UNSAT in 8.5 s" into a timeout as soon as the
    /// DL search is slower than the deadline (measured: FISCHER12-8-ninc,
    /// unsat 8.5 s before this lane opened, timeout with the attempt uncapped
    /// once propagation made the attempt slower). Half the remaining budget
    /// leaves the certified lane at least what it had, and a SAT the DL lane
    /// cannot find in half the budget it rarely finds in the other half. Only
    /// `solve_deadline` is shared; the certification deadline (the
    /// publication boundary) is untouched, and `pre_iter_check` /
    /// `Solver::set_solve_deadline` both read the shared cell, so the cap
    /// reaches the SAT search. The half is a deadline share (GT6, GuardTree
    /// step S3): the executor's deadline is never written, and the share
    /// counts itself spent as it closes. (The old `--rigor fast` lane
    /// budgeted nothing, and still does: there the DL refutation IS the
    /// verdict.)
    fn run_dl_attempt<F>(
        &mut self,
        disposition: DlUnsatDisposition,
        attempt: F,
    ) -> Result<SolveResult>
    where
        F: FnOnce(&mut Self) -> Result<SolveResult>,
    {
        let tracker_was_armed = self.proof_tracker.is_enabled();
        let found_deadline = self.solve_deadline.get();
        let mut share = None;
        if disposition == DlUnsatDisposition::Discard {
            if tracker_was_armed {
                self.proof_tracker.disable();
            }
            if self
                .solve_deadline
                .get()
                .is_some_and(|deadline| deadline >= ay_core::time::Instant::now())
            {
                share = self.open_deadline_share(ShareOf::Search);
            }
        }
        let result = attempt(self);
        self.end_sliced_attempt(share, found_deadline);
        if tracker_was_armed {
            self.proof_tracker.enable();
        }
        result
    }

    /// Forget a DL-lane outcome that is not being published, so the trusted
    /// lane that runs next starts from a clean slate. With the tracker disarmed
    /// the discarded attempt built no proof artefacts; only the verdict
    /// bookkeeping needs clearing (including an `Unknown` origin the capped
    /// attempt may have recorded when its narrowed deadline expired).
    fn forget_dl_attempt(&mut self) {
        self.last_result = None;
        self.last_model = None;
        self.last_model_validated = false;
        self.last_unknown_reason = None;
        self.last_unknown_origin = None;
    }
}

/// Restart schedule for the QF_RDL lane: `AY_RDL_RESTART=initial,factor,randfreq`.
fn restart_tuning() -> (f64, f64, f64) {
    // B25: the tuning env is retired; the shipped schedule is the constant.
    (100.0, 1.5, 0.01)
}

/// Optional one-line routing trace (`AY_RDL_ENGINE_DEBUG=1`).
fn rdl_engine_debug() -> bool {
    // B23: the debug trace env spelling is retired; flip for a diagnosis.
    false
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
    /// * `--dpll-no-rdl-engine`;
    /// * push/pop incremental mode;
    /// * ANY reachable theory atom that is not a pure Real difference-logic
    ///   atom (fail closed — the engine is never fed an approximation);
    /// * an `Unknown` verdict from the DL lane (today only reachable by
    ///   asserting a *negated* arithmetic equality, which is a disjunction);
    /// * an `Unsat` verdict from the DL lane when this solve demands a checked
    ///   certificate ([`DlUnsatDisposition::Discard`]) — the DL engine emits
    ///   no Farkas/proof artifacts, so the certified simplex lane re-derives
    ///   the refutation exactly as it did when it owned the whole route.
    ///
    /// # Soundness
    ///
    /// `Sat` clears `last_model_validated`, so `check_sat` re-evaluates every
    /// ORIGINAL assertion against the extracted model and degrades a spurious
    /// model to `Unknown`. `Unsat` rests on the theory's conflicts, each a
    /// genuine negative cycle re-verified by the DPLL conflict gate — and is
    /// only ever PUBLISHED from this lane when no certificate is demanded
    /// (the pre-existing `--rigor fast` raw-admission behaviour).
    pub(in crate::executor) fn solve_rdl(&mut self) -> Result<SolveResult> {
        if !rdl_engine_enabled() || self.incremental_mode {
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
        let disposition = self.dl_unsat_disposition();
        let result = self.run_dl_attempt(disposition, |exec| {
            exec.with_isolated_incremental_state(Some(lifted), |this| {
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
            })
        });

        match result {
            Ok(SolveResult::Sat) => {
                // The solve ran against the PREPROCESSED assertions; force
                // `check_sat` to re-validate the model against the originals.
                self.last_model_validated = false;
                Ok(SolveResult::Sat)
            }
            Ok(SolveResult::Unsat(cert)) if disposition == DlUnsatDisposition::PublishRaw => {
                Ok(SolveResult::Unsat(cert))
            }
            // A refutation this solve cannot publish uncertified: forget it and
            // let the certified simplex lane re-derive it with a real proof.
            Ok(SolveResult::Unsat(_)) => {
                if rdl_engine_debug() {
                    ay_core::safe_eprintln!(
                        "[RDL] DL-lane unsat under a certificate demand; re-deriving with solve_lra"
                    );
                }
                self.forget_dl_attempt();
                self.solve_lra()
            }
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
                        other.as_ref().map(std::mem::discriminant),
                        self.last_unknown_reason
                    );
                }
                self.forget_dl_attempt();
                self.solve_lra()
            }
        }
    }
}

// ---------------------------------------------------------------------------
// QF_IDL: the same engine over integer-tightened bounds
// ---------------------------------------------------------------------------

/// DEFAULT ON, disable with `--dpll-no-idl-engine` — same polarity as
/// [`rdl_engine_enabled`], and for the same reason: it earned it.
///
/// Full-division differential, 138 files even-strided over all 2,528, T:20,
/// arms interleaved per file: 43 decided by default vs 56 with the lane,
/// **+16 gained / 3 lost / 0 conflicts**, and zero verdicts contradicting the
/// declared `:status` on either arm. Net +13 at a 5:1 win ratio. Confirmed on a
/// SECOND, disjoint stride before flipping, so the ratio is not an artefact of
/// the sample it was tuned on.
///
/// The 3 losses are budget exhaustion, not wrong answers: the lane engages,
/// spends the deadline, and leaves nothing for the `solve_lia` fallback that
/// decides them. Budgeting the attempt to half the deadline was measured and
/// REFUTED — it recovers 2 losses but costs 6 of the 16 gains (net +9 vs +13),
/// because a difference graph that is going to close still needs most of the
/// budget.
fn idl_engine_enabled() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| !ay_core::theory_disable_flags().no_idl_engine)
}

/// Exact `LraModel` → `LiaModel`, FAIL-CLOSED on any non-integral value.
///
/// After integer tightening every edge weight is an integer with a zero
/// epsilon, so the engine's potentials — and therefore every extracted value —
/// are integers. A non-integral value here means that invariant did not hold,
/// so this returns `None` and the caller falls through to `solve_lia` rather
/// than rounding. Rounding would be exactly the silent relaxation this lane
/// exists to avoid.
fn lra_model_to_lia(model: &ay_lra::LraModel) -> Option<ay_lia::LiaModel> {
    let mut values = ay_core::kani_compat::DetHashMap::default();
    for (term, value) in &model.values {
        if !value.is_integer() {
            return None;
        }
        values.insert(*term, value.to_integer());
    }
    Some(ay_lia::LiaModel { values })
}

impl Executor {
    /// QF_IDL route: decide the instance with [`DiffLogicTheory`] in integer
    /// mode when every theory atom is a pure INT difference-logic atom, else
    /// fall straight through to [`Executor::solve_lia`].
    ///
    /// # Why this is not `solve_rdl` with a different sort check
    ///
    /// The fall-through is `solve_lia`, NOT `solve_lra`. Handing an integer
    /// problem to the simplex lane would drop integrality — measured: relabelling
    /// a QF_IDL file's `set-logic` to `QF_RDL` turns a derivable `unsat` into
    /// `unknown`. The model also lands in `TheoryModels::lia`, via a conversion
    /// that fails closed rather than rounding.
    ///
    /// # Soundness
    ///
    /// Identical to the Real lane, plus the tightening equivalence. `Sat` clears
    /// `last_model_validated`, so `check_sat` re-evaluates every ORIGINAL
    /// assertion against the extracted model and degrades a spurious model to
    /// `Unknown`. `Unsat` rests on the theory's conflicts, each a genuine
    /// negative cycle re-verified by the DPLL conflict gate — and, exactly as
    /// in the Real lane, is only PUBLISHED from here when no certificate is
    /// demanded ([`DlUnsatDisposition`]); otherwise `solve_lia` re-derives it
    /// with its Farkas-backed proof. `tighten_int` is an equivalence over Int,
    /// not a relaxation, so neither verdict can be strengthened by it.
    pub(in crate::executor) fn solve_idl(&mut self) -> Result<SolveResult> {
        if !idl_engine_enabled() || self.incremental_mode {
            return self.solve_lia();
        }
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }

        let mut lifted = self.preprocess_lra_assertions();
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
            .all(|&atom| crate::executor::dl_theory::atom_is_routable_int(&self.ctx.terms, atom));
        if !pure {
            return self.solve_lia();
        }

        // WEIGHT-LANE SELECTION, the same test as the Real lane: `IStar` keeps
        // every slack computation in registers, `RStar` pays a BigRational
        // allocation each. Measured on queen33-1 (skeptic re-measurement in
        // the development design notes §3.1): 82% of
        // the DL lane's worker time on `RStar` is `BigUint::gcd`/`reduce`
        // inside `assert_edge`'s slack arithmetic, and the same instance
        // relabelled to the IStar lane runs >= 3.4x more decisions per CPU
        // second. The test is made on the ORIGINAL constants; `tighten_int`
        // then only moves an integral constant by at most one, and an atom
        // whose tightened bound still does not lower exactly makes the theory
        // report `Unsupported`, which falls back to `solve_lia` — never a
        // rounded weight.
        let fast = reachable.iter().all(|&atom| {
            crate::executor::diff_logic::collect_comparison(&self.ctx.terms, atom)
                .is_none_or(|a| ay_diff_logic::IStar::fits_fast_lane(&a.c).is_some())
        });
        if fast {
            self.solve_idl_with::<ay_diff_logic::IStar>(lifted)
        } else {
            self.solve_idl_with::<ay_diff_logic::RStar>(lifted)
        }
    }

    fn solve_idl_with<W: ay_diff_logic::DlWeight + 'static>(
        &mut self,
        lifted: Vec<ay_core::TermId>,
    ) -> Result<SolveResult> {
        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline.clone();
        let disposition = self.dl_unsat_disposition();
        let mut model_conversion_failed = false;
        let result = self.run_dl_attempt(disposition, |exec| {
            exec.with_isolated_incremental_state(Some(lifted), |this| {
                let (ri, rf, rv) = restart_tuning();
                this.configure_sat_search_tuning(ri, rf, rv);
                solve_incremental_split_loop_pipeline!(this,
                    tag: "IDL",
                    persistent_sat_field: persistent_sat,
                    create_theory: DiffLogicTheory::<W>::new_int(&this.ctx.terms),
                    extract_models: |theory| {
                        use crate::executor::theories::solve_harness::TheoryModels;
                        let lra = theory.extract_model();
                        match lra_model_to_lia(&lra) {
                            Some(lia) => TheoryModels { lia: Some(lia), ..TheoryModels::default() },
                            None => {
                                model_conversion_failed = true;
                                TheoryModels::default()
                            }
                        }
                    },
                    max_splits: crate::executor::theories::MAX_SPLITS_LRA,
                    pre_theory_import: |_theory, _lc, _hc, _ds| {},
                    post_theory_export: |_theory| {
                        (vec![], Default::default(), Default::default())
                    },
                    eager_extension: true,
                    pre_iter_check: |_s| {
                        solve_interrupt
                            .as_ref()
                            .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                            || solve_deadline.expired()
                    }
                )
            })
        });

        // A failed integral conversion means the tightening invariant did not
        // hold; refuse the verdict and let the trusted lane own it.
        if model_conversion_failed {
            self.forget_dl_attempt();
            return self.solve_lia();
        }

        match result {
            Ok(SolveResult::Sat) => {
                self.last_model_validated = false;
                Ok(SolveResult::Sat)
            }
            Ok(SolveResult::Unsat(cert)) if disposition == DlUnsatDisposition::PublishRaw => {
                Ok(SolveResult::Unsat(cert))
            }
            // A refutation this solve cannot publish uncertified: forget it and
            // let the certified LIA lane re-derive it with a real proof.
            Ok(SolveResult::Unsat(_)) => {
                self.forget_dl_attempt();
                self.solve_lia()
            }
            other => {
                if self.solve_deadline.expired()
                    || self
                        .solve_interrupt
                        .as_ref()
                        .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                {
                    return other;
                }
                self.forget_dl_attempt();
                self.solve_lia()
            }
        }
    }
}

#[cfg(test)]
mod routing_tests {
    //! The certificate policy of the difference-logic lanes, end to end
    //! through the public `check-sat` path (`execute_all` arms the proof
    //! tracker exactly as the CLI does).
    //!
    //! The lane is identified by the ABSENCE of the LIA theory's `lia_checks`
    //! statistic: the simplex lane exports it on every solve, the DL lane never
    //! does. That is the same signal the 2026-09-05 diagnosis used.

    use super::{DlUnsatDisposition, Executor};
    use crate::executor::unsat_cert::CommandUnsatAdmission;
    use crate::executor_types::SolveResult;
    use ay_frontend::parse;

    fn verdict(exec: &mut Executor, script: &str) -> String {
        let cmds = parse(script).expect("parse");
        exec.execute_all(&cmds)
            .expect("execute")
            .into_iter()
            .rfind(|o| matches!(o.trim(), "sat" | "unsat" | "unknown"))
            .expect("a check-sat verdict")
            .trim()
            .to_string()
    }

    fn lia_lane_ran(exec: &Executor) -> bool {
        exec.statistics().get_int("lia_checks").is_some()
    }

    /// Disjunctive, so the `:ay-diff-logic` conjunctive pre-check cannot take
    /// it; every atom is a pure Int difference atom, so `solve_idl` does.
    const IDL_SAT: &str = "(set-logic QF_IDL)
         (declare-fun x () Int)
         (declare-fun y () Int)
         (declare-fun z () Int)
         (assert (or (<= (- x y) (- 3)) (>= (- x y) 3)))
         (assert (< (- y z) 2))
         (assert (<= (- z x) 5))
         (check-sat)";

    /// `x = y` forced by two bounds, then a disjunction of strict orderings
    /// that both contradict it — every disjunct closes a negative cycle.
    const IDL_UNSAT: &str = "(set-logic QF_IDL)
         (declare-fun x () Int)
         (declare-fun y () Int)
         (assert (or (< (- x y) 0) (< (- y x) 0)))
         (assert (<= (- x y) 0))
         (assert (>= (- x y) 0))
         (check-sat)";

    const RDL_SAT: &str = "(set-logic QF_RDL)
         (declare-fun x () Real)
         (declare-fun y () Real)
         (declare-fun z () Real)
         (assert (or (<= (- x y) (- 3)) (>= (- x y) 3)))
         (assert (< (- y z) 2))
         (assert (<= (- z x) 5))
         (check-sat)";

    const RDL_UNSAT: &str = "(set-logic QF_RDL)
         (declare-fun x () Real)
         (declare-fun y () Real)
         (assert (or (< (- x y) 0) (< (- y x) 0)))
         (assert (<= (- x y) 0))
         (assert (>= (- x y) 0))
         (check-sat)";

    /// Default posture (tracker armed on every public solve): a SAT from the
    /// DL lane publishes through model validation — no simplex lane runs.
    #[test]
    fn idl_sat_under_the_default_certificate_posture_is_decided_by_the_dl_lane() {
        let mut exec = Executor::new();
        assert_eq!(verdict(&mut exec, IDL_SAT), "sat");
        assert!(
            !lia_lane_ran(&exec),
            "the DL lane must decide a SAT instance itself"
        );
        assert!(
            exec.last_model_validated,
            "DL-lane models go through the validation gate"
        );
    }

    #[test]
    fn rdl_sat_under_the_default_certificate_posture_is_decided_by_the_dl_lane() {
        let mut exec = Executor::new();
        assert_eq!(verdict(&mut exec, RDL_SAT), "sat");
        assert!(!lia_lane_ran(&exec));
        assert!(exec.last_model_validated);
    }

    /// Default posture: the DL lane's refutation is discarded and the
    /// certified LIA lane re-derives it — the published UNSAT carries a proof
    /// and is NOT a raw admission.
    #[test]
    fn idl_unsat_under_the_default_certificate_posture_is_rederived_by_the_certified_lane() {
        let mut exec = Executor::new();
        assert_eq!(verdict(&mut exec, IDL_UNSAT), "unsat");
        assert!(
            lia_lane_ran(&exec),
            "a certificate demand must hand UNSAT to solve_lia"
        );
        assert_certified_admission(&exec);
    }

    #[test]
    fn rdl_unsat_under_the_default_certificate_posture_is_rederived_by_the_certified_lane() {
        let mut exec = Executor::new();
        assert_eq!(verdict(&mut exec, RDL_UNSAT), "unsat");
        assert_certified_admission(&exec);
    }

    /// The published UNSAT was admitted by a CHECKED certification lane.
    ///
    /// `admit_command_solve_result` consumes the minted one-shot certificate
    /// and records its admission kind, so the admission class is the
    /// observable that survives publication (the same one
    /// `competition_mode_tests` relies on): `Some` proves a certification lane
    /// admitted the verdict, and it must not be the raw competition
    /// carve-out. `last_proof()` is deliberately not used: it exposes the
    /// proof only when proof OUTPUT was requested, which a bare executor does
    /// not do.
    fn assert_certified_admission(exec: &Executor) {
        assert!(
            exec.last_command_unsat_admission.is_some(),
            "a published UNSAT records its admission class"
        );
        assert_ne!(
            exec.last_command_unsat_admission,
            Some(CommandUnsatAdmission::CompetitionRaw)
        );
    }

    /// Competition shedding (the pre-existing `--rigor fast` route): the DL
    /// lane's refutation publishes raw, exactly as before this change.
    #[test]
    fn idl_unsat_under_competition_shedding_publishes_raw_from_the_dl_lane() {
        let mut exec = Executor::new();
        exec.set_competition_mode(true);
        assert_eq!(verdict(&mut exec, IDL_UNSAT), "unsat");
        assert!(
            !lia_lane_ran(&exec),
            "shedding keeps the whole route on the DL lane"
        );
        assert_eq!(
            exec.last_command_unsat_admission,
            Some(CommandUnsatAdmission::CompetitionRaw)
        );
    }

    #[test]
    fn idl_sat_under_competition_shedding_is_decided_by_the_dl_lane() {
        let mut exec = Executor::new();
        exec.set_competition_mode(true);
        assert_eq!(verdict(&mut exec, IDL_SAT), "sat");
        assert!(!lia_lane_ran(&exec));
    }

    /// An explicit proof demand under competition mode re-arms the tracker
    /// (precedence over shedding), so the UNSAT is again re-derived certified.
    #[test]
    fn idl_unsat_with_an_explicit_proof_demand_is_rederived_even_in_competition_mode() {
        let mut exec = Executor::new();
        exec.set_competition_mode(true);
        exec.set_produce_proofs(true);
        assert_eq!(verdict(&mut exec, IDL_UNSAT), "unsat");
        assert!(lia_lane_ran(&exec));
        assert!(exec.last_proof().is_some());
    }

    /// A constant beyond the i128 fast lane sends the Int lane to exact
    /// rationals; the verdict is unaffected.
    #[test]
    fn idl_huge_constants_take_the_exact_lane_and_still_decide() {
        let mut exec = Executor::new();
        let script = "(set-logic QF_IDL)
             (declare-fun x () Int)
             (declare-fun y () Int)
             (assert (or (<= (- x y) (- 1180591620717411303424))
                         (>= (- x y) 1180591620717411303424)))
             (assert (<= (- x y) 5))
             (check-sat)";
        assert_eq!(verdict(&mut exec, script), "sat");
        assert!(!lia_lane_ran(&exec));
    }

    /// The disposition follows the recording predicate: off the public path
    /// the tracker is off (raw), a public solve arms it (discard), and a
    /// competition-shed public solve leaves it off (raw).
    #[test]
    fn disposition_tracks_the_certificate_demand() {
        let mut exec = Executor::new();
        assert_eq!(exec.dl_unsat_disposition(), DlUnsatDisposition::PublishRaw);
        exec.begin_public_solve(false);
        assert_eq!(exec.dl_unsat_disposition(), DlUnsatDisposition::Discard);

        let mut shed = Executor::new();
        shed.set_competition_mode(true);
        shed.begin_public_solve(false);
        assert_eq!(shed.dl_unsat_disposition(), DlUnsatDisposition::PublishRaw);
    }

    /// The attempt runs untracked ONLY when its refutation is to be discarded,
    /// and the tracker comes back exactly as it was.
    #[test]
    fn run_dl_attempt_disarms_only_under_discard_and_restores_the_tracker() {
        let mut exec = Executor::new();
        exec.proof_tracker.enable();
        let r = exec.run_dl_attempt(DlUnsatDisposition::Discard, |e| {
            assert!(
                !e.proof_tracker.is_enabled(),
                "discarded attempt must run untracked"
            );
            Ok(SolveResult::Unknown)
        });
        assert!(r.is_ok());
        assert!(
            exec.proof_tracker.is_enabled(),
            "tracker must be re-armed afterwards"
        );

        exec.proof_tracker.disable();
        let r = exec.run_dl_attempt(DlUnsatDisposition::PublishRaw, |e| {
            assert!(!e.proof_tracker.is_enabled());
            Ok(SolveResult::Unknown)
        });
        assert!(r.is_ok());
        assert!(
            !exec.proof_tracker.is_enabled(),
            "a disarmed tracker stays disarmed"
        );
    }

    /// A discarded attempt runs against HALF the remaining budget and the
    /// original deadline comes back afterwards; a raw-publishing attempt keeps
    /// the whole budget; no deadline stays no deadline.
    #[test]
    fn run_dl_attempt_caps_only_a_discarded_attempt_at_half_the_remaining_budget() {
        use ay_core::time::Instant;
        use std::time::Duration;
        let mut exec = Executor::new();
        let deadline = Instant::now() + Duration::from_secs(600);
        exec.solve_deadline.set(Some(deadline));

        let seen = exec
            .run_dl_attempt(DlUnsatDisposition::Discard, |e| {
                Ok(e.solve_deadline.get().map_or(SolveResult::Unknown, |d| {
                    // Between a quarter and just under the full budget: the
                    // cap is half of what remained at entry.
                    let left = d.saturating_duration_since(Instant::now());
                    assert!(
                        left > Duration::from_secs(150) && left < Duration::from_secs(301),
                        "capped deadline leaves {left:?}, expected ~300 s"
                    );
                    SolveResult::Sat
                }))
            })
            .expect("attempt");
        assert_eq!(seen, SolveResult::Sat, "the attempt saw a deadline");
        assert_eq!(
            exec.solve_deadline.get(),
            Some(deadline),
            "the original deadline is restored"
        );

        let seen = exec
            .run_dl_attempt(DlUnsatDisposition::PublishRaw, |e| {
                assert_eq!(
                    e.solve_deadline.get(),
                    Some(deadline),
                    "raw attempt keeps its budget"
                );
                Ok(SolveResult::Unknown)
            })
            .expect("attempt");
        assert_eq!(seen, SolveResult::Unknown);

        exec.solve_deadline.set(None);
        let _ = exec
            .run_dl_attempt(DlUnsatDisposition::Discard, |e| {
                assert_eq!(
                    e.solve_deadline.get(),
                    None,
                    "no deadline stays no deadline"
                );
                Ok(SolveResult::Unknown)
            })
            .expect("attempt");
        assert_eq!(exec.solve_deadline.get(), None);
    }

    /// A write inside the attempt that does not restore itself (as
    /// `eq_qe_bound_legacy_refutation` narrows the rest of its check-sat)
    /// never outlives the attempt: with a share it moved the share's cell,
    /// and without one the deadline the attempt found is put back, as before
    /// the slicers opened shares (GuardTree S3).
    #[test]
    fn run_dl_attempt_undoes_an_unbalanced_deadline_write_with_or_without_a_share() {
        use ay_core::time::Instant;
        use std::time::Duration;
        let narrowed = Instant::now() + Duration::from_secs(5);
        let unbalanced = |e: &mut Executor| {
            e.solve_deadline.set(Some(narrowed));
            Ok(SolveResult::Unknown)
        };
        let mut exec = Executor::new();
        let future = Instant::now() + Duration::from_secs(600);
        let passed = Instant::now()
            .checked_sub(Duration::from_millis(1))
            .expect("one millisecond must fit before the current instant");
        for (disposition, found, shared) in [
            (DlUnsatDisposition::Discard, Some(future), true),
            (DlUnsatDisposition::Discard, Some(passed), false),
            (DlUnsatDisposition::Discard, None, false),
            (DlUnsatDisposition::PublishRaw, Some(future), false),
            (DlUnsatDisposition::PublishRaw, None, false),
        ] {
            exec.solve_deadline.set(found);
            let own = exec.solve_deadline.live().generation();
            let verdict = exec
                .run_dl_attempt(disposition, unbalanced)
                .expect("attempt");
            assert_eq!(verdict, SolveResult::Unknown);
            assert_eq!(
                exec.solve_deadline.get(),
                found,
                "{disposition:?} from {found:?}: the deadline it found is back"
            );
            assert_eq!(
                exec.solve_deadline.live().generation() == own,
                shared,
                "{disposition:?} from {found:?}: only a share leaves the own cell unwritten"
            );
        }
    }
}
