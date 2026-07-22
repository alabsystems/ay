// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Check-sat pipeline: solve dispatch, interrupt handling, logic routing.
//!
//! Extracted from `executor.rs` for code health — the check-sat pipeline
//! is the largest cohesive unit in the executor.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::time::Instant;
use ay_core::TermId;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};
use std::thread;
use std::time::Duration;

use super::quantifier_loop::unsupported_arith_mentions_ce_var;
use super::theories::bv_cnf_dump;
use super::Executor;
use crate::ematching::contains_quantifier;
use crate::executor_types::{Result, SolveResult, StatValue, UnknownReason};
use crate::features::StaticFeatures;
use crate::logic_detection::LogicCategory;

use super::{EXECUTOR_STACK_RED_ZONE, EXECUTOR_STACK_SIZE};

/// #mgr-row-peel: emission cap for the demand-driven deep read-over-write
/// repair stage. The peel universe is #select-roots × max-chain-depth, tiny on
/// the corpus classes it exists for (a 15-store chain peels to ~30 clauses);
/// the cap only fences pathological term stores. Hitting it can never affect
/// soundness — peel clauses are array tautologies and verdicts stay licensed
/// by the solve pipeline + independent model gate.
const MGR_ROW_PEEL_CLAUSE_CAP: usize = 20_000;

/// Verify the finalized private CNF/DRAT pair emitted for a `--self-check`
/// QF_BV solve. This runs at the executor boundary, before any API caller can
/// observe `Unsat`; the CLI may report the certification but is not trusted to
/// repair an unverified library result afterward.
fn verify_bv_drat_self_cert() -> std::result::Result<(), String> {
    let config = ay_core::trace_config();
    let cnf_path = config
        .bv_drat_self_cert_cnf_path
        .as_deref()
        .ok_or_else(|| "self-cert CNF path not configured".to_string())?;
    let drat_path = config
        .bv_drat_self_cert_drat_path
        .as_deref()
        .ok_or_else(|| "self-cert DRAT path not configured".to_string())?;

    let cnf_data = std::fs::read(cnf_path).map_err(|e| format!("cannot read CNF: {e}"))?;
    let cnf = ay_drat_check::cnf_parser::parse_cnf(&cnf_data[..])
        .map_err(|e| format!("cannot parse CNF: {e}"))?;
    if cnf.num_vars > ay_drat_check::checker::MAX_DENSE_VARS {
        return Err(format!(
            "formula variable count {} exceeds native DRAT checker maximum {}",
            cnf.num_vars,
            ay_drat_check::checker::MAX_DENSE_VARS
        ));
    }

    let drat_data = std::fs::read(drat_path).map_err(|e| format!("cannot read DRAT: {e}"))?;
    let steps = ay_drat_check::drat_parser::parse_drat(&drat_data)
        .map_err(|e| format!("cannot parse DRAT: {e}"))?;
    let mut checker =
        ay_drat_check::checker::DratChecker::new(cnf.num_vars, /*check_rat=*/ true);
    checker
        .verify(&cnf.clauses, &steps)
        .map_err(|e| format!("native DRAT check rejected the proof: {e}"))
}

fn has_only_uf_lia_theories(features: &StaticFeatures) -> bool {
    !features.has_arrays
        && !features.has_real
        && !features.has_bv
        && !features.has_strings
        && !features.has_seq_ops
        && !features.has_fpa
        && !features.has_int_div_mod
}

/// Kill switch (`AY_DPLL_NO_DT_UFLIA=1`) for the array-free DT+LIA routing that
/// sends `DtAuflia`/`Ufdtlia`/`Aufdtlia` problems through the UF+LIA combiner
/// (`solve_dt_uf_lia`) instead of the array-enabled `solve_dt_auflia`. Cached so
/// the per-query dispatch stays allocation-free. Default OFF (routing enabled).
fn dt_uflia_routing_disabled() -> bool {
    static FLAG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *FLAG.get_or_init(|| {
        std::env::var("AY_DPLL_NO_DT_UFLIA")
            .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
            .unwrap_or(false)
    })
}

impl Executor {
    /// Suppress certificate export for fresh solver runs used only to validate
    /// a previously produced proof/model. Such re-solves are not new user
    /// decisions and must not replace the caller's sealed CNF artifact.
    pub(crate) fn suppress_bv_cnf_export_for_internal_checks() -> impl Drop {
        bv_cnf_dump::suppress_internal_export()
    }

    /// Return whether BV CNF export is active for the current thread.
    ///
    /// Unlike the raw trace configuration, this observes the scoped
    /// suppression used by subordinate proof/model validation solves.
    pub(crate) fn bv_cnf_export_requested() -> bool {
        bv_cnf_dump::requested()
    }

    /// Clear a requested BV CNF artifact for a decision command that is
    /// rejected before the normal check-sat pipeline runs.
    ///
    /// The same serialized transaction/lock protocol is used as a real check,
    /// so parser fail-closed paths and unsupported optimization commands cannot
    /// leave a preceding query's artifact authoritative.
    pub fn invalidate_bv_cnf_export_for_rejected_check() -> Result<()> {
        let transaction = bv_cnf_dump::prepare_for_check()?;
        drop(transaction);
        Ok(())
    }

    pub(in crate::executor) fn set_active_solve_phase(
        &mut self,
        phase: impl Into<String>,
        cost_center: impl Into<String>,
    ) {
        self.active_solve_phase = Some(phase.into());
        self.active_solve_cost_center = Some(cost_center.into());
    }

    pub(in crate::executor) fn clear_active_solve_phase(&mut self) {
        self.active_solve_phase = None;
        self.active_solve_cost_center = None;
    }

    pub(in crate::executor) fn record_phase_duration(
        &mut self,
        stat_name: &str,
        started_at: Instant,
    ) {
        self.last_statistics
            .set_float(stat_name, started_at.elapsed().as_secs_f64());
    }

    fn default_unknown_phase_and_cost(reason: UnknownReason) -> (&'static str, &'static str) {
        match reason {
            UnknownReason::Timeout => ("search-control", "deadline"),
            UnknownReason::Interrupted => ("search-control", "interrupt"),
            UnknownReason::MemoryLimit => ("resource-control", "memory"),
            // Deterministic count budget (`:rlimit` / the default ground
            // budget, #ground-determinism) — distinct from the memory
            // ceiling so a budget-exhausted stop is truthfully attributed.
            UnknownReason::ResourceLimit => ("resource-control", "deterministic-budget"),
            UnknownReason::QuantifierRoundLimit => ("quantifier-instantiation", "ematching"),
            UnknownReason::QuantifierDeferred => {
                ("quantifier-instantiation", "deferred-instantiation")
            }
            UnknownReason::QuantifierUnhandled => ("quantifier-instantiation", "unhandled"),
            UnknownReason::QuantifierCegqiIncomplete => ("quantifier-instantiation", "cegqi"),
            UnknownReason::QuantifierEmatchingExistsIncomplete => {
                ("quantifier-instantiation", "ematching-exists")
            }
            UnknownReason::SplitLimit => ("theory-search", "split-loop"),
            UnknownReason::ExpressionSplit => ("theory-search", "expression-split"),
            UnknownReason::UnsupportedArithmetic => ("theory-preprocessing", "arithmetic-div-mod"),
            UnknownReason::UnsupportedMixedCollection => ("theory-combination", "mixed-collection"),
            UnknownReason::Unsupported => ("theory-combination", "unsupported-fragment"),
            UnknownReason::InternalError => ("executor", "internal-error"),
            UnknownReason::ProofTrusted => ("proof-validation", "trusted-proof-step"),
            UnknownReason::Incomplete | UnknownReason::Unknown => ("theory-search", "unknown"),
        }
    }

    fn default_unknown_detail(&self, reason: UnknownReason) -> String {
        match reason {
            UnknownReason::Timeout => "deadline expired before a definitive result".to_string(),
            UnknownReason::Interrupted => {
                "interrupt requested before a definitive result".to_string()
            }
            UnknownReason::QuantifierRoundLimit => format!(
                "E-matching budget exhausted after {} rounds and {} created instances",
                self.last_statistics.ematching_rounds_completed,
                self.last_statistics.ematching_instances_created
            ),
            UnknownReason::QuantifierDeferred => {
                "deferred quantifier instantiations remained after search".to_string()
            }
            UnknownReason::QuantifierUnhandled => {
                "one or more quantifiers had no complete instantiation path".to_string()
            }
            UnknownReason::QuantifierCegqiIncomplete => {
                "CEGQI could not disambiguate or refine the quantified formula".to_string()
            }
            UnknownReason::QuantifierEmatchingExistsIncomplete => {
                "E-matching touched existential quantifiers in an incomplete mode".to_string()
            }
            UnknownReason::UnsupportedArithmetic => {
                "symbolic integer div/mod fell outside the supported arithmetic fragment"
                    .to_string()
            }
            UnknownReason::UnsupportedMixedCollection => {
                "the selected mixed collection/datatype fragment is unsupported".to_string()
            }
            UnknownReason::SplitLimit => "theory split-loop budget was exhausted".to_string(),
            UnknownReason::ExpressionSplit => {
                "an expression split was required but not available".to_string()
            }
            UnknownReason::MemoryLimit => {
                "resource budget was exhausted before a definitive result".to_string()
            }
            UnknownReason::ResourceLimit => format!(
                "deterministic resource budget exhausted before a definitive result \
                 (conflicts={}, decisions={}; `:rlimit` or the default ground budget, \
                 #ground-determinism)",
                self.last_statistics.conflicts, self.last_statistics.decisions
            ),
            UnknownReason::Unsupported => {
                "the selected theory combination is unsupported".to_string()
            }
            UnknownReason::InternalError => "executor reported an internal error".to_string(),
            UnknownReason::ProofTrusted => {
                "strict proof mode rejected a trusted proof step".to_string()
            }
            UnknownReason::Incomplete | UnknownReason::Unknown => {
                "solver returned Unknown without a more specific completion reason".to_string()
            }
        }
    }

    pub(in crate::executor) fn record_unknown_diagnostic(
        &mut self,
        reason: UnknownReason,
        detail: impl Into<String>,
    ) {
        let (default_phase, default_cost) = Self::default_unknown_phase_and_cost(reason);
        let use_active_phase = matches!(
            reason,
            UnknownReason::Timeout
                | UnknownReason::Interrupted
                | UnknownReason::Incomplete
                | UnknownReason::Unknown
        );
        let phase = if use_active_phase {
            self.active_solve_phase
                .clone()
                .unwrap_or_else(|| default_phase.to_string())
        } else {
            default_phase.to_string()
        };
        let cost_center = if use_active_phase {
            self.active_solve_cost_center
                .clone()
                .unwrap_or_else(|| default_cost.to_string())
        } else {
            default_cost.to_string()
        };
        self.last_statistics
            .set_string("unknown.reason", reason.to_string());
        self.last_statistics.set_string("unknown.phase", phase);
        self.last_statistics
            .set_string("unknown.cost_center", cost_center);
        self.last_statistics.set_string("unknown.detail", detail);
    }

    /// Did an EXTERNAL stop condition fire for the current solve?
    ///
    /// Returns `Some(Interrupted)` when the caller's interrupt flag is set,
    /// `Some(Timeout)` when the live solve deadline has expired, `None`
    /// otherwise. Shared by `finalize_unknown_diagnostics` and
    /// `refine_unsupported_fragment_unknown_reason` so every truncation
    /// attribution uses the same definition of "externally stopped"
    /// (#quantifier-determinism).
    pub(in crate::executor) fn external_stop_reason(&self) -> Option<UnknownReason> {
        if self
            .solve_interrupt
            .as_ref()
            .is_some_and(|flag| flag.load(Ordering::Relaxed))
        {
            Some(UnknownReason::Interrupted)
        } else if self.solve_deadline.expired() {
            Some(UnknownReason::Timeout)
        } else {
            None
        }
    }

    pub(in crate::executor) fn finalize_unknown_diagnostics(&mut self) {
        if !matches!(self.last_result, Some(SolveResult::Unknown)) {
            return;
        }
        // #quantifier-determinism: attribute EXTERNALLY-CAUSED stops truthfully.
        // When the caller's interrupt (e.g. an application-side watchdog thread
        // that flips the interrupt handle at its own wall-clock budget — the
        // deductive-checks pattern) or the solve deadline fired during the solve, a
        // quantifier-loop classification recorded on the way out
        // (QuantifierUnhandled / QuantifierRoundLimit / ...) describes a
        // TRUNCATED pipeline, not a converged incompleteness verdict: once the
        // flag/deadline fires, every `should_stop` guard keeps breaking the
        // remaining instantiation work, so the specific quantifier reason is an
        // artifact of WHERE the break happened to land. Report Interrupted /
        // Timeout instead, so callers can distinguish "budget expired — retry
        // with a bigger budget may succeed" (their timeout/retry ladders key on
        // Interrupted/Timeout) from "the engine deterministically cannot decide
        // this" — previously the masked reason made a load-dependent truncation
        // look like a definitive incompleteness and suppressed caller-side
        // retries (the deductive-checks calc.rs Verified<->Unknown load flip). VERDICT-
        // NEUTRAL: the result stays Unknown either way; only the reason (and
        // its diagnostic strings) change, and only when the external stop
        // condition really fired. Specific non-truncation reasons (MemoryLimit,
        // UnsupportedArithmetic, ...) are never overridden.
        let externally_stopped = self.external_stop_reason();
        // `Incomplete` is the GENERIC no-better-information reason; when the
        // external stop demonstrably fired it is exactly the load-dependent
        // truncation artifact described above (which break site the expired
        // deadline happened to unwind through), never a converged capability
        // verdict. The exact expired-deadline precedence is pinned directly by
        // unit tests; external_stop_attribution also requires an end-to-end
        // positive-budget Timeout without inferring internal ordering from a
        // post-return elapsed measurement. Specific reasons (MemoryLimit,
        // UnsupportedArithmetic, ...) are still never overridden.
        let truncation_artifact = matches!(
            self.last_unknown_reason,
            None | Some(
                UnknownReason::Incomplete
                    | UnknownReason::QuantifierUnhandled
                    | UnknownReason::QuantifierRoundLimit
                    | UnknownReason::QuantifierDeferred
                    | UnknownReason::QuantifierCegqiIncomplete
                    | UnknownReason::QuantifierEmatchingExistsIncomplete
            )
        );
        if truncation_artifact {
            if let Some(reason) = externally_stopped {
                self.last_unknown_reason = Some(reason);
                // Overwrite any diagnostic recorded by the (truncated) breaking
                // site so phase/cost-center/detail agree with the reason.
                let detail = self.default_unknown_detail(reason);
                self.record_unknown_diagnostic(reason, detail);
            }
        }
        let reason = self.last_unknown_reason.unwrap_or(UnknownReason::Unknown);
        if self.last_statistics.get_string("unknown.phase").is_none() {
            let detail = self.default_unknown_detail(reason);
            self.record_unknown_diagnostic(reason, detail);
        } else if self.last_statistics.get_string("unknown.reason").is_none() {
            self.last_statistics
                .set_string("unknown.reason", reason.to_string());
        }
    }

    /// Solve the current `ctx.assertions` with quantifier preprocessing enabled.
    ///
    /// Shared by `check_sat_internal` and the quantified `check_sat_assuming`
    /// fallback path. Handles E-matching/CEGQI preprocessing, logic detection,
    /// quantified-LIA div/mod bailout, solver dispatch, and result remapping.
    pub(super) fn solve_current_assertions_with_quantifier_support(
        &mut self,
    ) -> Result<SolveResult> {
        // `defer_model_validation` is SET (line ~314 below) and CONSUMED/cleared
        // (restore_assertions) WITHIN this call. The nested alternation re-entries
        // (alternation_overapprox_unsat / alternation_uf_overapprox_unsat, see
        // result_mapping.rs) call this function DIRECTLY, bypassing
        // check_sat_internal's per-check reset. Clear it here too so a nested call
        // never inherits a leaked outer `true`: otherwise a quantifier-eliminating
        // preprocessing pass (e.g. collapsing an abstracted `(forall x. true)` to
        // a quantifier-free set) flips `qr.original_assertions` to None while the
        // leaked flag is still set, panicking in restore_assertions. The outer
        // value is independently saved/restored by the alternation re-entrancy
        // guard, so resetting here is safe. (#quant-alt-WS)
        self.defer_model_validation = false;
        let saved_unknown_reason = self.last_unknown_reason;
        // #incremental-pushpop-soundness: theory-solve dispatch runs in-place
        // preprocessing passes (FlattenAnd, ITE lifting, DT/array axiom
        // injection, div/mod elimination) directly on `self.ctx.assertions`.
        // Several of those passes change the LENGTH of the vector — e.g.
        // FlattenAnd in `solve_with_dt_axioms` splits a single top-level
        // `(and a b)` into `[a, b]`. `Context::pop()` truncates
        // `ctx.assertions` to the scope frame's recorded `assertion_count`
        // (a COUNT, not a marker), so any length change silently corrupts the
        // scope boundary: a later `(pop n)` then drops the wrong assertions and
        // a subsequent `(check-sat)` over the surviving set can return a
        // spurious `sat` on an unsat formula.
        //
        // The quantifier loop already snapshots and restores `ctx.assertions`
        // via `qr.original_assertions` whenever quantifier preprocessing rewrote
        // the assertion set. For the (common) NON-quantifier case nothing
        // restored it, so capture the scope-tracked vector here and restore it
        // on every exit path when the quantifier loop will not. This keeps the
        // scope-frame `assertion_count` invariant intact regardless of which
        // theory route ran or which in-place passes it applied.
        let scope_tracked_assertions = self.ctx.assertions.clone();

        // #ite-lift (kill-switch AY_DPLL_ITE_LIFT, default OFF): eager LINEAR
        // definitional naming of term-level ITEs. Replaces the default Shannon
        // expansion (which explodes on chained min-selection ITEs compared by
        // ordering atoms — see executor::ite_lift) with fresh-variable
        // definitions so each ITE condition is a single shared decision rather
        // than being re-expanded inside every arithmetic atom. Equisatisfiable;
        // the added definitional guards are transient solve-time assertions,
        // reverted with the rest of the scope-tracked set on exit. A no-op when
        // the switch is off (byte-identical preprocessing) or when there are no
        // non-Bool ITEs to name.
        if crate::executor::ite_lift::ite_lift_enabled() {
            let mut ite_defs: Vec<TermId> = Vec::new();
            let named = self
                .ctx
                .terms
                .name_non_bool_ites_all(&self.ctx.assertions, &mut ite_defs);
            if !ite_defs.is_empty() {
                self.ctx.assertions = named;
                self.ctx.assertions.extend(ite_defs);
            }
        }

        // Purify compound Boolean arguments to uninterpreted functions: rewrite
        // `f((and ...))` to `f(p)` and append `(= p (and ...))` for a fresh Bool
        // proxy `p`. Without this, EUF cannot congruence-close over UF
        // applications whose Boolean argument is a compound term, producing
        // false-SAT on QF_UF / QF_UFLIA (B-method CLEARSY) benchmarks. This is an
        // in-place pass like the others here; `scope_tracked_assertions` is
        // restored on every exit path, preserving the scope `assertion_count`
        // invariant. Equisatisfiable; a no-op when there are no such arguments.
        crate::executor::purify_bool_args::purify_bool_args(
            &mut self.ctx.terms,
            &mut self.ctx.assertions,
        );

        // Sound symmetry breaking for finite-model QF_UF (default ON,
        // `AY_EUF_LNH=0` disables). Prefers CADE'11 least-index prefix clauses
        // over totality subjects (z3's symmetry-reduce; collapses SEQ/QG
        // pigeonhole cores to level-0 cascades), falling back to the
        // unary-predicate-signature lex-leader. Both gated on a proven S_n
        // interchangeability check, so equisatisfiable. The additions are
        // scope-transient like the other in-place passes here
        // (`scope_tracked_assertions` restore), so each check-sat re-proves
        // the symmetry against its own assertion set.
        if crate::executor::lnh_symmetry::lnh_enabled() {
            let added = crate::executor::lnh_symmetry::add_lnh_symmetry_breaking(
                &mut self.ctx.terms,
                &mut self.ctx.assertions,
            );
            if added > 0 {
                tracing::info!(target: "ay::euf", lnh_sig_constraints = added, "LNH signature ordering applied");
            }
        }

        // Nelson-Oppen purification of opaque Int-sorted UF applications that
        // appear inside arithmetic (e.g. `(__euclid!div a b)` in `(* b div)`):
        // replace each with a fresh Int variable `v` + `(= v u)`. Without this,
        // LRA/NIA treats the application as an opaque slack it cannot relate to
        // the surrounding arithmetic, so a shared (dis)equality over it never
        // resolves and a satisfiable formula stalls to Unknown (the Euclidean
        // div/mod reconstruction with no `b != 0` premise). Equisatisfiable
        // (`v` is fresh, fully defined by `v = u`); a no-op when there are no
        // such operands.
        crate::executor::purify_int_uf_arith::purify_int_uf_arith(
            &mut self.ctx.terms,
            &mut self.ctx.assertions,
        );

        // Congruence exposure for CONSTANT-divisor `mod`/`div` under an
        // uninterpreted function (#G2-uflia-mod-in-uf-congruence): a `(mod x 3)`
        // sitting as an ARGUMENT to `f` is eliminated to a per-assertion-DISTINCT
        // fresh remainder var by `mod_div_elim`, so `(f (mod x 3))` and a
        // separately-asserted `(= (mod x 3) 1)` are never congruence-linked
        // (`f((mod x 3)) = f(1)` is lost) and a ground-decidable formula stalls to
        // `unknown`. Naming the shared term with ONE proxy `v` (rewriting every
        // occurrence, so `(= (mod x 3) 1)` becomes `(= v 1)` and the UF arg
        // becomes `(f v)`) restores the EUF link `f(v) = f(1)`. Equisatisfiable
        // (`v` fresh, fully defined by `v = (mod x 3)`); a no-op when no
        // constant-divisor mod/div sits under a UF. Symbolic-divisor mod/div is
        // excluded (it uses different, proxy-fragile SAT machinery).
        crate::executor::purify_int_uf_arith::purify_mod_div_uf_args(
            &mut self.ctx.terms,
            &mut self.ctx.assertions,
        );

        // Rewrite const-array reads through a ground `V = const-array(c)`
        // equality: replace each syntactic `select(V, idx)` with `c`. Without
        // this, a read of a variable that is only tied to a constant array by a
        // separate ground assertion stays opaque to LRA/LIA, so arithmetic that
        // consumes it (e.g. the set-length ite-definitions
        // `(= len_n (+ len_{n-1} (ite (select V k) 0 1)))`) is left
        // unconstrained and a genuine counterexample stalls to Unknown under
        // strict BV-backed-array model validation. Equisatisfiable
        // (`select(const-array(c), idx) = c` is valid under `V = const-array(c)`,
        // asserted as a top-level unit fact); a no-op when there is no such
        // ground equality with a matching read.
        crate::executor::rewrite_const_array_reads::rewrite_const_array_reads(
            &mut self.ctx.terms,
            &mut self.ctx.assertions,
        );

        // Soundness pass (finite-enum DOMAIN COVERAGE, #dt-enum-func-coverage
        // wrong-SAT): every term of an all-nullary (enum) datatype sort equals one
        // of its constructor constants. Asserting that coverage disjunction for
        // each enum-sorted FUNCTION-APPLICATION term (which EUF otherwise floats
        // free of the finite domain) lets the SAT/EUF layer case-split and refute
        // a FUNCTIONAL pigeonhole the `distinct`-clique check cannot — e.g.
        // `(distinct (f a) (f (f (f a))))` over a 2-enum. Each disjunction is valid
        // in every model (a datatype value IS one of its constructors), so it
        // removes none. Runs HERE — before logic detection / Tseitin setup — so
        // the coverage equality atoms are registered as active theory atoms and
        // the datatype theory enforces them (running it post-detection left the
        // atoms theory-inactive, so a propositional model floated `f(a)` to a
        // fresh out-of-domain value and only the model-validation net caught it,
        // degrading to `unknown` instead of the correct `unsat`). In-place like
        // the other passes here; `scope_tracked_assertions` is restored on exit.
        self.add_finite_enum_domain_coverage();

        // Soundness pass (#P0.2 symbolic RoundingMode, Pass B): RoundingMode is
        // a FIXED 5-element domain, but its core representation is an
        // uninterpreted sort, so EUF alone merged distinct modes
        // (`(= RTP RTZ)` → wrong sat) and floated declared RM consts out of the
        // domain (`(distinct a b c d e f)` over 6 RM consts → wrong sat,
        // pigeonhole). Assert `(distinct RNE RNA RTP RTN RTZ)` plus a coverage
        // disjunction per non-literal RM-sorted ground term (all VALID — never
        // removes a model), and FAIL CLOSED to `unknown` on any RM shape the
        // pass cannot fully cover (RM under a quantifier, budget) — an
        // uncovered RM term leaves a wrong `sat` reachable. Strict no-op when
        // RoundingMode only occurs as a literal FP rounding-op operand
        // (literal-mode FP corpora stay byte-identical). Runs HERE, with the
        // other scope-transient in-place passes, so the axioms reach EVERY
        // theory route; the FP lane additionally folds them away under its
        // mode enumeration (see theories/fp/rm_expand.rs).
        let rm_roots = self.ctx.assertions.clone();
        match self.rm_domain_axioms(&rm_roots) {
            crate::executor::rm_domain::RmDomainAxioms::NoMention => {}
            crate::executor::rm_domain::RmDomainAxioms::Axioms(axioms) => {
                for axiom in axioms {
                    // Provenance-registered like the finite-enum precedent so
                    // proofs/cores attribute the injected axiom honestly.
                    self.push_array_axiom_assertion_site(axiom, "rm_domain_coverage");
                }
            }
            crate::executor::rm_domain::RmDomainAxioms::FailClose => {
                self.ctx.assertions = scope_tracked_assertions;
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                return Ok(SolveResult::Unknown);
            }
        }

        let (_, pre_quantifier_features) = self.detect_logic_category(&self.ctx.assertions);
        self.last_statistics
            .set_int("smt.bv_lia_bridge.pre_quantifier_runs", 0);
        if pre_quantifier_features.has_bv_int_conversion {
            self.last_statistics
                .set_int("smt.bv_lia_bridge.pre_quantifier_runs", 1);
            let bridge_result = self.solve_bv_lia_bridge()?;
            if bridge_result.is_unsat() {
                // Restore the scope-tracked assertion vector (the bridge may
                // have rewritten it in place) before the early exit.
                self.ctx.assertions = scope_tracked_assertions;
                return Ok(bridge_result);
            }
            self.last_unknown_reason = saved_unknown_reason;
        }

        // Quantifier preprocessing: E-matching, CEGQI, promote-unsat, assertion filtering.
        // Reads last_model.euf_model for congruence-aware E-matching, then clears it.
        self.set_active_solve_phase("quantifier-preprocess", "quantifier-instantiation");
        let quantifier_started_at = Instant::now();
        let has_quantified_assertions = self
            .ctx
            .assertions
            .iter()
            .any(|&assertion| contains_quantifier(&self.ctx.terms, assertion));
        // Record for the AUFLIA preprocessor's array-alias-collapse soundness
        // gate (see `original_problem_had_quantifiers`). Captured here, before
        // `process_quantifiers` strips/instantiates the quantifiers.
        self.original_problem_had_quantifiers = has_quantified_assertions;
        // #quantifier-determinism (Fix A): quantified solves terminate
        // PRIMARILY on the deterministic instantiation budgets (E-matching
        // round/instance caps, interleaved/CEGQI/MBQI round caps) so identical
        // inputs do identical instantiation work regardless of machine speed
        // or CPU load. Relax the caller's nominal wall-clock deadline into a
        // far-out hang-protection backstop for the remainder of this
        // quantified solve; the per-call install/restore pair at the check-sat
        // boundary unwinds it. See `install_quantifier_deadline_backstop` for
        // the verdict-safety argument.
        if has_quantified_assertions {
            self.install_quantifier_deadline_backstop();
        }
        let mut saved_quantified_incremental_state =
            if self.incremental_mode && has_quantified_assertions {
                // Quantifier preprocessing temporarily strips quantified assertions
                // and injects ground instances. Reusing persistent theory SAT/Tseitin
                // state, generation tracking, or a previous solve's model from an
                // earlier scoped quantified window can make the live incremental
                // solve diverge from a fresh replay of the same active assertions.
                // Start quantified incremental windows cleanly for this solve, then
                // restore the outer scoped state so later pop commands remain
                // balanced. The persistent BV incremental state is included
                // (#qmg-incr-bv-scope-leak): quantifier-lane nested probes
                // (closed-universal precheck, QMG confirm, disambiguation
                // re-solves) otherwise encode probe assertions into the outer
                // persistent BV SAT as scope activations that a later check-sat
                // in the same scope replays — flipping a satisfiable re-check
                // to a wrong UNSAT. Do not restore `last_model`: this check-sat call owns the
                // next visible model, and stale models can cause E-matching to skip
                // instances that are only "satisfied" by the old assignment.
                self.last_model = None;
                Some((
                    self.incr_theory_state.take(),
                    self.incr_bv_state.take(),
                    self.quantifier_manager.take(),
                ))
            } else {
                None
            };
        // Normalise linear equalities inside quantified assertions (e.g.
        // `(= (- q1 0) (- q1 1))` -> `false`) so a genuinely-arithmetic universal
        // is not misrouted as alternation by a witness-dependent dead literal.
        self.fold_quantified_linear_eqs();
        // #quantprod-g2: fold `select` over literal const-arrays (direct or
        // pinned by a retained top-level ground equality) inside quantified
        // assertions, so `(forall x. (= (select a x) k))` under `(= a ((as
        // const …) k))` collapses to a vacuous tautology the next pass
        // removes, instead of the whole problem failing closed through the
        // MBQI-unsafe quantified-array degrade. Equivalence-preserving in
        // both polarities (see the method docs); non-foldable quantified
        // array shapes flow on byte-identically.
        if has_quantified_assertions && pre_quantifier_features.has_arrays {
            self.fold_pinned_const_array_selects();
        }
        // Drop unused bound variables / collapse vacuous quantifiers (valid over
        // non-empty sorts). A body-ignores-binder universal like
        // `(forall y. (> b 0))` otherwise masquerades as an alternation candidate
        // and defeats the sound refutation of a sibling genuine forall, yielding a
        // wrong SAT (#quant-alt-WS). Safe in nested alternation re-entries because
        // solve_current_assertions_with_quantifier_support now clears the
        // defer_model_validation flag on entry.
        self.simplify_vacuous_quantifiers();
        // Deep QE pre-pass (#qe-prepass): equivalence-preserving quantifier
        // elimination (Cooper for Int, Loos-Weispfenning for Real) with binder
        // descent, ∀-duality, and capped ∃-over-∨ distribution. Adopts a
        // rewrite ONLY when the assertion becomes fully quantifier-free
        // (all-or-nothing); every refusal keeps the original TermId, so
        // out-of-fragment problems flow into the quantifier loop unchanged.
        // Each individual elimination is gated by the engines' independent
        // fail-closed equivalence self-checks. In-place and length-preserving
        // (`&mut [TermId]`), so the scope-frame `assertion_count` invariant
        // holds on every exit path, including the quantifier-loop restore
        // whose snapshot is taken after this point.
        if has_quantified_assertions {
            crate::executor::qe_prepass::deep_qe(
                &mut self.ctx.terms,
                &mut self.ctx.assertions,
                self.solve_interrupt.as_deref(),
            );
        }
        // Soundness precheck (#quant-ws closed-forall wrong-SAT): a top-level
        // conjunct that is a `(forall vars body)` with a CLOSED, quantifier-free
        // body (no free constant / UF / array / outer-bound var — only the
        // forall's own binders) is model-independent: either valid or
        // unconditionally FALSE. If it is provably false (skolemized `(not body)`
        // is definitively SAT) the whole conjunctive problem is UNSAT regardless
        // of the other assertions, so decide UNSAT here before the heavy
        // quantifier machinery (whose array/MBQI-unsafe handling otherwise leaves
        // the closed false universal unrefuted, yielding a wrong SAT). Only ever
        // returns UNSAT, and only on a PROVABLY-false conjunct — it cannot
        // over-degrade a genuine SAT or touch a `∀x∃y.P` alternation (body has a
        // quantifier ⇒ excluded) or an array-extensionality universal (free array
        // symbol ⇒ excluded). Gated on the presence of quantified assertions.
        if has_quantified_assertions {
            let (precheck_category, _) = self.detect_logic_category(&self.ctx.assertions);
            if let Some(precheck) = self.closed_universal_validity_precheck(precheck_category) {
                self.ctx.assertions = scope_tracked_assertions;
                if let Some((incr_theory_state, incr_bv_state, quantifier_manager)) =
                    saved_quantified_incremental_state.take()
                {
                    self.incr_theory_state = incr_theory_state;
                    self.incr_bv_state = incr_bv_state;
                    self.quantifier_manager = quantifier_manager;
                }
                return precheck;
            }
        }
        // Soundness pass (#qarr-ext-quant wrong-SAT): a top-level conjunctive
        // `(forall ((i S)) (= (select a i) (select b i)))` (or its guarded form
        // patched at the excluded index) forces `a = b` by array extensionality.
        // Assert that ground equality up front so the array solver refutes a
        // sibling `(not (= a b))` directly, instead of the bounded quantifier
        // path building a finite model over only the touched indices and missing
        // the extensionality witness (wrong SAT). `(= a b)` is a logical
        // consequence of the premise, so it removes no models. Runs before
        // `process_quantifiers` (which strips the forall) and only when arrays
        // and quantifiers are both present.
        if pre_quantifier_features.has_arrays {
            self.add_quantified_array_extensionality_equalities();
        }
        // M1 demand-campaign SHADOW family classifier: snapshot the positive
        // top-level foralls the E-matcher is about to see (post fold/simplify, before
        // `process_quantifiers` strips them). READ ONLY — introduces no terms; the
        // classification below feeds only statistics, never a decision. Skipped
        // entirely on ground problems (no walk overhead when there are no foralls).
        let classifier_foralls = if has_quantified_assertions {
            self.collect_classifiable_foralls()
        } else {
            Vec::new()
        };

        // M4 DT-MBQI-Sat RE-SEQUENCING (AY_DT_CERT-gated; byte-identical when the
        // gate is unset). The real rusthorn/bsl obligations DIVERGE in the ground
        // DT-unroll BEFORE ever producing a quantifier-class `Unknown`, so the
        // post-solve certificate consult never fires and no candidate survives.
        // Re-sequence: solve the GROUND-CORE fragment FIRST (bounded, terminating),
        // COMPLETE that candidate, and CERTIFY every `forall` against it — before
        // the divergent unroll. Grant-only and fail-closed: on ANY decline it
        // restores state untouched and the normal solve proceeds with its own
        // verdict. Runs only when quantifiers are present (fast-declines otherwise).
        if has_quantified_assertions {
            if let Some(sat) = self.dt_cert_resequence_probe() {
                // The certificate is the sole grant authority — it re-verified the
                // WHOLE snapshot (grounds + every forall route) against the single
                // completed model M'. The candidate left in `last_model` only
                // solves the GROUND CORE (the foralls were never asserted into it,
                // and the bridge UFs are not yet reinterpreted as their selectors),
                // so a blind re-validation of THAT candidate would spuriously
                // refute even though M' is a genuine model. Defer model validation
                // exactly as the E-matching-rewrote-assertions path does: the
                // strict pre-skip oracle still runs (no known-wrong ground model
                // can escape), but the full observation pipeline is skipped in
                // favour of the certificate. `last_model_validated` satisfies the
                // `emit_sat_verdict` gate.
                self.defer_model_validation = false;
                self.last_model_validated = true;
                self.dt_cert_grant_active = true;
                self.last_unknown_reason = None;
                self.ctx.assertions = scope_tracked_assertions;
                if let Some((incr_theory_state, incr_bv_state, quantifier_manager)) =
                    saved_quantified_incremental_state.take()
                {
                    self.incr_theory_state = incr_theory_state;
                    self.incr_bv_state = incr_bv_state;
                    self.quantifier_manager = quantifier_manager;
                }
                return sat;
            }
        }

        let mut qr = self.process_quantifiers();
        self.record_phase_duration("phase.quantifier_preprocess.seconds", quantifier_started_at);
        // Populate E-matching statistics from quantifier processing (#8614).
        self.last_statistics.ematching_rounds_completed = qr.ematching_rounds_completed;
        self.last_statistics.ematching_instances_created = qr.ematching_instances_created;
        // M0' demand-campaign instrumentation: surface the pure-observation
        // `quantifier.demand.*` counters accumulated on the quantifier manager
        // during `process_quantifiers`. Read-only; never influences any decision.
        // Cloning first ends the immutable borrow of `quantifier_manager` before
        // `last_statistics` is borrowed mutably.
        let demand_stats = self
            .quantifier_manager
            .as_ref()
            .map(crate::quantifier_manager::QuantifierManager::demand_stats_clone);
        if let Some(demand_stats) = demand_stats {
            demand_stats.write_statistics(&mut self.last_statistics);
            // M1 shadow classification: tag the M0' per-family tallies with the
            // demand-campaign family class and surface the per-class population +
            // activity counts. Pure observation; `classify_quantifier_families`
            // reads only the term store.
            let classes = self.classify_quantifier_families(&classifier_foralls);
            crate::executor::quantifier_loop::write_family_class_statistics(
                &demand_stats,
                &classes,
                &mut self.last_statistics,
            );
        }
        // M2+M3 demand-lane counters (SHADOW-ONLY; inert on production — the writer
        // is a no-op unless the lane was armed): frontier, parked/flushed tallies,
        // fence drains, DT resume depth.
        if let Some(qm) = self.quantifier_manager.as_ref() {
            qm.demand_write_statistics(&mut self.last_statistics);
        }
        self.last_model = None;

        self.set_active_solve_phase("logic-detection", "logic-category");
        let logic_started_at = Instant::now();
        let (category, features) = self.detect_logic_category(&self.ctx.assertions);
        self.record_phase_duration("phase.logic_detection.seconds", logic_started_at);
        self.last_statistics
            .set_string("solver.logic_category", format!("{category:?}"));

        // A Seq solve rewrites its assertion window in place (length proxies,
        // point-read reduction, and generated length axioms).  The inner model
        // gate therefore sees solver-internal assertions before the ordinary
        // non-quantifier scope restoration below.  In fail-closed self-check
        // mode that is the wrong certification boundary: internal auxiliaries
        // are deliberately not authored assertions, so they are skipped and a
        // perfectly concrete witness such as `seq.len(a) > 100` is degraded to
        // Unknown even though the reconstructed sequence independently satisfies
        // the user's formula.
        //
        // Reuse the quantified restoration protocol for QF Seq self-checks:
        // defer the inner gate, restore the exact pre-preprocessing assertion
        // snapshot in `restore_assertions`, and run the normal strict +
        // independent model validators there.  No SAT authority is added: the
        // final verdict still requires every authored assertion to evaluate to
        // true under the reconstructed model, and any incomplete reconstruction
        // remains Unknown.  Other theory lanes retain their existing validation
        // and refinement sequencing.
        if self.self_check
            && qr.original_assertions.is_none()
            && matches!(
                category,
                LogicCategory::QfSeq | LogicCategory::QfSeqBv | LogicCategory::QfSeqlia
            )
        {
            qr.original_assertions = Some(scope_tracked_assertions.clone());
        }

        // Defer model validation when quantifier E-matching modified the assertion set.
        // The theory solver would validate against ground instances instead of the original
        // quantified assertions, causing false violations (#2862). Validation happens after
        // original_assertions are restored in map_quantifier_result.
        if qr.original_assertions.is_some() {
            self.defer_model_validation = true;
        }

        // Bail early on quantified LIA/LRA only when unsupported arithmetic
        // depends on the CEGQI counterexample variables. A ground div/mod atom
        // elsewhere in a QuantifierConsumer query must not preempt the normal ground solve:
        // interleaved E-matching may still close the quantified obligation.
        if qr.cegqi_has_forall
            && features.has_int_div_mod
            && matches!(category, LogicCategory::Lia | LogicCategory::Lra)
            && unsupported_arith_mentions_ce_var(
                &self.ctx.terms,
                &self.ctx.assertions,
                &qr.cegqi_state,
            )
        {
            self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
            let result = Ok(SolveResult::Unknown);
            let quantifier_loop_restores = qr.original_assertions.is_some();
            let mapped = self.map_quantifier_result(result, qr, category);
            if !quantifier_loop_restores {
                self.ctx.assertions = scope_tracked_assertions;
            }
            if let Some((incr_theory_state, incr_bv_state, quantifier_manager)) =
                saved_quantified_incremental_state.take()
            {
                self.incr_theory_state = incr_theory_state;
                self.incr_bv_state = incr_bv_state;
                self.quantifier_manager = quantifier_manager;
            }
            return mapped;
        }

        // Soundness pass (card-1 element-sort arrays): if an array's element
        // sort has cardinality one, all arrays of that sort are equal, so any
        // asserted array disequality is UNSAT. Datatype cardinality is only
        // resolvable here (the array theory sees the element sort as an opaque
        // `Uninterpreted` name). Runs once before dispatch; a no-op unless a
        // card-1-element array disequality is present.
        self.add_singleton_array_sort_equalities();
        // Companion soundness pass: fold ANY equality atom over a singleton sort
        // (datatype or array) to `true`, including positive / nested uses such
        // as `(= v (store v i c))` over a singleton element sort that the
        // disequality-only pass above does not reach. (#bug05 wrong-sat)
        self.fold_singleton_sort_equalities();
        // Companion soundness pass (finite-enum CARDINALITY / pigeonhole): an
        // all-nullary datatype sort has exactly `k` inhabitants; forcing more
        // than `k` pairwise-distinct values of that sort is UNSAT. Generalizes
        // the singleton (`k == 1`) passes above to enums with `k > 1`. A no-op
        // unless a disequality clique over a finite-enum sort exceeds `k`.
        let pigeonhole_unsat = self.add_finite_enum_pigeonhole_conflict();
        // Companion soundness pass: const-arrays with provably-distinct defaults
        // are extensionally distinct; assert their disequality so model-based
        // theory combination can't merge them into one class (false UNSAT).
        // (#arr_lia561 wrong-unsat)
        if features.has_arrays {
            self.add_distinct_const_array_disequalities();
            // Companion soundness pass (finite-index array extensionality): an
            // array over a FINITE index domain (Bool {false,true}, a small BitVec
            // width, or an enum datatype) is equal iff it agrees at every index.
            // Without the biconditional, `(distinct a b)` / `(not (= a b))` over a
            // `(Array Bool _)` whose two selects are pinned equal was wrongly SAT
            // (#arr-bool-ext). The pass already runs inside solve_array_euf /
            // the BV path; emit it eagerly here too so combined array+LIA/ALL
            // dispatches (which bypass solve_array_euf) also get it. Sound — the
            // biconditional is a tautology of array extensionality over a finite
            // index domain.
            self.add_finite_index_array_extensionality();
            // Companion: a `(select arr i)` over a finite (Bool / enum) index
            // domain with a SYMBOLIC index `i` must equal the value at whichever
            // domain element `i` is; emit the ITE expansion so the ground solver
            // case-splits it (#arr-finite-symbolic-index). Sound tautology.
            self.add_finite_index_select_expansion();
        }

        self.set_active_solve_phase("solver-dispatch", format!("theory:{category:?}"));
        let solver_started_at = Instant::now();
        // Exact input the primary dispatch sees (after the pre-dispatch soundness
        // passes above), for the post-dispatch partition rescue.
        let pre_dispatch_assertions = self.ctx.assertions.clone();
        let result = if pigeonhole_unsat {
            // The finite-enum pigeonhole pass re-verified a disequality clique
            // of size `> k` over a `k`-inhabitant enum sort and asserted
            // `false`: the conjunction is UNSAT outright. Conclude here instead
            // of dispatching — on coloring-scale inputs (100k+ asserts, e.g.
            // SMT-LIB 20210312-Bouvier) the ground lane would spend minutes
            // Tseitin-encoding the full formula just to rediscover the pushed
            // unit conflict. Same answer, same downstream mapping/restore path.
            Ok(SolveResult::unsat())
        } else {
            self.route_to_solver(category, &features)
        };
        self.record_phase_duration("phase.solver_dispatch.seconds", solver_started_at);
        if std::env::var_os("AY_F1_DIAG").is_some() {
            if let Ok(r) = &result {
                eprintln!(
                    "AY_F1_DIAG: route_to_solver({category:?}) -> {r:?} model_present={}",
                    self.last_model.is_some()
                );
            }
        }

        // Post-dispatch symbol-disjoint partition rescue (Wave C P2-multitheory):
        // when the primary returns Unknown(Incomplete), split the conjunction
        // into symbol-connectivity components and combine. No-op on every result
        // that already decides. See executor/partition_rescue.rs.
        let result = self.try_partition_rescue(result, &pre_dispatch_assertions);

        // Map theory-solve result through quantifier/CEGQI semantics and restore assertions.
        self.set_active_solve_phase("quantifier-result-mapping", "quantifier-result-mapping");
        let mapping_started_at = Instant::now();
        let quantifier_loop_restores = qr.original_assertions.is_some();
        let mapped = self.map_quantifier_result(result, qr, category);
        self.record_phase_duration(
            "phase.quantifier_result_mapping.seconds",
            mapping_started_at,
        );
        if std::env::var_os("AY_F1_DIAG").is_some() {
            if let Ok(r) = &mapped {
                eprintln!(
                    "AY_F1_DIAG: map_quantifier_result -> {r:?} model_present={}",
                    self.last_model.is_some()
                );
            }
        }
        // When the quantifier loop did not snapshot/restore the assertion set
        // (no quantifiers were rewritten), restore the scope-tracked vector so
        // any in-place theory preprocessing cannot corrupt the scope-frame
        // assertion counts relied upon by `Context::pop()`.
        if !quantifier_loop_restores {
            self.ctx.assertions = scope_tracked_assertions;
        }
        if let Some((incr_theory_state, incr_bv_state, quantifier_manager)) =
            saved_quantified_incremental_state.take()
        {
            self.incr_theory_state = incr_theory_state;
            self.incr_bv_state = incr_bv_state;
            self.quantifier_manager = quantifier_manager;
        }
        mapped
    }

    /// M4 DT-MBQI-Sat ground-core RE-SEQUENCING probe.
    ///
    /// Returns `Some(Ok(Sat))` iff, with `AY_DT_CERT=on`, the snapshot is the
    /// DT-MBQI-sat shape (a top-level datatype-binder `forall` is present), its
    /// GROUND CORE (the quantifier-free assertions) is satisfiable, AND
    /// [`Executor::try_dt_model_sat_certificate`] certifies EVERY `forall`
    /// against that completed candidate. It never influences an UNSAT and never
    /// grants without the certificate.
    ///
    /// SOUNDNESS: the certificate re-verifies EVERY snapshot assertion (grounds
    /// + every forall route) against the ONE completed model `M'` (single
    /// authority, post-F3-rewrite). The ground-core solve only PRODUCES the
    /// candidate — the certificate is the sole grant authority, exactly as the
    /// finite-table certificate is on the post-solve consult. Byte-identical when
    /// the gate is unset (the env check is the first statement) or when no
    /// datatype-binder forall is present (fast decline). Fail-closed on every
    /// other path: state is restored and `None` returned.
    fn dt_cert_resequence_probe(&mut self) -> Option<Result<SolveResult>> {
        // Gate: byte-identical unless AY_DT_CERT=on.
        if !matches!(std::env::var("AY_DT_CERT").ok().as_deref(), Some("on")) {
            return None;
        }
        // Test-only route selector: the DT certificate has two independent
        // grant sites (this bounded pre-solve probe and the post-solve
        // quantifier-result mapper).  Production builds do not contain this
        // hook; tests use it to pin the latter path deterministically instead
        // of relying on host load to make this probe miss its wall budget.
        #[cfg(test)]
        if std::env::var_os("AY_INTERNAL_DT_CERT_SKIP_RESEQUENCE").is_some() {
            return None;
        }
        if self.external_stop_reason().is_some() {
            return None;
        }
        let snapshot = self.ctx.assertions.clone();
        // Shape gate: at least one top-level datatype-binder forall.
        let has_dt_forall = snapshot.iter().any(|&a| {
            matches!(self.ctx.terms.get(a), ay_core::TermData::Forall(vars, _, _)
                if vars.iter().any(|(_, s)| self.dt_cert_sort_is_datatype(s)))
        });
        let dbg = std::env::var_os("AY_DEBUG_CERT").is_some();
        if !has_dt_forall {
            return None;
        }
        // Ground core = the quantifier-free assertions.
        let ground: Vec<TermId> = snapshot
            .iter()
            .copied()
            .filter(|&a| !contains_quantifier(&self.ctx.terms, a))
            .collect();
        if ground.is_empty() {
            return None;
        }

        // M5 (net-negative re-sequencing fix, item 5a): census-informed precheck.
        // Decline BEFORE the expensive ground-core solve when a `forall` is
        // definitely unclaimable by the cert (e.g. the tuple-encoding premises
        // `∀a:Int,b:Tree. a=tuple_get_0(tuple2(a,b))` observed live). Decline-only
        // and model-free, so it never suppresses a grant; it removes the wasted
        // ground-core solve on snapshots the cert would reject anyway.
        if !self.dt_cert_snapshot_structurally_claimable(&snapshot) {
            if dbg {
                eprintln!("c CERT/dt-mbqi-sat re-sequence: precheck decline (unclaimable forall)");
            }
            return None;
        }

        // Scoped ground-core solve (assertion swap + incr-state take, mirroring
        // `ground_core_is_unsat`), leaving `last_model` = the candidate on Sat.
        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, ground.clone());
        let saved_incr = self.incr_theory_state.take();
        let saved_defer = self.defer_model_validation;
        let saved_reason = self.last_unknown_reason;
        self.defer_model_validation = false;
        self.last_model = None;
        let (category, features) = self.detect_logic_category(&ground);
        // The soundness passes the top-level dispatch runs before `route_to_solver`
        // (over the swapped-in ground core; discarded with it on restore).
        self.add_singleton_array_sort_equalities();
        self.fold_singleton_sort_equalities();
        let pigeonhole_unsat = self.add_finite_enum_pigeonhole_conflict();
        if features.has_arrays {
            self.add_distinct_const_array_disequalities();
            self.add_finite_index_array_extensionality();
            self.add_finite_index_select_expansion();
        }
        // M5 (net-negative re-sequencing fix, item 5b): budget-cap the ground-core
        // solve. A genuine cert candidate is cheap (fullsort-class ground fragments
        // solve in a few seconds); an expensive churn here is a pathological
        // DT-unroll that yields no Sat candidate, so bound it TIGHTLY (never loosen
        // the live deadline) and decline on expiry rather than burning the whole
        // obligation envelope — the 99s→232s cert-on regression came entirely from
        // this duplicated, never-Sat ground solve. Restored on every exit path.
        const DT_CERT_GROUNDCORE_BUDGET: Duration = Duration::from_secs(8);
        let saved_deadline = self.solve_deadline.get();
        let budget = Instant::now() + DT_CERT_GROUNDCORE_BUDGET;
        let capped = saved_deadline.map_or(budget, |d| d.min(budget));
        self.solve_deadline.set(Some(capped));
        let result = if pigeonhole_unsat {
            Ok(SolveResult::unsat())
        } else {
            self.route_to_solver(category, &features)
        };
        self.solve_deadline.set(saved_deadline);
        // Restore assertions + incremental state; KEEP `last_model` (the candidate).
        self.ctx.assertions = saved_assertions;
        self.incr_theory_state = saved_incr;
        if !matches!(result, Ok(SolveResult::Sat)) {
            self.defer_model_validation = saved_defer;
            self.last_unknown_reason = saved_reason;
            self.last_model = None;
            return None;
        }
        // Certify the FULL snapshot against the completed candidate. The cert is
        // the sole grant authority and re-verifies every assertion under M'.
        let cert = self.try_dt_model_sat_certificate(&snapshot, category);
        if dbg {
            eprintln!(
                "c CERT/dt-mbqi-sat re-sequence: ground-core={} category={category:?} grant={}",
                ground.len(),
                cert.is_some()
            );
        }
        if cert.is_some() {
            // Make the certified foralls DEFER-eligible in the mandated
            // quantified-model gate: strip the printed function-table
            // interpretation of every arity>0 head occurring in a certified
            // forall from the emitted candidate. The candidate only solves the
            // ground core, so those tables' arbitrary defaults do not witness the
            // universals; a blind nested re-check against them would spuriously
            // refute a genuine model. The certificate already validated every
            // forall against the completed M'. Per-application GROUND pins (which
            // the strict / independent / authoritative gates read) are
            // authoritative over the arg-keyed tables and survive, so ground
            // validation is unaffected.
            self.dt_cert_strip_forall_uf_tables(&snapshot);
            return Some(Ok(SolveResult::Sat));
        }
        // Declined: restore verdict-shaping state and fall through to the normal
        // (possibly divergent) solve with its own conclusion.
        self.defer_model_validation = saved_defer;
        self.last_unknown_reason = saved_reason;
        self.last_model = None;
        None
    }

    /// `sort` is a declared datatype (either a `Datatype` sort or an
    /// `Uninterpreted` name registered as a datatype).
    fn dt_cert_sort_is_datatype(&self, sort: &ay_core::Sort) -> bool {
        match sort {
            ay_core::Sort::Datatype(_) => true,
            ay_core::Sort::Uninterpreted(name) => self.ctx.datatype_iter().any(|(n, _)| n == name),
            _ => false,
        }
    }

    /// Run check-sat on current assertions.
    ///
    /// `pub(crate)`: External consumers MUST use `api::Solver::check_sat()` which
    /// returns `VerifiedSolveResult`. This method performs runtime validation
    /// (via `finalize_sat_model_validation`) but does not carry compile-time
    /// verification provenance. Part of #5787 (Phase 6).
    pub(crate) fn check_sat(&mut self) -> Result<SolveResult> {
        // Internal probes share this entry point, so retain their surrounding
        // state but never let an earlier certificate survive a new-solve error.
        self.last_sat_certificate = None;
        // Reset the BV-DRAT self-cert flag: it is (re)armed below only for an
        // eligible top-level pure-QF_BV check-sat and set true by the BV solver
        // when it actually emits a native-checkable UNSAT DRAT for this solve.
        self.last_bv_drat_self_cert = false;
        // `--self-check` BV DRAT self-certification: arm the eager bit-blast
        // CNF+DRAT export at the self-cert temp paths for a top-level pure-QF_BV
        // query. The arm is a thread-local RAII guard, so all export gating
        // (`requested`/`enabled`/`configured_path`) sees the temp files ONLY
        // inside this scope; any non-BV / probe / optimization solve leaves it
        // disarmed and behaves exactly as before.
        let _self_cert_arm = self.maybe_arm_bv_drat_self_cert();
        let dump_roots = if bv_cnf_dump::requested() {
            self.ctx.assertions.clone()
        } else {
            Vec::new()
        };
        let dump_transaction = bv_cnf_dump::prepare_for_check()?;
        self.validate_bv_cnf_export_roots(&dump_roots)?;
        let solve_started_at = Instant::now();
        let previous_deadline = self.install_timeout_deadline_for_call();
        // Guard against small thread stacks: grow once here so inner theory
        // guards (NRA, model eval, proof checking) don't repeatedly mmap/munmap
        // their own segments. This fixes #6783 where repeated stacker growth
        // cycles caused extreme slowdown on 2 MiB threads in debug mode.
        let result = stacker::maybe_grow(EXECUTOR_STACK_RED_ZONE, EXECUTOR_STACK_SIZE, || {
            self.check_sat_guarded()
        });
        self.restore_timeout_deadline_after_call(previous_deadline);
        self.record_z3_resource_statistics(solve_started_at);
        let mut result = result.and_then(|result| {
            bv_cnf_dump::finish_check(dump_transaction, &self.ctx.terms, &dump_roots)?;
            Ok(result)
        });
        // The eager BV solver finishes its DRAT before returning, while
        // `finish_check` above seals the matching CNF. Verify that finalized
        // pair HERE, before `check_sat` returns to either the public API or the
        // CLI. A failed/missing check revokes every UNSAT-derived artifact and
        // degrades to `Unknown`; no caller can observe a merely pending UNSAT.
        if self.self_check
            && self.last_bv_drat_self_cert
            && matches!(result, Ok(ref solve_result) if solve_result.is_unsat())
        {
            if let Err(reason) = verify_bv_drat_self_cert() {
                self.last_bv_drat_self_cert = false;
                self.replace_last_result_with_unknown(UnknownReason::Incomplete);
                self.record_model_validation_unknown_diagnostic(format!(
                    "self-check: BV DRAT verification failed: {reason}"
                ));
                tracing::warn!(
                    "self-check: BV DRAT verification failed, degrading to Unknown: {reason}"
                );
                result = Ok(SolveResult::Unknown);
            }
        }
        // #quantifier-determinism diagnostics: opt-in per-solve budget trace
        // for calibrating the deterministic quantifier budgets against real
        // workloads (e.g. the deductive-checks calc.rs boundary chain). Zero overhead
        // unless AY_QUANT_STATS is set.
        if std::env::var_os("AY_QUANT_STATS").is_some() {
            eprintln!(
                "[ay-quant-stats] result={:?} time_s={:.3} ematching_rounds={} \
                 ematching_instances={} unknown_reason={:?} conflicts={} decisions={} \
                 interrupted={} backstop_installed={}",
                result,
                self.last_statistics.time_seconds,
                self.last_statistics.ematching_rounds_completed,
                self.last_statistics.ematching_instances_created,
                self.last_unknown_reason,
                self.last_statistics.conflicts,
                self.last_statistics.decisions,
                self.solve_interrupt
                    .as_ref()
                    .is_some_and(|f| f.load(Ordering::Relaxed)),
                self.quantifier_deadline_backstop_installed,
            );
            eprintln!(
                "[ay-quant-stats]   phase={:?} cost={:?} detail={:?}",
                self.last_statistics.get_string("unknown.phase"),
                self.last_statistics.get_string("unknown.cost_center"),
                self.last_statistics.get_string("unknown.detail"),
            );
        }
        result
    }

    /// Arm the `--self-check` BV DRAT self-cert export for the current check-sat
    /// when eligible, returning the RAII disarm guard (or `None`).
    ///
    /// Eligible iff: self-check is on; the CLI populated the self-cert temp paths
    /// (only when the user did NOT request an explicit `--dump-bv-cnf`); and the
    /// current assertion set is exactly the fragment the single-invocation DRAT
    /// certificate covers — pure QF_BV, quantifier-free, no named-assertion
    /// unsat-core redirection ([`bv_cnf_export_supported`]). For anything else the
    /// export stays disarmed and the solve degrades to `unknown` as before —
    /// fail-closed. Deliberately NOT armed for `check_sat_assuming`: an
    /// assumption-augmented bit-blast has no standalone-refutation DRAT.
    fn maybe_arm_bv_drat_self_cert(&self) -> Option<bv_cnf_dump::SelfCertArm> {
        if !self.self_check {
            return None;
        }
        let config = ay_core::trace_config();
        // An explicit user `--dump-bv-cnf` owns the export transaction itself;
        // never shadow it with the auto self-cert paths.
        if config.dump_bv_cnf_path.is_some()
            || config.bv_drat_self_cert_cnf_path.is_none()
            || config.bv_drat_self_cert_drat_path.is_none()
        {
            return None;
        }
        if !self.bv_cnf_export_supported(&self.ctx.assertions) {
            return None;
        }
        Some(bv_cnf_dump::arm_self_cert())
    }

    /// Whether `roots` are in the fragment the single-invocation BV DRAT
    /// certificate soundly covers. This is the boolean twin of the acceptance
    /// conditions in [`validate_bv_cnf_export_roots`]: pure QF_BV, no quantifier,
    /// no non-BV theory, and no named-assertion unsat-core redirection. A
    /// trivially-{true,false} conjunction is exportable (the writer emits the
    /// canonical trivial CNF/DRAT). Kept in lockstep with the validator so the
    /// self-cert arm can only ever expose the temp paths for an input the export
    /// machinery would accept.
    pub(in crate::executor) fn bv_cnf_export_supported(&self, roots: &[TermId]) -> bool {
        if bv_cnf_dump::trivial_conjunction(&self.ctx.terms, roots).is_some() {
            return true;
        }
        if self.produce_unsat_cores_enabled()
            && self
                .ctx
                .named_terms_iter()
                .any(|(_, term)| self.ctx.assertions.contains(&term))
        {
            return false;
        }
        if roots
            .iter()
            .copied()
            .any(|root| contains_quantifier(&self.ctx.terms, root))
        {
            return false;
        }
        let (category, features) = self.detect_logic_category(roots);
        let has_non_bv_theory = features.has_int
            || features.has_real
            || features.has_arrays
            || features.has_strings
            || features.has_seq
            || features.has_seq_ops
            || features.has_set_ops
            || features.has_multiset_ops
            || features.has_map_ops
            || features.has_regex
            || features.has_fpa
            || features.has_uf
            || features.has_quantifiers
            || features.has_bv_int_conversion
            || self.terms_contain_datatype_terms(roots);
        category == LogicCategory::QfBv && !has_non_bv_theory
    }

    /// Reject certificate export outside the deliberately supported fragment.
    ///
    /// The Phase-10 snapshot is complete for pure, quantifier-free BV only.
    /// Arrays have post-solve FC CEGAR clauses and other combined BV families
    /// have theory-specific refinement, so accepting those here would make a
    /// pre-refinement CNF look authoritative.  Literal constants are handled by
    /// the canonical writer without theory dispatch.
    pub(in crate::executor) fn validate_bv_cnf_export_roots(&self, roots: &[TermId]) -> Result<()> {
        if !bv_cnf_dump::enabled()
            || bv_cnf_dump::trivial_conjunction(&self.ctx.terms, roots).is_some()
        {
            return Ok(());
        }
        if self.produce_unsat_cores_enabled()
            && self
                .ctx
                .named_terms_iter()
                .any(|(_, term)| self.ctx.assertions.contains(&term))
        {
            return Err(crate::executor_types::ExecutorError::ArtifactExport(
                "--dump-bv-cnf does not support named-assertion unsat-core redirection".to_string(),
            ));
        }
        if roots
            .iter()
            .copied()
            .any(|root| contains_quantifier(&self.ctx.terms, root))
        {
            return Err(crate::executor_types::ExecutorError::ArtifactExport(
                "--dump-bv-cnf supports quantifier-free QF_BV queries only".to_string(),
            ));
        }
        let (category, features) = self.detect_logic_category(roots);
        let has_non_bv_theory = features.has_int
            || features.has_real
            || features.has_arrays
            || features.has_strings
            || features.has_seq
            || features.has_seq_ops
            || features.has_set_ops
            || features.has_multiset_ops
            || features.has_map_ops
            || features.has_regex
            || features.has_fpa
            || features.has_uf
            || features.has_quantifiers
            || features.has_bv_int_conversion
            || self.terms_contain_datatype_terms(roots);
        if category != LogicCategory::QfBv || has_non_bv_theory {
            return Err(crate::executor_types::ExecutorError::ArtifactExport(
                format!(
                    "--dump-bv-cnf supports pure QF_BV only; detected {category:?} with features {features:?} (array/UF/FP/arithmetic/datatype refinements are not exportable)"
                ),
            ));
        }
        Ok(())
    }

    pub(super) fn record_z3_resource_statistics(&mut self, solve_started_at: Instant) {
        self.last_statistics.time_seconds = solve_started_at.elapsed().as_secs_f64();
        self.last_statistics.term_bytes = self.ctx.terms.instance_term_bytes() as u64;
        self.last_statistics.term_count = self.ctx.terms.len() as u64;
        if let Some(rt) = self.last_statistics.get_int("dpll.round_trips") {
            self.last_statistics.refinement_count = rt;
        }

        let rss_mb = ay_sys::current_rss_bytes() as f64 / (1024.0 * 1024.0);
        self.last_statistics.memory_mb = rss_mb;
        self.last_statistics.max_memory_mb = rss_mb;

        self.last_statistics.rlimit_count = self.z3_style_rlimit_count();
    }

    fn z3_style_rlimit_count(&self) -> u64 {
        let stats = &self.last_statistics;
        [
            stats.conflicts,
            stats.decisions,
            stats.propagations,
            stats.restarts,
            stats.theory_conflicts,
            stats.theory_propagations,
            stats.nelson_oppen_rounds,
            stats.theory_unknown_count,
            stats.partial_clause_count,
            stats.refinement_count,
            stats.num_assertions,
            stats.num_vars,
            stats.num_clauses,
            stats.term_count,
        ]
        .into_iter()
        .fold(0_u64, u64::saturating_add)
    }

    /// Run check-sat with an additional cooperative interrupt callback (#622).
    ///
    /// The callback is polled by a lightweight watchdog and reflected into the
    /// same interrupt flag used by `make_should_stop()`, so existing SAT/theory
    /// interrupt checks observe it without special-case plumbing. The callback
    /// should be cheap and non-blocking.
    pub(crate) fn check_sat_interruptible<F>(&mut self, should_stop: F) -> Result<SolveResult>
    where
        F: Fn() -> bool + Send + 'static,
    {
        let previous_interrupt = self.solve_interrupt.clone();
        let previous_deadline = self.solve_deadline.get();
        let local_interrupt = Arc::new(AtomicBool::new(
            previous_interrupt
                .as_ref()
                .is_some_and(|flag| flag.load(Ordering::Relaxed))
                || should_stop(),
        ));
        let done = Arc::new(AtomicBool::new(false));

        // The cooperative-interrupt watchdog runs on a background thread. wasm32
        // has no threads; the `should_stop` callback is folded into the initial
        // `local_interrupt` state above, and the default `Z3_solver_check` FFI
        // path (the only path the wasm build exercises) never installs one.
        #[cfg(not(target_arch = "wasm32"))]
        if !local_interrupt.load(Ordering::Relaxed) {
            let poll_done = Arc::clone(&done);
            let poll_interrupt = Arc::clone(&local_interrupt);
            let poll_previous_interrupt = previous_interrupt.clone();
            thread::spawn(move || {
                while !poll_done.load(Ordering::Relaxed) {
                    if poll_previous_interrupt
                        .as_ref()
                        .is_some_and(|flag| flag.load(Ordering::Relaxed))
                        || should_stop()
                    {
                        poll_interrupt.store(true, Ordering::Relaxed);
                        return;
                    }
                    thread::sleep(Duration::from_millis(1));
                }
            });
        }

        self.set_solve_controls(Some(local_interrupt), previous_deadline);
        let result = self.check_sat();
        done.store(true, Ordering::Relaxed);
        self.set_solve_controls(previous_interrupt, previous_deadline);
        result
    }

    /// Fail-closed set-cardinality gate (#capi-set-has-size): AY has no
    /// decision procedure for `(set.has_size s k)` over an infinitely-indexed
    /// set (the C API expands finite Bool/small-BV element domains into a REAL
    /// arithmetic sum instead of ever building this token). Left ungated, the
    /// token would flow to EUF as an uninterpreted predicate and could
    /// fabricate a SAT/UNSAT verdict; instead, any assertion or assumption
    /// containing it makes the solve an honest `unknown`
    /// (`UnknownReason::Incomplete`) — never a guess.
    pub(in crate::executor) fn terms_contain_set_has_size(&self, roots: &[TermId]) -> bool {
        use ay_core::{Symbol, TermData};
        let mut stack: Vec<TermId> = roots.to_vec();
        let mut visited = ay_core::kani_compat::DetHashSet::<TermId>::default();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(sym, args) => {
                    if matches!(sym, Symbol::Named(name) if name == "set.has_size") {
                        return true;
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, t)| *t));
                    stack.push(*body);
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                    stack.push(*body);
                }
                // Const / Var / any future childless variant (#[non_exhaustive]).
                _ => {}
            }
        }
        false
    }

    /// Return the first invalid dense-BV width nested anywhere in `sort`.
    ///
    /// Native callers can construct `Sort` values directly, so declaration and
    /// operation helpers are not a complete validation boundary. Keep this
    /// iterative: array/sequence/datatype sorts are caller-controlled trees and
    /// should not consume the thread stack during solve preflight.
    fn unsupported_bitvector_width_in_sort(sort: &ay_core::Sort) -> Option<u32> {
        use ay_core::Sort;

        let mut stack = vec![sort];
        while let Some(sort) = stack.pop() {
            match sort {
                Sort::BitVec(bv)
                    if bv.width == 0 || bv.width > crate::api::MAX_API_BITVECTOR_WIDTH =>
                {
                    return Some(bv.width);
                }
                Sort::Array(array) => {
                    stack.push(&array.index_sort);
                    stack.push(&array.element_sort);
                }
                Sort::Datatype(datatype) => {
                    for constructor in &datatype.constructors {
                        stack.extend(constructor.fields.iter().map(|field| &field.sort));
                    }
                }
                Sort::Seq(element) => stack.push(element),
                // Scalar sorts and supported BVs have no nested sorts. Keep a
                // wildcard for future variants of this non-exhaustive enum.
                _ => {}
            }
        }
        None
    }

    /// Return the first FP format that cannot be represented by the current
    /// concrete-model layer, nested anywhere in `sort`.
    ///
    /// [`ay_fp::FpModelValue`] stores the raw exponent and significand fields
    /// in `u64`. Model extraction also computes `(1u64 << eb) - 1`, so an
    /// exponent width of 64 is already outside that representation; the
    /// significand stores `sb - 1` fraction bits and therefore supports at
    /// most `sb == 65`. Native callers can construct `Sort` values directly,
    /// bypassing frontend/API constructor checks, so enforce both the SMT
    /// minimum and these representation maxima at the solve boundary.
    fn unsupported_fp_model_format_in_sort(sort: &ay_core::Sort) -> Option<(u32, u32)> {
        use ay_core::Sort;

        const MAX_MODEL_EXPONENT_BITS: u32 = 63;
        const MAX_MODEL_SIGNIFICAND_BITS: u32 = 65;

        let mut stack = vec![sort];
        while let Some(sort) = stack.pop() {
            match sort {
                Sort::FloatingPoint(eb, sb)
                    if !(2..=MAX_MODEL_EXPONENT_BITS).contains(eb)
                        || !(2..=MAX_MODEL_SIGNIFICAND_BITS).contains(sb) =>
                {
                    return Some((*eb, *sb));
                }
                Sort::Array(array) => {
                    stack.push(&array.index_sort);
                    stack.push(&array.element_sort);
                }
                Sort::Datatype(datatype) => {
                    for constructor in &datatype.constructors {
                        stack.extend(constructor.fields.iter().map(|field| &field.sort));
                    }
                }
                Sort::Seq(element) => stack.push(element),
                // Scalar sorts and model-representable FP formats have no
                // nested sorts. Keep a wildcard for future variants.
                _ => {}
            }
        }
        None
    }

    /// Find an unsupported BV width in declarations or in a solve-root DAG.
    ///
    /// The symbol-table scan is intentional even for unused declarations:
    /// model completion/printing enumerates those declarations after SAT and a
    /// huge width can allocate there without appearing below an assertion.
    /// The DAG scan additionally covers native-only derived terms (`int2bv`,
    /// concat/extensions/repeat, FP/string bridges), fresh variables, binder
    /// metadata, and trigger terms.
    pub(in crate::executor) fn unsupported_bitvector_width(&self, roots: &[TermId]) -> Option<u32> {
        use ay_core::TermData;

        for (_, info) in self.ctx.symbol_iter() {
            if let Some(width) = Self::unsupported_bitvector_width_in_sort(&info.sort) {
                return Some(width);
            }
            for sort in &info.arg_sorts {
                if let Some(width) = Self::unsupported_bitvector_width_in_sort(sort) {
                    return Some(width);
                }
            }
        }

        let mut stack = roots.to_vec();
        let mut visited = ay_core::kani_compat::DetHashSet::<TermId>::default();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            if let Some(width) =
                Self::unsupported_bitvector_width_in_sort(self.ctx.terms.sort(term))
            {
                return Some(width);
            }
            match self.ctx.terms.get(term) {
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, value)| *value));
                    stack.push(*body);
                }
                TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                    for (_, sort) in vars {
                        if let Some(width) = Self::unsupported_bitvector_width_in_sort(sort) {
                            return Some(width);
                        }
                    }
                    stack.push(*body);
                    stack.extend(triggers.iter().flatten().copied());
                }
                // Const / Var / any future childless variant (#[non_exhaustive]).
                _ => {}
            }
        }
        None
    }

    /// Find an FP format outside the concrete-model representation in either
    /// a declaration signature or the full solve-root DAG.
    ///
    /// Scanning unused declarations is required because model completion and
    /// printing enumerate them after SAT. The DAG walk additionally covers
    /// native-only derived terms, binder metadata, and quantifier triggers.
    pub(in crate::executor) fn unsupported_fp_model_format(
        &self,
        roots: &[TermId],
    ) -> Option<(u32, u32)> {
        use ay_core::TermData;

        for (_, info) in self.ctx.symbol_iter() {
            if let Some(format) = Self::unsupported_fp_model_format_in_sort(&info.sort) {
                return Some(format);
            }
            for sort in &info.arg_sorts {
                if let Some(format) = Self::unsupported_fp_model_format_in_sort(sort) {
                    return Some(format);
                }
            }
        }

        let mut stack = roots.to_vec();
        let mut visited = ay_core::kani_compat::DetHashSet::<TermId>::default();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            if let Some(format) =
                Self::unsupported_fp_model_format_in_sort(self.ctx.terms.sort(term))
            {
                return Some(format);
            }
            match self.ctx.terms.get(term) {
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, value)| *value));
                    stack.push(*body);
                }
                TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                    for (_, sort) in vars {
                        if let Some(format) = Self::unsupported_fp_model_format_in_sort(sort) {
                            return Some(format);
                        }
                    }
                    stack.push(*body);
                    stack.extend(triggers.iter().flatten().copied());
                }
                // Const / Var / any future childless variant (#[non_exhaustive]).
                _ => {}
            }
        }
        None
    }

    /// Reject a native problem outside the dense-BV resource envelope before
    /// preprocessing, bit-blasting, model construction, or optimization can
    /// allocate from its width. `Incomplete` is fail-closed: no SAT/UNSAT
    /// verdict or stale artifact survives this boundary.
    pub(in crate::executor) fn reject_unsupported_bitvector_width(
        &mut self,
        roots: &[TermId],
    ) -> Option<SolveResult> {
        let width = self.unsupported_bitvector_width(roots)?;
        self.invalidate_last_check_result();
        self.last_statistics = crate::executor_types::Statistics::default();
        self.last_statistics.num_assertions = self.ctx.assertions.len() as u64;
        self.last_unknown_reason = Some(UnknownReason::Incomplete);
        self.last_result = Some(SolveResult::Unknown);
        self.set_active_solve_phase("input-preflight", "bitvector-width");
        self.record_unknown_diagnostic(
            UnknownReason::Incomplete,
            format!(
                "bit-vector width {width} is outside the supported range 1..={}",
                crate::api::MAX_API_BITVECTOR_WIDTH
            ),
        );
        self.clear_active_solve_phase();
        Some(SolveResult::Unknown)
    }

    /// Reject an FP problem whose concrete values cannot be represented by
    /// the current `u64`-backed model before bit-blasting/model extraction can
    /// shift out of range or truncate high bits.
    pub(in crate::executor) fn reject_unsupported_fp_model_format(
        &mut self,
        roots: &[TermId],
    ) -> Option<SolveResult> {
        let (eb, sb) = self.unsupported_fp_model_format(roots)?;
        self.invalidate_last_check_result();
        self.last_statistics = crate::executor_types::Statistics::default();
        self.last_statistics.num_assertions = self.ctx.assertions.len() as u64;
        self.last_unknown_reason = Some(UnknownReason::Incomplete);
        self.last_result = Some(SolveResult::Unknown);
        self.set_active_solve_phase("input-preflight", "floating-point-model-width");
        self.record_unknown_diagnostic(
            UnknownReason::Incomplete,
            format!(
                "floating-point format (eb={eb}, sb={sb}) is outside the concrete-model range: eb=2..=63 and sb=2..=65"
            ),
        );
        self.clear_active_solve_phase();
        Some(SolveResult::Unknown)
    }

    /// Inner check-sat after stack guard. Separated to keep `check_sat` small.
    fn check_sat_guarded(&mut self) -> Result<SolveResult> {
        self.clear_active_solve_phase();
        // D1 lazy-extensionality shadow: reset the per-solve EAGER witness log
        // before any array axioms are emitted for this check-sat.
        self.array_ext_shadow.clear();
        // Native dense-BV fail-closed gate: declarations and derived term
        // widths bypass several constructor-local checks, so validate the full
        // asserted DAG and symbol signatures at the solve boundary.
        let solve_roots = self.ctx.assertions.clone();
        if let Some(result) = self.reject_unsupported_bitvector_width(&solve_roots) {
            return Ok(result);
        }
        if let Some(result) = self.reject_unsupported_fp_model_format(&solve_roots) {
            return Ok(result);
        }
        // Set-cardinality fail-closed gate: see `terms_contain_set_has_size`.
        if self.terms_contain_set_has_size(&solve_roots) {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            self.last_result = Some(SolveResult::Unknown);
            self.last_model = None;
            self.last_proof = None;
            return Ok(SolveResult::Unknown);
        }
        self.last_model_validated = false;
        self.last_validation_stats = None;
        self.dt_cert_grant_active = false;
        self.model_validation_delegated_assertions.clear();
        self.skip_model_eval = false;
        self.read_pin_repair_done = false;
        // Fail-closed default, re-enabled at ENTRY (original assertion shapes,
        // before preprocessing erases array structure) only via the
        // route-independent observational-completeness argument; the
        // bridge-axiom bypass is additionally re-enabled by
        // `solve_with_dt_axioms`, which emits those axioms.
        // OR the witness-index extensionality coverage
        // (#dt-array-extensionality-witness): when every datatype-carrying array
        // is a datatype-ELEMENT array with a datatype-free index, the witness
        // pass models the whole fragment soundly (no domain enumeration), so a
        // validated SAT is genuine and the degrade gate is bypassed.
        // A RECURSIVE / over-deep datatype-element array anywhere keeps the gate
        // closed over BOTH bypass paths (#dt-array-extensionality-witness): the
        // bounded field congruence cannot refute a deep constructor clash, so a
        // SAT there could be a false SAT — fail closed regardless of footprint.
        self.dt_array_injectivity_gate_bypass = !self.problem_has_uncovered_dt_element_array(&[])
            && (self.dt_array_footprint_observationally_complete(&[])
                || self.dt_array_extensionality_modeled(&[]));
        // Perf-backstop flag (#dt-array-degrade-backstop): fail-closed default,
        // set true only when the datatype-array degrade gate fires this solve.
        self.last_degrade_was_datatype_array = false;
        self.sat_validated_by_mod_div_or_branch = false;
        // #uflia-cong-repair-arm: fresh per public check-sat (these persist on
        // the incremental Executor). `arm_uflia_congruence_repair` must be
        // `false` for the FIRST solve so the UFLIA accept-point scan stays off
        // the fast path; the gate/retry orchestration below sets it only for
        // the single armed re-solve.
        self.arm_uflia_congruence_repair = false;
        self.uflia_congruence_gate_rejected = false;
        self.uflia_congruence_retry_done = false;
        // #uflia-model-repair: fresh per public check-sat (mirrors the trio
        // above; stale evidence from a prior solve must never seed a repair).
        self.uflia_repair_candidates.clear();
        self.uflia_repair_conflict_tables.clear();
        self.uflia_model_repair_done = false;
        self.uflia_repair_detour_direct = false;
        self.uflia_repair_eager_direct = false;
        // L2 lazy-DT-AUFLIA eager-arm routing: strictly lane-scoped
        // (set/reset around the inner solve in `try_solve_dt_auflia_lazy`), but
        // reset defensively here so an early return inside the lane can never
        // leak the forced arm into a later check-sat on an incremental Executor.
        self.dt_lazy_auflia_eager_arm = false;
        // #abv-subst-model-retry: fresh per public check-sat (mirrors the
        // UFLIA trio above). The disable-flag must also be reset so a panic or
        // early return during a prior retry cannot leave preprocessing
        // permanently disabled on an incremental Executor.
        self.bv_subst_model_rejected = false;
        self.bv_subst_retry_done = false;
        self.bv_subst_retry_disable_preprocess = false;
        // CEGAR budget (#dt-array-cegar): reset the refine-and-re-solve allowance
        // per user (check-sat). Persists across the per-round internal re-solves
        // in `cegar_refine_solve` (which wraps `check_sat_internal` and re-solves
        // while the in-loop model gates distill violated select-congruence
        // lemmas — array-theory tautologies, so verdict-preserving).
        self.cegar_rounds_remaining = 32;
        self.cegar_pending_lemma = None;
        self.cegar_emitted_lemmas.clear();
        let result = self.cegar_refine_solve()?;
        if result.is_unsat() && self.produce_proofs_enabled() && self.last_proof.is_none() {
            self.build_unsat_proof();
        }
        // #uflia-model-repair EVIDENCE CAPTURE (env-gated, flags-off = no
        // clone, byte-identical): snapshot the UFLIA candidate model BEFORE
        // the emission funnel runs, because every rejecting gate inside it
        // (strict oracle, independent gate, `uf_table_conflict` discard)
        // clears `last_model` — erasing exactly the evidence (the colliding
        // value assignment) the §3.2 targeted repair needs. Read-only with
        // respect to the funnel: the snapshot is consumed only on the
        // rejection path below.
        if super::uflia_model_repair::uflia_model_repair_enabled()
            && self.uflia_congruence_lane
            && result == SolveResult::Sat
        {
            if std::env::var_os("AY_DEBUG_READ_PIN").is_some() {
                eprintln!(
                    "[model-repair] outer capture: last_model={}",
                    if self.last_model.is_some() {
                        "some"
                    } else {
                        "NONE"
                    }
                );
            }
            if let Some(model) = self.last_model.clone() {
                super::uflia_model_repair::push_repair_candidate(
                    &mut self.uflia_repair_candidates,
                    model,
                );
            }
        }
        // SINGLE SAT-EMISSION CHOKEPOINT (#sat-chokepoint): route the proposed
        // verdict through `emit_sat_verdict`, the ONLY place a public `Sat` is
        // minted. It defaults unconstrained constants, then runs the strict,
        // independent, and authoritative-failclosed gates in sequence and mints
        // the SatCertificate. Non-`Sat` verdicts pass through untouched. This is
        // the exact strict->independent sequence that previously lived inline
        // here, now shared with check-sat-assuming and optimize so a wrong model
        // can no longer bypass the soundness kernel via those paths.
        let mut result = self.emit_sat_verdict(result, &[])?;
        // Arity>0 output completion now runs INSIDE emit_sat_verdict, after all
        // model gates but before certificate minting. No model mutation is
        // permitted after the certified witness leaves that boundary. (The
        // reactive re-solves below re-enter through emit_sat_verdict, so their
        // verdicts get the same completion + gate sequence.)
        // #uflia-model-repair (§3.2 targeted lever, `AY_UFLIA_MODEL_REPAIR=1`):
        // BEFORE the blind congruence-repair re-solve below, try ONE targeted
        // repair re-solve driven by the preserved rejection evidence — block
        // the colliding value assignments the gates refuted, arm the
        // accept-point repair scan, and route the arm pipeline by evidence
        // class (see uflia_model_repair.rs `RepairRoute`) so the remaining
        // window is spent in the arm that can actually re-find a candidate.
        // Structurally sound: a minted Sat passed the full unchanged gate
        // battery over the original window; an unsat found under a block is
        // suppressed (see uflia_model_repair.rs docs). Same
        // trigger/latch/deadline discipline as the blind path; if this does
        // not mint a Sat, the blind re-solve below is still reachable.
        if super::uflia_model_repair::uflia_model_repair_enabled()
            && result == SolveResult::Unknown
            && self.uflia_congruence_gate_rejected
            && !self.uflia_model_repair_done
            && !matches!(self.last_unknown_reason, Some(UnknownReason::Timeout))
            && !self.solve_deadline.expired()
        {
            self.uflia_model_repair_done = true;
            result = self.uflia_targeted_model_repair_resolve(result)?;
        }
        // #uflia-cong-repair-arm: REACTIVE re-solve. The independent model gate
        // (inside `emit_sat_verdict`) just refuted a UFLIA first-pass model as a
        // UF function-graph violation and downgraded `Sat` -> `Unknown`. Arm the
        // accept-point congruence-repair scan and re-solve ONCE: this pass runs
        // `discover_congruence_repair_eqs`, which case-splits the coincident
        // argument values so the split loop separates them and converges to a
        // correct verdict (the +12 Hash SAT family). A first-pass model the gate
        // ACCEPTS never reaches here (`uflia_congruence_gate_rejected` stays
        // false), so latent-consistent collisions (hash_sat_07_03) keep the fast
        // path with zero extra splits. Retry-once latch (loop guard): fires at
        // most once per check-sat; a still-refuted re-solve stays the
        // fail-closed `Unknown` the gate already produced (strictly sound). The
        // deadline/timeout guard mirrors the #qfax-budget-ladder retry so an
        // exhausted budget never spends a second solve.
        if result == SolveResult::Unknown
            && self.uflia_congruence_gate_rejected
            && !self.uflia_congruence_retry_done
            && !matches!(self.last_unknown_reason, Some(UnknownReason::Timeout))
            && !self.solve_deadline.expired()
        {
            self.uflia_congruence_retry_done = true;
            self.arm_uflia_congruence_repair = true;
            self.last_unknown_reason = None;
            self.last_result = None;
            self.last_model = None;
            let retry = self.check_sat_internal()?;
            if retry.is_unsat() && self.produce_proofs_enabled() && self.last_proof.is_none() {
                self.build_unsat_proof();
            }
            result = self.emit_sat_verdict(retry, &[])?;
            // Never let the combiner-facing enable-flag outlive the re-solve.
            self.arm_uflia_congruence_repair = false;
        }
        // #abv-subst-model-retry: REACTIVE preprocessing-free re-solve. The
        // eager BV lane's model-construction pipeline recovers values for
        // variables eliminated by preprocessing VariableSubstitution; when that
        // recovery manufactures an invalid model (wishlist#1: a select whose
        // index mentions eliminated variables is decoupled from its bit-blasted
        // instance), the in-loop semantic validator or the independent gate
        // refutes the model and the verdict fail-closes to Unknown even though
        // the underlying SAT search was consistent. Re-solve ONCE with
        // preprocessing disabled: the model is then built directly from the
        // bit-blasted ORIGINAL assertions with no substitution recovery, so the
        // same search returns a directly-validatable witness. Gated on
        // `bv_subst_model_rejected` (set only by an actual model refutation
        // from a substitution-carrying BV solve), so unaffected queries never
        // pay a second solve. SOUND: the retry solves the identical original
        // assertion set with strictly fewer preprocessing transforms and its
        // verdict passes the same strict/independent/authoritative gates via
        // `emit_sat_verdict`; a still-rejected re-solve stays the fail-closed
        // Unknown. Retry-once latch + deadline guard mirror the UFLIA arm.
        if result == SolveResult::Unknown
            && self.bv_subst_model_rejected
            && !self.bv_subst_retry_done
            && !matches!(self.last_unknown_reason, Some(UnknownReason::Timeout))
            && !self.solve_deadline.expired()
        {
            self.bv_subst_retry_done = true;
            self.bv_subst_retry_disable_preprocess = true;
            self.last_unknown_reason = None;
            self.last_result = None;
            self.last_model = None;
            let retry = self.check_sat_internal()?;
            if retry.is_unsat() && self.produce_proofs_enabled() && self.last_proof.is_none() {
                self.build_unsat_proof();
            }
            result = self.emit_sat_verdict(retry, &[])?;
            // Never let the lane-facing disable-flag outlive the re-solve.
            self.bv_subst_retry_disable_preprocess = false;
            self.last_statistics
                .set_int("model_validation.bv.subst_retry", 1);
        }
        // #nonstring-seq-unsat-corroboration: an UNSAT produced for a non-string
        // sequence problem WITHOUT proof production is not trustworthy on its own.
        // The no-proof search enables optimizations (eager LIA routing, guarded-eq
        // mining, second variable substitution) that are disabled under proofs and
        // carry latent soundness holes; combined with the heuristic non-string-seq
        // axiom battery (`solve_seq_lia`) they can close a satisfiable formula as a
        // SPURIOUS UNSAT. The witnessing shape is the `sequences` fuzzer seed 69
        // family — e.g. `(or (xor (distinct (seq.extract s0 0 (seq.len s0)) s0)
        // <replace/extract-of-empty equality>) (and (seq.nth (seq.++ s2 (seq.unit
        // false)) i) (seq.contains s3 s3) (seq.contains s3 s2)))` — which z3
        // decides SAT but the no-proof path reports UNSAT. This wrong UNSAT is
        // invisible to BOTH the SAT-side model-validation gate (SAT-only) and
        // proof-checking (in proof mode the spurious conflict is never derived, so
        // there is no proof to reject).
        //
        // The non-string sequence theory is fail-close territory (P0.1): it is not
        // a complete decision procedure. So corroborate any non-string-seq UNSAT
        // that was reached without proofs by re-solving ONCE with proofs forced on
        // — the strictly more conservative search that the CLI already runs by
        // default. If that proof-mode re-solve does NOT reconfirm UNSAT, the UNSAT
        // is not trustworthy and we fail-close to `unknown` (always sound; this arm
        // is demote-only, so it can never introduce a wrong verdict). GENUINE seq
        // unsats (length contradictions, `seq.extract s 0 (seq.len s) = s`)
        // reconfirm under proofs and survive unchanged. Fires AT MOST ONCE per
        // check-sat (reentry latch) and only when proofs are off, so proof-mode and
        // proof-consuming callers never pay a second solve.
        if result.is_unsat()
            && !self.produce_proofs_enabled()
            && !self.corroborating_nonstring_seq_unsat
            && !self.solve_deadline.expired()
            && self
                .ctx
                .assertions
                .clone()
                .iter()
                .any(|&a| self.assertion_references_nonstring_seq(a))
        {
            self.corroborating_nonstring_seq_unsat = true;
            self.set_produce_proofs(true);
            let corroboration = self.cegar_refine_solve();
            self.set_produce_proofs(false);
            // `set_produce_proofs(true)` also turned parsed-assertion retention on;
            // restore the no-proof default so an incremental FFI session does not
            // silently start paying the retention RSS cost after this gate fires.
            self.set_retain_parsed_assertions(false);
            self.corroborating_nonstring_seq_unsat = false;
            let corroborated_unsat = matches!(corroboration, Ok(ref r) if r.is_unsat());
            // Propagate a hard error from the re-solve; otherwise ignore its
            // model/proof artifacts (the user's run does not produce proofs) — the
            // verdict was already captured in `corroborated_unsat`.
            let _ = corroboration?;
            self.last_model = None;
            self.last_proof = None;
            if corroborated_unsat {
                // Reconfirmed: keep the original UNSAT verdict (`result` still
                // holds the first solve's `Unsat(cert)`; the corroboration ran on
                // a separate local binding and never touched it).
                self.last_unknown_reason = None;
            } else {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                self.record_model_validation_unknown_diagnostic(
                    "non-string sequence UNSAT not corroborated by a proof-producing re-solve",
                );
                result = SolveResult::Unknown;
            }
        }

        // Fail-closed self-check for UNSAT: AY may only emit `unsat` when it
        // produced a refutation proof that its OWN internal checker fully
        // verified — every step checked, no trust/`Hole` steps, no checker
        // error. If AY cannot certify the refutation itself, it degrades to a
        // sound `unknown` rather than assert an unsat it cannot prove. This is
        // the UNSAT half of "AY checks its own answers": together with the SAT
        // model-certification gate above (independent model gate is SAT-only),
        // no `sat`/`unsat` AY emits under `--self-check` is unverified by AY
        // itself. (#self-check-unsat)
        // BV DRAT self-cert exception: a pure-QF_BV UNSAT that emitted a
        // native-checkable bit-blast DRAT for THIS solve may pass this Alethe
        // gate. The outer `check_sat` boundary finalizes the matching CNF and
        // runs AY's native DRAT checker before returning the result to ANY
        // caller; a failed check is revoked and degraded to `Unknown` there.
        let bv_drat_self_cert = self.last_bv_drat_self_cert;
        let result = if self.self_check
            && result.is_unsat()
            && !self.unsat_proof_self_certified()
            && !bv_drat_self_cert
        {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            self.record_model_validation_unknown_diagnostic(
                "self-check: UNSAT is not backed by a fully-checked refutation proof",
            );
            tracing::warn!(
                "self-check: UNSAT not self-certified by internal proof checker, degrading to Unknown"
            );
            SolveResult::Unknown
        } else {
            result
        };
        self.last_result = Some(result);

        // D1 lazy-extensionality shadow: correlate the EAGER witness set against
        // the DEMANDED set and surface `auflia.ext.*` on `-st`. Measurement only.
        self.finalize_array_ext_shadow();

        // Capture trail provenance for SAT results (#8153)
        if self.last_result.as_ref().is_some_and(SolveResult::is_sat) {
            self.capture_trail_provenance();
        }
        self.finalize_unknown_diagnostics();

        // Postcondition: SAT must produce a model (unless trivially SAT with no
        // assertions, or all assertions simplified to true by term construction).
        debug_assert!(
            !self.last_result.as_ref().is_some_and(SolveResult::is_sat)
                || self.last_model.is_some()
                || self.ctx.assertions.is_empty()
                || self
                    .ctx
                    .assertions
                    .iter()
                    .all(|&a| a == self.ctx.terms.true_term()),
            "BUG: check_sat returned SAT without populating last_model"
        );
        // Postcondition: UNSAT with proofs enabled must produce a proof
        debug_assert!(
            !self.last_result.as_ref().is_some_and(SolveResult::is_unsat)
                || self.last_proof.is_some()
                || !self.produce_proofs_enabled(),
            "BUG: check_sat returned UNSAT without populating last_proof (proofs enabled)"
        );
        // Observability: log when SAT is returned without model validation (#5973).
        // This should only occur for incremental inner solves now (#8456).
        if self.last_result.as_ref().is_some_and(SolveResult::is_sat) && !self.last_model_validated
        {
            tracing::debug!(
                skip_model_eval = self.skip_model_eval,
                "SAT result returned without model validation (skip_model_eval or deferred)"
            );
        }

        // #7912 postcondition: every SAT result has been validated at some level.
        // - last_model_validated: full SMT-level assertion validation passed, OR
        //   trivially-SAT path where all assertions folded to true (#8456)
        // - skip_model_eval: validation deferred for incremental inner solve
        //   (incremental_scope.rs), boolean skeleton verified in release mode
        // - empty assertions: trivially SAT, no validation needed
        debug_assert!(
            !self.last_result.as_ref().is_some_and(SolveResult::is_sat)
                || self.last_model_validated
                || self.skip_model_eval
                || self.ctx.assertions.is_empty(),
            "BUG: check_sat returned SAT without any model validation path — \
             last_model_validated={}, skip_model_eval={}, assertions={}",
            self.last_model_validated,
            self.skip_model_eval,
            self.ctx.assertions.len(),
        );

        // #8640: Capture resource consumption statistics after solving.
        self.last_statistics.term_bytes = self.ctx.terms.instance_term_bytes() as u64;
        self.last_statistics.term_count = self.ctx.terms.len() as u64;
        // Populate refinement_count from the dpll.round_trips extra stat if set.
        if let Some(rt) = self.last_statistics.get_int("dpll.round_trips") {
            self.last_statistics.refinement_count = rt;
        }

        Ok(self.last_result.clone().expect("last_result was just set"))
    }

    // ========================================================================
    // Interrupt / Deadline helpers
    // ========================================================================

    /// Set a persistent interrupt flag that is checked during every check-sat.
    ///
    /// When the flag is set to `true`, ongoing and future solves return
    /// `Unknown` with reason `Interrupted`. This is used by the CLI watchdog
    /// to cooperatively stop the solver on global timeout (#2971).
    pub fn set_interrupt(&mut self, flag: Arc<AtomicBool>) {
        self.solve_interrupt = Some(flag);
    }

    /// Install a persistent wall-clock deadline (#8749).
    ///
    /// CLI consumers (`ay solve --timeout …`) call this in addition to
    /// [`Self::set_interrupt`] so theory solvers that poll deadlines (IntSat,
    /// LIA cascade, LRA split loop, …) can bail out promptly instead of
    /// waiting for the watchdog thread to fire two seconds after the timeout.
    ///
    /// Passing `None` clears any previously installed deadline.
    pub fn set_deadline(&mut self, deadline: Option<Instant>) {
        self.solve_deadline.set(deadline);
    }

    /// Set a relative timeout for subsequent executor solve commands.
    ///
    /// The timeout is converted into a fresh deadline at each `check-sat` or
    /// `check-sat-assuming` call. Passing `None` clears the timeout.
    pub fn set_timeout(&mut self, timeout: Option<Duration>) {
        self.timeout = timeout;
    }

    /// Return the relative timeout applied to subsequent executor solve commands.
    #[must_use]
    pub fn timeout(&self) -> Option<Duration> {
        self.timeout
    }

    /// Propagate API-level timeout/interrupt controls into theory split loops.
    pub(crate) fn set_solve_controls(
        &mut self,
        interrupt: Option<Arc<AtomicBool>>,
        deadline: Option<Instant>,
    ) {
        self.solve_interrupt = interrupt;
        self.solve_deadline.set(deadline);
    }

    /// Clear solve controls after a check-sat call completes.
    pub(crate) fn clear_solve_controls(&mut self) {
        self.solve_interrupt = None;
        self.solve_deadline.set(None);
    }

    fn earliest_deadline(left: Option<Instant>, right: Option<Instant>) -> Option<Instant> {
        match (left, right) {
            (Some(left), Some(right)) => Some(left.min(right)),
            (Some(deadline), None) | (None, Some(deadline)) => Some(deadline),
            (None, None) => None,
        }
    }

    fn timeout_deadline_from_now(&self) -> Option<Instant> {
        let now = Instant::now();
        self.timeout.and_then(|timeout| now.checked_add(timeout))
    }

    pub(super) fn install_timeout_deadline_for_call(&mut self) -> Option<Instant> {
        // #quantifier-determinism: the quantified-solve backstop extension is
        // one-shot PER check-sat call (see
        // `install_quantifier_deadline_backstop`); re-arm it here.
        self.quantifier_deadline_backstop_installed = false;
        // #read-congruence-quantified-scope: re-arm per check-sat call, like
        // the backstop one-shot above; `process_quantifiers` sets it once the
        // quantifier pipeline actually engages for this call.
        self.quantifier_pipeline_engaged = false;
        let previous_deadline = self.solve_deadline.get();
        if self.timeout.is_some() {
            self.solve_deadline.set(Self::earliest_deadline(
                previous_deadline,
                self.timeout_deadline_from_now(),
            ));
        }
        // Safety net: if NO deadline is in force for this call (no per-query
        // timeout AND no caller-installed absolute deadline), install a generous
        // default so a divergent conflict-free/decision-free theory-propagation
        // churn always terminates fail-closed to Unknown instead of spinning at
        // 100% CPU forever. Proof-seeking solves (panic-freedom obligations) run
        // without a timeout precisely because they want a proof, so this is the
        // executor-side twin of the ay-chc solve_init default — every solve path
        // is covered. Far above any legitimate solve time; only kills a true spin.
        if self.solve_deadline.get().is_none() {
            const DEFAULT_SAFETY_DEADLINE: Duration = Duration::from_mins(5);
            self.solve_deadline
                .set(Instant::now().checked_add(DEFAULT_SAFETY_DEADLINE));
        }
        // #ground-determinism (task #26 item 2): for a MIXED ground+quantified
        // solve, install the far-out wall-clock backstop AT SOLVE ENTRY, not
        // only at the quantified pipeline entry. Previously a solve whose
        // PRE-quantifier ground phase (e.g. the BV<->LIA bridge feeding
        // solve_auf_lia — the deductive-checks calc.rs line93 profile) consumed the
        // whole nominal budget never benefited from the backstop: by the time
        // control reached `install_quantifier_deadline_backstop` the deadline
        // had already expired and the install early-returned, so the whole
        // solve kept a load-sensitive nominal wall. With the default ground
        // budget the ground phase is governed by deterministic conflict +
        // decision counts, and the wall clock's only remaining job is far-out
        // hang protection — so secure the extension up front. Ground-ONLY
        // solves (no quantified assertion) keep their exact nominal deadline:
        // callers' tight retry ladders on ground/BV obligations stay prompt
        // (the deductive-checks BV_HARD_TIMEOUT design), and the ay-dpll suite's
        // wall-bounded ground timeout tests keep their latency. The one-shot
        // flag (just re-armed above) makes the later quantified-entry install
        // a no-op for this call; expired/absent deadlines are still left
        // untouched inside the install, preserving `set_timeout(ZERO)`
        // immediate-stop semantics.
        // A/B knob symmetry: AY_NO_GROUND_BUDGET must restore the exact
        // pre-change semantics — count budgets AND the solve-entry backstop —
        // matching `:rlimit 0` / set_ground_budget_enabled(false).
        if self.ground_budget_enabled
            && !crate::pipeline_fns::ground_budget_env_disabled()
            && self
                .ctx
                .assertions
                .iter()
                .any(|&assertion| contains_quantifier(&self.ctx.terms, assertion))
        {
            self.install_quantifier_deadline_backstop();
        }
        previous_deadline
    }

    /// Relax the nominal wall-clock deadline into a far-out hang-protection
    /// backstop for the remainder of a QUANTIFIED solve (#quantifier-determinism,
    /// Fix A of workflow w6ur8ni5u).
    ///
    /// WHY: the quantifier/E-matching pipeline is DETERMINISTICALLY bounded —
    /// `ematching_round_limit()` (default 16) rounds x `max_total` (10000)
    /// instances per round with deterministic generation-cost gates,
    /// `MAX_INTERLEAVED_EMATCHING_ROUNDS` (4) interleaved refinement rounds,
    /// `MAX_CEGQI_ROUNDS` (8), and the bounded MBQI candidate rounds — so on
    /// identical inputs it performs IDENTICAL instantiation work on any
    /// machine. Before this change the caller's nominal deadline
    /// (`set_timeout`) was the PRIMARY break at the operating boundary: the
    /// `should_stop` guards inside the round loops truncated the deterministic
    /// work mid-pipeline, so a proof whose instantiation chain converges just
    /// inside the budget on an idle machine was cut short on a loaded/slower
    /// machine and the verdict flipped Verified <-> Unknown with CPU load (the
    /// deductive-checks calc.rs ported-entry hazard). With the extension, the
    /// deterministic budgets are the primary termination and the wall clock
    /// only fires as hang protection far beyond the operating boundary.
    ///
    /// SOUNDNESS / VERDICT SAFETY: WHEN the loop stops cannot flip a verdict —
    /// every deadline break in the pipeline routes to fail-closed
    /// Unknown(QuantifierRoundLimit/Timeout), and allowing the deterministic
    /// work to complete can only surface a genuinely converged Sat/Unsat.
    /// Bounded churn: queries whose deterministic budgets exceed the machine's
    /// patience still stop at the backstop (remaining x FACTOR, capped at
    /// +MAX_EXTRA), so no solve becomes unbounded.
    ///
    /// One-shot per check-sat call (`quantifier_deadline_backstop_installed`,
    /// re-armed in `install_timeout_deadline_for_call`): nested quantified
    /// re-entries (alternation validation sub-solves, which install their own
    /// deliberately TIGHT sub-deadlines) never compound the extension. The
    /// per-call restore in `restore_timeout_deadline_after_call` unwinds it.
    ///
    /// #ground-determinism (task #26 item 2): for solves whose assertion set
    /// contains a quantifier, `install_timeout_deadline_for_call` now installs
    /// this backstop AT SOLVE ENTRY (consuming the one-shot), so a heavy
    /// PRE-quantifier ground phase (BV<->LIA bridge, AUFLIA dispatch) runs
    /// under the extended wall as well — previously it burned the nominal
    /// budget and this install early-returned on the already-expired deadline,
    /// leaving mixed ground+quantified solves with a load-sensitive nominal
    /// wall. The quantified-entry call site remains for solves that reach the
    /// quantified pipeline in other ways (defense in depth).
    ///
    /// An already-expired or absent deadline is left untouched: `set_timeout
    /// (Duration::ZERO)`-style hard aborts keep their immediate-stop semantics.
    pub(in crate::executor) fn install_quantifier_deadline_backstop(&mut self) {
        /// Scale factor applied to the REMAINING nominal budget. 4x covers
        /// realistic CPU-load slowdowns (a fully-contended machine typically
        /// runs 2-3x slower) with margin, while keeping worst-case churn on
        /// deterministic-budget-heavy queries bounded to a small multiple of
        /// the caller's budget.
        const QUANTIFIED_BACKSTOP_FACTOR: u32 = 4;
        /// Absolute cap on the extension so very generous caller budgets
        /// (e.g. a 300s last-resort strategy) do not balloon to 20 minutes:
        /// beyond this, a solve is not at the load-flip boundary — it is
        /// simply too hard, and the fail-closed Unknown is the right result.
        const QUANTIFIED_BACKSTOP_MAX_EXTRA: Duration = Duration::from_mins(3);

        if self.quantifier_deadline_backstop_installed {
            return;
        }
        self.quantifier_deadline_backstop_installed = true;
        let Some(deadline) = self.solve_deadline.get() else {
            return;
        };
        let now = Instant::now();
        let Some(remaining) = deadline.checked_duration_since(now) else {
            // Deadline already expired: preserve immediate-stop semantics.
            return;
        };
        let extra = remaining
            .saturating_mul(QUANTIFIED_BACKSTOP_FACTOR.saturating_sub(1))
            .min(QUANTIFIED_BACKSTOP_MAX_EXTRA);
        if let Some(backstop) = deadline.checked_add(extra) {
            self.solve_deadline.set(Some(backstop));
        }
        if std::env::var_os("AY_QUANT_STATS").is_some() {
            eprintln!(
                "[ay-quant-stats] backstop installed: remaining={remaining:?} extra={extra:?}"
            );
        }
    }

    pub(super) fn restore_timeout_deadline_after_call(
        &mut self,
        previous_deadline: Option<Instant>,
    ) {
        // Unconditionally restore the pre-call deadline so BOTH the per-timeout
        // install AND the default-safety-net install (added above, which fires
        // when `timeout` is None) are strictly per-call — otherwise a leaked
        // default from the first call would make every later solve inherit an
        // already-elapsing absolute deadline and eventually truncate a
        // legitimate proof. `install` returns exactly this value, so restoring
        // it always is correct for every branch.
        self.solve_deadline.set(previous_deadline);
    }

    /// Build a `should_stop` closure for `solve_interruptible` that checks
    /// the executor's interrupt flag and deadline without borrowing `self`.
    ///
    /// The returned closure captures the interrupt flag (Arc clone) and a LIVE
    /// deadline handle (shared-cell clone), so it can be passed to SAT solver
    /// methods that require `Fn() -> bool` while `self` remains available for
    /// other use.
    ///
    /// #quantifier-determinism: the deadline is read through the shared cell
    /// AT POLL TIME, never snapshotted. A closure built before
    /// `install_quantifier_deadline_backstop` therefore observes the backstop
    /// extension (previously a by-value snapshot kept the stale nominal
    /// deadline and stopped the solve at the pre-extension wall, silently
    /// defeating the backstop), and a closure built before an
    /// alternation-validation sub-deadline tightening observes the tight
    /// window while it is installed.
    pub(crate) fn make_should_stop(&self) -> impl Fn() -> bool {
        let interrupt_flag = self.solve_interrupt.clone();
        let deadline = self.solve_deadline.clone();
        move || {
            if let Some(ref flag) = interrupt_flag {
                if flag.load(Ordering::Relaxed) {
                    return true;
                }
            }
            deadline.expired()
        }
    }

    /// Check whether the current solve should abort due to interrupt/timeout.
    ///
    /// Returns `true` when the caller should return `Unknown` immediately.
    pub(crate) fn should_abort_theory_loop(&mut self) -> bool {
        if self
            .solve_interrupt
            .as_ref()
            .is_some_and(|flag| flag.load(Ordering::Relaxed))
        {
            self.last_unknown_reason = Some(UnknownReason::Interrupted);
            self.last_result = Some(SolveResult::Unknown);
            self.record_unknown_diagnostic(
                UnknownReason::Interrupted,
                "interrupt requested while the active solve phase was running",
            );
            return true;
        }

        if self.solve_deadline.expired() {
            self.last_unknown_reason = Some(UnknownReason::Timeout);
            self.last_result = Some(SolveResult::Unknown);
            self.record_unknown_diagnostic(
                UnknownReason::Timeout,
                "deadline expired while the active solve phase was running",
            );
            return true;
        }

        // Two memory ceilings are honored here, the single inner-loop
        // checkpoint reused by every theory loop:
        //  * `self.memory_limit`: the per-solver limit set via
        //    `Solver::set_memory_limit` (peak RSS vs that limit).
        //  * `ay_sys::process_memory_exceeded()`: the process-wide ceiling set
        //    once from `main()` (`set_process_memory_limit`). It consults the
        //    exact live-heap-bytes counter (instant, no syscall) as well as peak
        //    RSS, so a runaway bulk allocation inside this theory loop trips
        //    `Unknown(MemoryLimit)` here — before the OS OOM-killer can fire —
        //    rather than only at the check-sat boundary. Soundness-neutral: it
        //    can only drive Unknown, never a wrong SAT/UNSAT.
        if crate::memory::memory_exceeded(self.memory_limit) || ay_sys::process_memory_exceeded() {
            self.last_unknown_reason = Some(UnknownReason::MemoryLimit);
            self.last_result = Some(SolveResult::Unknown);
            self.record_unknown_diagnostic(
                UnknownReason::MemoryLimit,
                "process memory ceiling exceeded while the active solve phase was running",
            );
            return true;
        }

        false
    }

    /// CEGAR driver (#dt-array-cegar). Runs `check_sat_internal`; while it
    /// degrades to `Unknown` after the model census / general select-congruence
    /// gate distilled a select-congruence lemma the candidate model VIOLATED,
    /// install that lemma (an array-theory tautology — verdict-preserving) and
    /// re-solve. Budgeted (`cegar_rounds_remaining`) and dedup'd
    /// (`cegar_emitted_lemmas`), so the loop always terminates: to a certified
    /// Sat, a genuine Unsat (e.g. an uninterpreted-element derived-index
    /// disequality now becomes provably unsat), or a sound Unknown when the
    /// budget is spent. Covers every route (the plain array-BV path and the DT
    /// deepening path both flow through `check_sat_internal`). SOUNDNESS: each
    /// installed lemma is a theory tautology, so no Sat/Unsat verdict can flip —
    /// the loop can only refine an `Unknown` into a definite, correct answer.
    fn cegar_refine_solve(&mut self) -> Result<SolveResult> {
        // User assertion set BEFORE any lemma injection, restored on exit so the
        // scope `assertion_count` invariant and incremental push/pop stay intact.
        let cegar_snapshot = self.ctx.assertions.clone();
        let mut result = self.check_sat_internal()?;
        // CEGAR refinement runs only in non-proof mode: injecting lemmas mid-solve
        // would desynchronize the unsat-proof reconstruction from the user
        // assertion set. Sound either way — without refinement the verdict is a
        // sound Unknown, exactly the pre-CEGAR behavior (assertions untouched).
        if self.produce_proofs_enabled() {
            return Ok(result);
        }
        loop {
            if !matches!(&result, SolveResult::Unknown) {
                break;
            }
            let Some(lemma) = self.cegar_pending_lemma.take() else {
                break;
            };
            if self.cegar_rounds_remaining == 0 || !self.cegar_emitted_lemmas.insert(lemma) {
                break;
            }
            if self.should_abort_theory_loop() {
                break;
            }
            self.cegar_rounds_remaining -= 1;
            // Re-solve `user assertions + ALL accumulated congruence lemmas`, so
            // the DT lift/flatten is applied fresh each round rather than
            // compounding across rounds.
            self.ctx.assertions = cegar_snapshot.clone();
            self.ctx
                .assertions
                .extend(self.cegar_emitted_lemmas.iter().copied());
            if std::env::var_os("AY_PHASE_TRACE").is_some() {
                eprintln!(
                    "c phase-trace cegar-refine rounds-left={} lemma={}",
                    self.cegar_rounds_remaining, lemma.0
                );
            }
            result = self.check_sat_internal()?;
        }
        // Drop the injected lemmas from the user-visible assertion set.
        self.ctx.assertions = cegar_snapshot;
        Ok(result)
    }

    // ========================================================================
    // Internal check-sat (logic routing)
    // ========================================================================

    /// Internal check-sat that also stores the model
    pub(super) fn check_sat_internal(&mut self) -> Result<SolveResult> {
        // Clear previous state. Defer last_model clear until after process_quantifiers()
        // which reads last_model.euf_model for congruence-aware E-matching (Phase B1b #3325).
        self.last_assumptions = None;
        self.last_assumption_core = None;
        self.last_core_term_to_name = None;
        self.last_proof = None;
        self.last_proof_term_overrides = None;
        self.last_proof_quality = None;
        self.last_clause_trace = None;
        self.last_var_to_term = None;
        self.last_trail_provenance = None;
        self.last_clausification_proofs = None;
        self.last_original_clause_theory_proofs = None;
        self.last_unknown_reason = None;
        // Per-check-sat conflict-verification verdict memo (#4535): verdicts
        // must not outlive the assertion/support state they were computed
        // against.
        self.conflict_semantic_verify_memo.clear();
        // Same lifecycle for the propagation-verification memo (#verify-memo).
        self.prop_semantic_verify_memo.clear();
        // Clear NRA algebraic witnesses per check-sat so stale values from a
        // prior solve cannot leak into a later model in an incremental session.
        self.nra_algebraic_model.clear();
        // Same for the DT e-graph model export and its derived per-class
        // value assignment (#mv-dt-single-source).
        self.clear_dt_theory_model();
        self.proof_problem_assertion_provenance = None;
        self.quant_expansion_records.clear();
        self.last_proof_rebuild_originals.clear();
        self.last_statistics = crate::executor_types::Statistics::default();
        self.last_statistics.num_assertions = self.ctx.assertions.len() as u64;

        // Clear per-solve transient flags so they don't leak between (check-sat) calls
        // #uflia-cong-repair-arm: `uflia_congruence_lane` marks a UFLIA
        // combiner solve; `solve_uf_lia` re-asserts it before its split loop.
        // (`arm_uflia_congruence_repair` is deliberately NOT cleared here — the
        // armed re-solve re-enters this fn and must preserve the enable-flag.)
        self.uflia_congruence_lane = false;
        // #abv-subst-model-retry: `bv_subst_lane` marks a BV-lane solve that
        // ran preprocessing VariableSubstitution; `solve_bv_core_inner`
        // re-asserts it. (`bv_subst_retry_disable_preprocess` is deliberately
        // NOT cleared here — the retry re-solve re-enters this fn and must
        // preserve the disable-flag.)
        self.bv_subst_lane = false;
        self.bypass_string_tautology_guard = false;
        self.slia_accepted_unknown = false;
        self.array_axiom_scope = None;
        self.row_seeded_terms.clear();
        self.defer_model_validation = false;
        self.defer_counterexample_minimization = false;
        self.last_model_validated = false;
        self.last_validation_stats = None;
        self.dt_cert_grant_active = false;
        self.model_validation_delegated_assertions.clear();
        self.skip_model_eval = false;
        self.read_pin_repair_done = false;
        // Fail-closed default (see check_sat): re-enabled at entry via the
        // route-independent observational-completeness argument, the witness-index
        // extensionality coverage (#dt-array-extensionality-witness), or later by
        // `solve_with_dt_axioms` when its injectivity bridge covers every hazard.
        self.dt_array_injectivity_gate_bypass = !self.problem_has_uncovered_dt_element_array(&[])
            && (self.dt_array_footprint_observationally_complete(&[])
                || self.dt_array_extensionality_modeled(&[]));
        // Perf-backstop flag (#dt-array-degrade-backstop): cleared per solve.
        self.last_degrade_was_datatype_array = false;
        self.recorded_var_substitutions.clear();
        self.proof_check_result = None;

        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }

        // Sync proof tracker with :produce-proofs option
        if matches!(
            self.ctx.get_option("produce-proofs"),
            Some(ay_frontend::OptionValue::Bool(true))
        ) {
            self.proof_tracker.enable();
        }

        // Reset proof content for new solving session (keep scope tracking
        // for incremental push/pop balance) (#5992)
        self.proof_tracker.reset_session();

        if self.ctx.assertions.is_empty() {
            self.last_model = None;
            return Ok(SolveResult::Sat);
        }

        // #incremental-pushpop-soundness (QF_S push/pop wrong-UNSAT): the
        // preprocessing passes in `check_sat_internal_preprocess_and_solve`
        // rewrite `ctx.assertions` IN PLACE using facts mined from the CURRENT
        // (scope-mixed) assertion set. `inline_determined_string_vars` is the
        // sharpest case: a literal pinned by a scope-N equality (`(= s "abc")`)
        // is substituted into assertions from OUTER scopes and folded — an
        // outer `(= (str.len s) 2)` becomes `false` IN the assertion vector.
        // `ctx.assertions` is scope-tracked state owned by push/pop:
        // `Context::pop` truncates it by COUNT, so any content change leaks
        // scope-derived residue into outer scopes — after `(pop 1)` the
        // surviving outer assertion IS the folded `false` and every later
        // `(check-sat)` wrongly answers unsat. Snapshot here, BEFORE the first
        // in-place pass, and restore on every exit (the inner
        // `solve_current_assertions_with_quantifier_support` keeps its own,
        // LATER snapshot for the theory-route passes; it cannot cover the
        // passes that run before it). The restored vector is also what the
        // model-validation gates and `(get-assertions)` then see — the user's
        // original assertions, which every preprocessing pass in the helper
        // must (and does) preserve model-for-model.
        let scope_tracked_assertions = self.ctx.assertions.clone();
        // (#selfcert-authored) This snapshot — taken BEFORE the first in-place
        // preprocessing pass — is exactly the set of assertions the USER
        // authored for this check-sat. Publish it for the fail-closed
        // `--self-check` SAT gate, which must certify the emitted model against
        // the user's formula rather than against the solver's internal,
        // proof-mode assertion window. Save/restore so a nested `check_sat_internal`
        // (retry or probe solve) restores the outer window on the way out and can
        // never lend its narrower snapshot to the outer verdict. Only paid for
        // under `--self-check`; otherwise the field stays `None` (fails closed).
        let saved_authored = if self.self_check {
            self.self_check_authored_assertions
                .replace(scope_tracked_assertions.clone())
        } else {
            self.self_check_authored_assertions.take()
        };
        let result = self.check_sat_internal_preprocess_and_solve();
        self.self_check_authored_assertions = saved_authored;
        self.ctx.assertions = scope_tracked_assertions;
        result
    }

    /// Preprocessing passes + solve dispatch for `check_sat_internal`.
    ///
    /// Everything in here may rewrite `ctx.assertions` in place; the caller
    /// (`check_sat_internal`) snapshots and restores the scope-tracked
    /// assertion vector around this call, so no in-place residue can survive
    /// into a later `(pop)`/`(check-sat)` (#incremental-pushpop-soundness).
    fn check_sat_internal_preprocess_and_solve(&mut self) -> Result<SolveResult> {
        // Named-assert rewrite provenance is strictly per-preprocessing-run
        // (#uc-named-provenance): entries recorded by THIS call's passes are
        // consumed by THIS call's named-core redirect and never leak into a
        // later check.
        self.named_assert_rewrites.clear();

        if !self.produce_proofs_enabled() {
            self.rewrite_dense_bv_array_initializer_selects();
        }

        // Ground string constant folding (#mix-string-array, mix_WS_87): fold
        // fully-ground `str.*` ops to constants for EVERY theory path. The
        // pure-string solvers already do this, but a mixed string+array/UF
        // problem dispatches to a combined solver that does not, leaving a
        // ground-decidable conjunct like
        // `(= (str.len (str.substr (str.substr "ab" 2 2) 1 0)) 4)` unevaluated
        // (and an array-sourced sibling then forces a conservative Unknown).
        // Pure constant folding is sound; `mk_eq` folds the resulting `(= 0 4)`
        // to false so the enclosing conjunction is decided UNSAT. Runs in proof
        // mode too — the pure-string theory paths already fold ground ops under
        // proof production, so the proof checker handles the folded constants.
        let str_feats = StaticFeatures::collect(&self.ctx.terms, &self.ctx.assertions);
        if str_feats.has_strings {
            // Inline String variables fixed to a literal by a top-level equality
            // BEFORE folding (#mix-str2int-array-index). Makes string→Int ops over
            // such a variable (`(str.to_int s)` etc.) ground so the fold below
            // evaluates them to a concrete value; without this, a string→Int op
            // used as an ARRAY INDEX stays opaque to the combined array/EUF/LIA
            // solver, so `(select a (str.to_int s))` (with `s = ""`, value `-1`)
            // is never unified with `(select a (- 1))` and a contradictory pair of
            // selects is wrongly satisfiable. Sound/equisatisfiable: `s` is asserted
            // equal to the literal in every model, so substitution preserves truth.
            // Run the inlining whenever strings are present (not only with
            // arrays). It is a sound, equisatisfiable substitution of a string
            // variable by the literal a top-level equality pins it to. Besides
            // the array-index case above, this grounds a string-valued DATATYPE
            // SELECTOR concat fed to str.contains: `(str.contains s (str.++ (k
            // d) s s))` with `(= s "x")` becomes `(str.contains "x" (str.++ (k
            // d) "x" "x"))`, exposing the constant "xx" block whose length 2 >
            // |"x"| = 1 refutes contains in the StringOracle (#str-contains-dt-selector).
            let inlined = self.inline_determined_string_vars(&self.ctx.assertions.clone());
            self.ctx.assertions = inlined;
            let folded = self.fold_ground_string_ops(&self.ctx.assertions.clone());
            self.ctx.assertions = folded;
        }
        // Bool-valued ITE soundness rewrite (#A1-arr-lia561 + #b16-uflia-deep
        // wrong-UNSAT). A top-level `(ite c t e)` with Bool branches over theory
        // atoms can drive the combined solver to a SPURIOUS unsat (false
        // theorem):
        //   - ARRAY path: the eager array-axiom scan treats `select` terms from
        //     BOTH ite branches as simultaneously active and learns a
        //     cross-branch conflict that holds under neither branch alone.
        //   - UF path: the EUF congruence scan treats the Bool-valued UF
        //     predicate applications in BOTH ite branches (e.g. `(p0 x0 0)` and
        //     `(p0 4 (h -4))`) as simultaneously active and derives the same
        //     cross-branch conflict. Repro (QF_UFLIA, all 3 asserts needed):
        //       (not (ite (= (h x1) x1) (p0 x0 0) (p0 4 (h -4))))
        //       (not (ite (> x1 -6) (p0 -6 x0) (> x1 x0)))
        //       (ite (>= x0 x1) (not (= x1 x0)) (= x1 x0))
        //     AY returned unsat; z3 sat (x0=1,x1=0,h(0)=5,h(-4)=9, all p0 false).
        //     Rewriting ANY ONE of the Bool ITEs to and/=> form recovers sat.
        // The logically-identical `(and (=> c t) (=> (not c) e))` keeps the
        // branches mutually exclusive in the SAT structure. Rewrite each
        // assertion that is itself a Bool ITE, and each top-level conjunct that
        // is a Bool ITE, to that form. Semantically EXACT — it can never flip a
        // sat/unsat verdict, only avoid the unsound ITE path (worst case: a hard
        // instance stays Unknown rather than a wrong UNSAT). Scoped to array/UF
        // problems, where the eager-axiom / congruence cross-branch interaction
        // manifests.
        if str_feats.has_arrays || str_feats.has_uf {
            self.rewrite_assertion_bool_ites();
            // Companion for the array-VALUED ITE case: push select/store through
            // `(ite c A B)` so the eager array-axiom scan cannot relate both
            // branches' array terms across the split (#alia-select-over-ite).
            self.rewrite_select_over_array_ite();
        }
        // String length axioms (concat length-sum + non-negativity + empty
        // biconditional) for MIXED string+array problems (#mix-string-len). The
        // pure-string-LIA solver emits these, but a string+array problem dispatches
        // to a combined solver that skips them, leaving `(str.len (str.++ "ab"
        // (select a 3))) = 1` satisfiable (actually `2 + len(select) >= 2 > 1`).
        // Every emitted axiom is a valid string fact — only ADDS refutation power.
        if str_feats.has_strings && str_feats.has_arrays {
            let len_axioms = self.collect_str_len_axioms();
            if !len_axioms.is_empty() {
                let mut seen: std::collections::HashSet<TermId> =
                    self.ctx.assertions.iter().copied().collect();
                let fresh: Vec<TermId> =
                    len_axioms.into_iter().filter(|a| seen.insert(*a)).collect();
                self.ctx.assertions.extend(fresh);
            }
            // str.substr length UPPER-BOUND axioms (#mix-substr-len, mix_WS_167/282).
            // `(str.len (str.substr s i n))` is bounded by `n`, by `len(s)`, and by
            // `len(s) - i` (when non-empty). The combined string+array solver treats
            // it as an unconstrained non-negative integer, leaving e.g.
            // `(= (str.len (str.substr (select a 0) 0 2)) 4)` wrongly satisfiable.
            // Every emitted bound is a valid string fact (sound for all i/n).
            let substr_axioms = self.collect_substr_len_bound_axioms();
            if !substr_axioms.is_empty() {
                let mut seen: std::collections::HashSet<TermId> =
                    self.ctx.assertions.iter().copied().collect();
                let fresh: Vec<TermId> = substr_axioms
                    .into_iter()
                    .filter(|a| seen.insert(*a))
                    .collect();
                self.ctx.assertions.extend(fresh);
            }
            // String→Int VALUE axioms for terms used as array indices
            // (#mix-str2int-array-index): without these, a `str.to_int` /
            // `str.indexof` / `str.replace`-length term used as an array index is
            // opaque to the combined array/EUF/LIA solver, so `(select a <idx>)`
            // is never unified with another select sharing the determined index and
            // a contradictory pair is wrongly satisfiable.
            //   - str.to_int of a provably non-numeric string is -1
            //   - str.indexof out of range is -1
            //   - length-preserving str.replace preserves str.len
            // Each axiom is implied by SMT-LIB semantics (verified vs z3), so this
            // only ADDS refutation power and cannot manufacture a wrong-UNSAT.
            let to_int_axioms = self.collect_str_to_int_nonnumeric_axioms();
            let index_axioms = self.collect_str_index_value_axioms();
            let extra: Vec<TermId> = to_int_axioms.into_iter().chain(index_axioms).collect();
            if !extra.is_empty() {
                let mut seen: std::collections::HashSet<TermId> =
                    self.ctx.assertions.iter().copied().collect();
                let fresh: Vec<TermId> = extra.into_iter().filter(|a| seen.insert(*a)).collect();
                self.ctx.assertions.extend(fresh);
            }
        }

        // Trivially-true fast path: when all assertions have been simplified
        // to `true` by term construction (e.g., mk_select/mk_eq constant
        // folding reduces `select(store(a,i,v),i) = v` to `true`), return
        // SAT without invoking the solver pipeline. The pipeline's
        // TheoryExtension scans the full TermStore for theory terms and may
        // request spurious model equalities for terms unreachable from any
        // assertion, causing false Unknown results.
        //
        // Store an EMPTY model rather than `None`: the passes above may have
        // folded ground-true assertions (e.g. `(str.prefixof "a" "ab")`) to
        // `true`, and the caller restores the ORIGINAL assertion vector before
        // the check-sat postcondition and output paths run
        // (#incremental-pushpop-soundness). Ground assertions constrain no
        // variable, so the empty model (completed for declared constants by
        // `complete_unconstrained_constants_for_output`) is a genuine witness.
        {
            let true_term = self.ctx.terms.true_term();
            if self.ctx.assertions.iter().all(|&a| a == true_term) {
                self.last_model = Some(super::model::Model::empty());
                self.last_model_validated = true;
                return Ok(SolveResult::Sat);
            }
        }

        // Phase 5 difference-logic pre-check (default OFF; opt-in via
        // `(set-option :ay-diff-logic true)`). When ON and every hard assertion
        // is a pure QF_IDL/QF_RDL atom, the standalone self-certifying
        // Bellman-Ford engine decides the instance. Any non-DL assertion (or the
        // engine declining) returns `None` and we fall through to the normal
        // solver, so the default-OFF path is byte-identical to before. See
        // `executor::diff_logic`.
        self.record_diff_logic_decided_for_test(false);
        if let Some(dl_result) = self.try_diff_logic()? {
            self.record_diff_logic_decided_for_test(true);
            self.last_result = Some(dl_result.clone());
            return Ok(dl_result);
        }

        // Unsat core extraction: when produce-unsat-cores is enabled and there
        // are named assertions, redirect through check_sat_assuming with named
        // assertions as assumptions. The SAT solver's failed-assumption tracking
        // then gives us the minimal unsat core (MiniSat approach).
        if self.produce_unsat_cores_enabled() {
            let term_to_name: HashMap<TermId, String> = self
                .ctx
                .named_terms_iter()
                .map(|(name, tid)| (tid, name.to_string()))
                .collect();

            if !term_to_name.is_empty() {
                // Parse-time named TermIds, snapshotted BEFORE the rewrite-
                // provenance extension below (the coverage guard reasons in
                // parse-key space).
                let parse_named_keys: std::collections::HashSet<TermId> =
                    term_to_name.keys().copied().collect();

                // Rewrite-provenance extension (#uc-named-provenance): a
                // named assert rewritten in place by an equivalence-exact
                // preprocessing pass of THIS call (Bool-ITE and
                // select-over-array-ite rewrites; see
                // `named_assert_rewrites`) is still assumption-trackable —
                // its rewritten form carries the label. Without this, every
                // such assert landed in the unnamed base, the coverage guard
                // tripped, and the core padded to ALL named assertions
                // (reduction 0 across 2018-Goel-hwbench, whose named asserts
                // are Bool ITEs). Printing the label for the rewritten form
                // is sound because the rewrite preserves per-assertion
                // equivalence: the original named formula set the validator
                // re-checks is logically interchangeable with the solved set.
                let mut term_to_name = term_to_name;
                if !self.named_assert_rewrites.is_empty() {
                    for &assertion in &self.ctx.assertions {
                        if term_to_name.contains_key(&assertion) {
                            continue;
                        }
                        if let Some(&root) = self.named_assert_rewrites.get(&assertion) {
                            if let Some(name) = term_to_name.get(&root).cloned() {
                                term_to_name.insert(assertion, name);
                            }
                        }
                    }
                }

                // Split assertions: named become assumptions, unnamed stay as base
                let mut named_assumptions = Vec::new();
                let mut unnamed_assertions = Vec::new();
                for &assertion in &self.ctx.assertions {
                    if term_to_name.contains_key(&assertion) {
                        named_assumptions.push(assertion);
                    } else {
                        unnamed_assertions.push(assertion);
                    }
                }

                // Only redirect if there are named assertions in the assertion set
                if !named_assumptions.is_empty() {
                    // Finite-enum pigeonhole NAMED-CORE fast path (#uc-qfdt):
                    // runs BEFORE the named→assumptions split because the
                    // generic assumption engine never reaches the pigeonhole
                    // pass (it lives in the plain-path preprocessing), so
                    // coloring-scale QF_DT/QF_UFDT instances that plain
                    // check-sat refutes in seconds time out in named mode.
                    // FAIL-CLOSED: fires only on an in-process re-verified
                    // clique core whose assertions are all named; any doubt
                    // falls through to the redirect below (worst case: the
                    // all-named fallback core — valid, reduction 0). Under
                    // produce-proofs, `check_sat_guarded` materializes the
                    // proof envelope for this pre-SAT unsat exactly as it
                    // does for the plain-path pigeonhole fast path (#9037);
                    // under --self-check the envelope fails certification and
                    // the answer soundly degrades to unknown there.
                    if let Some(core) = self.try_enum_pigeonhole_named_core(&term_to_name) {
                        self.last_model = None;
                        self.last_proof = None;
                        self.last_assumptions = None;
                        self.last_unknown_reason = None;
                        self.last_assumption_core = Some(core);
                        self.last_core_term_to_name = Some(term_to_name);
                        return Ok(SolveResult::unsat());
                    }
                    // FAIL-CLOSED provenance-coverage guard (#uc-qfdt,
                    // invalidated-core root cause): `named_terms` registers
                    // the parse-time inner TermId, but assert-time
                    // elaboration/rewriting can store a DIFFERENT TermId in
                    // `ctx.assertions` (observed on 20230720-blocksworld:
                    // 6 of 23 named asserts). Those named asserts then land
                    // in `unnamed_assertions` (base) — always asserted but
                    // never eligible for the assumption core — so ANY
                    // minimized core under-covers them and the reduced
                    // benchmark can be SAT (an invalidated core, e=1 under
                    // 2025 UC scoring). Coverage is counted in PARSE-KEY
                    // space: an assumption-tracked assertion covers a parse
                    // key either verbatim or through this call's
                    // equivalence-exact rewrite chain (#uc-named-provenance).
                    // Anything unaccounted trips the guard and, on UNSAT,
                    // drops the minimized core so `unsat_core()` falls back
                    // to ALL named assertions (valid by construction,
                    // reduction 0). With no recorded rewrites this reduces
                    // byte-identically to the historical distinct-count
                    // check.
                    let provenance_broken = {
                        let covered_parse_keys: std::collections::HashSet<TermId> =
                            named_assumptions
                                .iter()
                                .map(|&a| {
                                    if parse_named_keys.contains(&a) {
                                        a
                                    } else {
                                        self.named_assert_rewrites.get(&a).copied().unwrap_or(a)
                                    }
                                })
                                .filter(|t| parse_named_keys.contains(t))
                                .collect();
                        covered_parse_keys.len() < parse_named_keys.len()
                    };

                    // Temporarily replace assertions with unnamed-only
                    let original_assertions =
                        std::mem::replace(&mut self.ctx.assertions, unnamed_assertions);

                    self.last_model = None;
                    let result = self.check_sat_assuming(&named_assumptions);
                    // Certificate gate while the base is still stripped: a
                    // harvested proper-subset core must re-prove UNSAT on its
                    // own or it is discarded (#unsat-core-miscount).
                    let result = self.certify_assumption_core(&named_assumptions, result);

                    // Completeness rescue (#named-cores-ground-sat): the
                    // named→assumption redirect is a core-TRACKING strategy,
                    // not a verdict authority — on Unknown, re-solve the
                    // un-named equivalent (the full original assertion set
                    // through the plain pipeline) while the base is still
                    // stripped. A rescue UNSAT records the all-named core
                    // (reduction 0, sound by construction). See
                    // `rescue_named_core_redirect_unknown`.
                    let (result, rescue_elapsed) = match result {
                        Ok(SolveResult::Unknown) => {
                            let rescue_started = Instant::now();
                            let rescued =
                                self.rescue_named_core_redirect_unknown(&named_assumptions);
                            (rescued, Some(rescue_started.elapsed()))
                        }
                        other => (other, None),
                    };

                    // Deletion-based EUF/ArrayEuf core minimization while the
                    // base is still stripped (#uc-core-minimize): shrinks the
                    // certified core — including the empty-harvest→pad-all
                    // theory-refutation case AND the rescue's conservative
                    // all-assumptions core — by re-solving subsets, budget-
                    // aware and fail-closed (only solve-verified subsets are
                    // adopted). Runs AFTER the rescue: the measured
                    // reduction-0 families (QG-classification, storecomm)
                    // reach unsat through it. Skipped when provenance is
                    // broken: the minimized core would be discarded below
                    // anyway.
                    let result = if provenance_broken {
                        result
                    } else {
                        self.minimize_assumption_core(&named_assumptions, result, rescue_elapsed)
                    };

                    // Restore original assertions
                    self.ctx.assertions = original_assertions;

                    if provenance_broken && matches!(result, Ok(ref r) if r.is_unsat()) {
                        self.last_assumption_core = None;
                    }

                    // Set the term-to-name mapping AFTER check_sat_assuming
                    // (which clears it as part of its own state reset).
                    self.last_core_term_to_name = Some(term_to_name);

                    return result;
                }
            }
        }

        let final_result = self.solve_current_assertions_with_quantifier_support();

        // #9037: Several theory/preprocessing fast paths can prove UNSAT before
        // entering SAT-level proof tracing. The check-sat boundary still owns the
        // public proof contract, so materialize a proof envelope before asserting
        // the invariant below.
        if matches!(final_result, Ok(ref result) if result.is_unsat())
            && self.produce_proofs_enabled()
            && self.last_proof.is_none()
        {
            self.build_unsat_proof();
        }

        // SolveResult boundary postcondition contracts (#4642).
        // Every SAT must have a model, every proof-enabled UNSAT must have a proof.
        if let Ok(ref result) = final_result {
            match result {
                SolveResult::Sat => {
                    debug_assert!(
                        self.last_model.is_some()
                            || self.ctx.assertions.is_empty()
                            || self
                                .ctx
                                .assertions
                                .iter()
                                .all(|&a| a == self.ctx.terms.true_term()),
                        "BUG: check_sat_internal returned SAT without populating last_model"
                    );
                }
                SolveResult::Unsat(_) => {
                    debug_assert!(
                        self.last_proof.is_some() || !self.produce_proofs_enabled(),
                        "BUG: check_sat_internal returned UNSAT without proof \
                         (produce-proofs is enabled)"
                    );
                }
                SolveResult::Unknown => {}
            }
        }

        final_result
    }

    /// Route to the appropriate theory solver based on detected logic category.
    ///
    /// Extracted from `check_sat_internal` for readability — the logic routing
    /// table is the largest single block in the check-sat pipeline.
    pub(in crate::executor) fn route_to_solver(
        &mut self,
        category: LogicCategory,
        features: &StaticFeatures,
    ) -> Result<SolveResult> {
        let assertion_features = StaticFeatures::collect(&self.ctx.terms, &self.ctx.assertions);
        let has_native_seq_ops = assertion_features.has_seq_ops;

        // A surviving `(rem a b)` application has a symbolic or literal-zero
        // divisor (a non-zero CONSTANT divisor is folded by `mk_rem` before
        // interning). Such a `rem` is not soundly solvable on every theory path
        // — notably the NIA tentative-model patch treats it as a FREE integer and
        // would wave through a model violating its defining bound (a wrong-SAT).
        // It is a rare operation, so degrade UNIVERSALLY (before any solver runs)
        // to a sound `unknown` rather than risk an unsound verdict
        // (#nia-symbolic-rem-bypass).
        if crate::executor::mod_div_elim::contains_int_rem(&self.ctx.terms, &self.ctx.assertions) {
            self.last_unknown_reason = Some(UnknownReason::UnsupportedArithmetic);
            return Ok(SolveResult::Unknown);
        }

        let result = match category {
            LogicCategory::Propositional => self.solve_propositional(),
            LogicCategory::QfUf => self.solve_euf(),
            LogicCategory::QfS => self.solve_strings(),
            LogicCategory::QfAx => {
                // #qfax-combiner-probe: route through the AUFLIA combiner
                // (live ArraysSolver + lazy Row2Down) instead of the
                // axiom-pregeneration pipeline — measurement flag for the
                // in-search ROW instantiation build.
                if std::env::var_os("AY_QFAX_COMBINER_ROUTE").is_some() {
                    self.solve_auf_lia()
                } else {
                    // #qfax-budget-ladder: the fixpoint's ROW-closure budgets
                    // are sized for 7-9 level chains; deeper swap/storeinv
                    // chains exhaust them and degrade to validated-unknown
                    // (measured: storeinv_t1_np_sf converts unknown -> unsat
                    // in 0.05s at 16x budgets). Retry ONCE at a raised tier
                    // when the standard solve returns a non-timeout Unknown —
                    // solved files never pay, and the gates re-validate the
                    // retry exactly like any solve.
                    // Snapshot BEFORE tier-1: solve_array_euf rewrites
                    // ctx.assertions destructively, and tier-2 must start
                    // from the ORIGINAL problem, not tier-1's residue.
                    let pre_tier_assertions = self.ctx.assertions.clone();
                    let tier1 = self.solve_array_euf();
                    match &tier1 {
                        Ok(SolveResult::Unknown)
                            if !matches!(
                                self.last_unknown_reason,
                                Some(UnknownReason::Timeout)
                            ) && !self.solve_deadline.expired() =>
                        {
                            self.ctx.assertions = pre_tier_assertions;
                            self.qfax_budget_multiplier = 16;
                            self.last_result = None;
                            self.last_model = None;
                            self.last_unknown_reason = None;
                            let tier2 = self.solve_array_euf();
                            self.qfax_budget_multiplier = 1;
                            tier2
                        }
                        _ => tier1,
                    }
                }
            }
            // `is_int` over a Real argument needs the NRA exact univariate
            // decider; pure LRA returns Unknown (it ignores integrality). The
            // NRA solver embeds the same LRA simplex plus the exact univariate
            // `is_int`/division decider, so it is a sound superset for these
            // QF_LRA problems (#9139).
            LogicCategory::QfLra if features.has_is_int_real => self.solve_nra(),
            LogicCategory::QfLra => self.solve_lra(),
            LogicCategory::QfLia => {
                if features.has_bv_int_conversion {
                    let bridge_result = self.solve_bv_lia_bridge()?;
                    if bridge_result.is_unsat() {
                        return Ok(bridge_result);
                    }
                }
                // A `(mod a b)` / `(div a b)` with a SYMBOLIC (non-constant)
                // divisor is genuine non-linear integer arithmetic that the pure
                // QF_LIA pipeline cannot decide: `preprocess_lia_artifacts` only
                // eliminates a CONSTANT divisor, so the symbolic term survives to
                // `poly_residual` as an UNCONSTRAINED opaque factor (no defining
                // axiom). A determined UNSAT such as `y>0 ∧ (mod x y) >= y` is then
                // MISSED (returned `unknown`) and a bound-violating model could
                // slip through (SND-ARITH-1). The NIA solver's `eliminate_int_mod_div`
                // replaces the term with a fresh remainder/quotient constrained by
                // the guarded Euclidean axioms (`d≠0 → a = d*q + r`, `d>0 → 0≤r<d`,
                // `d<0 → 0≤r<-d`, `d=0` unconstrained → #div0 validation bypass),
                // so route these to `solve_nia`. `solve_nia` is a sound superset of
                // `solve_lia` for the pure-integer fragment. This QF_LIA arm has no
                // UF/arrays (those categories route elsewhere: QF_UFLIA/QF_AUFLIA,
                // where a symbolic `mod` is handled soundly as an opaque
                // congruence term / fails closed), so pure-LIA re-routing cannot
                // perturb the UF-congruence completeness those paths rely on.
                if crate::executor::mod_div_elim::contains_symbolic_int_mod_div(
                    &self.ctx.terms,
                    &self.ctx.assertions,
                ) {
                    self.solve_nia()
                } else {
                    self.solve_lia()
                }
            }
            LogicCategory::QfNia => self.solve_nia(),
            LogicCategory::QfNra => self.solve_nra(),
            LogicCategory::QfNira => {
                if features.has_real {
                    self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    Ok(SolveResult::Unknown)
                } else {
                    self.solve_nia()
                }
            }
            // QF_UFNRA: UF + non-linear real arithmetic — combined via Nelson-Oppen (#6294).
            LogicCategory::QfUfnra => self.solve_uf_nra(),
            // QF_UFNIA/QF_UFNIRA: UF + non-linear integer arithmetic (#4525).
            // Combined EUF+NIA solver via Nelson-Oppen theory combination.
            // NIA is incomplete (QF_NIA is undecidable) so may return Unknown
            // on hard nonlinear instances, but handles linear + simple nonlinear.
            LogicCategory::QfUfnia => self.solve_uf_nia(),
            // QfUfnira with Real sort: solve_uf_nia() has only EUF+NIA (no LRA),
            // so Real constraints (e.g., to_real(x*x) < 0) would be treated as
            // opaque SAT literals, producing false SAT. Return Unknown instead (#8200).
            LogicCategory::QfUfnira => {
                if features.has_real {
                    self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    Ok(SolveResult::Unknown)
                } else {
                    self.solve_uf_nia()
                }
            }
            // Pure UF+LIA no longer needs the array-carrying AUFLIA combiner (#8778).
            // If detection sees arrays or another theory, keep the broader AUFLIA route.
            // Nonlinear terms upgraded to QfUfnia pre-dispatch (#6086).
            LogicCategory::QfUflia => {
                if features.has_bv_int_conversion {
                    let bridge_result = self.solve_bv_lia_bridge()?;
                    if bridge_result.is_unsat() {
                        return Ok(bridge_result);
                    }
                }
                if has_only_uf_lia_theories(&assertion_features) {
                    let main = self.solve_uf_lia();
                    // #mgr-uf-ackermann retry: the lazy N-O combination can
                    // fail-close on ground UFLIA when a candidate LIA model
                    // aliases two argument tuples by value while their UF
                    // applications differ (functional inconsistency the
                    // independent gate rejects). On a non-timeout Unknown,
                    // assert the pairwise Ackermann congruence tautologies
                    // once and re-solve; restore the window afterwards. A
                    // miss stays unknown — verdicts remain gate-licensed.
                    match &main {
                        Ok(SolveResult::Unknown)
                            if !self.incremental_mode
                                && !self.original_problem_had_quantifiers
                                && !matches!(
                                    self.last_unknown_reason,
                                    Some(UnknownReason::Timeout)
                                )
                                && !self.solve_deadline.expired() =>
                        {
                            let saved_assertions = self.ctx.assertions.clone();
                            let added =
                                self.add_uf_ackermann_congruence_clauses(MGR_ROW_PEEL_CLAUSE_CAP);
                            if added > 0 {
                                self.last_unknown_reason = None;
                                self.last_result = None;
                                self.last_model = None;
                                let retry = self.solve_uf_lia();
                                self.ctx.assertions = saved_assertions;
                                if !matches!(retry, Ok(SolveResult::Unknown)) {
                                    retry
                                } else {
                                    main
                                }
                            } else {
                                self.ctx.assertions = saved_assertions;
                                main
                            }
                        }
                        _ => main,
                    }
                } else {
                    self.solve_auf_lia()
                }
            }
            LogicCategory::QfSeq => self.solve_seq(),
            LogicCategory::QfSeqBv => self.solve_seq(),
            LogicCategory::QfSeqlia => self.solve_seq_lia(),
            LogicCategory::QfSet => self.solve_set_lia(),
            LogicCategory::QfSetlia => self.solve_set_lia(),
            LogicCategory::QfMultiset => self.solve_multiset_lia(),
            LogicCategory::QfMslia => self.solve_multiset_lia(),
            LogicCategory::QfMap => self.solve_map_lia(),
            LogicCategory::QfMaplia => self.solve_map_lia(),
            LogicCategory::QfSlia => self.solve_strings_lia(),
            // QF_SNIA: route linear formulas to strings+LIA (#3389).
            LogicCategory::QfSnia => {
                if features.has_nonlinear_int {
                    self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    Ok(SolveResult::Unknown)
                } else {
                    self.solve_strings_lia()
                }
            }
            // Nonlinear terms upgraded to QfUfnra pre-dispatch (#6086).
            LogicCategory::QfUflra => self.solve_uf_lra(),
            // Nonlinear terms upgraded to QfUfnia pre-dispatch (#6086).
            LogicCategory::QfAuflia => {
                if features.has_bv_int_conversion {
                    let bridge_result = self.solve_bv_lia_bridge()?;
                    if bridge_result.is_unsat() {
                        return Ok(bridge_result);
                    }
                }
                if has_native_seq_ops {
                    self.solve_seq_auflia()
                } else if has_only_uf_lia_theories(&assertion_features) {
                    self.solve_uf_lia()
                } else {
                    // #qf-auflia-arrayeuf-retry: when the window's only integer
                    // content is bare constants and (dis)equalities, the
                    // Array+EUF route is sound standalone (distinct Int
                    // constants are distinct EUF atoms; UNSAT derivations hold
                    // under the Int interpretation; SAT still passes the
                    // fail-closed gates) — and much FASTER on the SMT-COMP
                    // storecomm/swap/storeinv '_pp_' families, so it runs
                    // FIRST. The first pass is fully ISOLATED: it may append
                    // generated array axioms / rewrite the assertion window,
                    // and feeding those artifacts into the AUFLIA pipeline
                    // produced false UNSATs on the storeinv_invalid fences
                    // (route-first attempt #1) — the window is snapshotted and
                    // restored around it.
                    // #qf-alia-row2-divergence: unsat-only rescue via complete
                    // eager array saturation + Ackermannization to a ground
                    // constants-only problem (see combined/arrays_to_lia.rs).
                    // Runs BEFORE the escalation ladder because on the SVC
                    // QF_ALIA read/pointer family (read2) the lazy loop
                    // diverges to the deadline, so a post-ladder rescue would
                    // never fire. Starvation-bounded: bails (None) cheaply
                    // when the fragment does not apply or the reduced problem
                    // exceeds the solve-size cap, and the inner solve is
                    // capped at half the remaining time budget — an instance
                    // the normal pipeline already solves pays only the
                    // milliseconds-cheap reduction attempt.
                    if let Some(result) = self.try_unsat_via_arrays_to_lia_ackermann()? {
                        return Ok(result);
                    }
                    // #qfax-quantified-bypass: the isolated array-EUF escalation
                    // below is a QUANTIFIER-FREE fast path. When this ground
                    // window came from quantifier stripping (`(set-logic ALL)`
                    // auto-detection lands here as QfAuflia after
                    // process_quantifiers), a stage-1 `Sat` short-circuits the
                    // interleaved E-matching refinement: the isolated route's
                    // snapshot/restore discards its own witness artifacts and
                    // leaves no EUF model for `try_ematching_refinement_round`,
                    // so the quantifier loop can never instantiate at the
                    // extensionality witness and the #8729 guard degrades a
                    // provable UNSAT to Unknown (Z3 #7544: subset-antisymmetry
                    // over `(Array Int Bool)`; regressed in 4a853221). Route
                    // quantified problems through `solve_auf_lia` like the
                    // explicit-AUFLIA arm instead.
                    let constants_only = !self.incremental_mode
                        && !self.original_problem_had_quantifiers
                        && crate::term_helpers::int_constraints_are_constants_only(
                            &self.ctx.terms,
                            &self.ctx.assertions,
                        );
                    if constants_only {
                        // #qfax-escalation: ONE ordered sequence over the
                        // isolated array-EUF route. Cheapest first; each
                        // stage runs only when the previous returned a
                        // non-timeout validated-unknown; the assertion
                        // window is snapshotted once and restored on every
                        // exit; every stage's verdict passes the full gate
                        // battery like any solve.
                        //   1. standard budgets            (most files)
                        //   2. ladder: 16x ROW budgets     (deep chains)
                        //   3. CEGAR pattern-blocking      (opt-in: budget-
                        //      immune refutations; AY_QFAX_CEGAR=1)
                        let dbg_esc = std::env::var_os("AY_DEBUG_CEGAR").is_some();
                        let saved_assertions = self.ctx.assertions.clone();
                        let mut stage_result = self.solve_array_euf()?;
                        self.ctx.assertions = saved_assertions.clone();
                        if dbg_esc {
                            eprintln!(
                                "[escalation] stage1={stage_result:?} reason={:?}",
                                self.last_unknown_reason
                            );
                        }
                        if stage_result != SolveResult::Unknown {
                            return Ok(stage_result);
                        }
                        let can_continue = |exec: &Self| {
                            !matches!(exec.last_unknown_reason, Some(UnknownReason::Timeout))
                                && !exec.solve_deadline.expired()
                        };
                        // Stage 2: budget ladder.
                        if can_continue(self) {
                            self.last_unknown_reason = None;
                            self.last_result = None;
                            self.last_model = None;
                            self.qfax_budget_multiplier = 16;
                            let second = self.solve_array_euf();
                            self.qfax_budget_multiplier = 1;
                            stage_result = second?;
                            self.ctx.assertions = saved_assertions.clone();
                            if dbg_esc {
                                eprintln!(
                                    "[escalation] stage2={stage_result:?} reason={:?}",
                                    self.last_unknown_reason
                                );
                            }
                            if stage_result != SolveResult::Unknown {
                                return Ok(stage_result);
                            }
                        }
                        // Stage 2b (default-on, #mgr-row-peel): demand-driven
                        // deep read-over-write peel. The bounded eager phase
                        // withholds inner-layer ROW splits (#8785), so models
                        // that need index aliasing below the outermost store
                        // layer are inexpressible and fail-close to unknown
                        // (A2_alias/A3_comm classes). Reaching this stage IS
                        // the demand signal: assert the full per-layer
                        // ROW1/ROW2 tautologies for every reachable
                        // select-over-store chain and re-solve once. Sound in
                        // both directions (tautologies, Alethe-recorded); the
                        // verdict is still licensed by the solve + the
                        // independent model gate, never by this repair.
                        if can_continue(self) {
                            let peeled =
                                self.add_array_row_deep_peel_clauses(MGR_ROW_PEEL_CLAUSE_CAP);
                            if peeled > 0 {
                                self.last_unknown_reason = None;
                                self.last_result = None;
                                self.last_model = None;
                                stage_result = self.solve_array_euf()?;
                                self.ctx.assertions = saved_assertions.clone();
                                if dbg_esc {
                                    eprintln!(
                                        "[escalation] stage2b(row-peel, {peeled} clauses)={stage_result:?} reason={:?}",
                                        self.last_unknown_reason
                                    );
                                }
                                if stage_result != SolveResult::Unknown {
                                    return Ok(stage_result);
                                }
                            } else {
                                self.ctx.assertions = saved_assertions.clone();
                            }
                        }
                        // Stage 3 (opt-in): CEGAR pattern-blocking rounds.
                        // Each rejection derives a clause proving the
                        // rejected model's index pattern element-
                        // independently unsatisfiable; assert and re-solve.
                        let mut cegar_rounds = 0usize;
                        while std::env::var_os("AY_QFAX_CEGAR").is_some()
                            && cegar_rounds < 24
                            && can_continue(self)
                        {
                            let Some(lits) = self.qfax_refinement_clause.take() else {
                                break;
                            };
                            cegar_rounds += 1;
                            let mut disj: Vec<TermId> = Vec::new();
                            for (atom, val) in lits {
                                let lit = if val {
                                    self.ctx.terms.mk_not(atom)
                                } else {
                                    atom
                                };
                                disj.push(lit);
                            }
                            let clause = if disj.len() == 1 {
                                disj[0]
                            } else {
                                self.ctx.terms.mk_or(disj)
                            };
                            self.ctx.assertions.push(clause);
                            self.last_unknown_reason = None;
                            self.last_result = None;
                            self.last_model = None;
                            let refined = self.solve_array_euf()?;
                            if refined != SolveResult::Unknown {
                                self.ctx.assertions = saved_assertions;
                                return Ok(refined);
                            }
                        }
                        if cegar_rounds > 0 {
                            self.ctx.assertions = saved_assertions.clone();
                        }
                        self.qfax_refinement_clause = None;
                        self.last_unknown_reason = None;
                        self.last_result = None;
                        self.last_model = None;
                    }
                    let main = self.solve_auf_lia();
                    // #qfax-budget-ladder (AUFLIA side): the same fixpoint
                    // budget wall exists inside the AUFLIA pipeline's
                    // LazyRow2FinalCheck pass for the non-constants-only
                    // variants. Retry once at the raised tier on a
                    // non-timeout Unknown; with_deferred_postprocessing
                    // restores the original assertions, so the pipeline is
                    // re-runnable, and every gate re-validates the retry.
                    match &main {
                        Ok(SolveResult::Unknown)
                            if self.qfax_budget_multiplier == 1
                                && !matches!(
                                    self.last_unknown_reason,
                                    Some(UnknownReason::Timeout)
                                )
                                && !self.solve_deadline.expired() =>
                        {
                            self.last_unknown_reason = None;
                            self.last_result = None;
                            self.last_model = None;
                            self.qfax_budget_multiplier = 16;
                            let retry = self.solve_auf_lia();
                            self.qfax_budget_multiplier = 1;
                            // Stage 4 (#qfax-cegar, DEFAULT-ON as last
                            // resort): everything cheaper has failed. Each
                            // strict-oracle rejection along the way may have
                            // derived a sound pattern-blocking clause;
                            // assert it and re-solve, bounded. Reaches only
                            // otherwise-unknown files, so it can only add
                            // conversions (measured mechanism: swap_t's ~15
                            // rounds enumerate its pattern space to unsat).
                            let mut outcome = retry;
                            // Stage 3b (#mgr-row-peel, AUFLIA side): same
                            // demand-driven deep ROW peel as the isolated
                            // array-EUF escalation — the #8785 guard also
                            // starves the AUFLIA pipeline of inner-layer
                            // index-aliasing atoms. Assert the per-layer
                            // tautologies once and re-solve; restore the
                            // window afterwards on a residual Unknown.
                            if matches!(outcome, Ok(SolveResult::Unknown))
                                && !matches!(self.last_unknown_reason, Some(UnknownReason::Timeout))
                                && !self.solve_deadline.expired()
                            {
                                let saved_assertions = self.ctx.assertions.clone();
                                let peeled =
                                    self.add_array_row_deep_peel_clauses(MGR_ROW_PEEL_CLAUSE_CAP);
                                if peeled > 0 {
                                    self.last_unknown_reason = None;
                                    self.last_result = None;
                                    self.last_model = None;
                                    let peel_outcome = self.solve_auf_lia();
                                    // Restore the window on every outcome —
                                    // the verdict and model are already
                                    // banked inside the solve; the peel
                                    // tautologies must not leak into the
                                    // incremental assertion stack.
                                    self.ctx.assertions = saved_assertions;
                                    if !matches!(peel_outcome, Ok(SolveResult::Unknown)) {
                                        outcome = peel_outcome;
                                    }
                                } else {
                                    self.ctx.assertions = saved_assertions;
                                }
                            }
                            let mut cegar_rounds = 0usize;
                            while cegar_rounds < 24
                                && matches!(outcome, Ok(SolveResult::Unknown))
                                && !matches!(self.last_unknown_reason, Some(UnknownReason::Timeout))
                                && !self.solve_deadline.expired()
                            {
                                let Some(lits) = self.qfax_refinement_clause.take() else {
                                    break;
                                };
                                cegar_rounds += 1;
                                let mut disj: Vec<TermId> = Vec::new();
                                for (atom, val) in lits {
                                    let lit = if val {
                                        self.ctx.terms.mk_not(atom)
                                    } else {
                                        atom
                                    };
                                    disj.push(lit);
                                }
                                let clause = if disj.len() == 1 {
                                    disj[0]
                                } else {
                                    self.ctx.terms.mk_or(disj)
                                };
                                self.ctx.assertions.push(clause);
                                self.last_unknown_reason = None;
                                self.last_result = None;
                                self.last_model = None;
                                outcome = self.solve_auf_lia();
                            }
                            outcome
                        }
                        _ => main,
                    }
                }
            }
            // Nonlinear terms upgraded to QfUfnra pre-dispatch (#6086).
            LogicCategory::QfAuflra => self.solve_auf_lra(),
            // Nonlinear terms upgraded to QfNira pre-dispatch (#6086).
            LogicCategory::QfLira => self.solve_lira(),
            // Nonlinear terms upgraded to QfUfnira pre-dispatch (#6086).
            LogicCategory::QfAuflira => self.solve_auflira(),
            LogicCategory::QfFp => self.solve_fp(),
            LogicCategory::QfBvfp => self.solve_bvfp(),
            LogicCategory::QfAbvfp => self.solve_abvfp(),
            LogicCategory::QfBv => self.solve_bv(),
            LogicCategory::QfAbv => self.solve_abv(),
            LogicCategory::QfUfbv => self.solve_ufbv(),
            LogicCategory::QfAufbv => self.solve_aufbv(),
            // BV + integer arithmetic with conversion functions: conservative
            // BV-to-Int bridge for UNSAT, unknown otherwise (#9065).
            LogicCategory::QfBvLia => self.solve_bv_lia_bridge(),
            // BV + Int without conversions: BV-first with AUFLIA fallback (#5356)
            LogicCategory::QfBvLiaIndep => self.solve_bv_lia_indep(),
            // Quantified logics: route to same solver as QF_ version.
            // Nonlinear terms upgraded to Nia/Nra pre-dispatch (#6086).
            LogicCategory::Lia => {
                if features.has_bv_int_conversion {
                    let bridge_result = self.solve_bv_lia_bridge()?;
                    if bridge_result.is_unsat() {
                        return Ok(bridge_result);
                    }
                }
                self.solve_lia()
            }
            LogicCategory::Lra => self.solve_lra(),
            // Quantified nonlinear: process_quantifiers() has already
            // stripped quantifiers and added ground instances via E-matching/
            // CEGQI/Skolemization. Route to ground solvers; map_quantifier_result
            // handles incompleteness (SAT→Unknown when quantifiers unhandled).
            LogicCategory::Nia => self.solve_nia(),
            LogicCategory::Nra => self.solve_nra(),
            LogicCategory::Ufnra => self.solve_uf_nra(),
            // Ufnia/Ufnira: combined EUF+NIA solver via Nelson-Oppen (#4525).
            // Quantifier preprocessing has already stripped quantifiers at this point.
            LogicCategory::Ufnia => self.solve_uf_nia(),
            // Ufnira with Real sort: same issue as QfUfnira — solve_uf_nia()
            // lacks LRA, so Real constraints produce false SAT (#8200).
            LogicCategory::Ufnira => {
                if features.has_real {
                    self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    Ok(SolveResult::Unknown)
                } else {
                    self.solve_uf_nia()
                }
            }
            LogicCategory::Uf => self.solve_euf(),
            // Nonlinear terms upgraded to Ufnia/Ufnra/Ufnira pre-dispatch (#6086).
            LogicCategory::Uflia => {
                if features.has_bv_int_conversion {
                    let bridge_result = self.solve_bv_lia_bridge()?;
                    if bridge_result.is_unsat() {
                        return Ok(bridge_result);
                    }
                }
                if has_only_uf_lia_theories(&assertion_features) {
                    self.solve_uf_lia()
                } else {
                    self.solve_auf_lia()
                }
            }
            LogicCategory::Uflra => self.solve_uf_lra(),
            LogicCategory::Auflia => {
                if features.has_bv_int_conversion {
                    let bridge_result = self.solve_bv_lia_bridge()?;
                    if bridge_result.is_unsat() {
                        return Ok(bridge_result);
                    }
                }
                if has_native_seq_ops {
                    self.solve_seq_auflia()
                } else if has_only_uf_lia_theories(&assertion_features) {
                    self.solve_uf_lia()
                } else {
                    self.solve_auf_lia()
                }
            }
            LogicCategory::Auflra => self.solve_auf_lra(),
            // Nonlinear terms upgraded to Nira pre-dispatch (#6086).
            LogicCategory::Lira => self.solve_lira(),
            LogicCategory::Auflira => self.solve_auflira(),
            LogicCategory::Nira => {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                Ok(SolveResult::Unknown)
            }
            LogicCategory::QfDt => self.solve_dt(),
            // Combined DT + arithmetic: add DT axioms then route to arithmetic solver
            LogicCategory::DtAuflia => {
                if has_native_seq_ops {
                    self.solve_dt_seq_auflia()
                } else if !dt_uflia_routing_disabled()
                    && has_only_uf_lia_theories(&assertion_features)
                {
                    // Array-free DT+LIA: route the post-axiom residual through the
                    // UF+LIA combiner FIRST (mirrors the LogicCategory::Auflia fast
                    // path above). The array-enabled combiner stalls to Unknown on
                    // the enum/list catamorphism obligations; solve_uf_lia discharges
                    // them fast (empirically: +14 unsat on a 150-sample). On Unknown,
                    // fall back to the array-enabled path so the routing is STRICTLY
                    // ADDITIVE — it recovers the few sat instances only solve_auf_lia
                    // decides, never losing a solve. Sound: Unknown at worst
                    // (#chc25-dt-uflia).
                    let uf = self.solve_dt_uf_lia()?;
                    if matches!(uf, SolveResult::Unknown) {
                        self.solve_dt_auflia()
                    } else {
                        Ok(uf)
                    }
                } else {
                    self.solve_dt_auflia()
                }
            }
            LogicCategory::DtAuflra => self.solve_dt_auflra(),
            LogicCategory::DtAuflira => self.solve_dt_auflira(),
            // Combined DT + BV/Arrays: add DT axioms then route to BV/Array solver (#1766)
            LogicCategory::DtUfbv => self.solve_dt_ufbv(),
            LogicCategory::DtAufbv => self.solve_dt_aufbv(),
            LogicCategory::DtAx => self.solve_dt_ax(),
            // Quantified DT logics (#7150): quantifier preprocessing strips
            // quantifiers before reaching dispatch, so route to DT-combined solvers.
            LogicCategory::Ufdt | LogicCategory::Aufdt => self.solve_dt(),
            LogicCategory::Ufdtlia | LogicCategory::Aufdtlia => {
                if has_native_seq_ops {
                    self.solve_dt_seq_auflia()
                } else if !dt_uflia_routing_disabled()
                    && has_only_uf_lia_theories(&assertion_features)
                {
                    let uf = self.solve_dt_uf_lia()?;
                    if matches!(uf, SolveResult::Unknown) {
                        self.solve_dt_auflia()
                    } else {
                        Ok(uf)
                    }
                } else {
                    self.solve_dt_auflia()
                }
            }
            LogicCategory::Ufdtlra => self.solve_dt_auflra(),
            LogicCategory::Ufdtlira | LogicCategory::Aufdtlira => self.solve_dt_auflira(),
            LogicCategory::Ufdtnia | LogicCategory::Ufdtnra | LogicCategory::Ufdtnira => {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                Ok(SolveResult::Unknown)
            }
            LogicCategory::Other => {
                // DT + FP has no sound combined solver yet (#8728). Routing to
                // QF_DT dropped the FP theory entirely, producing spurious
                // `sat` on e.g. `distinct(Flt NaN, Flt x) & fp.isNaN(x)`.
                // Return Unknown+Incomplete rather than an error so callers
                // see the soundness-preserving standard SMT-LIB `unknown`.
                //
                // Likewise, recognized combined logics for which AY has the
                // component theories but not yet a sound combined decision
                // procedure (BV+LRA, Arrays+UF+BV+LIA): routing them to a
                // theory-dropping solver could fabricate a wrong UNSAT, so we
                // return the SMT-LIB-sanctioned `unknown` instead of a hard
                // `UnsupportedLogic` error — recognizing the logic (no parse-time
                // rejection) while staying sound. (#combined-bv-arith)
                let declared = self.ctx.logic().unwrap_or("");
                let recognized_unsupported_combination = matches!(
                    declared,
                    "QF_BVLRA" | "QF_AUFBVLIA" | "QF_UFBVLIA" | "QF_AUFBVLIRA"
                );
                if recognized_unsupported_combination
                    || (features.has_fpa && self.ctx.datatype_iter().next().is_some())
                {
                    self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    Ok(SolveResult::Unknown)
                } else {
                    Err(crate::executor_types::ExecutorError::UnsupportedLogic(
                        self.ctx.logic().unwrap_or("<unspecified>").to_string(),
                    ))
                }
            }
        };

        if matches!(result, Ok(SolveResult::Unknown)) {
            self.refine_unsupported_fragment_unknown_reason(features);
        }

        result
    }

    pub(in crate::executor) fn record_arithmetic_unsupported_fragment_diagnostics(&mut self) {
        self.last_statistics.extra.insert(
            "mixed_vc.arithmetic.unsupported_fragment".to_string(),
            StatValue::String("arithmetic-div-mod".to_string()),
        );
    }

    pub(in crate::executor) fn record_mixed_collection_unsupported_fragment_diagnostics(
        &mut self,
        fragment: &'static str,
    ) {
        self.last_statistics.extra.insert(
            "mixed_vc.collection.unsupported_fragment".to_string(),
            StatValue::String(fragment.to_string()),
        );
    }

    fn refine_unsupported_fragment_unknown_reason(&mut self, features: &StaticFeatures) {
        if !features.has_int_div_mod {
            return;
        }
        if !matches!(
            self.last_unknown_reason,
            None | Some(
                UnknownReason::Incomplete | UnknownReason::Unknown | UnknownReason::Unsupported
            )
        ) {
            return;
        }

        // #quantifier-determinism: attribute EXTERNALLY-CAUSED stops truthfully
        // (same rule as `finalize_unknown_diagnostics`, which deliberately never
        // overrides UnsupportedArithmetic once stamped — so the truth test must
        // happen HERE, before stamping). When the caller's interrupt flag or the
        // solve deadline fired mid-solve (e.g. mid-NIA), the generic
        // Incomplete/None reason describes a TRUNCATED solve, not an established
        // capability gap: stamping UnsupportedArithmetic made callers
        // misclassify a load-dependent truncation as a permanent unsupported
        // fragment (the deductive-checks bump-triage pattern: a ported nonlinear case
        // looked like a pin regression). Report Interrupted/Timeout instead.
        // VERDICT-NEUTRAL: the result stays Unknown either way.
        if let Some(reason) = self.external_stop_reason() {
            self.last_unknown_reason = Some(reason);
            let detail = self.default_unknown_detail(reason);
            self.record_unknown_diagnostic(reason, detail);
            return;
        }

        // #ssl-residue D2: stamp UnsupportedArithmetic only when unsupported
        // arithmetic actually SURVIVES preprocessing — a symbolic-divisor
        // `mod`/`div` (the constant-divisor pass fully eliminates constant
        // divisors via the guarded Euclidean axioms) or a surviving `rem`.
        // A formula whose every `mod`/`div` has a constant divisor was fully
        // and correctly eliminated; its Unknown is ordinary search
        // incompleteness, and relabeling it as a capability gap sent triage
        // down a wrong path (the lia_143 "negative-polarity mod elimination"
        // false lead). VERDICT-NEUTRAL: the result stays Unknown either way.
        if !crate::executor::mod_div_elim::contains_symbolic_int_mod_div(
            &self.ctx.terms,
            &self.ctx.assertions,
        ) && !crate::executor::mod_div_elim::contains_int_rem(
            &self.ctx.terms,
            &self.ctx.assertions,
        ) {
            return;
        }

        self.record_arithmetic_unsupported_fragment_diagnostics();
        self.last_unknown_reason = Some(UnknownReason::UnsupportedArithmetic);
    }

    /// Rewrite each assertion that is a Bool-valued `(ite c t e)` — or a
    /// top-level `(and ...)` conjunct that is one — into the logically-identical
    /// `(and (=> c t) (=> (not c) e))`. See the call site in
    /// `check_sat_internal` (#A1-arr-lia561). The rewrite is semantically exact;
    /// it only changes the Boolean structure handed to the solver, never the
    /// formula's models.
    fn rewrite_assertion_bool_ites(&mut self) {
        let asserts = self.ctx.assertions.clone();
        let mut changed = false;
        let new_asserts: Vec<TermId> = asserts
            .iter()
            .map(|&a| match self.ctx.terms.get(a).clone() {
                ay_core::term::TermData::Ite(c, t, e) => {
                    changed = true;
                    self.bool_ite_to_and_implies(c, t, e)
                }
                ay_core::term::TermData::App(sym, args) if sym.name() == "and" => {
                    let mut conj_changed = false;
                    let new_args: Vec<TermId> = args
                        .iter()
                        .map(|&x| {
                            if let ay_core::term::TermData::Ite(c, t, e) =
                                self.ctx.terms.get(x).clone()
                            {
                                conj_changed = true;
                                self.bool_ite_to_and_implies(c, t, e)
                            } else {
                                x
                            }
                        })
                        .collect();
                    if conj_changed {
                        changed = true;
                        self.ctx.terms.mk_and(new_args)
                    } else {
                        a
                    }
                }
                _ => a,
            })
            .collect();
        if changed {
            self.record_named_assert_rewrites(&asserts, &new_asserts);
            self.ctx.assertions = new_asserts;
        }
    }

    /// Record positional rewrite provenance for the named-core machinery
    /// (#uc-named-provenance). ONLY per-assertion semantically-EXACT passes
    /// may call this (see the `named_assert_rewrites` field docs): the label
    /// of a named assert rides its rewritten form, and the printed core
    /// denotes the ORIGINAL formulas that external validators re-check —
    /// equivalence is what makes that sound. Chained through earlier
    /// rewrites of the same run so values stay parse-time roots. Gated on
    /// produce-unsat-cores: plain solving pays nothing.
    fn record_named_assert_rewrites(&mut self, before: &[TermId], after: &[TermId]) {
        if !self.produce_unsat_cores_enabled() {
            return;
        }
        debug_assert_eq!(
            before.len(),
            after.len(),
            "BUG: positional rewrite provenance requires equal-length assertion vectors"
        );
        for (&old, &new) in before.iter().zip(after.iter()) {
            if old == new {
                continue;
            }
            let root = self.named_assert_rewrites.get(&old).copied().unwrap_or(old);
            self.named_assert_rewrites.insert(new, root);
        }
    }

    /// Build `(and (=> c t) (=> (not c) e))` for a Bool-valued ITE.
    fn bool_ite_to_and_implies(&mut self, c: TermId, t: TermId, e: TermId) -> TermId {
        let not_c = self.ctx.terms.mk_not(c);
        let imp_then = self.ctx.terms.mk_implies(c, t);
        let imp_else = self.ctx.terms.mk_implies(not_c, e);
        self.ctx.terms.mk_and(vec![imp_then, imp_else])
    }

    /// Push `select`/`store` through an ARRAY-VALUED `ite`:
    ///   `(select (ite c A B) i)`  -> `(ite c (select A i) (select B i))`
    ///   `(store  (ite c A B) i v)` -> `(ite c (store A i v) (store B i v))`
    ///
    /// SOUND (semantics-preserving): the `ite` is on the ARRAY operand, so the
    /// read/write commutes into both branches and no verdict can change.
    /// Companion to `rewrite_assertion_bool_ites` for the array-VALUED ITE case
    /// (#alia-select-over-ite wrong-SAT, arr_lia561 family): the outer-`select`
    /// form lets the eager array-axiom scan treat the `select`/`store` terms of
    /// BOTH ite branches as simultaneously active and relate them across the
    /// branch split, admitting a model that violates an asserted array equality at
    /// the read index (and the dual spurious UNSAT). The pushed-in form keeps the
    /// branches mutually exclusive in the SAT structure. Full bottom-up DAG
    /// rewrite — the pattern can be nested anywhere in an assertion. Scoped to
    /// array problems.
    fn rewrite_select_over_array_ite(&mut self) {
        let asserts = self.ctx.assertions.clone();
        let mut cache: HashMap<TermId, TermId> = HashMap::default();
        let new_asserts: Vec<TermId> = asserts
            .iter()
            .map(|&a| self.push_select_store_through_ite(a, &mut cache))
            .collect();
        // Semantics-preserving per assertion (see the doc above) — eligible
        // for named-core rewrite provenance (#uc-named-provenance).
        self.record_named_assert_rewrites(&asserts, &new_asserts);
        self.ctx.assertions = new_asserts;
    }

    /// Helper for `push_select_store_through_ite`: rewrite a 2-arg `=`/`distinct`
    /// whose one operand is an ARRAY-sorted `ite` into a branch-split `and` of
    /// per-branch (dis)equalities. Returns `None` when neither operand is an
    /// array-sorted ite (the caller then rebuilds normally).
    fn push_eqdistinct_through_array_ite(
        &mut self,
        is_distinct: bool,
        l: TermId,
        r: TermId,
        cache: &mut HashMap<TermId, TermId>,
    ) -> Option<TermId> {
        use ay_core::term::TermData;
        let is_array_ite = |s: &Self, t: TermId| {
            matches!(s.ctx.terms.get(t), TermData::Ite(..))
                && matches!(s.ctx.terms.sort(t), ay_core::Sort::Array(..))
        };
        let (c, a, b, other) = if is_array_ite(self, l) {
            match self.ctx.terms.get(l).clone() {
                TermData::Ite(c, a, b) => (c, a, b, r),
                _ => return None,
            }
        } else if is_array_ite(self, r) {
            match self.ctx.terms.get(r).clone() {
                TermData::Ite(c, a, b) => (c, a, b, l),
                _ => return None,
            }
        } else {
            return None;
        };
        let eq_a = self.ctx.terms.mk_eq(a, other);
        let atom_a = if is_distinct {
            self.ctx.terms.mk_not(eq_a)
        } else {
            eq_a
        };
        let eq_b = self.ctx.terms.mk_eq(b, other);
        let atom_b = if is_distinct {
            self.ctx.terms.mk_not(eq_b)
        } else {
            eq_b
        };
        // Recurse so a nested array-ite in `other` (both sides ite) also splits.
        let atom_a = self.push_select_store_through_ite(atom_a, cache);
        let atom_b = self.push_select_store_through_ite(atom_b, cache);
        let nc = self.ctx.terms.mk_not(c);
        let imp_t = self.ctx.terms.mk_implies(c, atom_a);
        let imp_e = self.ctx.terms.mk_implies(nc, atom_b);
        Some(self.ctx.terms.mk_and(vec![imp_t, imp_e]))
    }

    fn push_select_store_through_ite(
        &mut self,
        term: TermId,
        cache: &mut HashMap<TermId, TermId>,
    ) -> TermId {
        use ay_core::term::TermData;
        if let Some(&cached) = cache.get(&term) {
            return cached;
        }
        let result = match self.ctx.terms.get(term).clone() {
            TermData::App(sym, args) if !args.is_empty() => {
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&x| self.push_select_store_through_ite(x, cache))
                    .collect();
                let pushed = match sym.name() {
                    "select" if new_args.len() == 2 => {
                        if let TermData::Ite(c, a, b) = self.ctx.terms.get(new_args[0]).clone() {
                            let sa = self.ctx.terms.mk_select(a, new_args[1]);
                            let sb = self.ctx.terms.mk_select(b, new_args[1]);
                            let sa = self.push_select_store_through_ite(sa, cache);
                            let sb = self.push_select_store_through_ite(sb, cache);
                            Some(self.ctx.terms.mk_ite(c, sa, sb))
                        } else {
                            None
                        }
                    }
                    "store" if new_args.len() == 3 => {
                        if let TermData::Ite(c, a, b) = self.ctx.terms.get(new_args[0]).clone() {
                            let sa = self.ctx.terms.mk_store(a, new_args[1], new_args[2]);
                            let sb = self.ctx.terms.mk_store(b, new_args[1], new_args[2]);
                            let sa = self.push_select_store_through_ite(sa, cache);
                            let sb = self.push_select_store_through_ite(sb, cache);
                            Some(self.ctx.terms.mk_ite(c, sa, sb))
                        } else {
                            None
                        }
                    }
                    // `(= (ite c A B) Z)` / `(distinct ..)` over an ARRAY-sorted ite
                    // operand -> `(and (=> c (= A Z)) (=> ¬c (= B Z)))`. Sound
                    // (`(ite c A B) = Z` iff `ite c (A=Z) (B=Z)`), and it keeps the
                    // two array branches mutually exclusive so the eager array-axiom
                    // scan never relates them across the split (#alia-select-over-ite,
                    // store-over-ite-then-equate variant).
                    "=" | "distinct" if new_args.len() == 2 => self
                        .push_eqdistinct_through_array_ite(
                            sym.name() == "distinct",
                            new_args[0],
                            new_args[1],
                            cache,
                        ),
                    _ => None,
                };
                match pushed {
                    Some(t) => t,
                    None => {
                        if new_args.iter().zip(args.iter()).any(|(a, b)| a != b) {
                            let sort = self.ctx.terms.sort(term).clone();
                            self.ctx.terms.mk_app(sym, new_args, sort)
                        } else {
                            term
                        }
                    }
                }
            }
            TermData::Not(inner) => {
                let ni = self.push_select_store_through_ite(inner, cache);
                if ni != inner {
                    self.ctx.terms.mk_not(ni)
                } else {
                    term
                }
            }
            TermData::Ite(c, t, e) => {
                let nc = self.push_select_store_through_ite(c, cache);
                let nt = self.push_select_store_through_ite(t, cache);
                let ne = self.push_select_store_through_ite(e, cache);
                if nc != c || nt != t || ne != e {
                    self.ctx.terms.mk_ite(nc, nt, ne)
                } else {
                    term
                }
            }
            _ => term,
        };
        cache.insert(term, result);
        result
    }
}

#[cfg(test)]
mod quantifier_determinism_tests {
    //! Unit tests for the #quantifier-determinism mechanisms (Fix A of
    //! workflow w6ur8ni5u): the quantified-solve wall-clock backstop and the
    //! truthful attribution of externally-caused Unknown stops.

    use std::sync::atomic::AtomicBool;
    use std::sync::Arc;
    use std::time::{Duration, Instant};

    use super::super::Executor;
    use crate::executor_types::{SolveResult, UnknownReason};

    #[test]
    fn quantifier_deadline_backstop_extends_by_scaled_remaining() {
        let mut exec = Executor::new();
        let nominal = Instant::now() + Duration::from_secs(10);
        exec.set_deadline(Some(nominal));
        exec.install_quantifier_deadline_backstop();
        let extended = exec
            .solve_deadline
            .get()
            .expect("deadline must stay installed");
        let extra = extended.duration_since(nominal);
        // remaining ~10s => extra ~3x remaining = ~30s (factor 4 total).
        assert!(
            extra >= Duration::from_secs(29),
            "extra too small: {extra:?}"
        );
        assert!(
            extra <= Duration::from_secs(30),
            "extra too large: {extra:?}"
        );
        // One-shot per call: a second install must not compound.
        let after_first = exec.solve_deadline.get();
        exec.install_quantifier_deadline_backstop();
        assert_eq!(exec.solve_deadline.get(), after_first);
    }

    #[test]
    fn quantifier_deadline_backstop_caps_extension() {
        let mut exec = Executor::new();
        let nominal = Instant::now() + Duration::from_secs(300);
        exec.set_deadline(Some(nominal));
        exec.install_quantifier_deadline_backstop();
        let extra = exec
            .solve_deadline
            .get()
            .expect("deadline must stay installed")
            .duration_since(nominal);
        assert!(
            extra <= Duration::from_secs(180),
            "extension must be capped: {extra:?}"
        );
        assert!(
            extra >= Duration::from_secs(179),
            "cap not applied: {extra:?}"
        );
    }

    #[test]
    fn quantifier_deadline_backstop_leaves_expired_or_absent_deadline() {
        // Already expired: immediate-stop semantics (set_timeout(ZERO)) kept.
        let mut exec = Executor::new();
        let past = Instant::now()
            .checked_sub(Duration::from_millis(50))
            .expect("50 milliseconds must fit before the current test instant");
        exec.set_deadline(Some(past));
        exec.install_quantifier_deadline_backstop();
        assert_eq!(exec.solve_deadline.get(), Some(past));
        // Absent deadline stays absent.
        let mut exec2 = Executor::new();
        exec2.set_deadline(None);
        exec2.install_quantifier_deadline_backstop();
        assert_eq!(exec2.solve_deadline.get(), None);
    }

    #[test]
    fn stop_closures_observe_backstop_extension_live() {
        // #quantifier-determinism defect: `make_should_stop` used to SNAPSHOT
        // `solve_deadline` by value at construction, so a closure built before
        // `install_quantifier_deadline_backstop` kept polling the stale nominal
        // deadline and stopped the solve at the pre-extension wall — silently
        // defeating the backstop (observed in the deductive-checks bump triage: solve
        // stopped at exactly the nominal 300s despite `backstop installed:
        // remaining=110s extra=180s`). Stop closures must read the LIVE
        // deadline.
        let mut exec = Executor::new();
        let nominal = Instant::now() + Duration::from_millis(100);
        exec.set_deadline(Some(nominal));
        // Built BEFORE the backstop install, polled after it.
        let stop = exec.make_should_stop();
        exec.install_quantifier_deadline_backstop(); // 4x => backstop ~= +400ms
        std::thread::sleep(Duration::from_millis(180)); // past nominal, well before backstop
        assert!(
            !stop(),
            "stop closure built before the backstop install must observe the \
             extended (live) deadline, not a stale nominal snapshot"
        );
        std::thread::sleep(Duration::from_millis(280)); // past the ~400ms backstop
        assert!(stop(), "the backstop wall must still be enforced");
    }

    #[test]
    fn stop_closures_observe_tightened_subsolve_deadline_live() {
        // Companion guard for the alternation-validation TIGHT sub-deadlines
        // (result_mapping.rs): tightening via set_deadline must also be visible
        // to live-reading closures, and restoring must bring the outer deadline
        // back. This pins the non-compounding design: the tight window stays
        // tight even after the backstop extension.
        let mut exec = Executor::new();
        let outer = Instant::now() + Duration::from_secs(60);
        exec.set_deadline(Some(outer));
        exec.install_quantifier_deadline_backstop();
        let stop = exec.make_should_stop();
        // Tight sub-deadline already expired: a live-reading closure must stop
        // immediately (the 300ms alternation windows rely on this).
        let saved = exec.solve_deadline.get();
        let past = Instant::now()
            .checked_sub(Duration::from_millis(5))
            .expect("5 milliseconds must fit before the current test instant");
        exec.set_deadline(Some(past));
        assert!(
            stop(),
            "closures must observe a tightened (sub-solve) deadline live"
        );
        exec.set_deadline(saved);
        assert!(!stop(), "restoring the outer deadline must lift the stop");
    }

    #[test]
    fn finalize_attributes_external_interrupt_over_quantifier_reason() {
        // An application watchdog that flips the interrupt mid-quantifier-loop
        // must surface as Interrupted, not as the truncated loop's
        // QuantifierUnhandled classification (which callers read as a
        // definitive incompleteness and skip their timeout retry ladders).
        let mut exec = Executor::new();
        exec.last_result = Some(SolveResult::Unknown);
        exec.last_unknown_reason = Some(UnknownReason::QuantifierUnhandled);
        exec.solve_interrupt = Some(Arc::new(AtomicBool::new(true)));
        exec.finalize_unknown_diagnostics();
        assert_eq!(exec.last_unknown_reason, Some(UnknownReason::Interrupted));
    }

    #[test]
    fn finalize_attributes_expired_deadline_over_round_limit() {
        let mut exec = Executor::new();
        exec.last_result = Some(SolveResult::Unknown);
        exec.last_unknown_reason = Some(UnknownReason::QuantifierRoundLimit);
        let past = Instant::now()
            .checked_sub(Duration::from_millis(10))
            .expect("10 milliseconds must fit before the current test instant");
        exec.set_deadline(Some(past));
        exec.finalize_unknown_diagnostics();
        assert_eq!(exec.last_unknown_reason, Some(UnknownReason::Timeout));
    }

    #[test]
    fn finalize_keeps_specific_nontruncation_reason() {
        // MemoryLimit is not a truncation artifact; an external stop must not
        // mask it.
        let mut exec = Executor::new();
        exec.last_result = Some(SolveResult::Unknown);
        exec.last_unknown_reason = Some(UnknownReason::MemoryLimit);
        exec.solve_interrupt = Some(Arc::new(AtomicBool::new(true)));
        exec.finalize_unknown_diagnostics();
        assert_eq!(exec.last_unknown_reason, Some(UnknownReason::MemoryLimit));
    }

    #[test]
    fn finalize_keeps_quantifier_reason_without_external_stop() {
        // A genuinely converged quantifier classification stays untouched when
        // neither the interrupt nor the deadline fired.
        let mut exec = Executor::new();
        exec.last_result = Some(SolveResult::Unknown);
        exec.last_unknown_reason = Some(UnknownReason::QuantifierUnhandled);
        exec.set_deadline(Some(Instant::now() + Duration::from_secs(60)));
        exec.finalize_unknown_diagnostics();
        assert_eq!(
            exec.last_unknown_reason,
            Some(UnknownReason::QuantifierUnhandled)
        );
    }

    /// Load a small quantified+ground mixed assertion set (no check-sat).
    fn load_quantified_mix(exec: &mut Executor) {
        let commands = ay_frontend::parse(
            "(set-logic UFLIA)\
             (declare-fun f (Int) Int)\
             (declare-const a Int)\
             (assert (forall ((x Int)) (>= (f x) 0)))\
             (assert (> a 0))",
        )
        .expect("test input must parse");
        exec.execute_all(&commands)
            .expect("setup commands must run");
    }

    #[test]
    fn ground_entry_backstop_extends_at_install_for_quantified_mix() {
        // #ground-determinism (task #26 item 2): a MIXED ground+quantified
        // solve must get the far-out wall backstop AT SOLVE ENTRY, so a
        // heavy pre-quantifier ground phase (BV<->LIA bridge / AUFLIA
        // dispatch) cannot burn the nominal wall before the quantified-entry
        // install runs (which early-returns on an expired deadline).
        let mut exec = Executor::new();
        load_quantified_mix(&mut exec);
        exec.set_timeout(Some(Duration::from_secs(10)));
        let prev = exec.install_timeout_deadline_for_call();
        assert_eq!(prev, None, "no deadline was installed before the call");
        let deadline = exec
            .solve_deadline
            .get()
            .expect("a deadline must be installed");
        let total = deadline.duration_since(Instant::now());
        // nominal 10s + extra min(3 x 10s, 180s) => ~40s.
        assert!(
            total >= Duration::from_secs(35),
            "entry install must include the backstop extension: {total:?}"
        );
        assert!(
            exec.quantifier_deadline_backstop_installed,
            "entry install must consume the one-shot"
        );
        // The later quantified-entry install must be a no-op (one-shot).
        let after_entry = exec.solve_deadline.get();
        exec.install_quantifier_deadline_backstop();
        assert_eq!(exec.solve_deadline.get(), after_entry);
        // Per-call restore unwinds everything.
        exec.restore_timeout_deadline_after_call(prev);
        assert_eq!(exec.solve_deadline.get(), None);
    }

    #[test]
    fn ground_entry_backstop_skips_ground_only_solves() {
        // Ground-only solves keep their exact nominal deadline: callers'
        // tight retry ladders on ground/BV obligations must stay prompt.
        let mut exec = Executor::new();
        let commands = ay_frontend::parse("(set-logic QF_UF)(declare-const p Bool)(assert p)")
            .expect("test input must parse");
        exec.execute_all(&commands)
            .expect("setup commands must run");
        exec.set_timeout(Some(Duration::from_secs(10)));
        let _prev = exec.install_timeout_deadline_for_call();
        let deadline = exec
            .solve_deadline
            .get()
            .expect("a deadline must be installed");
        let total = deadline.duration_since(Instant::now());
        assert!(
            total <= Duration::from_secs(10),
            "ground-only solves must keep the exact nominal wall: {total:?}"
        );
        assert!(
            !exec.quantifier_deadline_backstop_installed,
            "no entry install may happen for ground-only solves"
        );
    }

    #[test]
    fn ground_entry_backstop_disabled_with_ground_budget() {
        // With the deterministic ground budget disabled (`:rlimit 0` /
        // set_ground_budget_enabled(false)) the pre-change semantics return:
        // nominal wall at entry, backstop only at the quantified entry.
        let mut exec = Executor::new();
        load_quantified_mix(&mut exec);
        exec.set_ground_budget_enabled(false);
        exec.set_timeout(Some(Duration::from_secs(10)));
        let _prev = exec.install_timeout_deadline_for_call();
        let deadline = exec
            .solve_deadline
            .get()
            .expect("a deadline must be installed");
        let total = deadline.duration_since(Instant::now());
        assert!(
            total <= Duration::from_secs(10),
            "no entry extension when the ground budget is disabled: {total:?}"
        );
        assert!(!exec.quantifier_deadline_backstop_installed);
    }

    #[test]
    fn ground_entry_backstop_preserves_zero_timeout_immediate_stop() {
        // set_timeout(ZERO)-style hard aborts keep immediate-stop semantics:
        // the entry install must not resurrect an already-expired deadline.
        let mut exec = Executor::new();
        load_quantified_mix(&mut exec);
        exec.set_timeout(Some(Duration::ZERO));
        let _prev = exec.install_timeout_deadline_for_call();
        let stop = exec.make_should_stop();
        assert!(
            stop(),
            "a zero timeout must stop immediately even for quantified solves"
        );
    }

    fn div_mod_features() -> crate::features::StaticFeatures {
        crate::features::StaticFeatures {
            has_int_div_mod: true,
            ..Default::default()
        }
    }

    #[test]
    fn refine_attributes_mid_nia_interrupt_as_interrupted() {
        // Defect: an EXTERNAL interrupt (caller watchdog flag) landing mid-NIA
        // used to surface as Unknown(UnsupportedArithmetic) via the div/mod
        // fragment refinement — callers then misclassified a truncation as a
        // permanent capability gap (a ported deductive-checks nonlinear case looked
        // like a pin regression). When the external stop actually fired, the
        // attribution must be Interrupted.
        let mut exec = Executor::new();
        exec.last_unknown_reason = Some(UnknownReason::Incomplete);
        exec.solve_interrupt = Some(Arc::new(AtomicBool::new(true)));
        exec.refine_unsupported_fragment_unknown_reason(&div_mod_features());
        assert_eq!(exec.last_unknown_reason, Some(UnknownReason::Interrupted));
    }

    #[test]
    fn refine_attributes_mid_nia_expired_deadline_as_timeout() {
        let mut exec = Executor::new();
        exec.last_unknown_reason = None;
        let past = Instant::now()
            .checked_sub(Duration::from_millis(10))
            .expect("10 milliseconds must fit before the current test instant");
        exec.set_deadline(Some(past));
        exec.refine_unsupported_fragment_unknown_reason(&div_mod_features());
        assert_eq!(exec.last_unknown_reason, Some(UnknownReason::Timeout));
    }

    #[test]
    fn refine_keeps_unsupported_arithmetic_without_external_stop() {
        // A solve that converged to its incompleteness verdict (no interrupt,
        // deadline not expired) keeps the genuine capability-gap attribution —
        // but ONLY when unsupported arithmetic actually survives preprocessing
        // (#ssl-residue D2): here a symbolic-divisor `mod`, which the
        // constant-divisor elimination pass cannot rewrite.
        let mut exec = Executor::new();
        let commands = ay_frontend::parse(
            "(set-logic QF_NIA)(declare-const x Int)(declare-const y Int)\
             (assert (= (mod x y) 0))",
        )
        .expect("test input must parse");
        exec.execute_all(&commands)
            .expect("setup commands must run");
        exec.last_unknown_reason = Some(UnknownReason::Incomplete);
        exec.set_deadline(Some(Instant::now() + Duration::from_secs(60)));
        exec.refine_unsupported_fragment_unknown_reason(&div_mod_features());
        assert_eq!(
            exec.last_unknown_reason,
            Some(UnknownReason::UnsupportedArithmetic)
        );
    }

    #[test]
    fn refine_keeps_incomplete_for_fully_eliminated_constant_mod() {
        // #ssl-residue D2: a formula whose every `mod` has a CONSTANT divisor
        // is fully eliminated by preprocessing (guarded Euclidean axioms), so
        // an Unknown from such a solve is ordinary search incompleteness —
        // stamping UnsupportedArithmetic here was a diagnostic lie (the
        // lia_143 false "negative-polarity mod elimination" lead).
        let mut exec = Executor::new();
        let commands =
            ay_frontend::parse("(set-logic QF_LIA)(declare-const x Int)(assert (= (mod x 4) 0))")
                .expect("test input must parse");
        exec.execute_all(&commands)
            .expect("setup commands must run");
        exec.last_unknown_reason = Some(UnknownReason::Incomplete);
        exec.set_deadline(Some(Instant::now() + Duration::from_secs(60)));
        exec.refine_unsupported_fragment_unknown_reason(&div_mod_features());
        assert_eq!(exec.last_unknown_reason, Some(UnknownReason::Incomplete));
    }
}

#[cfg(test)]
mod conflict_semantic_memo_tests {
    //! Unit tests for the per-check-sat conflict-verification verdict memo
    //! (#4535 memoized verifier) wired through the Executor field: both
    //! verdict polarities are cached keyed by the sorted literal set, and
    //! cached verdicts agree with direct verification.

    use super::super::Executor;
    use crate::verification::{verify_conflict_semantic_memoized, VerificationError};
    use ay_core::{Sort, TheoryLit};
    use num_bigint::BigInt;

    /// A genuinely-UNSAT conflict verifies Ok, is memoized as Ok, and an
    /// identical conflict (in any literal order) hits the memo with Ok.
    #[test]
    fn memoizes_ok_verdict_and_hits_on_reordered_identical_conflict() {
        let mut exec = Executor::new();
        let x = exec.ctx.terms.mk_var("x", Sort::Int);
        let zero = exec.ctx.terms.mk_int(BigInt::from(0));
        let x_eq_0 = exec.ctx.terms.mk_eq(x, zero);
        let x_le_0 = exec.ctx.terms.mk_le(x, zero);
        let zero_le_x = exec.ctx.terms.mk_le(zero, x);
        // {x != 0, x <= 0, 0 <= x} — jointly UNSAT (the #6853 shape).
        let conflict = vec![
            TheoryLit::new(x_eq_0, false),
            TheoryLit::new(x_le_0, true),
            TheoryLit::new(zero_le_x, true),
        ];
        assert!(verify_conflict_semantic_memoized(
            &mut exec.conflict_semantic_verify_memo,
            &conflict,
            &exec.ctx.terms,
            &exec.active_support_axioms,
        )
        .is_ok());
        assert_eq!(exec.conflict_semantic_verify_memo.len(), 1);
        // Reordered identical set: memo hit, same verdict, no new entry.
        let reordered = vec![conflict[2], conflict[0], conflict[1]];
        assert!(verify_conflict_semantic_memoized(
            &mut exec.conflict_semantic_verify_memo,
            &reordered,
            &exec.ctx.terms,
            &exec.active_support_axioms,
        )
        .is_ok());
        assert_eq!(exec.conflict_semantic_verify_memo.len(), 1);
    }

    /// A spurious (satisfiable) conflict fails verification, is memoized as
    /// Err, and the memoized re-check STAYS Err (fail-closed is preserved
    /// across the cache — a cached failure can never admit a clause).
    #[test]
    fn memoizes_err_verdict_and_stays_fail_closed() {
        let mut exec = Executor::new();
        let x = exec.ctx.terms.mk_var("x", Sort::Int);
        let zero = exec.ctx.terms.mk_int(BigInt::from(0));
        let ten = exec.ctx.terms.mk_int(BigInt::from(10));
        let x_ge_0 = exec.ctx.terms.mk_ge(x, zero);
        let x_le_10 = exec.ctx.terms.mk_le(x, ten);
        // {x >= 0, x <= 10} — satisfiable, so verification must reject.
        let conflict = vec![TheoryLit::new(x_ge_0, true), TheoryLit::new(x_le_10, true)];
        assert!(matches!(
            verify_conflict_semantic_memoized(
                &mut exec.conflict_semantic_verify_memo,
                &conflict,
                &exec.ctx.terms,
                &exec.active_support_axioms,
            ),
            Err(VerificationError::ConflictIsSat)
        ));
        assert_eq!(exec.conflict_semantic_verify_memo.len(), 1);
        // Memo hit: still an error (Internal carries the memo attribution).
        assert!(matches!(
            verify_conflict_semantic_memoized(
                &mut exec.conflict_semantic_verify_memo,
                &conflict,
                &exec.ctx.terms,
                &exec.active_support_axioms,
            ),
            Err(VerificationError::Internal(_))
        ));
        assert_eq!(exec.conflict_semantic_verify_memo.len(), 1);
    }
}
