// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! M1-PIVOT Part-A: per-solve LIA branch-count instrumentation.
//!
//! Falsifiable-fork diagnostic counters for the LIA search loop. These answer
//! the branch-COUNT vs branch-COST fork: is the rusthorn/engine wall an
//! unbounded integer branch-and-bound explosion (in-LIA cut-strength fixable),
//! a re-solve-cost problem (incrementality), or a generator-fed unbounded term
//! frontier (DT/quantifier lane)?
//!
//! ## Release-byte-identical / zero verdict dependence
//!
//! Every counter is incremented ONLY when `--lia-instrument` is passed in the
//! environment; the state read is a single cached relaxed atomic-u8 load. The
//! verdict path NEVER reads any counter — they are write-only telemetry. When
//! the env var is unset each `bump` returns after one relaxed load with no
//! counter mutation and no I/O, so the solver's control flow (and therefore its
//! verdict + reason set) is byte-for-byte the behaviour of the uninstrumented
//! build. Toggling the env var can only change what is PRINTED, never what is
//! DECIDED.
//!
//! ## Usage
//!
//! `--lia-instrument` enables counting. A background reporter thread dumps
//! the counter snapshot to stderr every `AY_LIA_INSTRUMENT_SECS` seconds
//! (default 3) so the counters are observable even when the solve diverges or
//! is killed by an external timeout without ever returning from `check()`.

use std::sync::atomic::{AtomicBool, AtomicU64, AtomicU8, Ordering::Relaxed};

macro_rules! define_counters {
    ($($name:ident => $label:literal),* $(,)?) => {
        $(pub(crate) static $name: AtomicU64 = AtomicU64::new(0);)*

        /// Ordered (label, value) view of every counter for reporting.
        pub(crate) fn snapshot() -> Vec<(&'static str, u64)> {
            vec![$(($label, $name.load(Relaxed))),*]
        }

        /// Reset all counters to zero (test / per-solve boundary helper).
        #[allow(dead_code)]
        pub(crate) fn reset() {
            $($name.store(0, Relaxed);)*
        }
    };
}

define_counters! {
    // How many times the full LIA check ran (≈ distinct theory-check rounds /
    // candidate models fed to the integer theory).
    LIA_CHECK_CALLS         => "lia_check_calls",
    // Inc0 (eager-theory-prop design §Inc0-0a): caller-class partition of
    // LIA_CHECK_CALLS. The headline counter is bumped by EVERY check_inner
    // entry — including conflict-probe solvers (~5.8 checks/probe, the
    // AY_PROBE_STATS-documented dominant wisas cost) and verify-only solvers —
    // so the 58k spin-cell headline is unattributed without this split.
    // TOP = neither probe nor verify (the top-level solve path).
    LIA_CHECK_TOP_CALLS     => "lia_check_top_calls",
    LIA_CHECK_PROBE_CALLS   => "lia_check_probe_calls",
    LIA_CHECK_VERIFY_CALLS  => "lia_check_verify_calls",
    // Inc0: check_during_propagate_inner entries (the eager arm's BCP-time
    // weak checks — a separate entry point that never reaches check_inner).
    LIA_CHECK_BCP_CALLS     => "lia_check_bcp_calls",
    // Inc0 (0c): Nelson-Oppen combiner check() invocations and fixpoint-loop
    // iterations (bumped from ay-dpll's combiner_check — distinguishes
    // "few combiner checks, many fixpoint iterations" from round-structured
    // spin).
    NO_CHECKS               => "no_checks",
    NO_FIXPOINT_ITERS       => "no_fixpoint_iters",
    // Inc0 (0c): lazy split-loop rounds started (bumped from the lazy macro).
    SPLIT_ROUNDS            => "split_rounds",
    // Inc0 (0d): theory propagations computed by the round's combiner and
    // discarded at round end (the G1 discard — harvestable material for Inc1).
    ROUND_PROPS_DISCARDED   => "round_props_discarded",
    ROUND_PENDING_DISCARDED => "round_pending_discarded",
    // extract_model() calls from the LIA branch/patch hot path — THE per-round
    // model-rebuild metric the pivot tracks (memory: 140k+/28s divergence).
    EXTRACT_MODEL_CALLS     => "extract_model_calls",
    // check_integer_constraints() returned Some (a fractional integer var was
    // selected — a branch candidate exists).
    INT_CONSTRAINT_SELECT   => "int_constraint_selections",
    // NeedSplit returned from the Sat-path branch-and-bound fallback (:1779).
    SPLITS_ISSUED_BNB       => "splits_issued_bnb",
    // NeedSplit returned from the Unknown-recovery midpoint path (:1520).
    SPLITS_ISSUED_UNKNOWN   => "splits_issued_unknown",
    // NeedSplit returned from the NeedModelEquality integrality guards.
    SPLITS_ISSUED_MODELEQ   => "splits_issued_modeleq",
    // NeedSplit forwarded straight from LRA (:1530).
    SPLITS_FORWARDED_LRA    => "splits_forwarded_lra",
    // Gomory cut generation rounds (calls to timed_generate_gomory_cuts).
    GOMORY_GEN_CALLS        => "gomory_gen_calls",
    // Total Gomory cuts produced across all rounds.
    GOMORY_GENERATED        => "gomory_generated",
    // Gomory cuts actually inserted into the tableau (accepted).
    GOMORY_ACCEPTED         => "gomory_accepted",
    // HNF cut attempts (calls to timed_try_hnf_cuts).
    HNF_ATTEMPTS            => "hnf_attempts",
    // HNF attempts that produced a cut (returned true).
    HNF_ROUNDS_FIRED        => "hnf_rounds_fired",
    // Iterations of the pre-loop iterative Diophantine tightening loop.
    DIOPH_TIGHTEN_ROUNDS    => "dioph_tighten_rounds",
    // Finite-domain CSP search entered (shared_equalities empty).
    FINITE_DOMAIN_TRIGGERS  => "finite_domain_triggers",
    // Finite-domain CSP search SKIPPED because shared equalities were present
    // (the rusthorn UFLIA regime — the flagged gate at check.rs:1164).
    FINITE_DOMAIN_SKIPS     => "finite_domain_skips",
    // try_patching() calls (each does an extract_model).
    PATCHING_CALLS          => "patching_calls",
    // Cube-test attempts.
    CUBE_TESTS              => "cube_tests",
    // INTERFACE-DIET M0/C5: Farkas shared-equality reason-minimization probe.
    // ATTEMPTS = conflict-augment reached with a non-empty reachable closure;
    // PROVED = probe returned a proven-sufficient subset (Some); SUBSET_SUM =
    // sum of |proven subset| (avg proven core size); CLOSURE_SUM = sum of the
    // full reachable-closure size (the fallback size the probe shrinks from).
    // "success rate" = PROVED/ATTEMPTS; when PROVED is high yet conflicts stay
    // fat, minimization is NOT the wall (the campaign's key premise).
    FARKAS_PROBE_ATTEMPTS   => "farkas_probe_attempts",
    FARKAS_PROBE_PROVED     => "farkas_probe_proved",
    FARKAS_PROBE_SUBSET_SUM => "farkas_probe_subset_sum",
    FARKAS_PROBE_CLOSURE_SUM => "farkas_probe_closure_sum",
    // #verify-memo (eager-theory-prop design §5.6 follow-up): caller-site
    // partition of the verify lane. LIA_CHECK_VERIFY_CALLS counts CHECKS
    // inside verification combiners (set_verify_only), so it conflates the
    // extension's sampled propagation verification with conflict
    // verification and multiplies each verification by its N-O fixpoint
    // iterations. These count VERIFICATIONS at the caller, per site.
    //
    // Extension sampled propagation-verify lane (extension/propagate.rs):
    // SELECTED = props chosen by the #8256 sampling policy (COVERAGE — must
    // be identical on-vs-off for AY_VERIFY_MEMO); MIXED_FULL = cached
    // Nelson-Oppen combiner checks performed; FRESH_FULL = fresh-solver
    // dispatch (verify_propagation_semantic) runs.
    VERIFY_PROP_SELECTED    => "verify_prop_selected",
    VERIFY_PROP_MIXED_FULL  => "verify_prop_mixed_full",
    VERIFY_PROP_FRESH_FULL  => "verify_prop_fresh_full",
    // AY_VERIFY_MEMO obligation memo: HIT = identical-obligation short-
    // circuit (verdict previously recorded from a FULL verification of the
    // byte-identical literal set); MISS = eligible obligation fully verified.
    VERIFY_PROP_MEMO_HITS   => "verify_prop_memo_hits",
    VERIFY_PROP_MEMO_MISSES => "verify_prop_memo_misses",
    // Conflict-verification memo traffic: EXT = the eager extension's
    // trust-true-only memo (extension/helpers.rs); MEMOIZED = the #4535
    // memoized wrapper used by the lazy/pipeline arms (dispatch.rs).
    // FULL = full fail-closed re-verification ran; HITS = memo short-circuit.
    VERIFY_CONFLICT_EXT_FULL     => "verify_conflict_ext_full",
    VERIFY_CONFLICT_EXT_HITS     => "verify_conflict_ext_memo_hits",
    VERIFY_CONFLICT_MEMOIZED_FULL => "verify_conflict_memoized_full",
    VERIFY_CONFLICT_MEMOIZED_HITS => "verify_conflict_memoized_hits",
    // Fresh bare verification solvers (NOT verify_only-flagged, so their LIA
    // checks land in LIA_CHECK_TOP_CALLS — this counter de-pollutes TOP) and
    // the verify_lra_propagation two-tier split (algebraic O(1) arm vs fresh
    // LRA solver per verification).
    VERIFY_FRESH_LIA_SOLVES => "verify_fresh_lia_solves",
    VERIFY_FRESH_LRA_SOLVES => "verify_fresh_lra_solves",
    VERIFY_LRA_ALGEBRAIC    => "verify_lra_algebraic",
}

/// 0 = uninitialised, 1 = disabled, 2 = enabled.
static ENABLED: AtomicU8 = AtomicU8::new(0);
static REPORTER_STARTED: AtomicBool = AtomicBool::new(false);

#[inline]
pub(crate) fn enabled() -> bool {
    match ENABLED.load(Relaxed) {
        2 => true,
        1 => false,
        _ => init_enabled(),
    }
}

#[cold]
fn init_enabled() -> bool {
    let on = ay_core::misc_cli_flags().lia_instrument;
    ENABLED.store(if on { 2 } else { 1 }, Relaxed);
    if on {
        start_reporter();
    }
    on
}

/// Increment a counter iff instrumentation is enabled. Verdict-neutral.
#[inline]
pub(crate) fn bump(c: &AtomicU64) {
    if enabled() {
        c.fetch_add(1, Relaxed);
    }
}

/// Add `n` to a counter iff instrumentation is enabled. Verdict-neutral.
#[inline]
pub(crate) fn bump_by(c: &AtomicU64, n: u64) {
    if enabled() && n != 0 {
        c.fetch_add(n, Relaxed);
    }
}

fn start_reporter() {
    if REPORTER_STARTED.swap(true, Relaxed) {
        return;
    }
    // B9: fixed cadence (the AY_LIA_INSTRUMENT_SECS override nothing set is
    // retired). The reporter only runs when instrumentation is enabled at all.
    let secs: u64 = 3;
    std::thread::spawn(move || {
        let start = std::time::Instant::now();
        loop {
            std::thread::sleep(std::time::Duration::from_secs(secs));
            dump(start.elapsed().as_secs_f64());
        }
    });
}

/// Print the current counter snapshot to stderr as a single line.
pub(crate) fn dump(elapsed_secs: f64) {
    use std::fmt::Write as _;
    let mut line = format!("[LIA-INSTRUMENT t={elapsed_secs:.1}s]");
    for (label, value) in snapshot() {
        let _ = write!(line, " {label}={value}");
    }
    eprintln!("{line}");
}

// ---------------------------------------------------------------------------
// Inc0 public surface (eager-theory-prop design §Inc0): non-draining snapshot
// + externally-bumpable counters for ay-dpll (combiner N-O loop, lazy split
// rounds, round-end propagation discard). Same contract as the rest of the
// module: every entry point is a no-op returning after one relaxed load when
// no --lia-instrument is passed — write-only telemetry, never read by any
// verdict path.
// ---------------------------------------------------------------------------

/// Whether instrumentation is enabled (public, for gating caller-side probes).
#[inline]
pub fn enabled_pub() -> bool {
    enabled()
}

/// Non-draining one-line snapshot of all counters, or `None` when disabled.
/// Used by the `AY_UFLIA_PHASE` phase-edge timeline for per-arm attribution
/// (synchronous, unlike the async reporter thread).
pub fn snapshot_line() -> Option<String> {
    if !enabled() {
        return None;
    }
    use std::fmt::Write as _;
    let mut line = String::from("lia:");
    for (label, value) in snapshot() {
        let _ = write!(line, " {label}={value}");
    }
    Some(line)
}

/// Current total of `lia_check_calls` (for per-round deltas). 0 when disabled.
#[inline]
pub fn check_calls_now() -> u64 {
    if enabled() {
        LIA_CHECK_CALLS.load(Relaxed)
    } else {
        0
    }
}

/// Bump the Nelson-Oppen combiner-check counter (ay-dpll combiner_check).
#[inline]
pub fn bump_no_check() {
    bump(&NO_CHECKS);
}

/// Bump the Nelson-Oppen fixpoint-iteration counter (ay-dpll combiner_check).
#[inline]
pub fn bump_no_fixpoint_iter() {
    bump(&NO_FIXPOINT_ITERS);
}

/// Bump the lazy split-loop round counter (ay-dpll lazy macro).
#[inline]
pub fn bump_split_round() {
    bump(&SPLIT_ROUNDS);
}

/// Record round-end discarded propagations (ay-dpll lazy macro, Inc0-0d).
#[inline]
pub fn add_round_props_discarded(props: u64, pending: u64) {
    bump_by(&ROUND_PROPS_DISCARDED, props);
    bump_by(&ROUND_PENDING_DISCARDED, pending);
}

// ---------------------------------------------------------------------------
// #verify-memo: verify-lane caller-partition bumps for ay-dpll. Same contract
// as every other entry point — no-op after one relaxed load when
// no --lia-instrument is passed; write-only telemetry, never read by verdicts.
// ---------------------------------------------------------------------------

/// A propagation was SELECTED for semantic verification by the sampling
/// policy (extension sampled-verify lane; coverage counter).
#[inline]
pub fn bump_verify_prop_selected() {
    bump(&VERIFY_PROP_SELECTED);
}

/// The cached mixed-domain Nelson-Oppen verifier performed a full check.
#[inline]
pub fn bump_verify_prop_mixed_full() {
    bump(&VERIFY_PROP_MIXED_FULL);
}

/// The fresh-solver dispatch (verify_propagation_semantic) ran from the
/// extension's sampled-verify lane.
#[inline]
pub fn bump_verify_prop_fresh_full() {
    bump(&VERIFY_PROP_FRESH_FULL);
}

/// AY_VERIFY_MEMO propagation-obligation memo outcome.
#[inline]
pub fn bump_verify_prop_memo(hit: bool) {
    bump(if hit {
        &VERIFY_PROP_MEMO_HITS
    } else {
        &VERIFY_PROP_MEMO_MISSES
    });
}

/// Extension conflict-verification memo outcome (trust-true-only memo).
#[inline]
pub fn bump_verify_conflict_ext(hit: bool) {
    bump(if hit {
        &VERIFY_CONFLICT_EXT_HITS
    } else {
        &VERIFY_CONFLICT_EXT_FULL
    });
}

/// #4535 memoized conflict-verification wrapper outcome (lazy/pipeline arms).
#[inline]
pub fn bump_verify_conflict_memoized(hit: bool) {
    bump(if hit {
        &VERIFY_CONFLICT_MEMOIZED_HITS
    } else {
        &VERIFY_CONFLICT_MEMOIZED_FULL
    });
}

/// A fresh bare LiaSolver verification re-solve ran (these bump
/// LIA_CHECK_TOP_CALLS, not the verify partition — see counter docs).
#[inline]
pub fn bump_verify_fresh_lia_solve() {
    bump(&VERIFY_FRESH_LIA_SOLVES);
}

/// A fresh bare LraSolver verification re-solve ran (invisible to the LIA
/// check counters entirely — LRA checks are not counted there).
#[inline]
pub fn bump_verify_fresh_lra_solve() {
    bump(&VERIFY_FRESH_LRA_SOLVES);
}

/// verify_lra_propagation resolved in the O(1) algebraic tier.
#[inline]
pub fn bump_verify_lra_algebraic() {
    bump(&VERIFY_LRA_ALGEBRAIC);
}
