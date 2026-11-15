// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::env;
use std::sync::atomic::AtomicBool;

use super::{SolveArgs, SAT_COMPETITION_WRAPPER_ENV};

/// Latched before executor construction so the competition-only surfaces
/// cannot race: the SAT-competition output grammar for memory/timeout
/// verdicts (`memory_grammar_is_sat_competition`) and, via
/// [`competition_mode`], the CHC validation battery and the DIMACS proof
/// re-check. Proof-cycle shedding is NOT keyed on this latch any more — see
/// [`PROOF_CYCLE_SHED_ENABLED`].
pub(crate) static COMPETITION_MODE_ENABLED: AtomicBool = AtomicBool::new(false);

/// Latched before executor construction: every executor `run::new_executor`
/// builds sheds the internal proof cycle on public solves with no proof
/// demand (`Executor::set_competition_mode`) — no search-time proof
/// recording, no post-UNSAT certificate mint, no nested corroboration
/// re-solves, no bookkeeping meter at all. Executor-side precedence still
/// applies: `--proof`, `--strict-proofs`, `--self-check`, `--verify-firewall`,
/// `--emit-firewall-lean`, and an in-script `(set-option :produce-proofs
/// true)` each re-arm the certified lanes regardless of this latch.
///
/// Distinct from [`COMPETITION_MODE_ENABLED`] on purpose: an explicit proof
/// opt-out is not a request for the SAT-competition verdict grammar or for
/// the CHC/DIMACS validation batteries to be switched off. Selected by
/// [`proof_cycle_shed`], which a PLAIN solve never trips — proofs and
/// certificates are the product, so the default keeps the cycle armed.
pub(crate) static PROOF_CYCLE_SHED_ENABLED: AtomicBool = AtomicBool::new(false);

/// Whether a benchmark harness requested competition behavior.
///
/// Shared with [`super::build_info::session_log`], so the provenance verbosity a
/// competition transcript gets can never drift from the set of signals that put
/// the solver in competition mode.
pub(crate) fn competition_env_active() -> bool {
    const SIGNALS: &[&str] = &[
        SAT_COMPETITION_WRAPPER_ENV,
        "AY_COMPETITION",
        "AY_SAT_COMPETITION_PROFILE",
        "AY_SAT_PROFILE_ID",
    ];
    SIGNALS
        .iter()
        .any(|name| env::var(name).is_ok_and(|value| !value.trim().is_empty()))
}

/// Competition mode disables optional batteries, never soundness defaults.
pub(crate) fn competition_mode(args: &SolveArgs) -> bool {
    args.competition || competition_env_active()
}

/// Whether this solve sheds the executor's internal proof cycle
/// ([`PROOF_CYCLE_SHED_ENABLED`]).
///
/// `--no-proof` and `--z3-mode` used to suppress only the sidecar: the
/// tracker stayed armed for the mandatory certificate with an UNBUDGETED
/// bookkeeping meter (`proof_reconstruction_step_budget = None`), the mint
/// and its nested re-solves still ran, and the flags were slower than the
/// default they claimed to opt out of (gensys_icl161: 8.65 s under
/// `--no-proof` vs 4.7 s default vs 0.15 s `--rigor fast`; vlsat3_c35
/// memouts). Both now shed exactly what `--rigor fast` sheds. Nothing else
/// changes for them: the CHC validation battery, the DIMACS proof re-check,
/// and the verdict grammar stay as they were.
///
/// A PLAIN solve is deliberately NOT in this set. Between 2026-09-06 and this
/// commit it was — `ay FILE.smt2` ran at the `fast` rung's proof posture, z3's
/// own default — and the owner reversed that decision: proofs and certificates
/// are what AY is for, and they are the signal that development is making
/// progress, so a flagless solve records a proof, mints and strict-checks its
/// certificate, and writes the `<input>.alethe` sidecar. `--z3-mode` is the
/// explicit escape hatch for z3-exact behaviour (`--no-proof` and
/// `--rigor fast` reach the same proof posture by their own routes).
pub(crate) fn proof_cycle_shed(args: &SolveArgs) -> bool {
    competition_mode(args) || args.no_proof || args.z3_mode
}

/// Whether the executors a library engine builds for its own SEARCH queries
/// (`ay_core::MiscCliFlags::search_executor_sheds_proof_cycle`; today the CHC
/// engines' SMT queries) shed the internal proof cycle.
///
/// This is the posture `run::new_executor`'s own executor EFFECTIVELY ends up
/// in: [`proof_cycle_shed`] selects `set_competition_mode(true)`, and the
/// executor-side precedence then re-arms the certified lanes for any proof
/// demand (`--proof`, `--strict-proofs`, `--self-check`, `--verify-firewall`,
/// `--emit-firewall-lean`, `--verify-proof`). Search executors get no such
/// demand wired in (they never did — the CHC certificate lanes build their own
/// proof-producing `api::Solver`), so the demand set is folded in HERE: under
/// any of those flags they keep the default proof-carrying posture, exactly as
/// before, and `--chc-checked-replay` (the opt-in checked replay that
/// re-executes certificate obligations on a fresh search executor) is treated
/// as a demand for the same reason. Measured on the LIA-Lin lustre consecution
/// class (T8): 11.68 s default vs 6.48 s shed for identical verdicts.
///
/// One search sheds in every posture, whatever this returns: the CHC
/// counterexample replay's bounded search (ay-chc `ScopedVerdictOnlySearch`).
/// No claim and no certificate rests on its verdicts: its Safe and Unknown
/// mean "not confirmed", and its Unsafe is accepted only by ground evaluation
/// of a derivation, after the search, in the default posture.
pub(crate) fn search_executor_sheds_proof_cycle(args: &SolveArgs) -> bool {
    proof_cycle_shed(args)
        && args.proof.is_none()
        && !args.strict_proofs
        && !args.self_check
        && !args.verify_firewall
        && args.emit_firewall_lean.is_none()
        && !args.verify_proof
        && !args.ab_switches.chc_checked_replay_requested()
}
