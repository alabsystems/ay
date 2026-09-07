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
/// Distinct from [`COMPETITION_MODE_ENABLED`] on purpose: shedding the proof
/// cycle is the z3 posture for an SMT-LIB solve and must not drag the
/// SAT-competition verdict grammar or the CHC/DIMACS validation batteries
/// along with it. Selected by [`proof_cycle_shed`].
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
pub(crate) fn proof_cycle_shed(args: &SolveArgs) -> bool {
    competition_mode(args) || args.no_proof || args.z3_mode || !certification_requested(args)
}

/// Whether this invocation asked AY to certify its own answer: any `--rigor`
/// rung above `fast`, a legacy rigor alias (`--strict-proofs`,
/// `--self-check`), an explicit proof artifact (`--proof` / `--drat` /
/// `--lrat` / `--proof-artifact`), or a checker gate (`--verify-proof`,
/// `--verify-firewall`, `--emit-firewall-lean`, `--lean-verify`).
///
/// A plain solve (`ay FILE.smt2`, `ay solve FILE.smt2`, `ay -in`) asks for
/// none of these and therefore runs at the `fast` rung's proof posture —
/// z3's own default: no proof recorded during search, no certificate minted
/// or re-checked, nothing written next to the input. Measured on the SMT-COMP
/// corpus, the certified default cost 2.7x–20x the search time on UNSAT
/// instances (gensys_icl161: search 0.23 s, mint 4.34 s; vlsat3_c35: 0.11 s
/// vs 17.95 s) for sidecars that were frequently 26-byte `hole` files, and
/// it left 46 stray `.alethe` files in the benchmark corpus in one day.
/// Certification stays one flag away and is unchanged when asked for.
pub(crate) fn certification_requested(args: &SolveArgs) -> bool {
    args.assurance
        .is_some_and(|level| level != super::CliAssuranceLevel::Fast)
        || args.strict_proofs
        || args.self_check
        || args.proof.is_some()
        || args.drat.is_some()
        || args.drat_binary.is_some()
        || args.lrat.is_some()
        || args.lrat_binary.is_some()
        || args.proof_artifact.is_some()
        || args.verify_proof
        || args.verify_firewall
        || args.emit_firewall_lean.is_some()
        || args.lean_verify
}
