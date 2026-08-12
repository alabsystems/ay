// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Competition-mode switch plumbing tests (#proof-capability B1).
//!
//! The matrix under test: `set_competition_mode` sheds the internal proof
//! cycle at `begin_public_solve` ONLY when no proof demand is in scope, and
//! every explicit proof demand takes PRECEDENCE over shedding (never a
//! conflict):
//! - `set_produce_proofs(true)` (the executor-side effect of `--proof`,
//!   `--strict-proofs`, `--self-check` CLI sessions),
//! - in-script `(set-option :produce-proofs true)`,
//! - the `(set-option :check-proofs-strict true)` context option,
//! - `set_self_check(true)`.
//!
//! Publication semantics are v1 (pre-B3): shedding removes tracking cost, but
//! UNSAT publication still fail-closes — an `unsat` may only be published
//! with a minted certificate; otherwise it degrades to `unknown`. The
//! raw-admission lane (`CompetitionRaw`) is a later milestone gated on the
//! B2 dormant-lane audit.

use super::Executor;
use ay_frontend::parse;

/// Feed a script to an executor without asserting on per-command outputs.
fn run(exec: &mut Executor, script: &str) -> Vec<String> {
    let cmds = parse(script).expect("parse");
    exec.execute_all(&cmds).expect("execute")
}

/// Certified default (no competition mode): `begin_public_solve` arms the
/// tracker for every public decision — the documented invariant.
#[test]
fn certified_default_arms_tracker_on_public_solve() {
    let mut exec = Executor::new();
    assert!(!exec.competition_mode());
    assert!(!exec.competition_shedding_active());
    exec.begin_public_solve(false);
    assert!(
        exec.proof_tracker.is_enabled(),
        "certified default must arm the proof tracker on every public solve"
    );
    assert!(exec.produce_proofs_enabled());
}

/// Competition mode with no proof demand: the tracker is left DISABLED after
/// `begin_public_solve`, so every `produce_proofs_enabled()` consumer sees
/// recording off (this is the B1 debug_assert's exact postcondition).
#[test]
fn competition_mode_without_demand_sheds_tracker() {
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    assert!(exec.competition_mode());
    assert!(exec.competition_shedding_active());
    exec.begin_public_solve(false);
    assert!(
        !exec.proof_tracker.is_enabled(),
        "competition mode with no proof demand must leave the tracker disabled"
    );
    assert!(!exec.produce_proofs_enabled());
}

/// PRECEDENCE row 1: an explicit API/CLI proof request
/// (`set_produce_proofs(true)`, i.e. `--proof` / `--strict-proofs` /
/// `--self-check` sessions) defeats shedding regardless of call order.
#[test]
fn explicit_produce_proofs_overrides_shedding_in_any_order() {
    // Demand set before the mode.
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    exec.set_competition_mode(true);
    assert!(!exec.competition_shedding_active());
    exec.begin_public_solve(false);
    assert!(exec.proof_tracker.is_enabled());

    // Mode set before the demand.
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    exec.set_produce_proofs(true);
    assert!(!exec.competition_shedding_active());
    exec.begin_public_solve(false);
    assert!(exec.proof_tracker.is_enabled());
}

/// PRECEDENCE row 2: the in-script `(set-option :produce-proofs true)`
/// restores the certified lanes for subsequent solves, and `... false`
/// re-sheds them — the toggle is evaluated fresh at every public solve.
#[test]
fn in_script_produce_proofs_toggles_shedding_per_solve() {
    let mut exec = Executor::new();
    exec.set_competition_mode(true);

    run(&mut exec, "(set-option :produce-proofs true)");
    assert!(!exec.competition_shedding_active());
    exec.begin_public_solve(false);
    assert!(
        exec.proof_tracker.is_enabled(),
        "in-script :produce-proofs true must restore the certified lanes"
    );

    run(&mut exec, "(set-option :produce-proofs false)");
    assert!(exec.competition_shedding_active());
    exec.begin_public_solve(false);
    assert!(
        !exec.proof_tracker.is_enabled(),
        ":produce-proofs false must re-shed on the next public solve"
    );
}

/// PRECEDENCE row 3: the `:check-proofs-strict` CONTEXT option (executor-side,
/// visible without any CLI flag) defeats shedding. This is the review-mandated
/// replacement for the CLI-crate `strict_proofs_enabled()` probe.
#[test]
fn strict_proofs_context_option_overrides_shedding() {
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    run(&mut exec, "(set-option :check-proofs-strict true)");
    assert!(!exec.competition_shedding_active());
    exec.begin_public_solve(false);
    assert!(
        exec.proof_tracker.is_enabled(),
        ":check-proofs-strict true must keep the certified lanes armed"
    );
}

/// PRECEDENCE row 4: library-API self-check mode (`set_self_check(true)`
/// without a paired `set_produce_proofs`) must keep the checked-refutation
/// lane armed — self-check UNSAT requires a checked proof.
#[test]
fn self_check_overrides_shedding() {
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    exec.set_self_check(true);
    assert!(!exec.competition_shedding_active());
    exec.begin_public_solve(false);
    assert!(exec.proof_tracker.is_enabled());
}

/// The parsed-assertion retention re-arm is gated exactly like the tracker:
/// a shedding session keeps retention OFF (the CLI turns it off at session
/// start), while the certified default re-arms it at the public-solve
/// boundary.
#[test]
fn retention_rearm_is_gated_with_the_tracker() {
    const SCRIPT: &str = r"
        (set-logic QF_UF)
        (declare-const p Bool)
        (check-sat)
        (assert p)
        (check-sat)
    ";

    // Certified default: the first check-sat's begin_public_solve re-arms
    // retention, so the later assert retains its parsed surface form.
    let mut exec = Executor::new();
    exec.set_retain_parsed_assertions(false);
    run(&mut exec, SCRIPT);
    assert_eq!(
        exec.context().assertions_parsed().len(),
        1,
        "certified default must re-arm retention at the public-solve boundary"
    );

    // Competition shedding: no re-arm, the parsed stack stays empty.
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    exec.set_retain_parsed_assertions(false);
    run(&mut exec, SCRIPT);
    assert_eq!(
        exec.context().assertions_parsed().len(),
        0,
        "competition shedding must not re-arm parsed-assertion retention"
    );

    // In-script :produce-proofs true restores retention mid-session even in
    // competition mode (frontend flips it at set-option time; the certified
    // re-arm keeps it on for every later solve).
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    exec.set_retain_parsed_assertions(false);
    run(
        &mut exec,
        r"
        (set-logic QF_UF)
        (declare-const p Bool)
        (set-option :produce-proofs true)
        (assert p)
        (check-sat)
        ",
    );
    assert_eq!(
        exec.context().assertions_parsed().len(),
        1,
        ":produce-proofs true must restore retention in competition mode"
    );
}

/// Certification still RUNS when proofs are demanded in competition mode:
/// an UNSAT publishes as `unsat` and carries a minted certificate.
#[test]
fn demanded_proofs_keep_certified_unsat_publication_in_competition_mode() {
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    let outputs = run(
        &mut exec,
        r"
        (set-logic QF_UF)
        (set-option :produce-proofs true)
        (declare-const p Bool)
        (assert p)
        (assert (not p))
        (check-sat)
        ",
    );
    assert!(
        outputs.iter().any(|o| o == "unsat"),
        "certified lane must still publish unsat, got {outputs:?}"
    );
    // `admit_command_solve_result` consumes the minted one-shot certificate
    // and records its admission kind; a Some here proves a certification lane
    // (not a bare verdict) admitted the publication.
    assert!(
        exec.last_command_unsat_admission.is_some(),
        "a competition-mode solve with demanded proofs must admit unsat \
         through a minted certificate"
    );
}

/// v1 fail-closed publication with shedding active: whatever the verdict, an
/// `unsat` may ONLY be published when a certification lane minted a token —
/// shedding never buys an uncertified `unsat`. (Degrading to `unknown` is the
/// EXPECTED cost of shedding until the B3 raw-admission lane lands behind the
/// B2 audit.)
#[test]
fn shedding_never_publishes_uncertified_unsat() {
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    let outputs = run(
        &mut exec,
        r"
        (set-logic QF_UF)
        (declare-const p Bool)
        (declare-const q Bool)
        (assert (or p q))
        (assert (or (not p) q))
        (assert (not q))
        (check-sat)
        ",
    );
    let verdict = outputs.last().expect("check-sat output");
    assert!(
        verdict == "unsat" || verdict == "unknown",
        "shed-mode refutation must publish unsat-with-certificate or degrade \
         to unknown, got {verdict}"
    );
    if verdict == "unsat" {
        assert!(
            exec.last_command_unsat_admission.is_some(),
            "published unsat without a certification admission — the \
             fail-closed gate was weakened"
        );
    }
}
