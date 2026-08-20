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
//! Publication semantics (#proof-capability B3): while shedding is active,
//! UNSAT publishes through the `CompetitionRaw` admission lane — the exact
//! public-query scope authenticates (unweakened epoch/source/term-entry/
//! assumption checks; proof-source provenance self-gates under shedding and
//! is the one tolerated absence) but no checked refutation backs the verdict.
//! This is the documented product carve-out, and the tests below prove its
//! boundary from both sides: EVERY shed-mode UNSAT admits (a missed admission
//! arm would silently score 0 as `unknown`), and ANY proof demand makes the
//! raw lane dead code with certified-mode behavior unchanged.

use super::unsat_cert::CommandUnsatAdmission;
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

/// B3 publication with shedding active: an `unsat` is never published without
/// an admission token. Post-B3 the token is the scope-authenticated
/// `CompetitionRaw` carve-out, and its admission class plus the
/// `unsat_admission=competition-raw` statistic are both recorded — nothing can
/// pass a raw admission off as a checked certification.
#[test]
fn shedding_publishes_raw_admitted_unsat_with_recorded_class() {
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
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("unsat"),
        "shed-mode refutation must publish through the raw admission lane"
    );
    assert_eq!(
        exec.last_command_unsat_admission,
        Some(CommandUnsatAdmission::CompetitionRaw),
        "shed-mode unsat must record the raw admission class"
    );
    assert_eq!(
        exec.statistics().get_string("unsat_admission"),
        Some("competition-raw"),
        "the raw admission must be visible in the statistics surface"
    );
    // A raw admission is an admission record, never a verification claim.
    assert!(!exec.last_command_unsat_was_strictly_verified());
    assert!(!exec.last_command_unsat_was_independently_verified());
    assert!(!exec.last_command_unsat_was_exact_semantically_verified());
}

/// #proof-capability B3 every-UNSAT-admits matrix: in shedding mode EVERY
/// refutation family publishes `unsat` through the `CompetitionRaw` lane. A
/// missed admission arm would not fail loudly — the verdict would silently
/// degrade to `unknown` and score 0 — so each family asserts the exact
/// verdict AND the exact admission class.
#[test]
fn shed_mode_every_unsat_family_admits_competition_raw() {
    for (family, script) in [
        (
            "propositional resolution",
            r"
            (set-logic QF_UF)
            (declare-const p Bool)
            (declare-const q Bool)
            (assert (or p q))
            (assert (or (not p) q))
            (assert (not q))
            (check-sat)
            ",
        ),
        (
            "EUF congruence",
            r"
            (set-logic QF_UF)
            (declare-sort U 0)
            (declare-fun f (U) U)
            (declare-const a U)
            (declare-const b U)
            (assert (= a b))
            (assert (distinct (f a) (f b)))
            (check-sat)
            ",
        ),
        (
            "LIA bounds",
            r"
            (set-logic QF_LIA)
            (declare-const x Int)
            (assert (< x 0))
            (assert (> x 0))
            (check-sat)
            ",
        ),
        (
            "BV equality",
            r"
            (set-logic QF_BV)
            (declare-const v (_ BitVec 8))
            (assert (= v #x01))
            (assert (= v #x02))
            (check-sat)
            ",
        ),
        (
            "check-sat-assuming",
            r"
            (set-logic QF_UF)
            (declare-const p Bool)
            (assert p)
            (check-sat-assuming ((not p)))
            ",
        ),
    ] {
        let mut exec = Executor::new();
        exec.set_competition_mode(true);
        let outputs = run(&mut exec, script);
        assert_eq!(
            outputs.last().map(String::as_str),
            Some("unsat"),
            "{family}: shed-mode UNSAT must ADMIT, not silently degrade to \
             unknown (a missed admission arm scores 0)"
        );
        assert_eq!(
            exec.last_command_unsat_admission,
            Some(CommandUnsatAdmission::CompetitionRaw),
            "{family}: shed-mode unsat must publish through the CompetitionRaw \
             admission lane"
        );
        assert_eq!(
            exec.statistics().get_string("unsat_admission"),
            Some("competition-raw"),
            "{family}: the raw admission statistic must be recorded"
        );
    }
}

/// A quantified AUFLIA refutation that routes through a PREPROCESSED-window
/// theory transaction (`with_deferred_postprocessing`), minimized from the
/// SMT-LIB SingleQuery instance
/// `non-incremental/AUFLIA/20170829-Rodin/smt5528103774414173689.smt2`.
///
/// The `forall` over the uninterpreted sort forces the combined AUFLIA route,
/// which swaps a preprocessed assertion window in; the `0 <= c <= 0 /\ c != 0`
/// bound clash is what refutes.
const QUANTIFIED_PREPROCESSING_WINDOW_UNSAT: &str = r"
    (set-logic AUFLIA)
    (declare-sort Color 0)
    (declare-fun c () Int)
    (declare-fun green () Color)
    (declare-fun red () Color)
    (assert (forall ((x Color)) (or (= x green) (= x red))))
    (assert (<= 0 c))
    (assert (<= c 0))
    (assert (not (= c 0)))
    (check-sat)
    ";

/// RIGOR MONOTONICITY (#rigor-fast-monotone): `--rigor fast` (competition
/// shedding) does strictly LESS checking than `--rigor standard`, so it may
/// never LOSE a verdict standard publishes.
///
/// It did. `with_deferred_postprocessing` installs a provenance describing its
/// PREPROCESSED window and, on UNSAT only, deliberately skips the restore so
/// the certification lanes can consume it. That is sound under standard rigor
/// because an outer public-query provenance exists and
/// `preserving_authority_from` re-roots the record onto the authored epoch.
/// Under shedding `begin_public_solve` installs no outer provenance at all, so
/// the re-rooting is the identity and what survived named the PREPROCESSED
/// window — a present-but-mismatched provenance that
/// `authenticate_unsat_query_scope` hard-fails, degrading the raw lane to
/// `unknown`. Measured on the SMT-LIB SingleQuery Equality_LinearArith
/// selection: 15 of 120 declared-unsat AUFLIA instances were lost this way,
/// on the competition posture, on every quantified division.
///
/// The mismatch check is NOT relaxed — present-but-mismatched provenance stays
/// a hard error under both policies. The transaction simply stops leaving the
/// record behind when no lane can consume it
/// (`theory_window_provenance_survives_unsat`).
#[test]
fn shed_mode_is_monotone_against_certified_on_preprocessing_window_unsat() {
    // `--rigor standard`: certified default, no competition switch.
    let mut standard = Executor::new();
    let standard_outputs = run(&mut standard, QUANTIFIED_PREPROCESSING_WINDOW_UNSAT);
    let standard_verdict = standard_outputs.last().map(String::as_str);
    assert_eq!(
        standard_verdict,
        Some("unsat"),
        "the fixture must still be a certified refutation, else this test \
         proves nothing about monotonicity"
    );

    // `--rigor fast`: `set_competition_mode(true)` is exactly what the CLI
    // level does (`CliAssuranceLevel::Fast` == the former `--competition`).
    let mut fast = Executor::new();
    fast.set_competition_mode(true);
    assert!(fast.competition_shedding_active());
    let fast_outputs = run(&mut fast, QUANTIFIED_PREPROCESSING_WINDOW_UNSAT);

    assert_eq!(
        fast_outputs.last().map(String::as_str),
        standard_verdict,
        "rigor must be MONOTONE: `fast` does less checking than `standard`, \
         so it can never lose a verdict `standard` publishes"
    );
    assert_eq!(
        fast.last_command_unsat_admission,
        Some(CommandUnsatAdmission::CompetitionRaw),
        "the shed-mode verdict must publish through the B3 raw admission lane"
    );
}

/// The mechanism behind the monotonicity failure, pinned directly: after a
/// shed-mode public solve NO proof-source provenance may be left installed.
///
/// Absence is the documented shed-mode norm the B3 raw lane authenticates
/// (`authenticate_unsat_query_scope` runs with `require_proof_provenance =
/// false`). Any record surviving a preprocessed-window theory transaction is
/// bound to that window rather than to `epoch.assertions`, so its mere
/// presence is what fails the scope check. Asserting the verdict alone would
/// not catch a future transaction re-introducing the same leftover on a route
/// this fixture does not take.
#[test]
fn shed_mode_public_solve_leaves_no_proof_source_provenance() {
    for (family, script) in [
        (
            "quantified AUFLIA preprocessing window",
            QUANTIFIED_PREPROCESSING_WINDOW_UNSAT,
        ),
        (
            "LIA preprocessing window",
            r"
            (set-logic QF_LIA)
            (declare-const x Int)
            (declare-const y Int)
            (assert (= y (+ x x)))
            (assert (< x 0))
            (assert (> x 0))
            (check-sat)
            ",
        ),
    ] {
        let mut exec = Executor::new();
        exec.set_competition_mode(true);
        let outputs = run(&mut exec, script);
        assert_eq!(
            outputs.last().map(String::as_str),
            Some("unsat"),
            "{family}: fixture must refute under shedding"
        );
        assert!(
            !exec.has_proof_problem_assertion_provenance(),
            "{family}: a shed-mode solve builds no proof, so it must leave no \
             proof-source provenance — a surviving record is bound to a \
             preprocessed window and fails the raw lane's scope check"
        );
    }
}

/// #proof-capability B3 unreachability invariant: with ANY proof demand in
/// scope — or without competition mode at all — the raw lane is dead code.
/// Each demand row runs TWIN executors, competition+demand vs demand-only,
/// and requires identical outputs and identical admission class: the
/// competition switch must be unobservable outside shedding. No row may
/// admit through `CompetitionRaw` and the `unsat_admission` statistic key
/// must never appear.
#[test]
fn competition_raw_is_dead_under_every_proof_demand() {
    const SCRIPT: &str = r"
        (set-logic QF_UF)
        (declare-const p Bool)
        (assert p)
        (assert (not p))
        (check-sat)
    ";
    let demands: [(&str, fn(&mut Executor)); 5] = [
        ("no demand (certified default twin)", |_| {}),
        ("set_produce_proofs(true)", |exec| {
            exec.set_produce_proofs(true);
        }),
        ("in-script :produce-proofs true", |exec| {
            run(exec, "(set-option :produce-proofs true)");
        }),
        (":check-proofs-strict true", |exec| {
            run(exec, "(set-option :check-proofs-strict true)");
        }),
        ("set_self_check(true)", |exec| {
            exec.set_self_check(true);
        }),
    ];
    for (demand, arm) in demands {
        let mut certified = Executor::new();
        arm(&mut certified);
        let mut competition = Executor::new();
        competition.set_competition_mode(true);
        arm(&mut competition);
        if demand == "no demand (certified default twin)" {
            // The one row where shedding IS active on the competition twin:
            // it exercises the raw lane and is asserted separately by
            // `shed_mode_every_unsat_family_admits_competition_raw`. Here
            // only the certified twin's surface is pinned.
            let outputs = run(&mut certified, SCRIPT);
            assert_eq!(outputs.last().map(String::as_str), Some("unsat"));
            assert_ne!(
                certified.last_command_unsat_admission,
                Some(CommandUnsatAdmission::CompetitionRaw),
                "{demand}: certified default must never admit raw"
            );
            assert_eq!(
                certified.statistics().get_string("unsat_admission"),
                None,
                "{demand}: certified statistics must not carry the raw marker"
            );
            continue;
        }
        assert!(
            !competition.competition_shedding_active(),
            "{demand}: the demand must deactivate shedding"
        );
        let certified_outputs = run(&mut certified, SCRIPT);
        let competition_outputs = run(&mut competition, SCRIPT);
        assert_eq!(
            certified_outputs, competition_outputs,
            "{demand}: with the demand in scope the competition switch must \
             be unobservable"
        );
        assert_eq!(
            certified.last_command_unsat_admission, competition.last_command_unsat_admission,
            "{demand}: both twins must publish through the same admission lane"
        );
        assert_ne!(
            competition.last_command_unsat_admission,
            Some(CommandUnsatAdmission::CompetitionRaw),
            "{demand}: the raw lane must be unreachable outside shedding"
        );
        for (twin, exec) in [("certified", &certified), ("competition", &competition)] {
            assert_eq!(
                exec.statistics().get_string("unsat_admission"),
                None,
                "{demand}: {twin} twin statistics must not carry the raw \
                 admission marker"
            );
        }
    }
}
