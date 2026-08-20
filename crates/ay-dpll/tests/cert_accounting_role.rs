// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #cert-accounting: the declared query role attributes cost and changes
//! nothing else.
//!
//! Every assertion here is either
//!   (a) a DELTA on the process-global counters — never an absolute, because
//!       the test runner is multi-threaded and other tests solve concurrently,
//!       so a concurrent solve can only inflate a delta, never deflate it; or
//!   (b) an EQUALITY between what `execute` and `execute_internal_lemma`
//!       publish, which is the behaviour-neutrality claim the landing rests on.

use ay_dpll::{CertificationAccounting, Executor};
use ay_frontend::parse;

const UNSAT_SCRIPT: &str = "(set-logic QF_LIA)\n\
     (declare-const x Int)\n\
     (assert (> x 5))\n\
     (assert (< x 3))\n";

const SAT_SCRIPT: &str = "(set-logic QF_LIA)\n\
     (declare-const x Int)\n\
     (assert (> x 5))\n";

fn run(script: &str, internal_lemma: bool) -> (String, Executor) {
    let commands = parse(script).expect("fixture script parses");
    let mut executor = Executor::new();
    for command in &commands {
        executor.execute(command).expect("setup command executes");
    }
    let check = parse("(check-sat)").expect("check-sat parses");
    let verdict = if internal_lemma {
        executor
            .execute_internal_lemma(&check[0])
            .expect("internal-lemma check-sat executes")
    } else {
        executor.execute(&check[0]).expect("check-sat executes")
    };
    (verdict.unwrap_or_default(), executor)
}

/// The declaration must not change the answer, on either polarity.
#[test]
fn internal_lemma_role_publishes_the_same_verdict_as_the_generic_entrypoint() {
    for script in [UNSAT_SCRIPT, SAT_SCRIPT] {
        let (published, _) = run(script, false);
        let (internal, _) = run(script, true);
        assert_eq!(
            published, internal,
            "declaring the internal-lemma role changed the published verdict"
        );
    }
    let (unsat, _) = run(UNSAT_SCRIPT, true);
    assert_eq!(unsat, "unsat", "the UNSAT fixture must still refute");
    let (sat, _) = run(SAT_SCRIPT, true);
    assert_eq!(sat, "sat", "the SAT fixture must still model");
}

/// ... and must not weaken certification: an internal-lemma UNSAT is minted
/// and admitted through the same mandatory funnel, so it still carries a
/// certificate-backed verdict rather than degrading to `unknown`.
#[test]
fn internal_lemma_unsat_still_runs_the_mandatory_certification_funnel() {
    let before = CertificationAccounting::snapshot();
    let (verdict, _executor) = run(UNSAT_SCRIPT, true);
    let delta = CertificationAccounting::snapshot().since(before);

    assert_eq!(verdict, "unsat");
    assert!(
        delta.mints >= 1,
        "an internal-lemma UNSAT must still mint a certificate (delta={delta})"
    );
    assert!(
        delta.mints_internal_lemma >= 1,
        "the mint must be attributed to the internal-lemma channel (delta={delta})"
    );
    assert!(
        delta.decisions_internal_lemma >= 1,
        "the decision must be attributed to the internal-lemma channel (delta={delta})"
    );
}

/// The generic entrypoint attributes nothing to the internal channel. Asserted
/// as "the published channel moved", not "the internal channel did not" — the
/// latter would be a race against any concurrently running test.
#[test]
fn generic_entrypoint_moves_the_decision_and_mint_totals() {
    let before = CertificationAccounting::snapshot();
    let (verdict, _executor) = run(UNSAT_SCRIPT, false);
    let delta = CertificationAccounting::snapshot().since(before);

    assert_eq!(verdict, "unsat");
    assert!(delta.decisions >= 1, "delta={delta}");
    assert!(delta.mints >= 1, "delta={delta}");
}

/// The declaration is scoped to the command it was declared for: a later
/// generic command on the same executor is accounted to the published channel.
///
/// Checked through the PER-EXECUTOR `cert.decision_role` statistic rather than
/// the process-global counters, so the assertion is exact rather than a
/// delta-bound that a parallel test runner could inflate.
#[test]
fn the_role_declaration_is_restored_after_the_declared_command() {
    let commands = parse(UNSAT_SCRIPT).expect("fixture script parses");
    let mut executor = Executor::new();
    for command in &commands {
        executor.execute(command).expect("setup command executes");
    }
    let check = parse("(check-sat)").expect("check-sat parses");

    executor
        .execute_internal_lemma(&check[0])
        .expect("internal-lemma check-sat executes");
    assert_eq!(
        executor.statistics().get_string("cert.decision_role"),
        Some("internal-lemma"),
        "the declared command must be attributed to the search channel"
    );

    executor.execute(&check[0]).expect("check-sat executes");
    assert_eq!(
        executor.statistics().get_string("cert.decision_role"),
        Some("published"),
        "the declaration must not leak past the command it was declared for"
    );
}

/// `execute_all_internal_lemma` declares the role for the whole sequence and
/// still returns the same outputs as `execute_all`.
#[test]
fn execute_all_internal_lemma_matches_execute_all() {
    let script = format!("{UNSAT_SCRIPT}(check-sat)\n");
    let commands = parse(&script).expect("fixture script parses");

    let mut published = Executor::new();
    let published_out = published
        .execute_all(&commands)
        .expect("generic batch executes");

    let mut internal = Executor::new();
    let internal_out = internal
        .execute_all_internal_lemma(&commands)
        .expect("internal-lemma batch executes");

    assert_eq!(published_out, internal_out);
    assert_eq!(published_out.first().map(String::as_str), Some("unsat"));
}

/// The counters reach `--stats` under their documented keys.
#[test]
fn certification_counters_are_published_into_statistics() {
    let (_verdict, executor) = run(UNSAT_SCRIPT, true);
    let statistics = executor.statistics();
    assert_eq!(
        statistics.get_string("cert.decision_role"),
        Some("internal-lemma"),
        "the per-executor role statistic must name the declared channel"
    );
    for key in [
        "cert.decisions",
        "cert.decisions_internal_lemma",
        "cert.decisions_proof_tracked",
        "cert.decisions_proof_tracked_internal_lemma",
        "cert.decision_nanos",
        "cert.proof_steps_recorded",
        "cert.mints",
        "cert.mint_nanos",
        "cert.mints_internal_lemma",
        "cert.mint_nanos_internal_lemma",
        "cert.nested_corroboration_solves",
        "cert.nested_corroboration_nanos",
        "cert.raw_admissions",
        "cert.publication_rejections",
    ] {
        assert!(
            statistics.get_int(key).is_some(),
            "statistics must carry {key}"
        );
    }
    assert!(
        statistics.get_int("cert.mints").unwrap_or(0) >= 1,
        "a minted UNSAT must be visible in statistics"
    );
}
