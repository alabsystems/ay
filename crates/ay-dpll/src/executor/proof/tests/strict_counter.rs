// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// M0(a) (the development design notes): the strict-check attribution
/// counters count every `check_proof_strict_with_datatypes` entry, survive to
/// the published statistics, and — with the #strict-verdict-memo in
/// `build_unsat_proof` — a happy-path certified UNSAT no longer opens one
/// strict probe per authored-replacement cascade member (~22 of them).
#[test]
#[timeout(60000)]
fn m0_strict_check_counters_publish_and_cascade_memo_collapses_probes() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-option :check-proofs-strict true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (< x 0))
        (assert (> x 0))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs[0], "unsat");

    let invocations = exec.strict_check_invocations.get();
    let steps = exec.strict_check_steps_validated.get();
    eprintln!(
        "M0(a) counters: strict_check_invocations={invocations} \
         strict_check_steps_validated={steps}"
    );
    assert!(
        invocations >= 1,
        "certified strict UNSAT must run the strict checker at least once"
    );
    assert!(
        steps >= invocations,
        "every counted invocation submits a non-empty proof here \
         (invocations={invocations}, steps={steps})"
    );
    // The memo bound: without #strict-verdict-memo this trivial flow ran the
    // ~22-member cascade's per-member entry probes on an already-valid proof
    // (>= 25 invocations). With the memo the whole publication needs only the
    // cascade-start verdict plus the fixed post-cascade validations and the
    // mint-time authority re-check. The bound is deliberately loose so it
    // pins the mechanism (no per-member probing), not an exact pass layout.
    assert!(
        invocations <= 12,
        "publication-flow strict checks did not collapse: {invocations} invocations"
    );

    // The counters must reach the published statistics. Proof-quality
    // population records an intermediate snapshot and the outer publication
    // funnel refreshes it after the mint-time strict re-check.
    let stats = exec.statistics();
    let published = stats
        .get_int("proof.strict_check_invocations")
        .expect("strict-check invocation statistic must be published");
    let published_steps = stats
        .get_int("proof.strict_check_steps_validated")
        .expect("strict-check steps statistic must be published");
    assert_eq!(
        published, invocations,
        "published invocation count must include the complete publication \
         funnel (published={published}, live={invocations})"
    );
    assert_eq!(
        published_steps, steps,
        "published step count must include the complete publication funnel \
         (published={published_steps}, live={steps})"
    );

    // Per-publication scoping: a second public solve restarts the counters
    // instead of accumulating across publications.
    let commands = parse("(check-sat)").unwrap();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs[0], "unsat");
    let second = exec.strict_check_invocations.get();
    assert!(
        (1..=12).contains(&second),
        "second publication must re-count from zero, not accumulate: {second}"
    );
}
