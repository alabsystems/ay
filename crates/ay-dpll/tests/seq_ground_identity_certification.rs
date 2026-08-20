// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Certification of ground-sequence identity refutations (deductive-checks
//! `calc_basic` class).
//!
//! The fixture asserts `(= a (seq.unit 1))` and denies the SAME sequence
//! written through a ground identity, `(seq.++ seq.empty (seq.unit 1))`.
//! Preprocessing folds the concat, so the recorded refutation's `assume`
//! leaves stop matching the authored surfaces and provenance demotion turns
//! them into explicit unit `trust` steps. Before the fix, the
//! substitution-bridge repair could not close the gap — the mandatory
//! certification funnel then refuted its own UNSAT and published
//! `unknown (incomplete self-check-rejected)` — because of two independent
//! defects, both fenced here:
//!
//! 1. No planner leg could derive the folded-vs-authored equality for a
//!    ground SEQUENCE pair. [`ay_core::TheoryLemmaKind::SeqGroundEval`] now
//!    covers it: both sides normalize (concat-flatten, empty-drop, unit of
//!    constants) to the same element list, validated semantically by
//!    `ay-proof` independent of the solver's seq engine.
//! 2. When one congruence kid IS the source assertion, the kid's `neg_eq`
//!    equals the negated source literal, the `eq_congruent_pred` lemma holds
//!    that literal TWICE, and the kid resolution eliminates both copies. The
//!    bridge emitter then appended its usual final resolution against the
//!    source assume with no pivot literal left — an invalid step the
//!    whole-proof gate rejected. The emitter now recognizes the
//!    already-complete unit and stops.
//!
//! The strict-proof seq gate is deliberately NOT relaxed: sequence proofs
//! remain externally uncheckable (carcara rejects the sort at parse time), so
//! `:check-proofs-strict` still withholds this UNSAT — see
//! `strict_proof_terminal_trust_library_gate.rs` for that fence.

use ay_core::{ProofStep, TheoryLemmaKind};
use ay_dpll::{Executor, UnknownReason};
use ay_frontend::parse;
use ntest::timeout;

/// Authored ground identity spelled two ways; UNSAT by `seq.++` folding.
const SEQ_GROUND_IDENTITY_UNSAT: &str = "\
(set-logic ALL)
(declare-const a (Seq Int))
(assert (= a (seq.unit 1)))
(assert (not (= a (seq.++ (as seq.empty (Seq Int)) (seq.unit 1)))))
(check-sat)
";

/// Proofs on, strict OFF — the deductive-checks encoder's mode.
const PLAIN: &str = "(set-option :produce-proofs true)\n";

fn solve(prefix: &str, script: &str) -> (String, Executor) {
    let commands = parse(&format!("{prefix}{script}")).expect("parse probe script");
    let mut executor = Executor::new();
    let outputs = executor
        .execute_all(&commands)
        .expect("execute probe script");
    let verdict = outputs.last().cloned().unwrap_or_else(|| "<none>".into());
    (verdict, executor)
}

/// The defect: this exact problem published
/// `unknown (incomplete self-check-rejected)` — a computed UNSAT the
/// certification funnel refused because the repaired proof was rejected.
#[test]
#[timeout(120_000)]
fn plain_proofs_certify_folded_seq_ground_identity_unsat() {
    let (verdict, executor) = solve(PLAIN, SEQ_GROUND_IDENTITY_UNSAT);
    assert_ne!(
        executor.unknown_reason(),
        Some(UnknownReason::SelfCheckRejected),
        "certification funnel refuted its own seq ground-identity UNSAT again \
         — the substitution-bridge repair regressed"
    );
    assert_eq!(verdict, "unsat");
}

/// The repaired proof must be internally trust-free: every demoted leaf is
/// rebuilt from the authored assumes through checkable bridge steps, with the
/// ground identity carried by a semantically validated `SeqGroundEval` lemma —
/// not re-admitted as `trust`.
#[test]
#[timeout(120_000)]
fn repaired_seq_proof_is_internally_trust_free() {
    let (verdict, executor) = solve(PLAIN, SEQ_GROUND_IDENTITY_UNSAT);
    assert_eq!(verdict, "unsat");
    let proof = executor
        .last_proof()
        .expect("produce-proofs mode must retain the refutation");
    let report = ay_proof::terminal_trust_report(proof);
    assert!(
        !report.has_terminal_trust(),
        "the published refutation still reaches the empty clause through a \
         trust/hole step: {report:?}"
    );

    // The whole proof passes AY's strict checker: the SeqGroundEval lemma is
    // independently re-validated by its own ground normalizer, and no
    // unvalidated trust/hole step remains in the internal proof IR.
    match ay_proof::check_proof_strict(proof, executor.terms()) {
        Ok(quality) => assert_eq!(
            quality.trust_count, 0,
            "strict check must count zero trust steps"
        ),
        Err(error) => panic!("proof must pass strict check, got {error:?}"),
    }

    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::SeqGroundEval,
                ..
            }
        )),
        "proof IR must carry the checked SeqGroundEval kind"
    );

    // `seq_ground_eval` is AY's internal checked kind, not a rule in the
    // shipped Alethe checker (which cannot even parse the `Seq` sort). The
    // wire format must use an honest `hole` — never an unknown rule name and
    // never AY's internal `trust` fallback.
    let text = ay_proof::export_alethe(proof, executor.terms());
    assert!(
        text.contains(":rule hole"),
        "Alethe wire proof must expose the custom lemma as a hole; got:\n{text}"
    );
    assert!(
        !text.contains("seq_ground_eval"),
        "must not emit a rule the external checker does not implement; got:\n{text}"
    );
}
