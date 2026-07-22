// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Documents the proof quality impact of missing resolution hints.
//
// When conflict_analysis.rs:897 discards the set_resolution_hints return
// value via `let _ =`, and the clause ID doesn't match, the learned clause
// entry has empty resolution_hints. In sat_proof_manager.rs:319-340,
// derive_clause_from_hints returns None for empty hints, causing a fallback
// to AletheRule::Trust (line 333). This degrades proof quality:
//   - Standard checker accepts Trust → validation becomes a no-op
//   - Strict checker rejects Trust → proof fails strict validation
//   - Proof quality metrics report non-zero trust_count
//
// The fix is in conflict_analysis.rs:897 — change `let _ =` to
// `debug_assert!(trace.set_resolution_hints(...))` so missing hints
// are caught immediately during solving.
//
// See sat-debuggability epic #4172.

use ay_core::{AletheRule, Proof, ProofStep, Sort, TermStore};
use ay_proof::{check_proof, check_proof_strict, check_proof_with_quality};

/// A proof where a learned clause uses Trust (simulating missing hints)
/// passes standard validation but fails strict validation.
///
/// This mirrors the real-world scenario where conflict_analysis discards
/// set_resolution_hints and process_trace falls back to Trust.
#[test]
fn test_trust_from_missing_hints_passes_standard_fails_strict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let y = terms.mk_var("y", Sort::Bool);
    let not_x = terms.mk_not(x);
    let not_y = terms.mk_not(y);

    let mut proof = Proof::new();
    let hx = proof.add_assume(x, None);
    let hy = proof.add_assume(y, None);

    // This Trust step simulates what process_trace emits when
    // resolution_hints is empty: the clause is claimed without derivation.
    let trust_step = proof.add_step(ProofStep::Step {
        rule: AletheRule::Trust,
        clause: vec![not_x, not_y],
        premises: vec![hx, hy],
        args: vec![],
    });

    // Resolve trust_step with hx on pivot x → {not_y}
    let r0 = proof.add_resolution(vec![not_y], x, trust_step, hx);
    // Resolve r0 with hy on pivot y → empty clause
    proof.add_resolution(vec![], y, r0, hy);

    // Standard checker: accepts (Trust is permitted).
    check_proof(&proof, &terms).expect("standard accepts trust");

    // Quality metrics: trust_count > 0, is_complete() returns false.
    let quality = check_proof_with_quality(&proof, &terms).expect("quality check succeeds");
    assert_eq!(
        quality.trust_count, 1,
        "quality metrics should report the Trust step"
    );
    assert!(!quality.is_complete(), "proof with Trust is not complete");

    // Strict checker: rejects (Trust steps are forbidden).
    let err = check_proof_strict(&proof, &terms);
    assert!(
        err.is_err(),
        "strict mode must reject Trust (the consequence of missing hints)"
    );
}

/// A proof where the same learned clause avoids Trust still passes standard
/// validation, but strict mode now rejects the unvalidated theory lemma.
///
/// This is the correct behavior when resolution_hints are present.
#[test]
fn test_resolution_from_valid_hints_still_needs_strict_theory_validation() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let y = terms.mk_var("y", Sort::Bool);
    let not_x = terms.mk_not(x);
    let not_y = terms.mk_not(y);

    let mut proof = Proof::new();
    let hx = proof.add_assume(x, None);
    let hy = proof.add_assume(y, None);

    // This is what process_trace produces when hints ARE available:
    // derive_clause_from_hints builds a resolution chain.
    // We simulate the two-step resolution: resolve {x} with {y} is not
    // valid (no complementary literal), so let's use a theory lemma.
    let theory_step = proof.add_theory_lemma("LRA", vec![not_x, not_y]);

    // Resolve theory_step with hx on pivot x → {not_y}
    let r0 = proof.add_resolution(vec![not_y], x, theory_step, hx);
    // Resolve r0 with hy on pivot y → empty clause
    proof.add_resolution(vec![], y, r0, hy);

    // Standard: passes.
    check_proof(&proof, &terms).expect("standard accepts theory + resolution");

    // Quality: no explicit Trust step, but the generic theory lemma still
    // exports as trust and is counted that way by proof quality metrics.
    let quality = check_proof_with_quality(&proof, &terms).expect("quality check succeeds");
    assert_eq!(
        quality.trust_count, 1,
        "generic theory lemmas still count as trust-exported steps"
    );
    assert_eq!(quality.hole_count, 0, "no hole steps");
    assert_eq!(quality.resolution_count, 2, "two resolution steps");

    let err = check_proof_strict(&proof, &terms)
        .expect_err("strict mode rejects unvalidated theory lemmas even without Trust");
    assert!(
        matches!(
            err,
            ay_proof::ProofCheckError::UnsupportedTheoryLemmaKind { .. }
        ),
        "unexpected strict-mode error: {err:?}"
    );
}
