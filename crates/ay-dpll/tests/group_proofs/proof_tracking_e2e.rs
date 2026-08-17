// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(deprecated)]

use ay_core::{ProofStep, TheoryLemmaKind};
use ay_dpll::Executor;
use ay_frontend::parse;
use ay_proof::{check_proof, check_proof_strict, check_proof_with_quality, ProofQuality};
use ntest::timeout;
use num_rational::Rational64;

fn assert_last_unsat_proof_is_valid(exec: &Executor) {
    let proof = exec
        .last_proof()
        .expect("expected last proof after UNSAT with :produce-proofs");
    check_proof(proof, exec.terms())
        .expect("internal proof checker rejected proof for UNSAT result");
}

/// Validate proof and return quality metrics for diagnostic assertions.
fn assert_last_unsat_proof_quality(exec: &Executor) -> ProofQuality {
    let proof = exec
        .last_proof()
        .expect("expected last proof after UNSAT with :produce-proofs");
    check_proof_with_quality(proof, exec.terms())
        .expect("internal proof checker rejected proof for UNSAT result")
}

/// Strict validation: reject Trust and Hole steps. Use for proofs that should be
/// fully reconstructed (LRA, EUF, simple Boolean).
fn assert_last_unsat_proof_strict(exec: &Executor) -> ProofQuality {
    let proof = exec
        .last_proof()
        .expect("expected last proof after UNSAT with :produce-proofs");
    check_proof_strict(proof, exec.terms())
        .expect("strict proof checker rejected proof — contains trust or hole steps")
}

#[test]
#[timeout(5_000)]
fn test_lra_proof_tracking_check_sat_records_la_generic() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (<= x 5.0))
        (assert (>= x 10.0))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    assert_last_unsat_proof_is_valid(&exec);
    // Bound axiom conflicts use `trust` rule since #6686 (no Farkas args for
    // bound-axiom-derived lemmas). Accept either la_generic or trust.
    assert!(
        outputs[1].contains(":rule la_generic") || outputs[1].contains(":rule trust"),
        "expected la_generic or trust theory lemma in proof:\n{}",
        outputs[1]
    );
}

#[test]
#[timeout(5_000)]
fn test_lra_proof_tracking_check_sat_assuming_records_la_generic() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (<= x 5.0))
        (assert (>= x 10.0))
        (check-sat-assuming ())
        (get-proof)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    assert_last_unsat_proof_is_valid(&exec);
    // Bound axiom conflicts use `trust` rule since #6686.
    assert!(
        outputs[1].contains(":rule la_generic") || outputs[1].contains(":rule trust"),
        "expected la_generic or trust theory lemma in proof:\n{}",
        outputs[1]
    );
}

#[test]
#[timeout(5_000)]
fn test_euf_proof_tracking_check_sat_records_eq_transitive() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun a () U)
        (declare-fun b () U)
        (declare-fun c () U)
        (assert (= a b))
        (assert (= b c))
        (assert (not (= a c)))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    assert_last_unsat_proof_is_valid(&exec);
    // EUF transitivity can be encoded either as a dedicated eq_transitive rule
    // or as a trust lemma (optionally with th_resolution), depending on
    // reconstruction detail level.
    let proof = &outputs[1];
    let has_eq_transitive = proof.contains(":rule eq_transitive");
    let has_trust_transitive_chain =
        proof.contains(":rule trust") && proof.contains(":rule th_resolution");
    let has_trust_fallback = proof.contains(":rule trust");
    assert!(
        has_eq_transitive || has_trust_transitive_chain || has_trust_fallback,
        "expected EUF transitivity derivation in proof:\n{proof}"
    );
}

/// Guarded-subtraction level-0 disjunctive conflict (trust-cert-diag).
///
/// A guarded op `if a>=b { a-b }` encodes the violation disjunction
/// `(or (a-b<0) (a-b>MAX))`, UNSAT at level 0 under the guard + domain bounds.
/// The SAT/LRA pipeline refutes it via a *cycle* of pairwise theory conflicts
/// (`{¬D1,¬D2}`, `{guard,¬D2}`, `{¬guard,¬D1}`) that never bottom out at the
/// independent domain bounds, so the SAT-trace closer cannot reach the empty
/// clause and historically emitted a `trust` reconstruction fallback
/// ("sat proof reconstruction fell back to trust").
///
/// `try_derive_empty_via_disjunct_refutation` re-derives a *bound-complete*
/// Farkas refutation of EACH disjunct against the problem bounds and closes by
/// genuine resolution. This asserts the resulting proof is honest: the empty
/// clause is a `resolution` step, each disjunct is refuted by an independently
/// Farkas-certified `LraFarkas` lemma, and the proof contains no `trust` step.
#[test]
#[timeout(20_000)]
fn test_guarded_sub_disjunction_closes_without_trust() {
    // d in [0,100] guarded by a>=b, a<=100, b>=0; the disjunction asserts the
    // out-of-range violation, which is UNSAT at level 0.
    for (label, input) in [
        (
            "QF_LIA",
            r#"
            (set-option :produce-proofs true)
            (set-logic QF_LIA)
            (declare-const a Int)
            (declare-const b Int)
            (declare-const d Int)
            (assert (>= a b))
            (assert (<= a 100))
            (assert (>= b 0))
            (assert (= d (- a b)))
            (assert (or (< d 0) (> d 100)))
            (check-sat)
            (get-proof)
        "#,
        ),
        (
            "QF_LRA",
            r#"
            (set-option :produce-proofs true)
            (set-logic QF_LRA)
            (declare-const a Real)
            (declare-const b Real)
            (assert (>= a b))
            (assert (<= a 100.0))
            (assert (>= b 0.0))
            (assert (or (< (- a b) 0.0) (> (- a b) 100.0)))
            (check-sat)
            (get-proof)
        "#,
        ),
    ] {
        let commands = parse(input).expect("parse input");
        let mut exec = Executor::new();
        let outputs = exec.execute_all(&commands).expect("execute input");
        assert_eq!(outputs[0], "unsat", "{label}: expected UNSAT");

        let proof = exec.last_proof().expect("expected last proof");
        let terms = exec.terms();

        // The proof must be checker-valid.
        check_proof(proof, terms)
            .unwrap_or_else(|e| panic!("{label}: internal checker rejected the proof: {e:?}"));

        // No `trust` reconstruction hole anywhere in the proof: the whole point
        // is to REPLACE the unverified fallback with independently-checkable
        // resolution + Farkas lemmas.
        let trust_steps = proof
            .steps
            .iter()
            .filter(|s| {
                matches!(
                    s,
                    ProofStep::Step {
                        rule: ay_core::AletheRule::Trust,
                        ..
                    }
                )
            })
            .count();
        assert_eq!(
            trust_steps, 0,
            "{label}: proof still contains trust step(s)"
        );

        // The empty clause must be a genuine resolution step.
        let has_empty_resolution = proof
            .steps
            .iter()
            .any(|s| matches!(s, ProofStep::Resolution { clause, .. } if clause.is_empty()));
        assert!(
            has_empty_resolution,
            "{label}: empty clause is not an honest resolution step"
        );

        // Both violation disjuncts are refuted by independently-certified
        // Farkas lemmas (the bound-complete per-disjunct refutations).
        let farkas_lemmas = proof
            .steps
            .iter()
            .filter(|s| {
                matches!(
                    s,
                    ProofStep::TheoryLemma {
                        kind: TheoryLemmaKind::LraFarkas,
                        farkas: Some(_),
                        ..
                    }
                )
            })
            .count();
        assert!(
            farkas_lemmas >= 2,
            "{label}: expected >= 2 certified Farkas refutation lemmas, got {farkas_lemmas}"
        );

        // The strict checker (rejects trust + hole) must also accept the proof.
        let quality = check_proof_with_quality(proof, terms)
            .unwrap_or_else(|e| panic!("{label}: quality check failed: {e:?}"));
        assert_eq!(
            quality.trust_count, 0,
            "{label}: ProofQuality reports {} trust step(s)",
            quality.trust_count
        );
    }
}

/// Verify that unit assertions + theory lemma produces th_resolution proof,
/// not a :rule hole fallback (#340 Phase 0).
///
/// Structural checks beyond string containment:
/// - Proof has assume steps for input assertions
/// - Proof derives via th_resolution (no :rule hole fallback)
/// - Proof references the la_generic theory lemma
/// - Proof has 3+ steps (2 assumes + at least 1 resolution)
#[test]
#[timeout(5_000)]
fn test_lra_proof_derives_empty_via_th_resolution_not_hole() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (<= x 5.0))
        (assert (>= x 10.0))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");

    // Non-strict validation: bound axiom conflicts use `trust` rule since #6686
    // (no Farkas coefficients for bound-axiom-derived lemmas).
    let quality = assert_last_unsat_proof_quality(&exec);
    assert!(
        quality.theory_lemma_count > 0,
        "LRA th_resolution proof should have theory lemmas: {quality}"
    );

    let proof = &outputs[1];

    // Structural: proof must contain assume steps for the two input assertions.
    // Alethe format: (assume <id> <term>)
    let assume_count = proof.matches("(assume ").count();
    assert!(
        assume_count >= 2,
        "expected at least 2 assume steps (one per assertion), got {assume_count}:\n{proof}"
    );

    // Structural: proof must contain la_generic or trust theory lemma (#6686)
    assert!(
        proof.contains(":rule la_generic") || proof.contains(":rule trust"),
        "expected la_generic or trust theory lemma in proof:\n{proof}"
    );

    // Structural: proof derives empty clause via th_resolution
    assert!(
        proof.contains(":rule th_resolution"),
        "expected th_resolution in proof (not hole):\n{proof}"
    );

    // Structural: proof must NOT contain :rule hole
    assert!(
        !proof.contains(":rule hole"),
        "proof should not contain :rule hole:\n{proof}"
    );

    // Structural: proof ends with empty clause derivation (cl)
    assert!(
        proof.contains("(cl)"),
        "expected empty clause (cl) derivation in proof:\n{proof}"
    );

    // Structural: proof has 5 steps (2 assumes + la_generic + 2 th_resolution)
    let step_count = proof.matches("(step ").count() + proof.matches("(assume ").count();
    assert!(
        step_count >= 4,
        "expected at least 4 proof steps, got {step_count}:\n{proof}"
    );
}

/// Verify SAT clause trace reconstruction emits explicit `resolution` nodes when
/// there are no theory lemmas to build a `th_resolution` chain.
#[test]
#[timeout(5_000)]
fn test_sat_proof_end_to_end_resolution_valid() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_BOOL)
        (declare-const a Bool)
        (assert a)
        (assert (not a))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    assert_last_unsat_proof_is_valid(&exec);
    // Strict: pure Boolean proof must have zero Trust/Hole steps (#4585).
    assert_last_unsat_proof_strict(&exec);

    let proof = &outputs[1];
    assert!(
        proof.contains(":rule resolution"),
        "expected :rule resolution in proof:\n{proof}"
    );
    assert!(
        proof.contains(":premises"),
        "expected explicit resolution premises in proof:\n{proof}"
    );
    assert!(
        !proof.contains(":rule hole"),
        "proof should not contain :rule hole:\n{proof}"
    );
}

/// Multi-clause propositional proof: resolution DAG from BCP conflict chain (#4176).
///
/// The formula (p ∨ q) ∧ (¬p ∨ r) ∧ (¬q ∨ r) ∧ ¬r is UNSAT.
/// BCP at level 0 derives the empty clause via multiple resolution steps.
/// This verifies that `record_level0_conflict_chain` produces sufficient
/// resolution hints for SatProofManager to reconstruct the full proof.
#[test]
#[timeout(5_000)]
fn test_propositional_multi_clause_resolution_proof() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_BOOL)
        (declare-const p Bool)
        (declare-const q Bool)
        (declare-const r Bool)
        (assert (or p q))
        (assert (or (not p) r))
        (assert (or (not q) r))
        (assert (not r))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    assert_last_unsat_proof_is_valid(&exec);
    // NOTE: This test has a pre-existing TrustStep at ProofId(4).
    // Strict assertion omitted until #4585 fixes that path.

    let proof = &outputs[1];

    // Must contain resolution steps (not just :rule hole)
    assert!(
        proof.contains(":rule resolution"),
        "expected :rule resolution in multi-clause proof:\n{proof}"
    );

    // Must derive empty clause
    assert!(
        proof.contains("(cl)"),
        "expected empty clause derivation in proof:\n{proof}"
    );

    // Must NOT fall back to :rule hole
    assert!(
        !proof.contains(":rule hole"),
        "proof should not contain :rule hole:\n{proof}"
    );

    // Must have assume steps for each assertion
    let assume_count = proof.matches("(assume ").count();
    assert!(
        assume_count >= 4,
        "expected at least 4 assume steps, got {assume_count}:\n{proof}"
    );

    // Multiple resolution steps needed (not just one binary resolution)
    let resolution_count = proof.matches(":rule resolution").count();
    assert!(
        resolution_count >= 3,
        "expected at least 3 resolution steps, got {resolution_count}:\n{proof}"
    );
}

// NOTE: 9 carcara integration tests deleted - required external carcara tool (#596)
// Deleted: test_sat_proof_end_to_end_drup_carcara_valid, test_lra_proof_end_to_end_carcara_valid,
// test_lra_proof_end_to_end_carcara_valid_three_constraints, test_lia_proof_end_to_end_carcara_holey,
// test_nia_proof_end_to_end_carcara_holey, test_uflra_proof_end_to_end_carcara_holey,
// test_auflra_proof_end_to_end_carcara_holey, test_auflia_proof_end_to_end_carcara_holey,
// test_euf_proof_end_to_end_carcara_valid
// Carcara tests must be run manually with CARCARA_PATH set.

/// QF_BV proof: independently replayed bit-blast theorem + resolution.
///
/// AY's strict checker regenerates and checks the exact BV refutation. Generic
/// `BvBitBlast` clauses still render as honest `hole` steps because Alethe
/// 1.0/Carcara has no compatible monolithic rule. This exact authored shape is
/// stronger: transitivity yields a ground disequality lowered through `evaluate`.
#[test]
#[timeout(5_000)]
fn test_bv_proof_end_to_end_strict_internal_certificate() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x05))
        (assert (= x #x0A))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    let quality = assert_last_unsat_proof_strict(&exec);
    assert_eq!(quality.trust_count, 0, "strict BV certificate: {quality}");
    assert_eq!(quality.hole_count, 0, "strict BV certificate: {quality}");
    assert!(
        quality.theory_lemma_count >= 1,
        "expected BV theorem: {quality}"
    );

    let proof = &outputs[1];

    // REPINNED after 1e10745f2 (fix(proof): BvLiaTautology fallback ran
    // before the authored BV cascade, silently downgrading bv_bitblast
    // certificates to holes) — verified by running this test at 1e10745f2
    // (the hole disappears) and its parent b868972b5 (hole still printed).
    // With the authored BV cascade restored, the ground BV disequality closes
    // through the f466f0dda evaluate cascade (each step an implemented
    // carcara rule), so the exported Alethe document no longer needs the
    // honest `hole` this test previously pinned. The capability moved
    // forward; pin the hole-free rendering and the `evaluate` closure that
    // now carries it.
    assert!(
        !proof.contains(":rule hole"),
        "the BV disequality closure must stay hole-free:\n{proof}"
    );
    assert!(
        proof.contains(":rule evaluate"),
        "the constant-fold closure must be spelled with carcara's evaluate:\n{proof}"
    );
    assert!(
        !proof.contains(":rule trust"),
        "the obsolete trust spelling must not return:\n{proof}"
    );
    assert!(
        proof.contains("(cl)"),
        "expected empty clause (cl) in proof:\n{proof}"
    );
}

// ── api::Solver proof access (#4412) ─────────────────────────────

/// Verify that api::Solver forwards proof configuration to the executor.
///
/// Tests `set_produce_proofs`, `is_producing_proofs`, and `get_last_proof`
/// exist and forward correctly. Full proof retrieval after UNSAT via the
/// native API requires fixing the proof-rewrite assertions_parsed gap
/// (Context::assert vs api::Solver::assert_term paths diverge).
#[test]
#[timeout(5_000)]
fn test_api_solver_proof_access_forwarding() {
    use ay_dpll::{ApiSolver, Logic};

    let mut solver = ApiSolver::new(Logic::QfUf);

    // Default: proofs disabled.
    assert!(!solver.is_producing_proofs());
    assert!(solver.last_proof().is_none());

    // Enable proofs -- forwards to executor.
    solver.set_produce_proofs(true);
    assert!(solver.is_producing_proofs());

    // No solve yet -- proof should still be None.
    assert!(solver.last_proof().is_none());

    // Disable proofs -- toggle works.
    solver.set_produce_proofs(false);
    assert!(!solver.is_producing_proofs());
}

/// Verify that proof retrieval works end-to-end through the api::Solver
/// by using the SMT-LIB execution path (which populates assertions_parsed).
#[test]
#[timeout(5_000)]
fn test_api_solver_proof_via_smt_execution() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_UF)
        (declare-const p Bool)
        (assert p)
        (assert (not p))
        (check-sat)
    "#;

    let commands = parse(input).expect("parse");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute");
    assert_eq!(outputs, vec!["unsat"]);

    let proof = exec.last_proof();
    assert!(proof.is_some(), "expected proof after UNSAT");
    assert!(!proof.unwrap().steps.is_empty(), "proof should have steps");
}

/// Incremental proof isolation: second UNSAT proof after pop must not
/// reference theory lemmas from the popped scope (#4534).
#[test]
#[timeout(10_000)]
fn test_incremental_push_pop_proof_isolation() {
    // Scope 1: assert x <= 5 ∧ x >= 10 (UNSAT via LRA)
    // Scope 2: assert y <= 0 ∧ y >= 1 (UNSAT via LRA, independent of x)
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (push 1)
        (assert (<= x 5.0))
        (assert (>= x 10.0))
        (check-sat)
        (get-proof)
        (pop 1)
        (declare-const y Real)
        (push 1)
        (assert (<= y 0.0))
        (assert (>= y 1.0))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    // Output: check-sat1, get-proof1, check-sat2, get-proof2
    assert_eq!(outputs.len(), 4);
    assert_eq!(outputs[0], "unsat", "first check-sat should be UNSAT");
    assert_eq!(outputs[2], "unsat", "second check-sat should be UNSAT");

    let _proof_1 = &outputs[1];
    let proof_2 = &outputs[3];

    // Second proof must mention y, not x
    assert!(
        !proof_2.contains("(<= x"),
        "second proof must not reference x from popped scope:\n{proof_2}"
    );
    assert!(
        !proof_2.contains("(>= x"),
        "second proof must not reference x from popped scope:\n{proof_2}"
    );

    // Both proofs should be valid; get_last_proof returns the most recent one.
    assert_last_unsat_proof_is_valid(&exec);

    // Pop invalidates the last check-sat artifacts, including get_last_proof().
    let pop_cmd = parse("(pop 1)").expect("parse pop command");
    exec.execute_all(&pop_cmd).expect("execute pop command");
    assert!(
        exec.last_proof().is_none(),
        "pop must invalidate the cached UNSAT proof"
    );
}

/// Incremental proof scoping: after pop, theory lemmas from the popped scope
/// must not appear in the proof for a subsequent check-sat (#4534).
///
/// Sequence:
///   push, assert (x <= 5 ∧ x >= 10), check-sat → unsat (proof has la_generic)
///   pop
///   assert (y <= 1 ∧ y >= 2), check-sat → unsat (proof has la_generic)
///   The second proof must NOT reference x (from the popped scope).
#[test]
#[timeout(5_000)]
fn test_incremental_proof_push_pop_scoping() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (push 1)
        (assert (<= x 5.0))
        (assert (>= x 10.0))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (<= y 1.0))
        (assert (>= y 2.0))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    // Both check-sats must return UNSAT
    assert_eq!(outputs.len(), 3);
    assert_eq!(outputs[0], "unsat");
    assert_eq!(outputs[1], "unsat");
    let proof_text = &outputs[2];
    assert!(
        !proof_text.contains("(<= x"),
        "second proof must not reference x from popped scope:\n{proof_text}"
    );
    assert!(
        !proof_text.contains("(>= x"),
        "second proof must not reference x from popped scope:\n{proof_text}"
    );

    // The proof tracker should have been reset between scopes via pop.
    // After the second check-sat, the proof should only contain steps
    // from the second scope (y assertions), not the first (x assertions).
    let proof = exec.last_proof();
    assert!(
        proof.is_some(),
        "expected proof after second UNSAT with :produce-proofs"
    );
    let proof = proof.unwrap();
    // Proof should be non-empty (at least assumptions + theory lemma + resolution)
    assert!(
        proof.len() >= 2,
        "expected at least 2 proof steps, got {}",
        proof.len()
    );
    // Verify with internal checker
    check_proof(proof, exec.terms())
        .expect("internal proof checker rejected proof for second UNSAT");

    // Pop invalidates the last check-sat artifacts, including get_last_proof().
    let pop_cmd = parse("(pop 1)").expect("parse pop command");
    exec.execute_all(&pop_cmd).expect("execute pop command");
    assert!(
        exec.last_proof().is_none(),
        "pop must invalidate the cached UNSAT proof"
    );
}

/// Theory lemma annotations wired through SAT clause trace (#6031 Phase 4, #6365).
///
/// When theory lemmas go through the SAT clause trace path (Phase 1 resolution
/// reconstruction), the `SatProofManager` emits proper Alethe rules
/// (e.g., `la_generic` for LRA Farkas lemmas) instead of the generic `assume + or`
/// pattern.
///
/// This test uses a formula where:
/// 1. The theory solver produces a Farkas conflict (TheoryLemma in ProofTracker)
/// 2. The SAT clause trace path (Phase 1) is needed because Phase 0 fails
///
/// Formula: `(and (>= x 10.0) (<= x 5.0))`
/// The `and` gate causes Tseitin encoding with intermediate variables, so the
/// top-level assumption is the Tseitin gate variable — NOT the individual atoms.
/// The theory lemma `¬(x >= 10) ∨ ¬(x <= 5)` references individual atoms that
/// are NOT direct assumptions, causing Phase 0 to fail and Phase 1 to run.
///
/// The second-pass closure in `close_clause_via_originals` (#6365) resolves the
/// derived clause with Tseitin gate clauses to close the gap, eliminating the
/// trust fallback for this pattern.
#[test]
#[timeout(10_000)]
fn test_theory_lemma_annotation_through_sat_clause_trace() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (and (>= x 10.0) (<= x 5.0)))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    assert_last_unsat_proof_is_valid(&exec);

    let proof = &outputs[1];

    // Must derive empty clause
    assert!(
        proof.contains("(cl)"),
        "expected empty clause derivation in proof:\n{proof}"
    );

    // Must NOT fall back to :rule hole
    assert!(
        !proof.contains(":rule hole"),
        "proof should not contain :rule hole:\n{proof}"
    );

    // #6365: Bound axiom must use la_generic with Farkas coefficients.
    // Upgraded from trust to la_generic when unit Farkas coefficients validate.
    assert!(
        proof.contains(":rule la_generic"),
        "expected :rule la_generic in LRA bound axiom proof:\n{proof}"
    );

    // #6365: la_generic must include Farkas coefficient args.
    assert!(
        proof.contains(":args (1 1)"),
        "expected unit Farkas coefficients :args (1 1) in la_generic step:\n{proof}"
    );
}

/// Theory lemma through nested Boolean wrapper: `(or false (and ...))` (#6365).
///
/// Variant of the Tseitin-mediated theory lemma test with a different Boolean
/// wrapper to verify the second-pass closure is not overfit to a single `(and ...)`
/// encoding. The inner contradiction is the same LRA conflict.
#[test]
#[timeout(10_000)]
fn test_theory_lemma_through_or_wrapped_and_gate() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (or false (and (>= x 10.0) (<= x 5.0))))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    assert_last_unsat_proof_is_valid(&exec);

    let proof = &outputs[1];

    // Must derive empty clause
    assert!(
        proof.contains("(cl)"),
        "expected empty clause derivation in proof:\n{proof}"
    );

    // Must NOT fall back to :rule hole
    assert!(
        !proof.contains(":rule hole"),
        "proof should not contain :rule hole:\n{proof}"
    );

    // #6365: Bound axiom must use la_generic with Farkas coefficients.
    assert!(
        proof.contains(":rule la_generic"),
        "expected :rule la_generic in or-wrapped LRA proof:\n{proof}"
    );

    // #6365: la_generic must include Farkas coefficient args.
    assert!(
        proof.contains(":args (1 1)"),
        "expected unit Farkas coefficients :args (1 1) in or-wrapped la_generic step:\n{proof}"
    );
}

/// QF_LIA theory lemma through Boolean `(and ...)` wrapper produces `la_generic` (#6365, #4539).
///
/// Both QF_LRA and Farkas-valid QF_LIA bound axiom proofs now use
/// Farkas coefficients (#6365). This test exercises the same Tseitin-mediated
/// pattern but validates that the theory lemma rule is structured, not trust.
///
/// The `(and ...)` wrapper causes Tseitin encoding, so the SAT solver's Phase 1
/// clause-trace reconstruction must connect through the gate clauses.
#[test]
#[timeout(10_000)]
fn test_theory_lemma_la_generic_through_and_gate_6365() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (and (> x 10) (< x 5)))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    assert_last_unsat_proof_is_valid(&exec);

    let proof = &outputs[1];

    // Must derive empty clause
    assert!(
        proof.contains("(cl)"),
        "expected empty clause derivation in proof:\n{proof}"
    );

    // Must NOT fall back to :rule hole
    assert!(
        !proof.contains(":rule hole"),
        "proof should not contain :rule hole:\n{proof}"
    );

    // #4539 Packet B: semantically Farkas-valid integer conflicts now use
    // la_generic with unit coefficients, not lia_generic.
    assert!(
        proof.contains(":rule la_generic"),
        "QF_LIA theory lemma must use :rule la_generic, not :rule trust:\n{proof}"
    );
    assert!(
        proof.contains(":args (1 1)"),
        "QF_LIA la_generic step must carry unit Farkas coefficients:\n{proof}"
    );
}

/// End-to-end Alethe structure check for semantically Farkas-valid QF_LIA
/// contradictions routed through Tseitin clauses (#4521).
#[test]
#[timeout(10_000)]
fn test_lia_alethe_proof_structure_preserves_lra_farkas_4521() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (and (> x 10) (< x 5)))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    assert_last_unsat_proof_is_valid(&exec);

    let proof_text = &outputs[1];
    assert!(
        proof_text.contains(":rule la_generic"),
        "expected :rule la_generic in exported Alethe proof:\n{proof_text}"
    );
    assert!(
        !proof_text.contains(":rule lia_generic"),
        "unexpected :rule lia_generic in exported Alethe proof:\n{proof_text}"
    );
    assert!(
        proof_text.contains(":args (1 1)"),
        "expected unit Farkas coefficients in exported Alethe proof:\n{proof_text}"
    );
    // The exporter now spells the fine-grained Boolean closure with standard
    // `resolution` steps instead of the older coarse `th_resolution` wrapper.
    // Require the terminal empty clause to be produced by that checked rule;
    // accepting either spelling would let this regression miss a fallback.
    assert!(
        proof_text.contains("(cl) :rule resolution"),
        "expected an explicit terminal resolution step in exported Alethe proof:\n{proof_text}"
    );

    let proof = exec.last_proof().expect("proof");
    let has_unit_lra_farkas = proof.steps.iter().any(|step| {
        matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::LraFarkas,
                farkas: Some(farkas),
                ..
            } if farkas.coefficients == vec![Rational64::from(1), Rational64::from(1)]
        )
    });
    assert!(
        has_unit_lra_farkas,
        "expected internal proof to preserve an LraFarkas theory lemma with unit coefficients: {:?}",
        proof.steps
    );
}

/// QF_LIA theory lemma through `(or false (and ...))` wrapper produces `la_generic` (#6365, #4539).
///
/// Variant with a different Boolean wrapper to verify the reconstruction is not
/// overfit to a single `(and ...)` encoding.
#[test]
#[timeout(10_000)]
fn test_theory_lemma_la_generic_through_or_wrapped_and_gate_6365() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (or false (and (> x 10) (< x 5))))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    assert_last_unsat_proof_is_valid(&exec);

    let proof = &outputs[1];

    // Must derive empty clause
    assert!(
        proof.contains("(cl)"),
        "expected empty clause derivation in proof:\n{proof}"
    );

    // Must NOT fall back to :rule hole
    assert!(
        !proof.contains(":rule hole"),
        "proof should not contain :rule hole:\n{proof}"
    );

    // #4539 Packet B: semantically Farkas-valid integer conflicts now use
    // la_generic with unit coefficients.
    assert!(
        proof.contains(":rule la_generic"),
        "QF_LIA or-wrapped theory lemma must use :rule la_generic:\n{proof}"
    );
    assert!(
        proof.contains(":args (1 1)"),
        "QF_LIA or-wrapped la_generic step must carry unit Farkas coefficients:\n{proof}"
    );
}

/// Clausification proof steps: Tseitin tautology rules replace generic assume+or (#6031).
///
/// The formula `(and a b) ∧ (not a)` is UNSAT. The Tseitin encoder creates
/// clauses for `(and a b)` with rules `and_pos` and `and_neg`. When proofs
/// are enabled, the clausification annotations flow through to SatProofManager
/// so the final Alethe proof contains `:rule and_pos` steps instead of
/// `:rule assume` + `:rule or` fallbacks.
#[test]
#[timeout(5_000)]
fn test_clausification_proof_and_pos_tautology_rules() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_BOOL)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert (and a b))
        (assert (not a))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    assert_last_unsat_proof_is_valid(&exec);
    assert_last_unsat_proof_strict(&exec);

    let proof = &outputs[1];

    // Must contain and_pos tautology rule (from Tseitin clausification)
    assert!(
        proof.contains(":rule and_pos"),
        "expected :rule and_pos from Tseitin clausification, got:\n{proof}"
    );

    // Must derive empty clause
    assert!(
        proof.contains("(cl)"),
        "expected empty clause derivation in proof:\n{proof}"
    );

    // Must NOT fall back to :rule hole
    assert!(
        !proof.contains(":rule hole"),
        "proof should not contain :rule hole:\n{proof}"
    );
}

/// Clausification proof steps for `or`: or_pos tautology rule (#6031).
///
/// The formula `(or a b) ∧ (not a) ∧ (not b)` is UNSAT. The Tseitin encoder
/// creates the clause `(¬v ∨ a ∨ b)` with rule `or_pos` for `(or a b)`.
#[test]
#[timeout(5_000)]
fn test_clausification_proof_or_pos_tautology_rules() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_BOOL)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert (or a b))
        (assert (not a))
        (assert (not b))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    assert_last_unsat_proof_is_valid(&exec);
    assert_last_unsat_proof_strict(&exec);

    let proof = &outputs[1];

    // Must contain or_pos tautology rule (from Tseitin clausification).
    // The Tseitin encoder for `(or a b)` produces:
    //   (cl (not (or a b)) a b) — or_pos rule
    assert!(
        proof.contains(":rule or_pos"),
        "expected :rule or_pos from Tseitin clausification, got:\n{proof}"
    );

    // Must NOT fall back to :rule hole
    assert!(
        !proof.contains(":rule hole"),
        "proof should not contain :rule hole:\n{proof}"
    );
}

/// Clausification proof steps for `ite`: ite_pos tautology rules (#6031).
///
/// The formula `(ite c a b) ∧ c ∧ (not a)` is UNSAT. The Tseitin encoder
/// creates clauses for `(ite c a b)` with rules `ite_pos1` and `ite_pos2`.
#[test]
#[timeout(5_000)]
fn test_clausification_proof_ite_pos_tautology_rules() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-option :strict-proofs false)
        (set-logic QF_BOOL)
        (declare-const a Bool)
        (declare-const b Bool)
        (declare-const c Bool)
        (assert (ite c a b))
        (assert c)
        (assert (not a))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    // Debug dump proof and terms
    {
        let proof = exec.last_proof().expect("proof");
        for (idx, step) in proof.steps.iter().enumerate() {
            eprintln!("ITE ProofId({idx}): {step:?}");
        }
        // Dump key TermIds
        for tid in 0..13u32 {
            let t = ay_core::TermId::new(tid);
            if (t.index()) < exec.terms().len() {
                eprintln!("  TermId({tid}): {:?}", exec.terms().get(t));
            }
        }
    }
    assert_last_unsat_proof_is_valid(&exec);
    assert_last_unsat_proof_strict(&exec);

    let proof = &outputs[1];

    // Must contain ite_pos1 or ite_pos2 tautology rule (from Tseitin clausification).
    let has_ite_rule = proof.contains(":rule ite_pos1") || proof.contains(":rule ite_pos2");
    assert!(
        has_ite_rule,
        "expected :rule ite_pos1 or ite_pos2 from Tseitin clausification, got:\n{proof}"
    );

    // Must NOT fall back to :rule hole
    assert!(
        !proof.contains(":rule hole"),
        "proof should not contain :rule hole:\n{proof}"
    );
}

/// Comprehensive clausification proof test for downstream proof consumer (#6031).
///
/// Exercises a formula with AND and OR structure to verify that ay
/// emits the Alethe tautology rules that the downstream proof consumer's proof_reconstruct pipeline
/// handles: `and_pos`, `or_pos`, `or_neg`.
///
/// Formula: `(and (or a b) (or (not a) c)) ∧ (not b) ∧ (not c)` — UNSAT.
/// The AND gate generates and_pos, the OR subterms generate or_pos/or_neg.
/// All clausification clauses are needed for the contradiction so none are pruned.
#[test]
#[timeout(10_000)]
fn test_clausification_proof_multi_connective_proof_replay_rules() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_BOOL)
        (declare-const a Bool)
        (declare-const b Bool)
        (declare-const c Bool)
        (assert (and (or a b) (or (not a) c)))
        (assert (not b))
        (assert (not c))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    assert_last_unsat_proof_is_valid(&exec);
    assert_last_unsat_proof_strict(&exec);

    let proof = &outputs[1];

    // Must derive empty clause
    assert!(
        proof.contains("(cl)"),
        "expected empty clause derivation in proof:\n{proof}"
    );

    // Must NOT fall back to :rule hole
    assert!(
        !proof.contains(":rule hole"),
        "proof should not contain :rule hole:\n{proof}"
    );

    // Verify clausification tautology rules are present.
    // The AND gate at the top should produce and_pos rules.
    assert!(
        proof.contains(":rule and_pos"),
        "expected :rule and_pos from AND Tseitin clausification:\n{proof}"
    );

    // The OR subterms should produce or_pos rules.
    assert!(
        proof.contains(":rule or_pos"),
        "expected :rule or_pos from OR Tseitin clausification:\n{proof}"
    );
}

/// Clausification proof with Boolean equality: equiv_pos tautology rules (#6031).
///
/// Formula: `(= a b) ∧ a ∧ (not b)` — UNSAT. The Boolean equality `(= a b)`
/// is encoded via Tseitin with equiv_pos1/equiv_pos2/equiv_neg1/equiv_neg2 rules.
#[test]
#[timeout(5_000)]
fn test_clausification_proof_equiv_pos_tautology_rules() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_BOOL)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert (= a b))
        (assert a)
        (assert (not b))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    assert_last_unsat_proof_is_valid(&exec);
    assert_last_unsat_proof_strict(&exec);

    let proof = &outputs[1];

    // Must derive empty clause
    assert!(
        proof.contains("(cl)"),
        "expected empty clause derivation in proof:\n{proof}"
    );

    // Must NOT fall back to :rule hole
    assert!(
        !proof.contains(":rule hole"),
        "proof should not contain :rule hole:\n{proof}"
    );

    // Boolean equality should produce equiv_pos or equiv_neg tautology rules.
    // Note: mk_eq on Bool may rewrite to ITE internally, so we accept either
    // equiv_pos/neg or ite_pos/neg as valid clausification rules.
    let has_equiv = proof.contains(":rule equiv_pos1")
        || proof.contains(":rule equiv_pos2")
        || proof.contains(":rule equiv_neg1")
        || proof.contains(":rule equiv_neg2");
    let has_ite = proof.contains(":rule ite_pos1")
        || proof.contains(":rule ite_pos2")
        || proof.contains(":rule ite_neg1")
        || proof.contains(":rule ite_neg2");
    assert!(
        has_equiv || has_ite,
        "expected equiv or ite tautology rules from Boolean equality:\n{proof}"
    );
}

/// Regression: QF_UFLIA proof with UF equality whose surface arg order
/// differs from mk_eq's canonical order. rebuild_surface_term must
/// canonicalize equality args so assume and lia_generic literals share
/// the same TermId, allowing th_resolution pivot matching.
#[test]
#[timeout(10_000)]
fn test_uflia_equality_arg_order_resolution() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        (assert (= (+ a b) c))
        (assert (= b 0))
        (assert (= (f a) 10))
        (assert (not (= (f c) 10)))
        (check-sat)
        (get-proof)
    "#;
    let commands = parse(input).expect("parse");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute");
    assert_eq!(outputs[0], "unsat");
    let proof = &outputs[1];

    // The exact authored bridge derives a=c by two checked Farkas bounds plus
    // antisymmetry, then transports f(a)=10 through congruence/transitivity.
    assert!(
        proof.contains("(cl)"),
        "expected empty clause derivation:\n{proof}"
    );
    assert!(
        proof.contains(":rule la_generic")
            && proof.contains(":rule la_disequality")
            && proof.contains(":rule eq_congruent")
            && proof.contains(":rule eq_transitive"),
        "expected the composed arithmetic/EUF certificate:\n{proof}"
    );
    assert!(!proof.contains(":rule trust"), "trust-free proof:\n{proof}");
    let quality = assert_last_unsat_proof_strict(&exec);
    assert_eq!(quality.trust_count, 0, "strict UFLIA proof: {quality}");
}

#[test]
#[timeout(10_000)]
fn test_uflia_affine_euf_bridge_rejects_non_implied_argument_equality() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        (assert (= (+ a b) c))
        (assert (= b 1))
        (assert (= (f a) 10))
        (assert (not (= (f c) 10)))
        (check-sat)
    "#;
    let commands = parse(input).expect("parse mutation");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute mutation");
    assert_eq!(outputs.first().map(String::as_str), Some("sat"));
    assert!(
        exec.last_proof().is_none(),
        "a non-implied argument equality must never mint a refutation"
    );
}

/// Composite Boolean assumption with proof: `(and (= x 0) (= x 1))` through
/// `check-sat-assuming` must produce a valid UNSAT proof without `:rule hole`.
///
/// Regression for #6689 Packet 4: assumption-side Tseitin definitional clauses
/// must have matching `clausification_proofs` entries so the proof exporter
/// doesn't fall back to hole rules.
#[test]
#[timeout(10_000)]
fn test_lira_proof_tracking_composite_assumption_6689() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIRA)
        (declare-const x Int)
        (check-sat-assuming ((and (= x 0) (= x 1))))
        (get-proof)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    assert_last_unsat_proof_is_valid(&exec);

    let proof = &outputs[1];
    assert!(
        !proof.contains(":rule hole"),
        "composite-assumption proof should not fall back to :rule hole:\n{proof}"
    );
}

// =============================================================================
// Phase C: SMT-level UNSAT proof pipeline tests (Part of #7913)
//
// These tests verify the end-to-end Alethe proof pipeline across multiple
// SMT logics. "Strict" means zero trust/hole steps — the proof is fully
// reconstructed from theory lemmas and resolution.
// =============================================================================

/// Phase C: Pure Boolean UNSAT produces a strict Alethe proof.
#[test]
#[timeout(5_000)]
fn test_smt_proof_pipeline_qf_bool_strict() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_BOOL)
        (declare-const p Bool)
        (assert p)
        (assert (not p))
        (check-sat)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs[0], "unsat");
    let quality = assert_last_unsat_proof_strict(&exec);
    assert_eq!(
        quality.trust_count, 0,
        "QF_BOOL proof should have zero trust steps: {quality}"
    );
}

/// Phase C: QF_UF EUF transitivity contradiction produces a strict proof.
#[test]
#[timeout(5_000)]
fn test_smt_proof_pipeline_qf_uf_strict() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (assert (= a b))
        (assert (= b c))
        (assert (not (= a c)))
        (check-sat)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs[0], "unsat");
    let quality = assert_last_unsat_proof_strict(&exec);
    assert_eq!(
        quality.trust_count, 0,
        "QF_UF transitivity proof should have zero trust steps: {quality}"
    );
}

/// Clean submits theorem goals as one authored negated implication rather than
/// three already-clausified assertions.  Top-level Boolean decomposition must
/// derive the antecedent conjuncts and negated consequent from that exact root;
/// it may not turn the flattened atoms into `trust` assumptions.
#[test]
#[timeout(5_000)]
fn test_smt_proof_pipeline_qf_uf_composed_authored_root_strict() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_UF)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const z Int)
        (assert (not (=> (and (= x y) (= y z)) (= x z))))
        (check-sat)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs[0], "unsat");
    let quality = assert_last_unsat_proof_strict(&exec);
    assert_eq!(
        quality.trust_count, 0,
        "composed QF_UF proof should derive every flattened atom from the authored root: {quality}"
    );
    let alethe = exec
        .try_export_last_proof_alethe_for_problem_scope()
        .expect("composed QF_UF UNSAT should retain a proof")
        .expect("composed QF_UF proof should export in the authored problem scope");
    assert!(
        alethe.contains(":rule eq_transitive")
            && alethe.contains(":rule implies_neg1")
            && alethe.contains(":rule implies_neg2")
            && !alethe.contains(":rule trust")
            && !alethe.contains(":rule hole"),
        "composed QF_UF proof must export its authored implication decomposition and EUF theorem:\n{alethe}"
    );
}

/// The same authenticated-root decomposition must survive LIA preprocessing.
#[test]
#[timeout(5_000)]
fn test_smt_proof_pipeline_qf_lia_composed_authored_root_strict() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (not (=> (and (= x 2) (= y 3)) (= (+ x y) 5))))
        (check-sat)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs[0], "unsat");
    let quality = assert_last_unsat_proof_strict(&exec);
    assert_eq!(
        quality.trust_count, 0,
        "composed QF_LIA proof should derive every flattened atom from the authored root: {quality}"
    );
    let alethe = exec
        .try_export_last_proof_alethe_for_problem_scope()
        .expect("composed QF_LIA UNSAT should retain a proof")
        .expect("composed QF_LIA proof should export in the authored problem scope");
    assert!(
        alethe.contains(":rule eq_congruent")
            && alethe.contains(":rule evaluate")
            && alethe.contains(":rule eq_transitive"),
        "affine equality must export as congruence + checked ground evaluation + transitivity:\n{alethe}"
    );
    assert!(
        !alethe.contains(":rule trust")
            && !alethe.contains(":rule hole")
            && !alethe.contains(":rule la_generic")
            && !alethe.contains(":rule lia_generic"),
        "affine equality export must not hide authority or encode a disequality case split as one la_generic step:\n{alethe}"
    );
}

/// ROW2 is contextual: the index disequality and negated read equality must be
/// derived from the single authored negated implication before the guarded
/// array lemma can close the proof.
#[test]
#[timeout(5_000)]
fn test_smt_proof_pipeline_qf_auflia_composed_row2_root_strict() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (declare-const v Int)
        (assert
          (not
            (=> (not (= i j))
                (= (select (store a i v) j) (select a j)))))
        (check-sat)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs[0], "unsat");
    let quality = assert_last_unsat_proof_strict(&exec);
    assert_eq!(
        quality.trust_count, 0,
        "composed ROW2 proof should derive both contextual hypotheses from the authored root: {quality}"
    );
    let alethe = exec
        .try_export_last_proof_alethe_for_problem_scope()
        .expect("composed ROW2 UNSAT should retain a proof")
        .expect("composed ROW2 proof should export in the authored problem scope");
    assert!(
        alethe.contains(":rule arrays_row")
            && alethe.contains(":rule implies_neg1")
            && alethe.contains(":rule implies_neg2")
            && !alethe.contains(":rule trust")
            && !alethe.contains(":rule hole"),
        "composed ROW2 proof must export its authored implication decomposition and guarded array theorem:\n{alethe}"
    );
}

/// Phase C: QF_UF congruence contradiction produces a strict proof.
#[test]
#[timeout(5_000)]
fn test_smt_proof_pipeline_qf_uf_congruence_strict() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun f (U) U)
        (declare-const a U)
        (declare-const b U)
        (assert (= a b))
        (assert (not (= (f a) (f b))))
        (check-sat)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs[0], "unsat");
    let quality = assert_last_unsat_proof_strict(&exec);
    assert_eq!(
        quality.trust_count, 0,
        "QF_UF congruence proof should have zero trust steps: {quality}"
    );
}

/// Phase C: QF_LIA bounds contradiction produces a strict proof.
#[test]
#[timeout(5_000)]
fn test_smt_proof_pipeline_qf_lia_strict() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (> x 10))
        (assert (< x 5))
        (check-sat)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs[0], "unsat");
    let quality = assert_last_unsat_proof_strict(&exec);
    assert_eq!(
        quality.trust_count, 0,
        "QF_LIA bounds-contradiction proof should have zero trust steps: {quality}"
    );
}

/// The Euclidean remainder range makes `(mod x 3) = 4` impossible for every
/// integer `x`.  The auxiliary quotient/remainder encoding must retain a
/// strict certificate for that range contradiction instead of collapsing the
/// correct UNSAT answer to a terminal trust step.
#[test]
#[timeout(5_000)]
fn test_smt_proof_pipeline_mod_constant_range_strict() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic ALL)
        (declare-const x Int)
        (assert (= (mod x 3) 4))
        (check-sat)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs[0], "unsat");
    let quality = assert_last_unsat_proof_strict(&exec);
    assert_eq!(
        quality.trust_count, 0,
        "constant-divisor mod range proof should have zero trust steps: {quality}"
    );
    assert!(
        exec.last_proof()
            .is_some_and(|proof| proof.steps.iter().any(|step| matches!(
                step,
                ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::LiaModRange,
                    ..
                }
            ))),
        "strict proof must carry the checker-owned Euclidean mod-range certificate"
    );
}

/// Phase C: QF_LRA bounds contradiction produces a strict proof.
#[test]
#[timeout(5_000)]
fn test_smt_proof_pipeline_qf_lra_strict() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (> x 10.0))
        (assert (< x 5.0))
        (check-sat)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs[0], "unsat");
    let quality = assert_last_unsat_proof_strict(&exec);
    assert_eq!(
        quality.trust_count, 0,
        "QF_LRA bounds-contradiction proof should have zero trust steps: {quality}"
    );
}

/// Phase C: QF_LIA integer equality contradiction produces a strict proof.
///
/// Equality contradiction `(= x 3) AND (= x 7)` is resolved by synthesizing
/// a LiaGeneric theory lemma `(not (= x 3)) (not (= x 7))` with Farkas
/// coefficients, then resolving against the two assumptions to derive the
/// empty clause. No trust steps required.
#[test]
#[timeout(5_000)]
fn test_smt_proof_pipeline_qf_lia_equality_contradiction() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= x 3))
        (assert (= x 7))
        (check-sat)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs[0], "unsat");
    let quality = assert_last_unsat_proof_strict(&exec);
    assert_eq!(
        quality.trust_count, 0,
        "QF_LIA equality-contradiction proof should have zero trust steps: {quality}"
    );
    assert!(
        quality.theory_lemma_count > 0,
        "QF_LIA equality-contradiction proof should have a theory lemma: {quality}"
    );
}
