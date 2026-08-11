// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Producer-side tests for the complementary-literal propositional closure
//! (`try_rebuild_with_complementary_literals` in `proof_original_rebuild.rs`).
//!
//! The level-0 EUF/interned-enum root-conflict class: the assertion set
//! contradicts SYNTACTICALLY (a conjunct `p` in one assertion, `(not p)` in
//! another), ay-dpll's preprocessor folds the whole problem to `false`, and
//! the exported proof degenerates to a terminal trust-⊥ no Farkas backbone
//! can replace (a disequality is not a Farkas premise). The rebuild re-proves
//! `∅` from the ORIGINAL assertions with ONLY strictly-validated rules —
//! `assume`, `and_pos`, `or`, `resolution` — so the proof is theory-
//! independent and checkable offline.
//!
//! This is the model-checker consumer `certify-all-n` string-enum TypeOK wall (glowingRaccoon
//! conjunct 1, `tee \in {"Warm","Hot","TooHot"}` int-coded): initiation is
//! `Init ∧ ¬J` = `(and (= tee c) ..)` against `(and (not (= tee c)) ..)`;
//! consecution is `or`-of-actions each pinning the enum var against a `¬J'`
//! conjunct; safety is the `or`-of-equalities J against the `¬J` conjunction.

use ay_dpll::Executor;
use ay_frontend::parse;
use ay_proof::{check_proof_strict, ProofQuality};
use ntest::timeout;

/// Solve an UNSAT script with proofs enabled; return the executor and the
/// rendered Alethe text.
fn solve_unsat(script: &str) -> (Executor, String) {
    let commands = parse(script).expect("parse SMT-LIB script");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute SMT-LIB script");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "expected UNSAT, got {outputs:?}"
    );
    let alethe = outputs.last().cloned().unwrap_or_default();
    (exec, alethe)
}

fn strict_quality(exec: &Executor) -> ProofQuality {
    let proof = exec.last_proof().expect("last proof after UNSAT");
    check_proof_strict(proof, exec.terms())
        .expect("strict checker rejected the rebuilt proof (trust/hole or invalid step)")
}

/// Shape 1 (the raccoon INITIATION wall): `Init` pins the int-coded enum var
/// while `¬J` conjoins its disequality — a cross-assertion complementary
/// conjunct pair. The rebuilt proof must be fully strict-checkable with zero
/// trust steps: two assumes + `and_pos` extraction + one resolution.
#[test]
#[timeout(10_000)]
fn test_cross_assertion_complementary_conjuncts_rebuild_strict() {
    let script = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const tee Int)
        (declare-const primer Int)
        (declare-const n Int)
        (assert (and (= tee (- 1000000008)) (= primer n) (= tee tee)))
        (assert (and (not (= tee (- 1000000008))) (not (= tee (- 1000000007)))))
        (check-sat)
        (get-proof)
    "#;
    let (exec, alethe) = solve_unsat(script);
    let quality = strict_quality(&exec);
    assert_eq!(quality.trust_count, 0, "no trust steps: {quality}");
    assert_eq!(quality.hole_count, 0, "no hole steps: {quality}");
    assert!(
        !alethe.contains(":rule trust"),
        "printed Alethe must be trust-free:\n{alethe}"
    );
    assert!(
        alethe.contains(":rule and_pos"),
        "expected and_pos conjunct extraction:\n{alethe}"
    );
}

/// Shape 2, literal disjuncts (the raccoon SAFETY shape): the `or`-of-
/// equalities J against the `¬J` conjunction of disequalities. Every
/// disjunct's complement is a conjunct unit.
#[test]
#[timeout(10_000)]
fn test_or_of_equalities_against_negation_conjunction_rebuilds_strict() {
    let script = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const tee Int)
        (assert (or (= tee (- 1000000007)) (= tee (- 1000000008)) (= tee (- 1000000009))))
        (assert (and (not (= tee (- 1000000007)))
                     (not (= tee (- 1000000008)))
                     (not (= tee (- 1000000009)))))
        (check-sat)
        (get-proof)
    "#;
    let (exec, alethe) = solve_unsat(script);
    let quality = strict_quality(&exec);
    assert_eq!(quality.trust_count, 0, "no trust steps: {quality}");
    assert!(
        !alethe.contains(":rule trust"),
        "printed Alethe must be trust-free:\n{alethe}"
    );
}

/// Shape 2, `and`-tree disjuncts (the raccoon CONSECUTION shape): Next is an
/// `or` of actions, each action an `and` pinning the enum var to a literal
/// that a `¬J'` conjunct denies. Each disjunct is refuted through ONE of its
/// conjuncts (`and_pos` on the DISJUNCT, not on an assertion root).
#[test]
#[timeout(10_000)]
fn test_or_of_actions_pinning_enum_against_neg_j_prime_rebuilds_strict() {
    let script = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const tee0 Int)
        (declare-const tee1 Int)
        (declare-const dna0 Int)
        (declare-const dna1 Int)
        (assert (or (and (= tee0 (- 1000000007)) (= tee1 (- 1000000009)) (= dna1 dna0))
                    (and (= tee0 (- 1000000009)) (= tee1 (- 1000000007)) (= dna1 (+ dna0 1)))
                    (and (= tee1 (- 1000000008)) (= dna1 dna0))))
        (assert (and (not (= tee1 (- 1000000007)))
                     (not (= tee1 (- 1000000008)))
                     (not (= tee1 (- 1000000009)))))
        (check-sat)
        (get-proof)
    "#;
    let (exec, alethe) = solve_unsat(script);
    let quality = strict_quality(&exec);
    assert_eq!(quality.trust_count, 0, "no trust steps: {quality}");
    assert!(
        !alethe.contains(":rule trust"),
        "printed Alethe must be trust-free:\n{alethe}"
    );
}

/// The NATIVE-API path (how the model-checker consumer's `certify-all-n` drives ay): assertions carry
/// the `__ay_api_assertion__` parsed-form sentinel, so the rebuild works from
/// the assertion-stack terms directly. The exported BUNDLE must re-check
/// strictly offline with zero trust steps and its assume axioms must be a
/// subset of the obligation assertions — exactly the downstream
/// `re_check_bundle_strict` gate.
#[test]
#[timeout(10_000)]
fn test_native_api_enum_initiation_bundle_recheck_strict() {
    use ay_dpll::api::{Logic, Solver, Sort as ApiSort};
    use ay_proof::re_check_bundle_strict;

    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_proofs(true);
    let tee = solver.declare_const("tee__0", ApiSort::Int);
    let primer = solver.declare_const("primer__0", ApiSort::Int);
    let n = solver.declare_const("PRIMER", ApiSort::Int);
    let c_warm = solver.int_const(-1_000_000_008);
    let c_hot = solver.int_const(-1_000_000_007);
    let c_toohot = solver.int_const(-1_000_000_009);
    // Init: (and (= tee c_warm) (= primer PRIMER))
    let eq_tee = solver.eq(tee, c_warm);
    let eq_primer = solver.eq(primer, n);
    let init = solver.and(eq_tee, eq_primer);
    solver.assert_term(init);
    // ¬J: (and (not (= tee c_hot)) (not (= tee c_warm)) (not (= tee c_toohot)))
    let d1 = solver.eq(tee, c_hot);
    let d2 = solver.eq(tee, c_warm);
    let d3 = solver.eq(tee, c_toohot);
    let nd1 = solver.not(d1);
    let nd2 = solver.not(d2);
    let nd3 = solver.not(d3);
    let a12 = solver.and(nd1, nd2);
    let neg_j = solver.and(a12, nd3);
    solver.assert_term(neg_j);

    assert!(
        solver.check_sat().is_unsat(),
        "enum initiation must be UNSAT"
    );
    let bundle = solver
        .export_last_unsat_bundle()
        .expect("bundle after UNSAT with proofs enabled");
    let recheck = re_check_bundle_strict(&bundle)
        .expect("offline strict re-check must accept the rebuilt proof");
    assert_eq!(
        recheck.quality.trust_count, 0,
        "no trust steps: {}",
        recheck.quality
    );
    assert_eq!(recheck.quality.hole_count, 0);
    for assume in &recheck.assume_terms {
        assert!(
            bundle.obligation_assertions.contains(assume),
            "assume {assume:?} must be one of the obligation assertions {:?}",
            bundle.obligation_assertions
        );
    }
}

/// NO STRICT REBUILD, BUT A CERTIFIED VERDICT: no syntactic complement and no
/// linear certificate — an opaque nonlinear contradiction with a DISEQUALITY
/// (Farkas cannot consume it, and no `p`/`(not p)` pair exists among the
/// asserted conjuncts). The rebuild still must not fabricate a derivation, and
/// it does not: the exported proof keeps its honest unproved step and the
/// strict checker keeps rejecting it.
///
/// WHY THE EXPECTATION MOVED (was: `unknown` + revoked artifacts).
/// The query is GENUINELY UNSAT — `y = 3` forces `x = y*y = 9`, so `x != 9` is
/// false — verified by inspection and confirmed by z3 (`unsat`). The old
/// `unknown` was a CHECKER-COVERAGE downgrade, not a solver limit: AY computed
/// the right answer and then discarded it at the publication funnel because
/// `check_proof_strict` rejects `trust`/`hole` steps BY RULE NAME.
///
/// AY has since gained the deferred-trust discharge path
/// (`Executor::discharge_trust_steps_for_certification`, twinned in
/// `api::proofs::strict_verdict_with_deferred_trust`). It replaces "reject by
/// name" with "verify": a fresh forged-UNSAT guard must not re-decide the
/// problem as definitive SAT, every NON-trust step must still clear the full
/// strict boundary, and each deferred trust clause must be independently
/// discharged — here via the context-dependent fallback, which re-decides the
/// ORIGINAL authored assertions in a fresh `Executor` and requires UNSAT. So
/// the VERDICT is certified by an independent re-solve, and `unsat` publishes.
///
/// THE PROOF IS NOT EXTERNALLY CHECKABLE, and this test still pins that.
/// The independent re-solve certifies the CONCLUSION, not the document: the
/// exported certificate is unchanged and still terminates in
/// `(step t1 (cl false) :rule hole)`. `check_proof_strict` must keep REJECTING
/// it, so AY's own `--self-check` / `--strict-proofs` gate answers `unknown`
/// for this query while default mode answers `unsat`. That divergence is the
/// honest state of affairs, not a bug in this test. Should AY ever learn a real
/// nonlinear proof rule for this shape, the strict-rejection assertion below is
/// what will fire and demand this test be promoted.
#[test]
#[timeout(10_000)]
fn test_nonlinear_diseq_contradiction_publishes_uncheckable_certificate() {
    let script = r#"
        (set-option :produce-proofs true)
        (set-logic QF_NIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (and (= x (* y y)) (= y 3)))
        (assert (not (= x 9)))
        (check-sat)
        (get-proof)
    "#;
    let commands = parse(script).expect("parse nonlinear script");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("execute nonlinear script");
    // Genuinely UNSAT: y = 3 forces x = 9, contradicting `(not (= x 9))`.
    assert_eq!(outputs.first().map(String::as_str), Some("unsat"));

    // The verdict is certified (independent re-solve), so the artifacts are
    // published rather than revoked.
    let proof = exec
        .last_proof()
        .expect("a certified UNSAT must publish its proof artifacts");
    assert!(
        outputs
            .get(1)
            .is_some_and(|output| !output.contains("proof is not available")),
        "get-proof must succeed after certified publication: {outputs:?}"
    );

    // SOUNDNESS GUARD (the point of this test): the rebuild must NOT fabricate
    // a strict derivation for a shape it cannot prove. The published document
    // is honest about its gap — it retains an unproved step and the strict
    // checker rejects it.
    let strict = check_proof_strict(proof, exec.terms());
    assert!(
        strict.is_err(),
        "no strict certificate exists for this nonlinear shape; the checker \
         must not accept a fabricated one: {strict:?}"
    );
    let alethe = outputs.get(1).expect("get-proof output");
    assert!(
        alethe.contains(":rule hole") || alethe.contains(":rule trust"),
        "the uncheckable gap must be disclosed as an unproved step:\n{alethe}"
    );
}
