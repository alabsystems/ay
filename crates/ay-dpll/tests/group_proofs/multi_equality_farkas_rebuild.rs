// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Producer-side tests for the multi-equality Farkas rebuild
//! (`try_rebuild_with_pure_bounds` + conjunct-bound extraction in
//! `proof_original_rebuild.rs`).
//!
//! Preprocessing substitution dissolves a conjunction of equalities into the
//! remaining linear assertion (e.g. `x = N ∧ y = 0` into `N < x + y` leaves
//! only the unit `x < x`), and the demotion pass used to export that bridge
//! as a premiseless `:rule trust` step the strict checker rejects. The
//! rebuild re-proves the contradiction from the ORIGINAL assertions: one
//! certified `la_generic` Farkas lemma over the equality/inequality bounds,
//! each conjunct unit derived from its root's `assume` by strictly-validated
//! `and_pos` + resolution steps.
//!
//! Every ACCEPTED proof here is verified by the UNCHANGED strict checker,
//! which recomputes the Farkas combination semantically (equalities searched
//! in both orientations, strict/nonstrict combination rules, fail-closed Int
//! tightening) — nothing is accepted on annotation presence alone.

use ay_dpll::Executor;
use ay_frontend::parse;
use ay_proof::{check_proof, check_proof_strict, ProofQuality};
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

/// THE WALL (shape B of the model-checker consumer `certify-all-n` eq-split halves): two
/// equalities asserted as ONE conjunction, substituted by preprocessing into
/// the strict inequality. The rebuilt proof must be fully strict-checkable
/// with zero trust steps: assume(and-root) + and_pos conjunct extraction +
/// one certified multi-equality `la_generic` lemma + resolution.
#[test]
#[timeout(10_000)]
fn test_conjoined_equalities_substituted_into_strict_inequality_rebuilds_strict() {
    let script = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const n Int)
        (assert (and (= x n) (= y 0)))
        (assert (< n (+ x y)))
        (check-sat)
        (get-proof)
    "#;
    let (exec, alethe) = solve_unsat(script);
    let quality = strict_quality(&exec);
    assert_eq!(quality.trust_count, 0, "no trust steps: {quality}");
    assert_eq!(quality.hole_count, 0, "no hole steps: {quality}");
    assert!(
        quality.theory_lemma_count >= 1,
        "expected a certified Farkas lemma: {quality}"
    );
    assert!(
        !alethe.contains(":rule trust"),
        "printed Alethe must be trust-free:\n{alethe}"
    );
    assert!(
        alethe.contains(":rule la_generic"),
        "expected a printed la_generic lemma:\n{alethe}"
    );
    assert!(
        alethe.contains(":rule and_pos"),
        "expected and_pos conjunct extraction:\n{alethe}"
    );
}

/// Same class with the equalities asserted SEPARATELY (direct bounds, no
/// conjunct extraction needed).
#[test]
#[timeout(10_000)]
fn test_separate_equalities_substituted_into_strict_inequality_rebuilds_strict() {
    let script = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const n Int)
        (assert (= x n))
        (assert (= y 0))
        (assert (< n (+ x y)))
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

/// A LONGER equality chain (three equalities + one strict inequality) — the
/// Farkas combination must eliminate all six variables across four premises.
#[test]
#[timeout(10_000)]
fn test_three_equality_chain_rebuilds_strict() {
    let script = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const z Int)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        (assert (and (= x a) (= y b) (= z c)))
        (assert (< (+ a b c) (+ x (+ y z))))
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

/// Mixed equality + non-strict inequality bounds against a strict inequality.
#[test]
#[timeout(10_000)]
fn test_mixed_equality_inequality_bounds_rebuild_strict() {
    let script = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const n Int)
        (assert (and (= x n) (<= y 0)))
        (assert (< n (+ x y)))
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

/// Shape A of the model-checker consumer wall: the conjunction of equalities against a
/// DISEQUALITY. A single Farkas combination cannot orient the disequality
/// for printing, so the printed proof must come from the `la_disequality`
/// case-split backbone (now reachable because the conjunct bounds exist),
/// with the conjunct units extracted by `and_pos`. The printed proof is
/// trust-free; carcara validates `la_disequality` natively (the internal
/// strict checker intentionally does not — that fragment stays fail-closed
/// for the offline bundle path).
#[test]
#[timeout(10_000)]
fn test_conjoined_equalities_against_disequality_prints_la_disequality_split() {
    let script = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const n Int)
        (assert (and (= x n) (= y 0)))
        (assert (not (= n (+ x y))))
        (check-sat)
        (get-proof)
    "#;
    let (exec, alethe) = solve_unsat(script);
    let proof = exec.last_proof().expect("last proof after UNSAT");
    check_proof(proof, exec.terms()).expect("proof structurally valid");
    assert!(
        !alethe.contains(":rule trust"),
        "printed Alethe must be trust-free:\n{alethe}"
    );
    assert!(
        alethe.contains(":rule la_disequality"),
        "expected the la_disequality case split:\n{alethe}"
    );
    assert!(
        alethe.contains(":rule and_pos"),
        "expected and_pos conjunct extraction:\n{alethe}"
    );
}

/// The NATIVE-API path (how the model-checker consumer's `certify-all-n` drives ay): assertions
/// carry the `__ay_api_assertion__` parsed-form sentinel, so the rebuild
/// must work from the assertion-stack terms directly (no surface). The
/// exported BUNDLE must re-check strictly offline with zero trust steps and
/// its assume axioms must be a subset of the obligation assertions — exactly
/// the model-checker consumer `re_check_bundle_strict` gate.
#[test]
#[timeout(10_000)]
fn test_native_api_conjoined_equalities_bundle_recheck_strict() {
    use ay_dpll::api::{Logic, Solver, Sort as ApiSort};
    use ay_proof::re_check_bundle_strict;

    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_proofs(true);
    let x = solver.declare_const("x", ApiSort::Int);
    let y = solver.declare_const("y", ApiSort::Int);
    let n = solver.declare_const("n", ApiSort::Int);
    let zero = solver.int_const(0);
    // (and (= x n) (= y 0))  — shape B of the model-checker consumer initiation wall.
    let eq_x = solver.eq(x, n);
    let eq_y = solver.eq(y, zero);
    let conj = solver.and(eq_x, eq_y);
    solver.assert_term(conj);
    // (< n (+ x y))
    let sum = solver.add(x, y);
    let lt = solver.lt(n, sum);
    solver.assert_term(lt);

    assert!(solver.check_sat().is_unsat(), "shape B must be UNSAT");
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
    // Assume-coverage: every proof axiom is an asserted obligation.
    for assume in &recheck.assume_terms {
        assert!(
            bundle.obligation_assertions.contains(assume),
            "assume {assume:?} must be one of the obligation assertions {:?}",
            bundle.obligation_assertions
        );
    }
}

/// Native-API shape A (the disequality half): `(and (= x n) (= y 0))` +
/// `(not (= n (+ x y)))`. The certified single-lemma diseq form is not
/// printable as signed `la_generic` (fail-closed dry run), so the pure-bounds
/// backbone declines and the `la_disequality` split backbone produces the
/// printed proof — trust-free Alethe, but intentionally OUTSIDE the strict
/// bundle fragment (`la_disequality` has no internal strict validator).
#[test]
#[timeout(10_000)]
fn test_native_api_diseq_half_prints_trust_free() {
    use ay_dpll::api::{Logic, Solver, Sort as ApiSort};

    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_proofs(true);
    let x = solver.declare_const("x", ApiSort::Int);
    let y = solver.declare_const("y", ApiSort::Int);
    let n = solver.declare_const("n", ApiSort::Int);
    let zero = solver.int_const(0);
    let eq_x = solver.eq(x, n);
    let eq_y = solver.eq(y, zero);
    let conj = solver.and(eq_x, eq_y);
    solver.assert_term(conj);
    let sum = solver.add(x, y);
    let eq_sum = solver.eq(n, sum);
    let neq = solver.not(eq_sum);
    solver.assert_term(neq);

    assert!(solver.check_sat().is_unsat(), "shape A must be UNSAT");
    let alethe = solver
        .export_last_proof_alethe()
        .expect("alethe text after UNSAT");
    assert!(
        !alethe.contains(":rule trust"),
        "printed Alethe must be trust-free:\n{alethe}"
    );
    assert!(
        alethe.contains(":rule la_disequality"),
        "expected the la_disequality case split:\n{alethe}"
    );
}

/// FAIL-CLOSED: a conjunct outside the linear fragment (an opaque nonlinear
/// product the bounds refutation cannot use) must NOT be bridged by trust
/// surgery or a fabricated certificate — the proof keeps its demoted trust
/// step and the strict checker keeps rejecting it.
#[test]
#[timeout(10_000)]
fn test_nonlinear_conjunct_stays_fail_closed() {
    let script = r#"
        (set-option :produce-proofs true)
        (set-logic QF_NIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (and (= x (* y y)) (= y 3)))
        (assert (< x 0))
        (check-sat)
        (get-proof)
    "#;
    let (exec, _alethe) = solve_unsat(script);
    let proof = exec.last_proof().expect("last proof after UNSAT");
    let strict = check_proof_strict(proof, exec.terms());
    assert!(
        !matches!(&strict, Ok(q) if q.trust_count == 0),
        "nonlinear-conjunct contradiction must stay OUTSIDE the verified strict \
         fragment (fail-closed), got {strict:?}"
    );
}
