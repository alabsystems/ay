// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for trust class 4 (`TheoryLemmaKind::Generic` → `:rule
//! trust`): the two most frequent empirically-observed shapes now export
//! certified derivations instead of trust steps.
//!
//! Shape A — opaque-atom Farkas conflicts: inequality conflicts over
//! uninterpreted Int/Real atoms (`(select a i)`, `(f x)`), previously rejected
//! by the pure-LA `la_generic` eligibility and emitted as trust. Alethe
//! checkers treat non-arithmetic subterms as opaque variables, so a fully
//! (LINEAR-only) verified certificate exports as `la_generic`.
//!
//! Shape B — EUF congruence chain + one arithmetic comparison:
//! `x=y ∧ f(x)<f(y) ⊢ ⊥` and `a=b ∧ b=c ∧ f(a)>f(c) ⊢ ⊥` were fused
//! Generic/trust lemmas. They now split into (eq_transitive +) eq_congruent +
//! a solver-certified `la_generic` bridge + th_resolution.

#![allow(clippy::panic)]

use ay_dpll::Executor;
use ay_frontend::parse;
use ay_proof::{check_proof, check_proof_with_quality, ProofQuality};
use ntest::timeout;

fn run_unsat_proof(input: &str) -> (Executor, String, ProofQuality) {
    let (exec, proof_text, quality) = run_unsat_proof_object(input);
    assert!(
        proof_text.contains("(cl)"),
        "expected empty-clause derivation in proof:\n{proof_text}"
    );
    (exec, proof_text, quality)
}

/// Solve, check the proof OBJECT, and hand back whatever the exporter produced
/// — including a refusal.
///
/// The two are different artifacts and this file previously conflated them. A
/// proof object the internal checker accepts can still have a printed rendering
/// the external checker refuses, because the rule name comes from the term DAG
/// and the term text comes from a surface override. Tests whose subject is the
/// OBJECT use this; tests that also assert a shippable document use
/// [`run_unsat_proof`].
fn run_unsat_proof_object(input: &str) -> (Executor, String, ProofQuality) {
    let commands = parse(input).expect("proof-enabled SMT-LIB script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("proof-enabled SMT-LIB script should execute");

    assert_eq!(outputs.len(), 2, "expected check-sat + get-proof output");
    assert_eq!(outputs[0].trim(), "unsat", "expected UNSAT result");

    let proof_text = outputs[1].clone();

    let proof = exec
        .last_proof()
        .expect("expected get-proof to populate the last proof object");
    check_proof(proof, exec.terms()).expect("internal proof checker rejected proof");
    let quality = check_proof_with_quality(proof, exec.terms())
        .expect("proof quality checker rejected proof");

    (exec, proof_text, quality)
}

/// Shape A: a Farkas-contradictory pair of inequalities over an opaque
/// `select` atom (`(select a i) > 5` vs `(select a i) < 3`) exports as a
/// certified `la_generic` step, not trust.
#[test]
#[timeout(10_000)]
fn test_opaque_select_atom_farkas_exports_la_generic() {
    let input = r#"
        (set-logic QF_ALIA)
        (set-option :produce-proofs true)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (assert (> (select a i) 5))
        (assert (< (select a i) 3))
        (check-sat)
        (get-proof)
    "#;

    let (_exec, proof_text, quality) = run_unsat_proof(input);

    assert!(
        !proof_text.contains(":rule trust"),
        "opaque select-atom Farkas conflict must not export trust:\n{proof_text}"
    );
    assert_eq!(quality.trust_count, 0, "trust_count must be 0: {quality:?}");
    assert!(
        proof_text.contains(":rule la_generic"),
        "expected a la_generic step:\n{proof_text}"
    );
}

/// Shape B (direct congruence): `x = y ∧ f(x) < f(y)` splits into
/// eq_congruent + a `la_generic` bridge, not a fused trust lemma.
#[test]
#[timeout(10_000)]
fn test_euf_congruence_plus_comparison_splits_certified() {
    let input = r#"
        (set-logic QF_UFLIA)
        (set-option :produce-proofs true)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= x y))
        (assert (< (f x) (f y)))
        (check-sat)
        (get-proof)
    "#;

    let (_exec, proof_text, quality) = run_unsat_proof(input);

    assert!(
        !proof_text.contains(":rule trust"),
        "EUF congruence + comparison conflict must not export trust:\n{proof_text}"
    );
    assert_eq!(quality.trust_count, 0, "trust_count must be 0: {quality:?}");
    assert!(
        proof_text.contains(":rule eq_congruent"),
        "expected an eq_congruent step:\n{proof_text}"
    );
    assert!(
        proof_text.contains(":rule la_generic"),
        "expected a la_generic bridge step:\n{proof_text}"
    );
}

/// Shape B (chain congruence): `a = b ∧ b = c ∧ f(a) > f(c)` splits into
/// eq_transitive + eq_congruent + a `la_generic` bridge.
#[test]
#[timeout(10_000)]
fn test_euf_chain_congruence_plus_comparison_splits_certified() {
    let input = r#"
        (set-logic QF_UFLIA)
        (set-option :produce-proofs true)
        (declare-fun f (Int) Int)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        (assert (= a b))
        (assert (= b c))
        (assert (> (f a) (f c)))
        (check-sat)
        (get-proof)
    "#;

    let (_exec, proof_text, quality) = run_unsat_proof(input);

    assert!(
        !proof_text.contains(":rule trust"),
        "EUF chain congruence + comparison conflict must not export trust:\n{proof_text}"
    );
    assert_eq!(quality.trust_count, 0, "trust_count must be 0: {quality:?}");
    assert!(
        proof_text.contains(":rule eq_transitive"),
        "expected an eq_transitive step:\n{proof_text}"
    );
    assert!(
        proof_text.contains(":rule eq_congruent"),
        "expected an eq_congruent step:\n{proof_text}"
    );
    assert!(
        proof_text.contains(":rule la_generic"),
        "expected a la_generic bridge step:\n{proof_text}"
    );
}

/// MODEL_CHECKER_CONSUMER's minimal strict-replay reproducer: the negation of a polynomial
/// ring identity must be closed by a checked `poly_simp` lemma rather than a
/// premiseless Generic/trust leaf.
#[test]
#[timeout(10_000)]
fn test_ring_identity_exports_checked_poly_simp() {
    let input = r#"
        (set-logic QF_NIA)
        (set-option :produce-proofs true)
        (set-option :check-proofs-strict true)
        (declare-const i Int)
        (assert (not (= (* (+ i 1) (+ i 1)) (+ (* i i) (+ (* 2 i) 1)))))
        (check-sat)
        (get-proof)
    "#;

    let (_exec, proof_text, quality) = run_unsat_proof(input);

    assert!(
        proof_text.contains(":rule poly_simp"),
        "ring identity must use Alethe's checked polynomial rule:\n{proof_text}"
    );
    assert!(
        !proof_text.contains(":rule hole") && !proof_text.contains(":rule trust"),
        "ring identity proof must contain no unproved step:\n{proof_text}"
    );
    assert_eq!(quality.trust_count, 0, "trust_count must be 0: {quality:?}");
}

/// The ReLU-disjunction family (#relu-trust-glue), 1-ReLU smoke shape:
/// `y = relu(x)` encoded as an `(or (and ..) (and ..))` case split over
/// linear atoms, `x ∈ [1, 2]`, query `y < 1/2`. The eager pipeline refutes
/// the dead branch without recording its exclusion lemma, which previously
/// left the traced clause set propositionally satisfiable and forced the
/// final `(cl)` onto an unverifiable `trust` glue step. The level-0 rescue
/// (widened propagation context) + bounded DPLL(T) closer must now derive
/// `(cl)` by genuine resolution over certified `la_generic` leaves.
#[test]
#[timeout(10_000)]
fn test_relu_case_split_disjunction_exports_certified_resolution() {
    let input = r#"
        (set-logic QF_LRA)
        (set-option :produce-proofs true)
        (declare-const x Real)
        (declare-const y Real)
        (declare-const z Real)
        (assert (>= x 1))
        (assert (= z x))
        (assert (or (and (<= z 0) (= y 0)) (and (>= z 0) (= y z))))
        (assert (< y (/ 1 2)))
        (check-sat)
        (get-proof)
    "#;

    let (_exec, proof_text, quality) = run_unsat_proof_object(input);

    // The no-trust-glue claim is about the proof OBJECT and is asserted there.
    // It cannot be read off `proof_text` here: the refusal document below
    // itself contains the words ":rule trust" in its explanation.
    assert_eq!(quality.trust_count, 0, "trust_count must be 0: {quality:?}");
    assert_relu_or_pos_surface_is_refused(&proof_text);
}

/// The ReLU family's `or_pos` gate does not survive PRINTING, and the export
/// must say so rather than ship it.
///
/// This assertion used to be `proof_text.contains("(cl)")`, and that was the
/// blind spot the whole printed-surface gate exists to close: the proof OBJECT
/// is fine — the internal checker accepts it and `trust_count` is 0 — while the
/// document it prints is refused by the pinned external checker. MEASURED on
/// carcara 1.1.0 against the PREVIOUS output of this exact fixture:
///
/// ```text
/// (step t4 (cl (not (or (and (<= z 0.0) (= y 0.0)) (and (<= 0.0 z) (= y z))))
///              (and (<= z 0.0) (= y 0.0))
///              (and (>= z 0.0) (= y z))) :rule or_pos)
/// [ERROR] checking failed on step 't4' with rule 'or_pos':
/// expected terms to be equal: '(and (<= 0.0 z) (= y z))' and '(and (>= z 0.0) (= y z))'
/// ```
///
/// The authored `(>= z 0)` and the canonical `(<= 0 z)` are the same atom and
/// the clause is TRUE; the printed step is simply not an `or_pos` instance. The
/// faithful repair is a bridge — `comp_simplify` + `cong` + `equiv_pos2` per
/// differing operand, exactly the chain this document already builds at `t3.n`
/// — for a POSITIVE operand nested inside a conjunct. `format_surface_tautology`
/// carries that bridge only for NEGATED top-level operands
/// (`Bridge::LinearOrder`), so until it is extended the honest outcome is a
/// refusal, not a document the checker throws away.
fn assert_relu_or_pos_surface_is_refused(proof_text: &str) {
    assert!(
        proof_text.contains("UNVERIFIABLE PROOF"),
        "expected the export to refuse the unprintable or_pos gate:\n{proof_text}"
    );
    assert!(
        proof_text.contains("no or_pos instance over the printed surface"),
        "the refusal must name the printed-surface mismatch:\n{proof_text}"
    );
}

/// The 2-ReLU chain variant: TWO eagerly-refuted branch patterns are
/// missing their exclusion lemmas, so the level-0 rescue alone cannot close
/// the proof — only the bounded DPLL(T) closer (fresh-solver certified
/// lemma per infeasible branch) reaches `(cl)` without trust.
#[test]
#[timeout(10_000)]
fn test_relu_chain_two_case_splits_export_certified_resolution() {
    let input = r#"
        (set-logic QF_LRA)
        (set-option :produce-proofs true)
        (declare-const x Real)
        (declare-const y1 Real)
        (declare-const z1 Real)
        (declare-const y2 Real)
        (declare-const z2 Real)
        (assert (>= x 1))
        (assert (= z1 x))
        (assert (or (and (<= z1 0) (= y1 0)) (and (>= z1 0) (= y1 z1))))
        (assert (= z2 (- y1 (/ 1 4))))
        (assert (or (and (<= z2 0) (= y2 0)) (and (>= z2 0) (= y2 z2))))
        (assert (< y2 (/ 1 2)))
        (check-sat)
        (get-proof)
    "#;

    let (_exec, proof_text, quality) = run_unsat_proof_object(input);

    // See the 1-ReLU shape: the no-trust-glue claim lives on the object.
    assert_eq!(quality.trust_count, 0, "trust_count must be 0: {quality:?}");
    // Same printed-surface refusal as the 1-ReLU shape; see
    // `assert_relu_or_pos_surface_is_refused`.
    assert_relu_or_pos_surface_is_refused(&proof_text);
}
