// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[test]
fn test_get_proof_not_enabled() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (< x 0))
        (assert (> x 0))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "unsat");
    assert!(outputs[1].contains("proof generation is not enabled"));
}

#[test]
fn test_get_proof_after_sat() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (> x 0))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    assert!(outputs[1].contains("proof is not available"));
}

#[test]
fn test_get_proof_after_unsat() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (< x 0))
        (assert (> x 0))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "unsat");
    // Should get an actual proof (not an error)
    assert!(
        outputs[1].starts_with('('),
        "Expected proof output, got: {}",
        outputs[1]
    );
}

/// A logically inert `(= (= a b) false)` wrapper installs an authored surface
/// override that re-spells AY's canonical `(not (= a b))`. The pure-EUF
/// transitivity refutation reconstructs an `eq_transitive` lemma whose first
/// hypothesis is that exact term, and its ONLY wire rendering under the override
/// is the shape Carcara rejects. Mandatory certification must fail closed to
/// `unknown` rather than publish an `eq_transitive` step over the alias.
#[test]
fn eq_transitive_boolean_equality_surface_fails_closed_under_produce_proofs() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_UF)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        (assert (= a b))
        (assert (= b c))
        (assert (not (= a c)))
        (assert (or (= (= a b) false) (= a b)))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Fail-closed: the un-renderable eq_transitive is demoted to an honest
    // unproved leaf, so mandatory certification withholds the UNSAT.
    assert_eq!(
        outputs[0], "unknown",
        "expected fail-closed unknown, got: {outputs:?}"
    );

    // Whatever `(get-proof)` returns, it must never publish the native-only
    // rendering Carcara rejects.
    assert!(
        !(outputs[1].contains("(= (= a b) false)") && outputs[1].contains(":rule eq_transitive")),
        "must not publish an eq_transitive over the boolean-equality alias: {}",
        outputs[1]
    );
}

/// The external-codegen dom-bounds obligation family: `(and P (not (= P true)))` with
/// `P` a BV comparison atom folds to `false` at elaboration and used to export
/// the Carcara-rejected `:rule false` collapse.
/// `promote_and_true_eq_contradiction_collapse` must rebuild it into the
/// checkable and_pos/not_equiv2/true refutation (cand6) — no `false`, no
/// `trust`.
#[test]
fn test_and_true_eq_contradiction_promotes_to_checkable_proof() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_BV)
        (declare-const bridge_dom_bce_idx (_ BitVec 64))
        (assert (and (bvult bridge_dom_bce_idx (_ bv1024 64)) (not (= (bvult bridge_dom_bce_idx (_ bv1024 64)) true))))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "unsat");
    let proof = &outputs[1];
    assert!(
        !proof.contains(":rule false"),
        "dom-bounds proof must not use the Carcara-rejected false collapse:\n{proof}"
    );
    assert!(
        !proof.contains(":rule trust"),
        "dom-bounds proof must be fully checkable, no trust step:\n{proof}"
    );
    assert!(
        proof.contains("and_pos") && proof.contains("not_equiv2") && proof.contains(":rule true"),
        "dom-bounds proof must be the cand6 and_pos/not_equiv2/true refutation:\n{proof}"
    );
}
