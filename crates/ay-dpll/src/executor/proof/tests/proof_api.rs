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
/// override that re-spells AY's canonical `(not (= a b))`.
///
/// Was `eq_transitive_boolean_equality_surface_fails_closed_under_produce_proofs`,
/// which pinned a fail-closed `unknown`. **CONTRACT CHANGED, AND THE CHANGE IS
/// MEASURED.** `0593543ff` demoted the un-renderable `eq_transitive` step — the
/// pure-EUF transitivity reconstruction whose first hypothesis is that exact
/// aliased term, and whose only wire rendering under the override is the shape
/// Carcara rejects — to an honest unproved leaf, and mandatory certification
/// then withheld the UNSAT.
///
/// The refutation no longer goes through that step. Measured at `cc1bc0a30`,
/// in this worktree, the published document is a `trans`/`cong`/`refl` +
/// `equiv_neg*`/`equiv_pos*` derivation with NO `eq_transitive` anywhere, and:
///
///   * it carries no `hole` and no `trust` step, and `terminal_trust_report`
///     reports it trust-free;
///   * every `assume` is one of the four authored assertions, printed
///     verbatim;
///   * `export_last_unsat_artifact` reports `strict_verdict = Verified`
///     (`trust_count: 0`, `hole_count: 0`) and `carcara_surface = supported`;
///   * **pinned Carcara 1.1.0 answers `valid`** on the exact published
///     document paired with the artifact's own `alethe_problem_smt2` bytes.
///
/// `a = b`, `b = c`, `a != c` is genuinely UNSAT, so this is a capability
/// gain, not a widened acceptance. The soundness assertion the old test
/// carried is KEPT verbatim: whatever is published, it must never be an
/// `eq_transitive` step over the boolean-equality alias — the rendering the
/// external checker refuses. Publishing that shape, or any hole or trust step,
/// still fails here.
#[test]
fn eq_transitive_boolean_equality_surface_publishes_a_checkable_refutation() {
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

    assert_eq!(
        outputs[0], "unsat",
        "the alias-free reconstruction must certify this genuinely-unsatisfiable \
         query: {outputs:?}"
    );

    // UNCHANGED SOUNDNESS PIN: the native-only rendering Carcara rejects must
    // never reach the wire.
    assert!(
        !(outputs[1].contains("(= (= a b) false)") && outputs[1].contains(":rule eq_transitive")),
        "must not publish an eq_transitive over the boolean-equality alias: {}",
        outputs[1]
    );
    assert!(
        !outputs[1].contains(":rule hole") && !outputs[1].contains(":rule trust"),
        "a published refutation must carry no unproved step:\n{}",
        outputs[1]
    );

    // Every `assume` is one of the authored assertions, printed verbatim: an
    // `assume` the author did not write is `invalid` to an external checker.
    let authored = [
        "(= a b)",
        "(= b c)",
        "(not (= a c))",
        "(or (= (= a b) false) (= a b))",
    ];
    for line in outputs[1].lines().filter(|l| l.starts_with("(assume ")) {
        let term = line
            .splitn(3, ' ')
            .nth(2)
            .and_then(|rest| rest.strip_suffix(')'))
            .unwrap_or("");
        assert!(
            authored.contains(&term),
            "published `assume` {term:?} is not an authored assertion:\n{}",
            outputs[1]
        );
    }

    let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
    assert!(
        ay_proof::terminal_trust_report(proof).is_trust_free(),
        "the published refutation must be trust-free"
    );
}

/// The external-codegen dom-bounds obligation family: `(and P (not (= P true)))` with
/// `P` a BV comparison atom folds to `false` at elaboration and used to export
/// the Carcara-rejected `:rule false` collapse.
/// `promote_and_true_eq_contradiction_collapse` rebuilds it into an
/// and_pos/not_equiv2/true refutation (cand6) — no `false`, no `trust`.
///
/// AND THAT DOCUMENT IS EXTERNALLY INVALID. This test used to assert it was
/// "fully checkable" on the strength of two absent strings. Measured against
/// pinned carcara 1.1.0 at the parent commit:
///
/// ```text
/// (step t5 (cl (not (= (bvult ...) true)) (not true)) :rule not_equiv2 :premises (t4))
/// [ERROR] checking failed on step 't5' with rule 'not_equiv2':
///         expected terms to be equal: '(bvult ...)' and '(= (bvult ...) true)'
/// invalid
/// ```
///
/// Elaboration folds `(= P true)` to `P`, so `not_equiv2`'s conclusion is
/// internally `(cl (not P) (not true))` — correct — while the surface override
/// that the `assume` needs re-spells `P` as `(= P true)` inside that derived
/// clause. The printed step therefore does not instantiate the rule it names,
/// and its consumer `t6` resolves a pivot that no longer prints as a
/// complement, which is what the printed-text judgement refuses.
///
/// The earlier ground closure now builds a different, complete derivation
/// directly from the original conjunction. Its actual production document
/// verifies with signed Clean13482; the same document against a changed SAT
/// source is refused at its assumption. Keep that authored-scope contract,
/// rather than requiring the obsolete cand6 route or its refusal marker.
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

    assert_eq!(outputs[0], "unsat", "the verdict must not move");
    let proof = &outputs[1];
    assert!(
        proof.contains("(step ")
            && !proof.contains(":rule false")
            && !proof.contains(":rule hole")
            && !proof.contains(":rule trust"),
        "the original assertion needs a complete published derivation:\n{proof}"
    );
    let internal = exec.last_proof().expect("UNSAT retains its derivation");
    assert!(ay_proof::terminal_trust_report(internal).is_trust_free());
    assert!(exec
        .check_proof_strict_with_datatypes(internal)
        .unwrap()
        .is_complete());
    let mut authored = Vec::new();
    exec.try_export_last_proof_alethe_for_problem_scope_to(&mut authored)
        .unwrap()
        .expect("the complete original assertion remains the export scope");
    assert_eq!(String::from_utf8(authored).unwrap().trim(), proof.trim());

    let changed = input.replacen(
        "(assert (and (bvult bridge_dom_bce_idx (_ bv1024 64))",
        "(assert (and (not (bvult bridge_dom_bce_idx (_ bv1024 64)))",
        1,
    );
    let mut changed_exec = Executor::new();
    let changed_outputs = changed_exec.execute_all(&parse(&changed).unwrap()).unwrap();
    assert_eq!(changed_outputs[0], "sat");
    assert!(changed_exec.last_proof().is_none());
}
