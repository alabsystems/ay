// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// The endpoint lane pins one opaque term to two different bit-vector
/// CONSTANTS and closes it with a `bv_bitblast` unit lemma. Carcara cannot
/// re-derive AY's bit-blasting, but `(= #x05 #x06)` is a GROUND term its own
/// `evaluate` reduces to `false`, so this lemma exports checked instead of as
/// a hole. Both arms of the lane are covered: the QF_ABV array read and the
/// QF_BV term (`bvudiv`) that is deliberately held opaque.
#[test]
#[timeout(120_000)]
fn test_carcara_trust_free_bv_constant_endpoint_mismatch() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let cases = [
        (
            "trust_free_qf_abv_shared_endpoint_constant_mismatch",
            "(set-logic QF_ABV)\n\
             (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))\n\
             (declare-const i (_ BitVec 8))\n\
             (assert (= (select a i) #x05))\n\
             (assert (= (select a i) #x06))\n\
             (check-sat)\n",
        ),
        (
            "trust_free_qf_bv_opaque_udiv_endpoint_mismatch",
            "(set-logic QF_BV)\n\
             (declare-const x (_ BitVec 8))\n\
             (assert (= (bvudiv x #x03) #x02))\n\
             (assert (= (bvudiv x #x03) #x03))\n\
             (check-sat)\n",
        ),
    ];
    for (label, problem) in cases {
        let proof = solve_unsat_and_get_proof(problem, label);
        assert!(
            !proof.contains(":rule trust") && !proof.contains(":rule hole"),
            "{label}: constant-endpoint proof must not contain unchecked rules:\n{proof}"
        );
        assert!(
            !proof.contains(":rule bv_bitblast"),
            "{label}: AY's private coarse rule name must never reach the wire:\n{proof}"
        );
        assert!(
            proof.contains(":rule evaluate"),
            "{label}: the constant mismatch must be certified by evaluate:\n{proof}"
        );
        assert!(
            run_carcara_trust_free(&carcara, label, problem, &proof),
            "{label}: constant-endpoint proof must be verified by Carcara without \
             allowed trust"
        );
    }
}

/// The `ay z3-audit` canonical QF_UF transitivity fixture must export a
/// genuine `eq_transitive` + `th_resolution` derivation that carcara accepts
/// WITHOUT `--allowed-rules trust`. This is the exact fixture used by the audit
/// (sorts declared as `Int`, contradiction is pure transitivity a=b, b=c, a≠c).
#[test]
#[timeout(60_000)]
fn test_carcara_trust_free_qf_uf_transitivity_fixture() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let problem =
        benchmark_content("tests/fixtures/proof/smt_alethe_qf_uf_transitivity_not_eq.smt2");
    let proof = solve_unsat_and_get_proof(&problem, "trust_free_qf_uf_transitivity_fixture");
    assert!(
        proof.contains(":rule eq_transitive"),
        "fixture proof must use a genuine eq_transitive step:\n{proof}"
    );
    assert!(
        !proof.contains(":rule trust"),
        "fixture proof must not contain any trust step:\n{proof}"
    );
    assert!(
        run_carcara_trust_free(
            &carcara,
            "trust_free_qf_uf_transitivity_fixture",
            &problem,
            &proof
        ),
        "QF_UF transitivity fixture proof must be trust-free verifiable by carcara"
    );
}

/// A logically inert authored Boolean-equality wrapper installs the surface
/// spelling `(= (= a b) false)` for AY's canonical `not (= a b)` term. That
/// spelling is not a legal negated-equality hypothesis of `eq_transitive`.
/// Standalone generic-EUF promotion must therefore either leave publication
/// to a later fully audited repair or make the proof request fail closed; it
/// must never publish the native-only rendering.
#[test]
#[timeout(60_000)]
fn test_carcara_qf_uf_boolean_equality_surface_is_valid_or_fails_closed() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    const PROBLEM: &str = r#"
(set-logic QF_UF)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(assert (= a b))
(assert (= b c))
(assert (not (= a c)))
; Tautological, but its first child supplies the adversarial surface alias.
(assert (or (= (= a b) false) (= a b)))
(check-sat)
"#;
    let label = "qf_uf_boolean_equality_surface";
    let Some(proof) = solve_or_fail_closed_and_maybe_get_proof(PROBLEM, label) else {
        return;
    };
    assert!(
        !proof.contains(":rule trust") && !proof.contains(":rule hole"),
        "{label}: any published proof must be fully checkable:\n{proof}"
    );
    assert!(
        run_carcara_trust_free(&carcara, label, PROBLEM, &proof),
        "{label}: Carcara must accept any published proof"
    );
}

/// QF_LIA arithmetic proofs may still contain `trust`-backed theory steps when
/// coefficient annotations are unavailable. This test checks the current export
/// contract: the proof must remain structurally valid via carcara with AY's
/// supported allowlist.
#[test]
#[timeout(60_000)]
fn test_carcara_qf_lia_holey_valid() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };

    let proof = solve_unsat_and_get_proof(QF_LIA_UNSAT, "qf_lia_holey");
    verify_alethe_with_carcara(&carcara, "qf_lia_holey", QF_LIA_UNSAT, &proof);
}

/// AY strictly validates datatype exhaustiveness in its native proof IR, but
/// the pinned Alethe calculus has no corresponding inference. The exported
/// diagnostic must therefore be structurally accepted as `holey`, never claim
/// `valid`, and never invent an unsupported wire-rule name.
#[test]
#[timeout(60_000)]
fn test_carcara_finite_enum_pigeonhole_is_honestly_holey() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let label = "finite_enum_pigeonhole_holey";
    let proof = solve_unsat_and_get_proof(QF_DT_FINITE_ENUM_PIGEONHOLE_UNSAT, label);
    assert_eq!(proof.matches(":rule hole").count(), 1, "{proof}");
    assert_eq!(
        proof
            .lines()
            .filter(|line| line.starts_with("(assume "))
            .count(),
        6,
        "{proof}"
    );
    assert_eq!(proof.matches(":rule resolution").count(), 1, "{proof}");
    assert!(!proof.contains(":rule dt_enum_pigeonhole"), "{proof}");
    let (problem_path, proof_path) =
        write_problem_and_proof(label, QF_DT_FINITE_ENUM_PIGEONHOLE_CARCARA_SCOPE, &proof);
    let output = std::process::Command::new(&carcara)
        .arg("check")
        .arg("--expand-let-bindings")
        .arg("--")
        .arg(&proof_path)
        .arg(&problem_path)
        .output()
        .expect("run carcara finite-enum holey check");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let keep_artifacts = keep_alethe_artifacts() || !output.status.success();
    if !keep_artifacts {
        let _ = std::fs::remove_file(&problem_path);
        let _ = std::fs::remove_file(&proof_path);
    }
    assert!(
        output.status.success(),
        "Carcara rejected finite-enum skeleton: stdout={} stderr={}",
        stdout.trim(),
        stderr.trim()
    );
    assert_eq!(stdout.trim(), "holey");
}

/// The trust-FREE normalized-assume class: every step is checkable, but the
/// exported assumes are preprocessing-normalized (`(>= a 0)` -> `(<= 0 a)`,
/// `(> a 5)` -> `(< 5 a)`) and print unlike the problem premises. The
/// trust-surgery pass must fire without a trust anchor and bridge both the
/// normalized `and` conjunction and the plain normalized bound literal.
#[test]
#[timeout(60_000)]
fn test_carcara_qf_lia_normalized_assumes_no_trust_anchor_valid() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };

    const PROBLEM: &str = r#"
(set-logic QF_LIA)
(declare-const a Int)
(assert (and (>= a 0) (<= a 5)))
(assert (> a 5))
(check-sat)
"#;
    let proof = solve_unsat_and_get_proof(PROBLEM, "qf_lia_normalized_assumes_no_trust");
    assert!(
        !proof.contains(":rule trust"),
        "expected a trust-free proof, got:\n{proof}"
    );
    let assumes = extract_assume_terms(&proof);
    assert!(
        assumes.contains(&"(and (>= a 0) (<= a 5))".to_string()),
        "and-assume must print with the problem file's surface syntax:\n{proof}"
    );
    assert!(
        assumes.contains(&"(> a 5)".to_string()),
        "bound assume must print with the problem file's surface syntax:\n{proof}"
    );
    verify_alethe_with_carcara(
        &carcara,
        "qf_lia_normalized_assumes_no_trust",
        PROBLEM,
        &proof,
    );
}

#[test]
#[timeout(60_000)]
fn test_carcara_qf_lia_harder_binary_ilp_unsat_valid() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };

    let problem = benchmark_content("benchmarks/smt/QF_LIA/harder_binary_ilp_unsat.smt2");
    let proof = solve_unsat_and_get_proof(&problem, "QF_LIA_harder_binary_ilp_unsat");
    verify_alethe_with_carcara(&carcara, "QF_LIA_harder_binary_ilp_unsat", &problem, &proof);
}

#[test]
#[timeout(60_000)]
fn test_qf_lia_ring_exported_assumes_match_original_premises() {
    let problem = std::fs::read_to_string(
        workspace_root().join("benchmarks/smt/QF_LIA/ring_2exp4_3vars_0ite_unsat.smt2"),
    )
    .expect("read ring benchmark");
    let proof = solve_unsat_and_get_proof(&problem, "qf_lia_ring_assume_surface");

    let original_assertions = extract_asserted_terms(&problem);
    let assume_terms = extract_assume_terms(&proof);

    assert!(
        !assume_terms.is_empty(),
        "expected exported proof to contain assume steps:\n{proof}"
    );

    for term in &assume_terms {
        assert!(
            original_assertions.contains(term),
            "exported assume term is not an original SMT-LIB premise: {term}\n\
             original premises: {original_assertions:?}\nproof:\n{proof}"
        );
    }

    if let Some(carcara) = require_carcara_or_skip() {
        verify_alethe_with_carcara(
            &carcara,
            "qf_lia_ring_composed_divisibility",
            &problem,
            &proof,
        );
    }
}

#[test]
#[timeout(60_000)]
fn test_carcara_regression_parity_xor_unsat_valid() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };

    let problem = benchmark_content("benchmarks/smt/regression/parity_xor_unsat.smt2");
    let proof = solve_unsat_and_get_proof(&problem, "regression_parity_xor_unsat");
    verify_alethe_with_carcara(&carcara, "regression_parity_xor_unsat", &problem, &proof);
}

/// Multi-equality Farkas rebuild (the model-checker consumer `certify-all-n` initiation wall):
/// a conjunction of equalities substituted by preprocessing into a strict
/// inequality. The rebuilt proof — assume(and) + `and_pos` conjunct
/// extraction + ONE signed-coefficient `la_generic` lemma + resolution —
/// must be carcara-verifiable with NO trust allowance.
#[test]
#[timeout(60_000)]
fn test_carcara_trust_free_multi_equality_conjunction() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    const PROBLEM: &str = r#"
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(declare-const n Int)
(assert (and (= x n) (= y 0)))
(assert (< n (+ x y)))
(check-sat)
"#;
    let proof = solve_unsat_and_get_proof(PROBLEM, "trust_free_multi_equality_conjunction");
    assert!(
        !proof.contains(":rule trust"),
        "multi-equality conjunction proof must not contain trust steps:\n{proof}"
    );
    assert!(
        run_carcara_trust_free(
            &carcara,
            "trust_free_multi_equality_conjunction",
            PROBLEM,
            &proof
        ),
        "multi-equality conjunction proof must be trust-free verifiable by carcara"
    );
}

/// The disequality variant of the same wall: `x = n ∧ y = 0` against
/// `n ≠ x + y`. A single Farkas combination cannot orient the disequality
/// for printing, so the export must go through the `la_disequality` case
/// split (carcara validates that rule natively), with the equality units
/// extracted from the conjunction by `and_pos`.
#[test]
#[timeout(60_000)]
fn test_carcara_trust_free_multi_equality_diseq_split() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    const PROBLEM: &str = r#"
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(declare-const n Int)
(assert (and (= x n) (= y 0)))
(assert (not (= n (+ x y))))
(check-sat)
"#;
    let proof = solve_unsat_and_get_proof(PROBLEM, "trust_free_multi_equality_diseq_split");
    assert!(
        !proof.contains(":rule trust"),
        "multi-equality disequality proof must not contain trust steps:\n{proof}"
    );
    assert!(
        proof.contains(":rule la_disequality"),
        "expected the la_disequality case split:\n{proof}"
    );
    assert!(
        run_carcara_trust_free(
            &carcara,
            "trust_free_multi_equality_diseq_split",
            PROBLEM,
            &proof
        ),
        "multi-equality disequality proof must be trust-free verifiable by carcara"
    );
}
