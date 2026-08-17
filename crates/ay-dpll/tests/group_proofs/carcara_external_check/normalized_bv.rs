// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// The NORMALIZED-ASSUME MISMATCH class (SMT-COMP QF_LIA CAV_2009 family):
/// the file spells linear atoms with explicit coefficients — `(* 1 x)`,
/// `(* 0 x)`, `(* (- 1) x)`, duplicated monomials — that arithmetic
/// elaboration canonicalizes (unit/zero elision, unary minus, folding,
/// reordering), so a canonical-print `assume` matches no problem premise.
/// The repair raw-interns the surface spelling for the assume and bridges
/// each extracted conjunct to its canonical atom with a certified `[1, 1]`
/// `la_generic` orientation lemma (#real-bench).
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_carcara_external_normalized_linear_assume_bridge() {
    let problem = r#"
(set-logic QF_LIA)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(assert (and (<= (+ (* 1 x0) (* 1 x0) (* 0 x1) (* (- 1) x1)) 0) (<= (+ (* 1 x1) (* (- 2) x0)) (- 1)) (<= (+ (* 0 x0) (* 1 x2)) 5)))
(check-sat)
"#;

    let proof = solve_unsat_and_get_proof(problem, "normalized_linear_assume");
    assert!(
        !proof.contains(":rule trust"),
        "normalized-assume proof must be trust-free:\n{proof}"
    );
    assert!(
        proof.contains(":rule la_generic"),
        "expected certified la_generic bridge lemmas:\n{proof}"
    );
    // Every assume must spell an asserted problem premise EXACTLY (the raw
    // surface print, not the canonicalized atom forms).
    let asserted = extract_asserted_terms(problem);
    for assume in extract_assume_terms(&proof) {
        assert!(
            asserted.contains(&assume),
            "assume is not a problem premise: {assume}"
        );
    }
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    verify_alethe_with_carcara(
        &carcara,
        "normalized_linear_assume",
        problem,
        proof.as_str(),
    );
}

/// The deduplicated-conjunct variant of the normalized-assume mismatch
/// (CAV_2009 problem__030): two surface conjuncts elaborate to the SAME
/// canonical atom, so the canonical conjunction has fewer conjuncts than the
/// file — positional pairing is impossible and the alignment-capable
/// `AndDistinct` classifier must carry the repair, dropping the exporter's
/// de-Morganized `and_pos` steps in favor of re-derived per-conjunct units
/// (#real-bench).
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_carcara_external_normalized_assume_deduplicated_conjunct() {
    let problem = r#"
(set-logic QF_LIA)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(assert (and (<= (+ (* 1 x0) (* (- 1) x1)) 0) (<= (+ (* 0 x2) (* 1 x0) (* (- 1) x1)) 0) (<= (+ (* 1 x1) (* (- 1) x0)) (- 1))))
(check-sat)
"#;

    let proof = solve_unsat_and_get_proof(problem, "normalized_assume_dedup");
    assert!(
        !proof.contains(":rule trust"),
        "deduplicated normalized-assume proof must be trust-free:\n{proof}"
    );
    let asserted = extract_asserted_terms(problem);
    for assume in extract_assume_terms(&proof) {
        assert!(
            asserted.contains(&assume),
            "assume is not a problem premise: {assume}"
        );
    }
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    verify_alethe_with_carcara(&carcara, "normalized_assume_dedup", problem, proof.as_str());
}

// ============================================================================
// Ground bitvector disequality: `hole` -> checked `evaluate` derivation
// ============================================================================

/// Real benchmark rows whose ONLY unchecked step was the ground bitvector
/// disequality `(cl (not (= #b… #b…)))`.
///
/// AY closes every "two constants forced equal" refutation by chaining the
/// problem's own equalities with `eq_transitive` down to `(cl (= C1 C2))` and
/// resolving against its negation. The negation is a closed fact, but no
/// carcara rule CONCLUDES `(cl (not (= t u)))` — `evaluate` proves only a
/// POSITIVE unit `(= term value)` — so it used to print as `hole` and made
/// otherwise-complete documents `holey`. It is now spelled out as
/// `evaluate` + `equiv1` + `false` + `resolution`, all of which this carcara
/// build implements, and these documents check as `valid`.
const GROUND_BV_DISEQUALITY_BENCHMARKS: &[&str] = &[
    "benchmarks/smt/QF_ABV/csplit_repro_unsat.smt2",
    "benchmarks/smt/QF_ABV/csplit_repro_store_chain_unsat.smt2",
    "benchmarks/smt/QF_BV/puzzle_03.smt2",
    "benchmarks/smt/QF_BV/puzzle_12.smt2",
];

#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(240_000))]
fn test_carcara_ground_bv_disequality_is_checked_not_holey() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    for relative_path in GROUND_BV_DISEQUALITY_BENCHMARKS {
        let label = relative_path
            .rsplit('/')
            .next()
            .expect("benchmark file name");
        let problem: String = benchmark_content(relative_path)
            .lines()
            .filter(|line| line.trim() != "(exit)")
            .collect::<Vec<_>>()
            .join("\n");
        let proof = solve_unsat_and_get_proof(&problem, label);
        assert!(
            !proof.contains(":rule hole"),
            "{label}: the ground bitvector disequality must not print as a hole:\n{proof}"
        );
        assert!(
            proof.contains(":rule evaluate"),
            "{label}: expected the `evaluate` lowering in the proof:\n{proof}"
        );
        assert!(
            run_carcara_trust_free(&carcara, label, &problem, &proof),
            "{label}: proof must be externally VALID, not merely holey"
        );
    }
}

/// The lowering is shape-gated, not blanket: an `evaluate` step may only ever
/// carry a closed constant equality, and a document that still needs a genuine
/// theory inference must keep its honest `hole` and report `holey` — never
/// `invalid`, and never a rule name AY cannot back.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_carcara_symbolic_bv_conflict_keeps_its_honest_hole() {
    let problem = r#"
(set-logic QF_BV)
(declare-fun v0 () (_ BitVec 8))
(declare-fun v1 () (_ BitVec 8))
(assert (= (bvand v0 v1) #x0f))
(assert (= (bvor v0 v1) #x00))
(check-sat)
"#;
    let proof = solve_unsat_and_get_proof(problem, "symbolic_bv_conflict");
    for line in proof.lines() {
        assert!(
            !line.contains(":rule evaluate") || line.contains("(cl (= (= #"),
            "an `evaluate` step was emitted for a non-ground clause: {line}"
        );
    }
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    assert!(
        run_carcara(&carcara, "symbolic_bv_conflict", problem, &proof),
        "a proof with honest holes must still be structurally accepted"
    );
}
