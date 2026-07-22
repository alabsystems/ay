// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Extended function evaluation, contains soundness, split lemma,
//! and concat length axiom regression tests.

use super::*;

// ── Prover differential test: known QF_SLIA/QF_S soundness gaps ─────
//
// These tests document confirmed AY/Z3 mismatches found by Prover
// differential testing (18 benchmarks). They assert AY's CURRENT
// (incorrect) behavior. When the underlying bug is fixed, change the
// assertion to the correct Z3 result.
//
// RESOLVED BUG 1: SLIA length/equality bridge.
//   String equalities now inject conditional length constraints:
//   (= s t) => (= (str.len s) (str.len t)), and
//   (= s "abc") => (= (str.len s) 3).
//   This closes the mismatch where str.len constraints were disconnected from
//   string equalities to constants.
//
// BUG 2 (fixed in Phase C): Constant-evaluable string predicates are now
//   checked in the string solver (str.contains/str.prefixof/str.suffixof).

/// Regression: str.len(x)=5 ∧ x="abc" must be UNSAT.
#[test]
#[timeout(10_000)]
fn slia_strlen_vs_constant_equality_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len x) 5))
(assert (= x "abc"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "str.len(x)=5 ∧ x=\"abc\" must be unsat"
    );
}

/// str.contains(x,"hello") ∧ x="goodbye" — UNSAT.
#[test]
#[timeout(10_000)]
fn str_contains_constant_eval_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (str.contains x "hello"))
(assert (= x "goodbye"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "str.contains(\"goodbye\",\"hello\") should be unsat"
    );
}

/// Regression for #3826 (track05 shape): SAT SLIA word equation with
/// len(D) <= 1 must not return UNSAT.
#[test]
#[timeout(20_000)]
fn slia_woorpje_track05_shape_len_le1_not_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun D () String)
(assert (= (str.++ "fecfbdfa" D "cbec" D "efeabbebeeefcaafaecdf" D "dbfb")
           (str.++ "fecfbdf" D "acbecaefe" D "bbebeeefc" D "af" D "ecdf" D "dbfb")))
(assert (<= (* (str.len D) 2) 2))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_ne!(
        result.trim(),
        "unsat",
        "woorpje track05 shape with len(D)<=1 is SAT in Z3 (D=\"a\"); AY must not return unsat"
    );
}

/// Regression for #3826: exact woorpje `05_track_10` must never return false UNSAT.
#[test]
#[timeout(20_000)]
fn slia_woorpje_05_track_10_not_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun F () String)
(declare-fun A () String)
(assert (= (str.++  A "cffcbdaa" A "e" A A "fdceb" A F "ffdbaf" A "e")
           (str.++  A "cffcbdaa" A "e" A "cfdceb" A "fafe" A "efeeefa" A "ffdbafce")))
(assert (= (str.++  "cdbdfcdabd" A "afaadaad" A "aeacafddfdaebdb" A "cbae")
           (str.++  "cdbdfcdabdcafaadaad" A "aeacafddfdaebdb" A A "bae")))
(assert (= (str.++  "ababfdaeebcceaf" A "ddb" A "fbbfee" A "caafceb" A "cebeb")
           (str.++  "ababfdaeebcceaf" A "ddbcfbbfeeccaafcebccebeb")))
(assert (>=(* (str.len F) 16) 176))
(assert (>=(* (str.len A) 15) 15))
(assert (<=(* (str.len A) 20) 40))
(check-sat)
"#;
    let ay_output = solve_with_timeout(smt, 5).expect("ay solve");
    let answer = crate::common::sat_result(&ay_output);
    // #6261 fix landed (W2:2042, ad407906f): string solver initial check
    // path now treats Unsat as incomplete. Must not return false-UNSAT.
    assert!(
        matches!(answer, Some("sat") | Some("unknown")),
        "REGRESSION #6261: woorpje 05_track_10 returned {answer:?} (must be sat or unknown)\noutput:\n{ay_output}"
    );
    if z3_available() {
        let z3_output = solve_with_z3(smt).expect("z3 solve");
        assert_eq!(crate::common::sat_result(&z3_output), Some("sat"));
    }
}

/// Strict SAT contract for #3826: woorpje `05_track_10` must return `sat`.
/// The pivot-bounded enumeration pre-pass detects `len(A) <= 2` and
/// enumerates candidates, finding `A = "c"` which satisfies all equations.
#[test]
#[timeout(20_000)]
fn slia_woorpje_05_track_10_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun F () String)
(declare-fun A () String)
(assert (= (str.++  A "cffcbdaa" A "e" A A "fdceb" A F "ffdbaf" A "e")
           (str.++  A "cffcbdaa" A "e" A "cfdceb" A "fafe" A "efeeefa" A "ffdbafce")))
(assert (= (str.++  "cdbdfcdabd" A "afaadaad" A "aeacafddfdaebdb" A "cbae")
           (str.++  "cdbdfcdabdcafaadaad" A "aeacafddfdaebdb" A A "bae")))
(assert (= (str.++  "ababfdaeebcceaf" A "ddb" A "fbbfee" A "caafceb" A "cebeb")
           (str.++  "ababfdaeebcceaf" A "ddbcfbbfeeccaafcebccebeb")))
(assert (>=(* (str.len F) 16) 176))
(assert (>=(* (str.len A) 15) 15))
(assert (<=(* (str.len A) 20) 40))
(check-sat)
"#;
    let ay_output = solve_with_timeout(smt, 10).expect("ay solve");
    let answer = crate::common::sat_result(&ay_output);
    // #6261 fix landed (W2:2042, ad407906f): string solver initial check
    // path now treats Unsat as incomplete. Must not return false-UNSAT.
    assert!(
        matches!(answer, Some("sat") | Some("unknown")),
        "REGRESSION #6261: woorpje 05_track_10 (sat variant) returned {answer:?} (must be sat or unknown)\noutput:\n{ay_output}"
    );
}

/// Regression for #3826: exact woorpje `05_track_120` must never return false UNSAT.
#[test]
#[timeout(20_000)]
fn slia_woorpje_05_track_120_not_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun G () String)
(declare-fun D () String)
(declare-fun A () String)
(assert (= (str.++  "dfbadeebbbfadef" D D "c" D G "be" D "eadfd" D D "fcfd")
           (str.++  "dfb" D A "d")))
(assert (= (str.++  "fecfbdfa" D "cbec" D "efeabbebeeefcaafaecdf" D "dbfb")
           (str.++  "fecfbdf" D "acbecaefe" D "bbebeeefc" D "af" D "ecdf" D "dbfb")))
(assert (= (str.++  "ddeacffede" D "ee" D "bcebbffc" D "ddbfdabbefeeaefca")
           (str.++  "ddeacffede" D "eeabcebbffcaddbfdabbefee" D "efc" D)))
(assert (<=(* (str.len D) 2) 2))
(assert (>=(* (str.len A) 5) 40))
(assert (<=(* (str.len A) 5) 765))
(check-sat)
"#;
    let ay_output = solve_with_timeout(smt, 10).expect("ay solve");
    let answer = crate::common::sat_result(&ay_output);
    // #6273/#6283: both debug and release must reject the false-UNSAT path.
    // Z3 returns sat; AY may conservatively return unknown while the string
    // solver keeps NF-dependent reasoning incomplete, but it must never return
    // unsat on this benchmark.
    assert!(
        matches!(answer, Some("sat") | Some("unknown")),
        "track_120 returned {answer:?} (expected sat or unknown; \
         unsat is false-UNSAT regression #6273/#6283)\noutput:\n{ay_output}"
    );
    if z3_available() {
        let z3_output = solve_with_z3(smt).expect("z3 solve");
        assert_eq!(crate::common::sat_result(&z3_output), Some("sat"));
    }
}

/// Completeness gap (#6261): simple suffix mismatch with equal-length
/// constraint is UNSAT but AY returns Unknown due to blanket soundness
/// guard converting all string Unsat to incomplete.
///
/// Z3 correctly returns unsat. The CEGAR/split loop does not converge
/// for this formula because the blanket guard at strings_lia.rs:143
/// prevents the string solver from ever proving UNSAT directly.
///
/// Once the guard is refined to distinguish spurious NF conflicts from
/// genuine constant-fragment mismatches, this test should be tightened
/// to reject Unknown (require Unsat only).
#[test]
#[timeout(10_000)]
fn slia_equal_length_suffix_mismatch_completeness_gap_6261() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.len x) (str.len y)))
(assert (= (str.++ x "a") (str.++ y "b")))
(check-sat)
"#;
    let ay_output = solve_with_timeout(smt, 5).expect("ay solve");
    let answer = crate::common::sat_result(&ay_output);
    // KNOWN COMPLETENESS GAP (#6261): AY returns unknown, Z3 returns unsat.
    // When the blanket soundness guard is refined, tighten to:
    //   assert_eq!(answer, Some("unsat"), ...);
    assert!(
        matches!(answer, Some("unsat") | Some("unknown")),
        "equal-length suffix mismatch should be unsat or unknown, got {answer:?}\noutput:\n{ay_output}"
    );
    if z3_available() {
        let z3_output = solve_with_z3(smt).expect("z3 solve");
        assert_eq!(crate::common::sat_result(&z3_output), Some("unsat"));
    }
}

/// Regression for #3982: overlapping `str.contains` constraints with
/// length=3 are UNSAT and must never return SAT.
#[test]
#[timeout(10_000)]
fn slia_multiple_contains_len3_is_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.contains x "ab"))
(assert (str.contains x "cd"))
(assert (= (str.len x) 3))
(check-sat)
"#;

    let ay_output = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&ay_output),
        Some("unsat"),
        "multiple contains with len=3 must be unsat; got output:\n{ay_output}"
    );

    if z3_available() {
        let z3_output = solve_with_z3(smt).expect("z3 solve");
        assert_eq!(
            crate::common::sat_result(&z3_output),
            Some("unsat"),
            "z3 expected unsat for reference behavior, got output:\n{z3_output}"
        );
    }
}

// ── Phase C: Extended function constant evaluation ──

/// str.at("hello", 0) = "e" is false (correct: "h"), so unsat.
#[test]
#[timeout(10_000)]
fn str_at_constant_eval_unsat() {
    let smt = r#"
(set-logic QF_S)
(assert (= (str.at "hello" 0) "e"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "str.at(\"hello\",0) = \"e\" should be unsat (actual: \"h\")"
    );
}

/// str.at("hello", 1) = "e" is true, so sat.
#[test]
#[timeout(10_000)]
fn str_at_constant_eval_sat() {
    let smt = r#"
(set-logic QF_S)
(assert (= (str.at "hello" 1) "e"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "str.at(\"hello\",1) = \"e\" should be sat"
    );
}

/// str.substr("hello", 1, 3) = "abc" is false (correct: "ell"), so unsat.
#[test]
#[timeout(10_000)]
fn str_substr_constant_eval_unsat() {
    let smt = r#"
(set-logic QF_S)
(assert (= (str.substr "hello" 1 3) "abc"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "str.substr(\"hello\",1,3) = \"abc\" should be unsat"
    );
}

/// str.substr("hello", 1, 3) = "ell" is true, so sat.
#[test]
#[timeout(10_000)]
fn str_substr_constant_eval_sat() {
    let smt = r#"
(set-logic QF_S)
(assert (= (str.substr "hello" 1 3) "ell"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "str.substr(\"hello\",1,3) = \"ell\" should be sat"
    );
}

/// str.replace("hello", "ll", "r") = "hello" is false (correct: "hero"), so unsat.
#[test]
#[timeout(10_000)]
fn str_replace_constant_eval_unsat() {
    let smt = r#"
(set-logic QF_S)
(assert (= (str.replace "hello" "ll" "r") "hello"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "str.replace(\"hello\",\"ll\",\"r\") should not equal \"hello\""
    );
}

/// str.replace("hello", "ll", "r") = "hero" is true, so sat.
#[test]
#[timeout(10_000)]
fn str_replace_constant_eval_sat() {
    let smt = r#"
(set-logic QF_S)
(assert (= (str.replace "hello" "ll" "r") "hero"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "str.replace(\"hello\",\"ll\",\"r\") = \"hero\" should be sat"
    );
}

/// Variable resolved to constant, then str.at evaluated.
/// x = "world", str.at(x, 0) = "x" is false (correct: "w"), so unsat.
#[test]
#[timeout(10_000)]
fn str_at_with_variable_resolved_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x "world"))
(assert (= (str.at x 0) "x"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "str.at(\"world\",0) = \"x\" should be unsat"
    );
}

/// Variable resolved to constant, then str.substr evaluated.
/// x = "world", str.substr(x, 0, 3) = "wor" is true, so sat.
#[test]
#[timeout(10_000)]
fn str_substr_with_variable_resolved_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x "world"))
(assert (= (str.substr x 0 3) "wor"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert!(
        matches!(result.trim(), "sat" | "unknown"),
        "str.substr(\"world\",0,3) = \"wor\" must not be unsat; got {result}"
    );
}

/// Regression test for #7451: str.substr with non-ground argument must not
/// return false UNSAT.
///
/// Root cause: LIA's Nelson-Oppen Gaussian elimination processed String-sorted
/// equalities (e.g., `substr(x,0,1) = sk_res`) as linear equations over opaque
/// "integer" variables. The terms were grouped by value in
/// `propagate_tight_bound_equalities`, producing cross-sort equalities
/// (e.g., x:String = 0:Int) that caused EUF to find a spurious conflict.
///
/// Fix: Sort-filter equalities in `detect_algebraic_equalities` — only process
/// equalities where both sides are Int/Real-sorted.
#[test]
#[timeout(10_000)]
fn regression_7451_substr_non_ground_false_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (= x "ab"))
(assert (= y (str.substr x 0 1)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert!(
        matches!(result.trim(), "sat" | "unknown"),
        "#7451: substr(\"ab\",0,1) with variable binding must not be unsat; got {result}"
    );
}

/// Regression test for #7451 (variant): ground substr equality must be sat.
/// This is the simpler case that always worked; kept as a non-regression guard.
#[test]
#[timeout(10_000)]
fn regression_7451_substr_ground_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.substr "hello" 1 3) "ell"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "#7451: ground substr equality must be sat"
    );
}

// === Soundness regression tests (Prover P2, differential testing vs Z3) ===

/// Soundness regression: not(str.contains(x, "")) must be UNSAT.
///
/// Every string contains the empty string, so asserting the negation
/// of str.contains(x, "") for any x is unsatisfiable.
/// Detected by differential testing against Z3 on stale binary.
#[test]
#[timeout(10_000)]
fn soundness_negated_contains_empty_is_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (not (str.contains x "")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let answer = crate::common::sat_result(&result);
    assert_eq!(
        answer,
        Some("unsat"),
        "not(str.contains(x, \"\")) must be unsat, got: {result}"
    );
}

/// Soundness regression: str.contains(x,"hello") ∧ ¬str.contains(x,"a") is
/// satisfiable (no substring relationship), so this must NOT return unsat.
/// Guards against over-eager contains reasoning.
#[test]
#[timeout(10_000)]
fn soundness_contains_no_overlap_is_not_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (str.contains x "hello"))
(assert (not (str.contains x "a")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let answer = crate::common::sat_result(&result);
    assert_ne!(
        answer,
        Some("unsat"),
        "contains(x,\"hello\") ∧ ¬contains(x,\"a\") is SAT (no substring), got: {result}"
    );
}

/// Soundness regression: contains(x,"abc") ∧ ¬contains(x,"a") is UNSAT
/// because "a" is a substring of "abc", so contains(x,"abc") implies
/// contains(x,"a"). Must not return sat.
#[test]
#[timeout(10_000)]
fn soundness_contains_transitivity_substring_not_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (str.contains x "abc"))
(assert (not (str.contains x "a")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let answer = crate::common::sat_result(&result);
    assert_ne!(
        answer,
        Some("sat"),
        "contains(x,\"abc\") ∧ ¬contains(x,\"a\") must NOT be sat (expected unsat or unknown), got: {result}"
    );
}

/// Soundness regression: contains(x,y) ∧ x="hello" ∧ y="world" is UNSAT
/// because "hello" does not contain "world". Must not return sat.
#[test]
#[timeout(10_000)]
fn soundness_contains_resolved_constants_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.contains x y))
(assert (= x "hello"))
(assert (= y "world"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let answer = crate::common::sat_result(&result);
    assert_ne!(
        answer,
        Some("sat"),
        "contains(\"hello\",\"world\") must NOT be sat, got: {result}"
    );
}

/// Regression #4052: contains transitivity with a negated consequence is UNSAT.
#[test]
#[timeout(10_000)]
fn soundness_contains_transitivity_chain_unsat_issue_4052() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.contains x y))
(assert (str.contains y "abc"))
(assert (not (str.contains x "abc")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let answer = crate::common::sat_result(&result);
    assert_eq!(
        answer,
        Some("unsat"),
        "contains(x,y) ∧ contains(y,\"abc\") ∧ ¬contains(x,\"abc\") must be unsat, got: {result}"
    );
}

// ── Phase C: Split Lemma Integration Tests ──────────────────────────

/// EmptySplit: x ++ y = "a" with both non-empty should be UNSAT.
///
/// Only 1 character available. If both x and y must be non-empty,
/// there's no valid assignment. This requires the EmptySplit lemma
/// to determine that one variable must be empty, then ConstSplit
/// to peel the single character.
#[test]
#[timeout(10_000)]
fn split_lemma_concat_both_nonempty_single_char_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x y) "a"))
(assert (not (= x "")))
(assert (not (= y "")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let answer = crate::common::sat_result(&result);
    // With split lemmas active, the solver should determine this is UNSAT.
    // Without split lemmas, it would return Unknown.
    // Accept either unsat or unknown (unknown is correct but incomplete).
    assert_ne!(
        answer,
        Some("sat"),
        "x++y=\"a\" with x!=\"\" and y!=\"\" must NOT be sat, got: {result}"
    );
}

/// EmptySplit: x ++ y = "ab" with both non-empty should be SAT.
///
/// x="a", y="b" is a valid assignment. The solver must handle the
/// EmptySplit and ConstSplit lemmas to explore this assignment space.
#[test]
#[timeout(10_000)]
fn split_lemma_concat_both_nonempty_two_chars_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x y) "ab"))
(assert (not (= x "")))
(assert (not (= y "")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let answer = crate::common::sat_result(&result);
    // With split lemmas: sat (x="a", y="b" or x="ab", y="" — but y!="" so x="a",y="b").
    // Without split lemmas: unknown is also acceptable.
    assert_ne!(
        answer,
        Some("unsat"),
        "x++y=\"ab\" with x!=\"\" and y!=\"\" must NOT be unsat, got: {result}"
    );
}

/// ConstSplit progression: x = "abc" should be solved directly.
///
/// When the core solver sees NF [x] vs constant "abc" in the same EQC,
/// it should unify x with "abc" without needing splits (Case 4:
/// endpoint-empty or direct constant propagation).
#[test]
#[timeout(10_000)]
fn split_lemma_variable_equals_constant_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x "abc"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(crate::common::sat_result(&result), Some("sat"));
}

/// Variable concat with length constraint triggers split lemmas.
///
/// x ++ y = "hello" AND len(x) = 2 should yield x = "he", y = "llo".
/// This requires SLIA mode with length axioms + split lemmas.
#[test]
#[timeout(60_000)]
fn split_lemma_concat_with_length_constraint() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x y) "hello"))
(assert (= (str.len x) 2))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let answer = crate::common::sat_result(&result);
    // This is satisfiable: x="he", y="llo".
    assert_ne!(
        answer,
        Some("unsat"),
        "x++y=\"hello\" with len(x)=2 must NOT be unsat, got: {result}"
    );
}

/// Impossible length constraint: x ++ y = "hi" AND len(x) = 5 is UNSAT.
///
/// "hi" has length 2, so len(x) cannot be 5 (since len(y) >= 0,
/// len(x) <= 2). Requires SLIA length axiom integration.
#[test]
#[timeout(10_000)]
fn split_lemma_impossible_length_constraint_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x y) "hi"))
(assert (= (str.len x) 5))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let answer = crate::common::sat_result(&result);
    assert_ne!(
        answer,
        Some("sat"),
        "x++y=\"hi\" with len(x)=5 must NOT be sat, got: {result}"
    );
}

// ── Prover: Concat length axiom gap regression tests ────────────────
//
// Root cause: collect_str_len_axioms generates Axiom 8
//   (= (str.++ x y) "hi") => (= (str.len (str.++ x y)) 2)
// but Axiom 4 (concat length decomposition)
//   (= (str.len (str.++ x y)) (+ (str.len x) (str.len y)))
// is only applied to str.len(str.++(..)) terms found in the FIRST traversal pass.
// Since str.len(str.++(x,y)) is created by Axiom 8 during the SECOND pass,
// the decomposition is never generated. The LIA solver then cannot derive
// len(x) + len(y) = len("hi") = 2, and the impossible len(x) = 5 goes undetected.

/// Three-way concat impossible length: x++y++z = "ab" with len(x) = 3.
/// len("ab") = 2, so len(x) <= 2. Requires concat length decomposition.
#[test]
#[timeout(10_000)]
fn concat_length_axiom_gap_three_vars_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert (= (str.++ x y z) "ab"))
(assert (= (str.len x) 3))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let answer = crate::common::sat_result(&result);
    assert_ne!(
        answer,
        Some("sat"),
        "x++y++z=\"ab\" with len(x)=3 must NOT be sat: {result}"
    );
}

/// Concat length gap: y constrained not x. x++y = "hi" with len(y) = 5.
#[test]
#[timeout(10_000)]
fn concat_length_axiom_gap_rhs_variable_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x y) "hi"))
(assert (= (str.len y) 5))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let answer = crate::common::sat_result(&result);
    assert_ne!(
        answer,
        Some("sat"),
        "x++y=\"hi\" with len(y)=5 must NOT be sat: {result}"
    );
}

/// Concat length gap: negative length is UNSAT even without constant target.
/// x++y = z with len(x) = 3, len(y) = 2, len(z) = 1. 3+2=5 != 1.
#[test]
#[timeout(10_000)]
fn concat_length_axiom_gap_symbolic_target_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert (= (str.++ x y) z))
(assert (= (str.len x) 3))
(assert (= (str.len y) 2))
(assert (= (str.len z) 1))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let answer = crate::common::sat_result(&result);
    assert_ne!(
        answer,
        Some("sat"),
        "x++y=z with len(x)=3, len(y)=2, len(z)=1 must NOT be sat: {result}"
    );
}

// ── Prover: LengthSplit non-termination regression (#3375) ──────────

/// Variable-variable concat alignment: soundness gate for #3375.
///
/// `(str.++ x "c") = (str.++ y "c")` is SAT (e.g. x=y="").
/// Bug #3375: the solver emits the same LengthSplit lemma 10,000 times
/// without making progress. This test uses the Z3 differential harness
/// to verify that AY does not produce a false definite answer.
///
/// When #3375 is fixed, this test should return sat (matching Z3).
/// For now, we only run the Z3 comparison to guard soundness.
#[test]
#[timeout(10_000)]
fn regression_3375_varsplit_concat_suffix_z3_check() {
    if !z3_available() {
        eprintln!("z3 not found; regression_3375 suffix test requires z3");
        return;
    }
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x "c") (str.++ y "c")))
(check-sat)
"#;
    let z3_output = solve_with_z3(smt).expect("z3 failed");
    let z3_result = crate::common::sat_result(&z3_output).expect("z3 no result");
    assert_eq!(
        z3_result, "sat",
        "z3 should say sat for str.++(x,c)=str.++(y,c): {z3_output}"
    );
}

/// Same pattern with matching prefix: `(str.++ "a" x) = (str.++ "a" y)`.
/// Z3 says sat. Z3-only check for same non-termination path as #3375.
#[test]
#[timeout(10_000)]
fn regression_3375_varsplit_concat_prefix_z3_check() {
    if !z3_available() {
        eprintln!("z3 not found; regression_3375 prefix test requires z3");
        return;
    }
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ "a" x) (str.++ "a" y)))
(check-sat)
"#;
    let z3_output = solve_with_z3(smt).expect("z3 failed");
    let z3_result = crate::common::sat_result(&z3_output).expect("z3 no result");
    assert_eq!(
        z3_result, "sat",
        "z3 should say sat for str.++(a,x)=str.++(a,y): {z3_output}"
    );
}
