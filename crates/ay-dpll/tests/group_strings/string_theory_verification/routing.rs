// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Logic acceptance and ill-typed rejection tests.

use super::*;

#[test]
#[timeout(10_000)]
fn str_pred_small_rw_negated_equivalences_are_unsat_issue_3850() {
    let cases = [
        (
            "str-pred-small-rw_15",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (not (= (str.contains "" x) (= x ""))))
(check-sat)
"#,
        ),
        (
            "str-pred-small-rw_127",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (not (= (str.contains x (str.++ x x)) (= x ""))))
(check-sat)
"#,
        ),
        (
            "str-pred-small-rw_130",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (not (= (str.contains x (str.++ x y)) (= x (str.++ x y)))))
(check-sat)
"#,
        ),
        (
            "str-pred-small-rw_135",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (not (= (= x (str.++ y x)) (= x (str.++ x y)))))
(check-sat)
"#,
        ),
        (
            "str-pred-small-rw_137",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (not (= (str.contains x (str.++ y x)) (= x (str.++ x y)))))
(check-sat)
"#,
        ),
    ];

    for (name, smt) in cases {
        let ay_output = crate::common::solve(smt);
        assert_ne!(
            crate::common::sat_result(&ay_output),
            Some("sat"),
            "{name}: AY must not return sat on this known-unsat equivalence, got output:\n{ay_output}"
        );

        if z3_available() {
            let z3_output = solve_with_z3(smt).expect("z3 solve");
            assert_eq!(
                crate::common::sat_result(&z3_output),
                Some("unsat"),
                "{name}: Z3 expected unsat, got output:\n{z3_output}"
            );
        }
    }
}

#[test]
#[timeout(10_000)]
fn qf_s_logic_is_accepted() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x "a"))
(assert (= x "b"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(result.trim(), "unsat");
}

#[test]
#[timeout(10_000)]
fn qf_slia_logic_is_accepted() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun n () Int)
(assert (= (str.len x) n))
(assert (= n 3))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(result.trim(), "sat");
}

#[test]
#[timeout(10_000)]
fn qf_snia_logic_routes_to_strings_lia_when_linear() {
    let smt = r#"
(set-logic QF_SNIA)
(declare-fun x () String)
(assert (= x "a"))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_ok(),
        "QF_SNIA should be recognized, got: {result:?}"
    );
    assert_eq!(
        crate::common::sat_result(&result.unwrap_or_default()),
        Some("sat")
    );
}

#[test]
#[timeout(10_000)]
fn qf_s_check_sat_assuming_routes() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x "a"))
(check-sat-assuming ((= x "b")))
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "check-sat-assuming should use QF_S routing"
    );
}

#[test]
#[timeout(10_000)]
fn qf_slia_check_sat_assuming_routes() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun n () Int)
(assert (= (str.len x) n))
(assert (= n 0))
(check-sat-assuming ((> n 0)))
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "check-sat-assuming should use QF_SLIA routing"
    );
}

#[test]
#[timeout(10_000)]
fn qf_slia_check_sat_assuming_multi_bound_bad_candidate_not_sat_issue_7464() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x y) "abc"))
(assert (= (str.len x) 2))
(assert (= (str.len y) 2))
(check-sat-assuming ((= x "ab")))
"#;
    let result = crate::common::solve(smt);
    assert_ne!(
        crate::common::sat_result(&result),
        Some("sat"),
        "multi-bound SLIA assumption solve must not return false sat (#7464): {result}"
    );
}

#[test]
#[timeout(10_000)]
fn qf_slia_check_sat_assuming_multi_bound_good_candidate_sat_issue_7464() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x y) "abcd"))
(assert (= (str.len x) 2))
(assert (= (str.len y) 2))
(check-sat-assuming ((= x "ab")))
"#;
    let result = crate::common::solve(smt);
    assert!(
        matches!(
            crate::common::sat_result(&result),
            Some("sat") | Some("unknown")
        ),
        "consistent multi-bound SLIA assumption solve must not be unsat (#7464): {result}"
    );
}

#[test]
#[timeout(10_000)]
fn qf_slia_check_sat_assuming_upgrades_seq_terms_from_assumptions() {
    let smt = r#"
(set-logic QF_SLIA)
(check-sat-assuming ((= (seq.len (seq.unit 1)) 0)))
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "assumption-only Seq terms in QF_SLIA should upgrade to QF_SEQLIA routing"
    );
}

#[test]
#[timeout(10_000)]
fn str_concat_is_typed() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x y) x))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(result.is_ok(), "str.++ should elaborate, got: {result:?}");
}

#[test]
#[timeout(10_000)]
fn str_len_is_typed() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len x) 0))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(result.is_ok(), "str.len should elaborate, got: {result:?}");
}

#[test]
#[timeout(10_000)]
fn str_predicates_are_typed() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.contains x y))
(assert (str.prefixof x y))
(assert (str.suffixof x y))
(assert (str.< x y))
(assert (str.<= x y))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_ok(),
        "string predicates should elaborate, got: {result:?}"
    );
}

#[test]
#[timeout(10_000)]
fn regex_membership_smoke_parses_and_elaborates() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (str.in_re x (re.* (str.to_re "a"))))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_ok(),
        "(str.in_re x (re.* (str.to_re \"a\"))) should elaborate, got: {result:?}"
    );
}

#[test]
#[timeout(10_000)]
fn regex_membership_ground_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x "aaaa"))
(assert (str.in_re x (re.* (str.to_re "a"))))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(ay, Some("sat"), "ground membership should be sat");
}

#[test]
#[timeout(10_000)]
fn regex_membership_ground_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x "ab"))
(assert (str.in_re x (re.* (str.to_re "a"))))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "ground membership mismatch should be unsat"
    );
}

#[test]
#[timeout(10_000)]
fn regex_negative_membership_ground_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x "aaaa"))
(assert (not (str.in_re x (re.* (str.to_re "a")))))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "negative ground membership on matching string should be unsat"
    );
}

#[test]
#[timeout(10_000)]
fn str_substr_indexof_replace_are_typed() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun i () Int)
(assert (= (str.substr x i i) y))
(assert (= (str.indexof x y i) i))
(assert (= (str.replace x y x) x))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_ok(),
        "str.substr/indexof/replace should elaborate, got: {result:?}"
    );
}

#[test]
#[timeout(10_000)]
fn str_int_conversions_are_typed() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun i () Int)
(assert (= (str.to_int x) i))
(assert (= (str.to.int x) i))
(assert (= (str.from_int i) x))
(assert (= (int.to.str i) x))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_ok(),
        "conversion ops should elaborate, got: {result:?}"
    );
}

#[test]
#[timeout(10_000)]
fn str_len_rejects_non_string_argument() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.len 0) 0))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_err(),
        "str.len on Int should be rejected, got: {result:?}"
    );
}

// ── Ill-typed rejection tests (sort checking) ──────────────────────────

#[test]
#[timeout(10_000)]
fn str_concat_rejects_int_argument() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () Int)
(assert (= (str.++ x "a") "a"))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_err(),
        "str.++ with Int arg should be rejected, got: {result:?}"
    );
}

#[test]
#[timeout(10_000)]
fn str_at_rejects_string_index() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.at x "a") "a"))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_err(),
        "str.at with String index should be rejected, got: {result:?}"
    );
}

#[test]
#[timeout(10_000)]
fn str_contains_rejects_int_argument() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun n () Int)
(assert (str.contains n "a"))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_err(),
        "str.contains with Int arg should be rejected, got: {result:?}"
    );
}

#[test]
#[timeout(10_000)]
fn str_substr_rejects_wrong_types() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.substr x "a" 1) "a"))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_err(),
        "str.substr with String offset should be rejected, got: {result:?}"
    );
}

#[test]
#[timeout(10_000)]
fn str_indexof_rejects_wrong_types() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun n () Int)
(assert (= (str.indexof n "a" 0) 0))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_err(),
        "str.indexof with Int haystack should be rejected, got: {result:?}"
    );
}

#[test]
#[timeout(10_000)]
fn str_replace_rejects_int_argument() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun n () Int)
(assert (= (str.replace n "a" "b") "b"))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_err(),
        "str.replace with Int arg should be rejected, got: {result:?}"
    );
}

#[test]
#[timeout(10_000)]
fn str_to_int_rejects_int_argument() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun n () Int)
(assert (= (str.to_int n) 0))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_err(),
        "str.to_int with Int arg should be rejected, got: {result:?}"
    );
}

#[test]
#[timeout(10_000)]
fn str_to_dot_int_rejects_int_argument() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun n () Int)
(assert (= (str.to.int n) 0))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_err(),
        "str.to.int with Int arg should be rejected, got: {result:?}"
    );
}

#[test]
#[timeout(10_000)]
fn str_from_int_rejects_string_argument() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.from_int x) "0"))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_err(),
        "str.from_int with String arg should be rejected, got: {result:?}"
    );
}

#[test]
#[timeout(10_000)]
fn int_to_str_rejects_string_argument() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (int.to.str x) "0"))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_err(),
        "int.to.str with String arg should be rejected, got: {result:?}"
    );
}

#[test]
#[timeout(10_000)]
fn str_prefixof_rejects_int_argument() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun n () Int)
(assert (str.prefixof n "abc"))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_err(),
        "str.prefixof with Int arg should be rejected, got: {result:?}"
    );
}

#[test]
#[timeout(10_000)]
fn str_suffixof_rejects_int_argument() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun n () Int)
(assert (str.suffixof n "abc"))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_err(),
        "str.suffixof with Int arg should be rejected, got: {result:?}"
    );
}

#[test]
#[timeout(10_000)]
fn str_lt_rejects_int_argument() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun n () Int)
(declare-fun x () String)
(assert (str.< n x))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_err(),
        "str.< with Int arg should be rejected, got: {result:?}"
    );
}

#[test]
#[timeout(10_000)]
fn str_le_rejects_int_argument() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun n () Int)
(declare-fun x () String)
(assert (str.<= n x))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_err(),
        "str.<= with Int arg should be rejected, got: {result:?}"
    );
}

#[test]
#[timeout(10_000)]
fn str_is_digit_is_typed() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.is_digit x))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_ok(),
        "str.is_digit should elaborate, got: {result:?}"
    );
}

#[test]
#[timeout(10_000)]
fn str_is_digit_rejects_int_argument() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun n () Int)
(assert (str.is_digit n))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_err(),
        "str.is_digit with Int arg should be rejected, got: {result:?}"
    );
}

#[test]
#[timeout(10_000)]
fn str_concat_rejects_single_argument() {
    // str.++ requires at least 2 arguments
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= (str.++ x) x))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_err(),
        "str.++ with 1 arg should be rejected, got: {result:?}"
    );
}

#[test]
#[timeout(10_000)]
fn str_len_rejects_wrong_arity() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len x x) 0))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_err(),
        "str.len with 2 args should be rejected, got: {result:?}"
    );
}

#[test]
#[timeout(10_000)]
fn str_at_rejects_wrong_arity() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.at x 0 1) "a"))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_err(),
        "str.at with 3 args should be rejected, got: {result:?}"
    );
}
