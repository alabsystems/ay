// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// ===================================================================
// P5 iteration 3: proof coverage — self-concat equality reasoning
// ===================================================================

/// Self-concat equality: x = str.++(x, y) implies y = "".
/// This is a basic property the string solver must handle.
/// Reference: CVC5 check_self_concat_equalities.
#[test]
fn self_concat_equality_implies_empty() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= x (str.++ x y)))
(assert (not (= y "")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "x = x++y with y != \"\" should be unsat, got {ay:?}"
    );
}

/// Self-concat equality: x = str.++(y, x) implies y = "".
/// Symmetric case: prefix instead of suffix.
#[test]
fn self_concat_equality_prefix_implies_empty() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= x (str.++ y x)))
(assert (not (= y "")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "x = y++x with y != \"\" should be unsat, got {ay:?}"
    );
}

/// Self-concat with ground constant: x = str.++(x, "a") is UNSAT.
/// Because "a" cannot be empty, this is always contradictory.
#[test]
fn self_concat_ground_nonempty_suffix_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x (str.++ x "a")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "x = x++\"a\" should be unsat, got {ay:?}"
    );
}

// ===================================================================
// P5 iteration 3: proof coverage — extf string equality conflicts
// ===================================================================

/// str.replace(x, x, "") must equal "" when x is ground.
/// If x = "abc", then str.replace("abc", "abc", "") = "" is a tautology.
#[test]
fn replace_self_with_empty_is_empty() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x "abc"))
(assert (not (= (str.replace x x "") "")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "str.replace(\"abc\", \"abc\", \"\") = \"\" is a tautology, got {ay:?}"
    );
}

/// Ground str.indexof equality conflict: str.indexof("hello", "ll", 0) = 2.
/// If the solver asserts it equals something else, that's a conflict.
#[test]
fn ground_indexof_equality_conflict() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (not (= (str.indexof "hello" "ll" 0) 2)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "str.indexof(\"hello\", \"ll\", 0) = 2 should be derivable, got {ay:?}"
    );
}

/// Ground str.to_int range conflict: str.to_int(x) = -2 is impossible.
/// str.to_int returns -1 for non-digit strings and >= 0 for digit strings.
#[test]
fn str_to_int_out_of_range_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.to_int x) (- 2)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "str.to_int(x) = -2 is out of range, should be unsat, got {ay:?}"
    );
}

/// Ground str.to_code range conflict: str.to_code(x) = -2 is impossible.
/// str.to_code returns -1 for non-single-char strings and 0..196607 otherwise.
#[test]
fn str_to_code_out_of_range_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.to_code x) (- 2)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "str.to_code(x) = -2 is out of range, should be unsat, got {ay:?}"
    );
}

// ===================================================================
// P5 iteration 3: proof coverage — str.to_lower / str.to_upper
// ===================================================================

/// str.to_lower ground evaluation must produce correct result.
#[test]
fn to_lower_ground_eval_correct() {
    let smt = r#"
(set-logic QF_S)
(assert (not (= (str.to_lower "HELLO") "hello")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "str.to_lower(\"HELLO\") = \"hello\" is a tautology, got {ay:?}"
    );
}

/// str.to_upper ground evaluation must produce correct result.
#[test]
fn to_upper_ground_eval_correct() {
    let smt = r#"
(set-logic QF_S)
(assert (not (= (str.to_upper "hello") "HELLO")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "str.to_upper(\"hello\") = \"HELLO\" is a tautology, got {ay:?}"
    );
}

/// str.to_lower of str.to_upper is idempotent with str.to_lower.
/// Checks: NOT(str.to_lower(str.to_upper("HeLLo")) = "hello") should be UNSAT.
#[test]
fn to_lower_to_upper_composition() {
    let smt = r#"
(set-logic QF_S)
(assert (not (= (str.to_lower (str.to_upper "HeLLo")) "hello")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "str.to_lower(str.to_upper(\"HeLLo\")) = \"hello\" is a tautology, got {ay:?}"
    );
}

// ===================================================================
// P5 iteration 3: proof coverage — str.< / str.<= ordering
// ===================================================================

/// str.< lexicographic: "abc" < "abd" is true.
#[test]
fn str_lt_ground_true() {
    let smt = r#"
(set-logic QF_S)
(assert (not (str.< "abc" "abd")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "\"abc\" < \"abd\" is true, got {ay:?}"
    );
}

/// str.< lexicographic: "abd" < "abc" is false.
#[test]
fn str_lt_ground_false() {
    let smt = r#"
(set-logic QF_S)
(assert (str.< "abd" "abc"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "\"abd\" < \"abc\" is false, got {ay:?}"
    );
}

/// str.<= reflexive: "abc" <= "abc" is true.
#[test]
fn str_le_reflexive() {
    let smt = r#"
(set-logic QF_S)
(assert (not (str.<= "abc" "abc")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "\"abc\" <= \"abc\" is true (reflexive), got {ay:?}"
    );
}

// ===================================================================
// P5 iteration 3: proof coverage — str.is_digit
// ===================================================================

/// str.is_digit on single digit character is true.
#[test]
fn is_digit_single_digit_true() {
    let smt = r#"
(set-logic QF_S)
(assert (not (str.is_digit "5")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "str.is_digit(\"5\") should be true, got {ay:?}"
    );
}

/// str.is_digit on letter is false.
#[test]
fn is_digit_letter_false() {
    let smt = r#"
(set-logic QF_S)
(assert (str.is_digit "a"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "str.is_digit(\"a\") should be false, got {ay:?}"
    );
}

/// str.is_digit on multi-char string is false.
#[test]
fn is_digit_multi_char_false() {
    let smt = r#"
(set-logic QF_S)
(assert (str.is_digit "12"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "str.is_digit(\"12\") should be false (multi-char), got {ay:?}"
    );
}

// ===================================================================
// P5 iteration 3: #3850 verification — W14 tautology guard fix status
// ===================================================================

/// #3850 case 15: (not (= (str.contains "" x) (= x "")))
/// Previously false-Sat. Fixed: str.contains("", x) reduces to x = "".
#[test]
fn regression_3850_case_15_contains_empty_haystack() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (not (= (str.contains "" x) (= x ""))))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "#3850 case 15: contains empty haystack tautology should be unsat, got {ay:?}"
    );
}

/// #3850 case 127: (not (= (str.contains x (str.++ x x)) (= x "")))
/// Previously false-Sat. Fixed: infer_eqs_from_contains detects len(x++x) >= len(x).
#[test]
fn regression_3850_case_127_contains_self_concat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (not (= (str.contains x (str.++ x x)) (= x ""))))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "#3850 case 127: contains self-concat tautology should be unsat, got {ay:?}"
    );
}

/// #3850 case 130: (not (= (str.contains x (str.++ x y)) (= x (str.++ x y))))
/// Previously false-Sat. Fixed: infer_eqs_from_contains handles the x ++ y pattern.
#[test]
fn regression_3850_case_130_contains_x_concat_xy() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (not (= (str.contains x (str.++ x y)) (= x (str.++ x y)))))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "#3850 case 130: contains x concat xy tautology should be unsat, got {ay:?}"
    );
}

/// #3850 case 135: (not (= (= x (str.++ y x)) (= x (str.++ x y))))
/// Previously false-Sat. Fixed: AY now correctly returns unsat.
/// The self-concat symmetry `(= x (y ++ x)) <=> (= x (x ++ y))` holds because
/// both sides require `y = ""`, making the inner equalities equivalent.
#[test]
fn regression_3850_case_135_self_concat_symmetry() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (not (= (= x (str.++ y x)) (= x (str.++ x y)))))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "#3850 case 135: self-concat symmetry should be unsat, got {ay:?}"
    );
}

// ===================================================================
// Disequality explanation completeness (algorithm audit)
// ===================================================================

/// Deq explanation audit: two concatenations equal the same constant.
///
/// `str.++("a","b") != str.++("a","b")` is trivially UNSAT. Both sides
/// have singleton NFs that resolve to "ab" via nf_to_constant. The deq
/// checker's Check 3 fires. The explanation must be sound — even though
/// the two concat terms are in different EQCs, the conflict is valid
/// because the ground evaluation proves them equal.
///
/// Regression: check_normal_forms_deq Checks 2-4 produce explanations
/// containing only the disequality literal when state.explain() fails
/// (different EQCs). This is sound for ground terms but potentially
/// under-specified when non-ground equalities are involved.
#[test]
fn deq_explanation_ground_concat_equal_constant() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= x (str.++ "a" "b")))
(assert (= y (str.++ "a" "b")))
(assert (not (= x y)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "x=ab, y=ab, x!=y should be unsat, got {ay:?}"
    );
}

/// Deq explanation audit: variables equal to same constant via different paths.
///
/// x = str.++(a, b), a = "he", b = "llo" → x's NF resolves to "hello".
/// y = "hello" directly.
/// x != y is UNSAT because both resolve to "hello".
///
/// This exercises Check 3 of check_normal_forms_deq where the NFs resolve
/// to the same constant through different EQC paths. The explanation for
/// the conflict must include enough premises for the SAT solver to learn
/// a correct blocking clause.
#[test]
fn deq_explanation_variable_concat_vs_constant() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun a () String)
(declare-fun b () String)
(declare-fun x () String)
(assert (= a "he"))
(assert (= b "llo"))
(assert (= x (str.++ a b)))
(assert (not (= x "hello")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "x=str.++(a,b), a=he, b=llo, x!=hello should be unsat, got {ay:?}"
    );
}

/// Deq explanation audit: disequality with length-bridged concat equality.
///
/// x = str.++(y, z), len(y) = 1, len(z) = 2, y++z = "abc", x != "abc".
/// This should be UNSAT because x = y++z = "abc". Tests that the deq
/// explanation captures the transitive chain through the SLIA theory.
#[test]
fn deq_explanation_transitive_concat_chain() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert (= x (str.++ y z)))
(assert (= (str.++ y z) "abc"))
(assert (= (str.len y) 1))
(assert (= (str.len z) 2))
(assert (not (= x "abc")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "x=y++z, y++z=abc, x!=abc should be unsat, got {ay:?}"
    );
}
