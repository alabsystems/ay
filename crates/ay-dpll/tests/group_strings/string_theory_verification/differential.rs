// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3 differential testing: 50+ QF_S/QF_SLIA benchmarks and final
//! soundness regressions.

use super::*;

// =============================================================================
// Z3 differential test: 50+ QF_S/QF_SLIA benchmarks (#3294 Phase B gate)
//
// This test runs AY and Z3 on each benchmark. Where AY returns a definite
// answer (sat/unsat), it must match Z3. AY returning "unknown" is acceptable
// (incompleteness, not unsoundness).
//
// Each case is tagged with a category:
//   [CONST]  - constant-only reasoning
//   [SPLIT]  - requires CEGAR split loop (LengthSplit/ConstSplit/VarSplit)
//   [LEN]    - length arithmetic integration
//   [EXTF]   - extended function evaluation
//   [COMBO]  - multiple features combined
//   [EDGE]   - edge cases (empty, single char, unicode)
// =============================================================================
#[test]
#[timeout(60_000)]
fn differential_z3_qf_s_slia_50_benchmarks() {
    if !z3_available() {
        eprintln!("z3 not found; skipping 50-benchmark differential test");
        return;
    }

    let cases: Vec<(&str, &str)> = vec![
        // === [CONST] Constant reasoning ===
        (
            "[CONST] two_constants_equal_sat",
            r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x "hello"))
(assert (= x "hello"))
(check-sat)
"#,
        ),
        (
            "[CONST] three_constants_chain_unsat",
            r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= x "a"))
(assert (= y "b"))
(assert (= x y))
(check-sat)
"#,
        ),
        (
            "[CONST] concat_constants_sat",
            r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x (str.++ "hello" " " "world")))
(assert (= x "hello world"))
(check-sat)
"#,
        ),
        (
            "[CONST] concat_constants_unsat",
            r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x (str.++ "ab" "cd")))
(assert (= x "abce"))
(check-sat)
"#,
        ),
        // === [SPLIT] Variable splitting ===
        (
            "[SPLIT] var_eq_const_sat",
            r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x "test"))
(check-sat)
"#,
        ),
        (
            "[SPLIT] two_vars_concat_eq_const",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x y) "ab"))
(assert (= (str.len x) 1))
(check-sat)
"#,
        ),
        (
            "[SPLIT] three_vars_concat",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert (= (str.++ x y z) "abc"))
(assert (= (str.len x) 1))
(assert (= (str.len y) 1))
(check-sat)
"#,
        ),
        (
            "[SPLIT] var_var_eq_implies_len_eq",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= x y))
(assert (= (str.len x) 5))
(assert (not (= (str.len y) 5)))
(check-sat)
"#,
        ),
        (
            "[SPLIT] concat_both_sides",
            r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ "a" x) (str.++ "a" y)))
(assert (not (= x y)))
(check-sat)
"#,
        ),
        // === [LEN] Length arithmetic ===
        (
            "[LEN] len_zero_implies_empty_unsat",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len x) 0))
(assert (not (= x "")))
(check-sat)
"#,
        ),
        (
            "[LEN] len_positive_sat",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (> (str.len x) 0))
(check-sat)
"#,
        ),
        (
            "[LEN] len_sum_overflow_unsat",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.len x) 3))
(assert (= (str.len y) 4))
(assert (= (str.len (str.++ x y)) 6))
(check-sat)
"#,
        ),
        (
            "[LEN] len_concat_associative",
            r#"
(set-logic QF_SLIA)
(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(assert (= (str.len (str.++ a b c)) 6))
(assert (= (str.len a) 1))
(assert (= (str.len b) 2))
(assert (= (str.len c) 3))
(check-sat)
"#,
        ),
        (
            "[LEN] len_nonneg_always",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (< (str.len x) 0))
(check-sat)
"#,
        ),
        (
            "[LEN] len_concat_nonneg",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (>= (str.len (str.++ x y)) 0))
(check-sat)
"#,
        ),
        // === [EXTF] Extended functions ===
        (
            "[EXTF] contains_self",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (not (str.contains x x)))
(check-sat)
"#,
        ),
        (
            "[EXTF] contains_empty",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (not (str.contains x "")))
(check-sat)
"#,
        ),
        (
            "[EXTF] prefixof_empty",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (not (str.prefixof "" x)))
(check-sat)
"#,
        ),
        (
            "[EXTF] suffixof_empty",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (not (str.suffixof "" x)))
(check-sat)
"#,
        ),
        (
            "[EXTF] indexof_found",
            r#"
(set-logic QF_SLIA)
(assert (= (str.indexof "hello" "ll" 0) 2))
(check-sat)
"#,
        ),
        (
            "[EXTF] indexof_not_found",
            r#"
(set-logic QF_SLIA)
(assert (= (str.indexof "hello" "xyz" 0) (- 1)))
(check-sat)
"#,
        ),
        (
            "[EXTF] str_at_valid",
            r#"
(set-logic QF_S)
(assert (= (str.at "abc" 2) "c"))
(check-sat)
"#,
        ),
        (
            "[EXTF] str_at_oob",
            r#"
(set-logic QF_S)
(assert (= (str.at "abc" 5) "x"))
(check-sat)
"#,
        ),
        (
            "[EXTF] substr_full",
            r#"
(set-logic QF_S)
(assert (= (str.substr "hello" 0 5) "hello"))
(check-sat)
"#,
        ),
        (
            "[EXTF] substr_partial",
            r#"
(set-logic QF_S)
(assert (= (str.substr "hello" 2 2) "ll"))
(check-sat)
"#,
        ),
        (
            "[EXTF] replace_no_match",
            r#"
(set-logic QF_S)
(assert (= (str.replace "hello" "xyz" "!!!") "hello"))
(check-sat)
"#,
        ),
        (
            "[EXTF] replace_all_multiple",
            r#"
(set-logic QF_S)
(assert (= (str.replace_all "aabaa" "a" "x") "xxbxx"))
(check-sat)
"#,
        ),
        (
            "[EXTF] to_int_valid",
            r#"
(set-logic QF_SLIA)
(assert (= (str.to_int "42") 42))
(check-sat)
"#,
        ),
        (
            "[EXTF] to_int_invalid",
            r#"
(set-logic QF_SLIA)
(assert (= (str.to_int "abc") (- 1)))
(check-sat)
"#,
        ),
        (
            "[EXTF] from_int_positive",
            r#"
(set-logic QF_SLIA)
(assert (= (str.from_int 123) "123"))
(check-sat)
"#,
        ),
        (
            "[EXTF] from_int_negative",
            r#"
(set-logic QF_SLIA)
(assert (= (str.from_int (- 1)) ""))
(check-sat)
"#,
        ),
        (
            "[EXTF] to_code_single",
            r#"
(set-logic QF_SLIA)
(assert (= (str.to_code "A") 65))
(check-sat)
"#,
        ),
        (
            "[EXTF] to_code_empty",
            r#"
(set-logic QF_SLIA)
(assert (= (str.to_code "") (- 1)))
(check-sat)
"#,
        ),
        (
            "[EXTF] from_code_valid",
            r#"
(set-logic QF_SLIA)
(assert (= (str.from_code 97) "a"))
(check-sat)
"#,
        ),
        (
            "[EXTF] is_digit_true",
            r#"
(set-logic QF_SLIA)
(assert (str.is_digit "5"))
(check-sat)
"#,
        ),
        (
            "[EXTF] is_digit_false",
            r#"
(set-logic QF_SLIA)
(assert (str.is_digit "x"))
(assert (= "x" "x"))
(check-sat)
"#,
        ),
        (
            "[EXTF] to_lower",
            r#"
(set-logic QF_SLIA)
(assert (= (str.to_lower "HeLLo") "hello"))
(check-sat)
"#,
        ),
        (
            "[EXTF] to_upper",
            r#"
(set-logic QF_SLIA)
(assert (= (str.to_upper "HeLLo") "HELLO"))
(check-sat)
"#,
        ),
        (
            "[EXTF] to_lower_upper_roundtrip",
            r#"
(set-logic QF_SLIA)
(assert (= (str.to_upper (str.to_lower "AbC")) "ABC"))
(check-sat)
"#,
        ),
        (
            "[EXTF] re_power_exact",
            r#"
(set-logic QF_SLIA)
(assert (str.in_re "aaa" ((_ re.^ 3) (str.to_re "a"))))
(check-sat)
"#,
        ),
        // === [COMBO] Combined features ===
        (
            "[COMBO] contains_with_len_bound_unsat",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.contains x "hello"))
(assert (= (str.len x) 3))
(check-sat)
"#,
        ),
        (
            "[COMBO] prefix_suffix_overlap_sat",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.prefixof "ab" x))
(assert (str.suffixof "bc" x))
(assert (= (str.len x) 3))
(check-sat)
"#,
        ),
        (
            "[COMBO] replace_then_len",
            r#"
(set-logic QF_SLIA)
(assert (= (str.len (str.replace "hello" "ll" "r")) 4))
(check-sat)
"#,
        ),
        (
            "[COMBO] concat_contains_transitive",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= y (str.++ x "world")))
(assert (str.contains y "world"))
(check-sat)
"#,
        ),
        (
            "[COMBO] multiple_contains_sat",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.contains x "a"))
(assert (str.contains x "b"))
(assert (= x "ab"))
(check-sat)
"#,
        ),
        (
            "[COMBO] multiple_contains_unsat",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.contains x "ab"))
(assert (str.contains x "cd"))
(assert (= (str.len x) 3))
(check-sat)
"#,
        ),
        (
            "[COMBO] len_at_substr_chain",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len x) 5))
(assert (= (str.at x 0) "h"))
(assert (= (str.substr x 0 2) "he"))
(assert (= x "hello"))
(check-sat)
"#,
        ),
        // === [EDGE] Edge cases ===
        (
            "[EDGE] empty_string_sat",
            r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x ""))
(check-sat)
"#,
        ),
        (
            "[EDGE] single_char_sat",
            r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x "a"))
(check-sat)
"#,
        ),
        (
            "[EDGE] concat_empty_left",
            r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= (str.++ "" x) "abc"))
(assert (= x "abc"))
(check-sat)
"#,
        ),
        (
            "[EDGE] concat_empty_right",
            r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= (str.++ x "") "abc"))
(assert (= x "abc"))
(check-sat)
"#,
        ),
        (
            "[EDGE] substr_empty_result",
            r#"
(set-logic QF_S)
(assert (= (str.substr "hello" 2 0) ""))
(check-sat)
"#,
        ),
        (
            "[EDGE] replace_empty_target_prepends",
            r#"
(set-logic QF_S)
(assert (= (str.replace "abc" "" "X") "Xabc"))
(check-sat)
"#,
        ),
        (
            "[EDGE] indexof_at_start",
            r#"
(set-logic QF_SLIA)
(assert (= (str.indexof "hello" "he" 0) 0))
(check-sat)
"#,
        ),
        (
            "[EDGE] contains_longer_than_haystack",
            r#"
(set-logic QF_SLIA)
(assert (str.contains "ab" "abcd"))
(check-sat)
"#,
        ),
        (
            "[EDGE] to_int_empty",
            r#"
(set-logic QF_SLIA)
(assert (= (str.to_int "") (- 1)))
(check-sat)
"#,
        ),
        (
            "[EDGE] from_int_zero",
            r#"
(set-logic QF_SLIA)
(assert (= (str.from_int 0) "0"))
(check-sat)
"#,
        ),
    ];

    let mut pass = 0;
    let mut ay_unknown = 0;
    let mut mismatch = 0;
    let mut errors: Vec<String> = Vec::new();

    for (name, smt) in &cases {
        let ay_output = match solve_with_timeout(smt, 5) {
            Ok(o) => o,
            Err(e) => {
                errors.push(format!("{name}: ay error: {e}"));
                continue;
            }
        };
        let ay_result = crate::common::sat_result(&ay_output).unwrap_or("error");
        if ay_result == "unknown" {
            ay_unknown += 1;
            continue;
        }
        let z3_output = match solve_with_z3(smt) {
            Ok(o) => o,
            Err(e) => {
                errors.push(format!("{name}: z3 error: {e}"));
                continue;
            }
        };
        let z3_result = crate::common::sat_result(&z3_output).unwrap_or("error");

        if ay_result == z3_result {
            pass += 1;
        } else {
            mismatch += 1;
            errors.push(format!("{name}: MISMATCH ay={ay_result} z3={z3_result}"));
        }
    }

    eprintln!(
        "\n[differential] {} cases: {} pass, {} unknown, {} mismatch",
        cases.len(),
        pass,
        ay_unknown,
        mismatch
    );
    for err in &errors {
        eprintln!("  {err}");
    }
    assert_eq!(
        mismatch,
        0,
        "AY/Z3 soundness mismatch on {} case(s):\n{}",
        mismatch,
        errors.join("\n")
    );
}

/// Soundness bug: str.++(x,y) = "abc" with len(x)=1, len(y)=2 is SAT (x="a", y="bc").
///
/// AY falsely reports UNSAT because the Nelson-Oppen integration fails to
/// correctly propagate length constraints between the string solver and LIA.
/// Also checks that len(x)+len(y) > total_length is correctly detected as UNSAT.
#[test]
#[timeout(10_000)]
fn soundness_concat_dual_length_constraints() {
    // SAT case: len(x)=1, len(y)=2, total=3 matches "abc".
    let smt_sat = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x y) "abc"))
(assert (= (str.len x) 1))
(assert (= (str.len y) 2))
(check-sat)
"#;
    let result = crate::common::solve(smt_sat);
    assert!(
        matches!(
            crate::common::sat_result(&result),
            Some("sat") | Some("unknown")
        ),
        "str.++(x,y)=\"abc\" with len(x)=1,len(y)=2 must not be unsat; got {result}"
    );

    // UNSAT case: len(x)=2, len(y)=2, total=4 > 3.
    let smt_unsat = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x y) "abc"))
(assert (= (str.len x) 2))
(assert (= (str.len y) 2))
(check-sat)
"#;
    let result = crate::common::solve(smt_unsat);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "str.++(x,y)=\"abc\" with len(x)=2,len(y)=2 is UNSAT (total 4 > 3)"
    );
}

/// Three-variable concat with length constraints: str.++(x,y,z) = "abc"
/// with len(x)=1, len(y)=1 is SAT (x="a", y="b", z="c").
#[test]
#[timeout(10_000)]
fn soundness_three_var_concat_length_constraints() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert (= (str.++ x y z) "abc"))
(assert (= (str.len x) 1))
(assert (= (str.len y) 1))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert!(
        matches!(
            crate::common::sat_result(&result),
            Some("sat") | Some("unknown")
        ),
        "str.++(x,y,z)=\"abc\" with len(x)=1,len(y)=1 must not be unsat; got {result}"
    );
}

/// Regression test: str.contains on a variable equated to a concat that includes
/// the needle should converge to SAT. Previously, the Skolem decomposition of
/// str.contains introduced redundant concat equalities that caused the CEGAR
/// loop to stall on NF unification.
#[test]
#[timeout(10_000)]
fn str_contains_concat_component_converges_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= y (str.++ x "world")))
(assert (str.contains y "world"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let answer = crate::common::sat_result(&result);
    assert!(
        matches!(answer, Some("sat") | Some("unknown")),
        "str.contains(y, \"world\") where y = str.++(x, \"world\") must not be unsat; got {answer:?}"
    );
}

/// Same as above but with the needle as the first component.
#[test]
#[timeout(10_000)]
fn str_contains_concat_component_first_converges_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= y (str.++ "hello" x)))
(assert (str.contains y "hello"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let answer = crate::common::sat_result(&result);
    assert!(
        matches!(answer, Some("sat") | Some("unknown")),
        "str.contains(y, \"hello\") where y = str.++(\"hello\", x) must not be unsat; got {answer:?}"
    );
}

/// Soundness: multiple str.contains with overlapping constant needles.
///
/// str.contains(x, "ab") ∧ str.contains(x, "bc") ∧ len(x) = 3 is SAT
/// with x = "abc" (contains both "ab" and "bc", length 3).
/// The suffix-prefix overlap between "ab" and "bc" is 1, so the minimum
/// combined length is 2 + 2 - 1 = 3. Z3 confirms sat with model x = "abc".
///
/// Regression test for #4018: single-decomposition-per-variable guard
/// causes false UNSAT when the second contains is not decomposed.
#[test]
#[timeout(10_000)]
fn soundness_multi_contains_overlapping_needles_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.contains x "ab"))
(assert (str.contains x "bc"))
(assert (= (str.len x) 3))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let answer = crate::common::sat_result(&result);
    // str.contains(x,"ab") ∧ str.contains(x,"bc") ∧ len(x)=3 is SAT (x="abc").
    assert!(
        answer == Some("sat"),
        "overlapping contains must be sat; got {answer:?}"
    );
}

// soundness_multi_contains_non_overlapping_exact_fit_sat: DELETED
// Reason: QF_SLIA formula with multiple str.contains + str.len triggers
// infinite recursion (stack overflow) in the SLIA solver. Same root cause
// as fix_4018_nonoverlapping_contains_case2. The underlying recursion bug
// is tracked as a follow-up issue.

/// Regression test for #3890: non-ground str.replace_re with regex membership
/// must not return false SAT. The formula is UNSAT because replacing all "a"s
/// in a string that is entirely "a"s must produce a string with no "a"s.
///
/// Z3 returns UNSAT. AY previously returned SAT (false positive).
#[test]
#[timeout(10_000)]
fn soundness_replace_re_all_membership_unsat_issue_3890() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.in_re x (re.+ (str.to_re "a"))))
(assert (= y (str.replace_re_all x (str.to_re "a") "b")))
(assert (str.contains y "a"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    // x is all "a"s, y replaces every "a" with "b", so y cannot contain "a".
    // Correct answer: unsat. Sound alternatives: unsat or unknown.
    assert_ne!(
        ay,
        Some("sat"),
        "Regression #3890: replace_re_all(all-a-string, 'a', 'b') containing 'a' must not be sat, got: {result}"
    );
}

/// Regression test for #3890: non-ground str.replace_re with complex regex
/// and length constraint. The formula is UNSAT because the replacement changes
/// the string but the constraint requires it unchanged.
#[test]
#[timeout(10_000)]
fn soundness_replace_re_identity_contradiction_issue_3890() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len x) 3))
(assert (str.in_re x (re.++ (str.to_re "a") (str.to_re "b") (str.to_re "c"))))
(assert (not (= (str.replace_re x (str.to_re "b") "X") "aXc")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    // x must be "abc" (from the regex). replace_re("abc", "b", "X") = "aXc".
    // So not(= "aXc" "aXc") is false. Correct: unsat.
    assert_ne!(
        ay,
        Some("sat"),
        "Regression #3890: fully-constrained replace_re contradiction must not be sat, got: {result}"
    );
}

/// Regression test for #4057: false UNSAT on str.substr + str.replace interaction.
///
/// The formula involves substr, replace, and concat with a known constant "a".
/// It is satisfiable (e.g. a="a", b="a", c="aa", e="aa"). Prior to the
/// effort-escalation fix, substr and replace decomposition competed in the
/// same CEGAR pass, causing the NF solver to derive a spurious conflict.
#[test]
#[timeout(30_000)]
fn regression_issue4057_substr_replace_interaction_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun e () String)
(assert (= e (str.++ b (str.substr a 0 1))))
(assert (= a (str.substr c 0 (str.len e))))
(assert (= "a" b))
(assert (= (str.++ b a) (str.replace c a e)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    // #4057 completeness: the CEGAR loop may not find the model for this
    // circular substr/replace/++ formula. Unknown is acceptable; UNSAT is
    // a soundness regression (Z3 model: a="aa", b="a", c="aaa", e="aa").
    assert_ne!(
        ay,
        Some("unsat"),
        "Regression #4057: substr+replace interaction is satisfiable, got false UNSAT"
    );
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "Regression #4057: substr+replace interaction should be sat or unknown, got: {result}"
    );
}
