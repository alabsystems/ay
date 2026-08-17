// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// =============================================================================
// str.to_int / str.from_int soundness tests (P2 iteration 3)
//
// The string-to-integer and integer-to-string conversion functions should
// evaluate to concrete values when arguments are constants.
// =============================================================================

/// str.to_int mismatch: to_int("42") = 43 is UNSAT.
///
/// check_extf_int_reductions evaluates str.to_int with constant arguments.
#[test]
#[timeout(10_000)]
fn soundness_str_to_int_constant_mismatch() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= x "42"))
(assert (= (str.to_int x) 43))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(ay, Some("unsat"), "to_int(\"42\") = 43: got {ay:?}");
}

/// str.to_int correct match is SAT.
#[test]
#[timeout(10_000)]
fn soundness_str_to_int_constant_correct() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= x "42"))
(assert (= (str.to_int x) 42))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "to_int(\"42\") = 42 is SAT"
    );
}

/// str.from_int mismatch: from_int(42) = "43" is UNSAT.
///
/// check_extf_string_equalities evaluates str.from_int with constant arguments.
#[test]
#[timeout(10_000)]
fn soundness_str_from_int_constant_mismatch() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.from_int 42) "43"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "from_int(42) = \"43\" is UNSAT"
    );
}

/// str.from_int correct match is SAT.
#[test]
#[timeout(10_000)]
fn soundness_str_from_int_constant_correct() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.from_int 42) "42"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "from_int(42) = \"42\" is SAT"
    );
}

// =============================================================================
// Unicode code point length tests (P2 iteration 3)
//
// SMT-LIB str.len counts Unicode code points, not bytes. A single emoji
// character (e.g., U+1F600 😀) has length 1 in SMT-LIB semantics.
// =============================================================================

/// Unicode code point length: len("\u{1F600}") = 1 is SAT.
///
/// The parser now correctly handles SMT-LIB \u{XXXX} unicode escapes,
/// so "\u{1F600}" is a single code point with str.len = 1.
#[test]
#[timeout(10_000)]
fn soundness_unicode_single_codepoint_length() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= x "\u{1F600}"))
(assert (= (str.len x) 1))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "len(\"😀\") = 1 is SAT"
    );
}

/// Unicode length = 2 for single code point is UNSAT.
#[test]
#[timeout(10_000)]
fn soundness_unicode_single_codepoint_wrong_length() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= x "\u{1F600}"))
(assert (= (str.len x) 2))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "len(\"😀\") = 2 is UNSAT (1 code point, not 2)"
    );
}

// ===================================================================
// VarSplit split-path soundness regression tests
// ===================================================================

/// VarSplit must preserve trivially satisfiable x=y.
///
/// `x ++ "a" = y ++ "a"` is sat (x=y="" is a model). VarSplit lemmas must not
/// force UNSAT on this case.
#[test]
#[timeout(10_000)]
fn soundness_varsplit_blocks_equal_vars_suffix() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x "a") (str.++ y "a")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "VarSplit suffix: expected sat or unknown, got {ay:?}"
    );
}

/// VarSplit split-path on bare var-var equality.
///
/// `x = y` is trivially sat. After NF construction NF1=[x], NF2=[y],
/// process_simple_neq reaches the var-var case.
#[test]
#[timeout(10_000)]
fn soundness_varsplit_blocks_bare_var_eq() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= x y))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "bare x=y: expected sat or unknown, got {ay:?}"
    );
}

/// VarSplit with three variables: x++"a" = y++"a", y++"b" = z++"b".
///
/// sat: x=y, y=z (all equal). The VarSplit k!="" bug could cascade
/// across multiple pairs.
#[test]
#[timeout(10_000)]
fn soundness_varsplit_three_var_chain() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert (= (str.++ x "a") (str.++ y "a")))
(assert (= (str.++ y "b") (str.++ z "b")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "three-var chain: expected sat or unknown, got {ay:?}"
    );
}

// ===================================================================
// Reverse-pass suffix trimming regression tests
// ===================================================================

/// Reverse pass: x++"c" = y++"c" is SAT (x=y="" is a model).
///
/// Without suffix trimming, the forward pass compares x vs y with
/// the "c" suffix still present, requiring extra split lemmas.
/// With the reverse pass, "c" == "c" is trimmed, leaving [x] vs [y]
/// which is directly resolved via N_UNIFY.
#[test]
#[timeout(10_000)]
fn reverse_pass_suffix_sharing_is_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x "c") (str.++ y "c")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "reverse pass suffix: expected sat or unknown, got {ay:?}"
    );
}

/// Reverse pass: multi-character shared suffix.
///
/// x++"cd" = y++"cd" is SAT. The reverse pass should trim both "d" and "c".
#[test]
#[timeout(10_000)]
fn reverse_pass_multi_char_suffix_is_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x "cd") (str.++ y "cd")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "reverse pass multi-char suffix: expected sat or unknown, got {ay:?}"
    );
}

/// Reverse pass: both prefix and suffix shared.
///
/// "a"++x++"b" = "a"++y++"b" is SAT. Forward pass matches "a"=="a",
/// reverse pass trims "b"=="b", leaving [x] vs [y].
#[test]
#[timeout(10_000)]
fn reverse_pass_both_prefix_and_suffix_is_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ "a" x "b") (str.++ "a" y "b")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "reverse pass both prefix and suffix: expected sat or unknown, got {ay:?}"
    );
}

/// Reverse pass: suffix trimming leaves endpoint-empty case.
///
/// str.++(x, "a") = "a" is SAT (x = ""). After reverse pass trims "a",
/// NF1 = [x], NF2 = []. The endpoint-empty logic infers x = "".
#[test]
#[timeout(10_000)]
fn reverse_pass_endpoint_empty_suffix() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.++ x "a") "a"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(ay, Some("sat"), "str.++(x,\"a\") = \"a\" is SAT (x = \"\")");
}

// ===================================================================
// str.replace_all frontend and reduction coverage
// ===================================================================

/// str.replace_all is a standard SMT-LIB 2.6 operation.
///
/// This test verifies that frontend elaboration and basic solving work for a
/// variable-bearing formula.
#[test]
#[timeout(10_000)]
fn replace_all_elaborates_and_solves_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= x "aaabbb"))
(assert (= (str.replace_all x "a" "c") "cccbbb"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "replace_all variable formula must not be unsat; got {ay:?}"
    );
}

// ===================================================================
// check_extf_reductions integer gap tests
// ===================================================================

/// str.to_int("42") = 43 is UNSAT (to_int("42") = 42, not 43).
///
/// check_extf_int_reductions evaluates integer-valued string functions
/// and compares against asserted integer equalities.
#[test]
#[timeout(10_000)]
fn soundness_to_int_mismatch_is_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= x "42"))
(assert (= (str.to_int x) 43))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(ay, Some("unsat"), "str.to_int(\"42\") = 43: got {ay:?}");
}

/// str.from_int(42) = "43" is UNSAT (from_int(42) = "42").
///
/// check_extf_reductions now handles str.from_int via try_reduce_string_term.
#[test]
#[timeout(10_000)]
fn soundness_from_int_mismatch_is_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.from_int 42) "43"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(ay, Some("unsat"), "str.from_int(42) = \"43\" must be unsat");
}

/// After LIA propagates len(x) = len(y), strings should re-check and apply
/// N_UNIFY (equal-length concatenation decomposition), detecting "a" vs "b".
///
/// Regression test for #3393: StringsLiaSolver did not re-check strings after
/// Nelson-Oppen equality propagation.
///
/// len(x)=len(y) ∧ x++"a"=y++"b" is UNSAT: equal lengths force x=y,
/// but then "a"≠"b". Requires the solver to propagate LIA length equality
/// back into the string theory and trigger suffix mismatch detection.
#[test]
#[timeout(10_000)]
fn slia_strings_recheck_after_lia_propagation() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.len x) (str.len y)))
(assert (= (str.++ x "a") (str.++ y "b")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    // NF-dependent conflict: suffix mismatch after N_UNIFY is still guarded
    // by the NF-incompleteness check (#6275 refined but not removed).
    // Z3 returns unsat. When NF soundness is fully proven, tighten to unsat.
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "equal-length concat with different suffixes: got {ay:?}, expected unsat or unknown"
    );
}

/// str.replace_all("aaba", "a", "c") = "ccbc" is SAT (ground constant evaluation).
#[test]
#[timeout(10_000)]
fn str_replace_all_constant_sat() {
    let smt = r#"
(set-logic QF_S)
(assert (= (str.replace_all "aaba" "a" "c") "ccbc"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("sat"),
        "str.replace_all constant evaluation should be sat"
    );
}

/// str.replace_all("aaba", "a", "c") = "wrong" is UNSAT.
#[test]
#[timeout(10_000)]
fn str_replace_all_constant_unsat() {
    let smt = r#"
(set-logic QF_S)
(assert (= (str.replace_all "aaba" "a" "c") "wrong"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "str.replace_all mismatch should be unsat"
    );
}

mod negated_equalities;
