// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core string solver tests: cycle detection, endpoint-empty inference,
//! containment bounds, prefix/suffix Skolem decomposition.

use super::*;

// ── Resolved mismatch: QF_S cycle detection now works ───────────────────

#[test]
#[timeout(10_000)]
fn concat_nonempty_prefix_neq_self_is_unsat() {
    // Z3: unsat (concat with non-empty prefix can't equal original)
    // AY: unsat — string solver cycle detection catches str.++("a",x)=x
    //     with non-empty sibling "a".
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= (str.++ "a" x) x))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(result.trim(), "unsat");
}

// ── Endpoint-empty inference (Case 4) ────────────────────────────────────

#[test]
#[timeout(10_000)]
fn endpoint_empty_concat_suffix_must_be_empty() {
    // x ++ y = "abc" with x = "abc" implies y = "".
    // Asserting y != "" should be unsat.
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x y) "abc"))
(assert (= x "abc"))
(assert (not (= y "")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "endpoint-empty should derive y = \"\""
    );
}

// ── Known AY/Z3 mismatches (QF_SLIA lacks string-length integration) ───

#[test]
#[timeout(10_000)]
fn known_ay_z3_mismatches() {
    // These QF_SLIA cases are expected UNSAT by SMT-LIB semantics and by Z3.
    //
    // `strict_match` cases must now match Z3 exactly.
    // Non-strict cases document known incompleteness where AY may still return
    // Unknown; they still hard-fail on unsound Sat.
    let cases: Vec<(&str, &str, &str, bool)> = vec![
        // len("") = 0, so str.len(x)=0 implies x=""
        (
            "len_zero_implies_empty",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len x) 0))
(assert (not (= x "")))
(check-sat)
"#,
            "unsat",
            true,
        ),
        // len(concat(a,b)) = len(a) + len(b), so len must be >= 1.
        // With the StringsLiaSolver NeedStringLemma/LIA ordering fix, this is
        // now expected to prove UNSAT directly.
        (
            "concat_length_lower_bound",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len (str.++ x "a")) 0))
(check-sat)
            "#,
            "unsat",
            true,
        ),
        // a != "" and str.len(str.++(a,b)) = 0 is unsat:
        // concat decomposition + zero-length axioms for sub-args
        (
            "concat_nonempty_arg_length_zero",
            r#"
(set-logic QF_SLIA)
(declare-const a String)
(declare-const b String)
(assert (not (= a "")))
(assert (= (str.len (str.++ a b)) 0))
(check-sat)
"#,
            "unsat",
            false,
        ),
    ];

    for (name, smt, expected, strict_match) in &cases {
        let ay_output = solve_or_error(smt);
        match &ay_output {
            Ok(output) => {
                let ay_result = crate::common::sat_result(output);
                if *strict_match {
                    assert_eq!(
                        ay_result,
                        Some(*expected),
                        "AY mismatch on {name}: got={ay_result:?}, expected={expected}"
                    );
                } else {
                    assert!(
                        ay_result == Some(*expected) || ay_result == Some("unknown"),
                        "AY incompleteness mismatch on {name}: got={ay_result:?}, expected {expected} or unknown"
                    );
                    assert_ne!(
                        ay_result,
                        Some("sat"),
                        "AY unsoundness on {name}: expected {expected} or unknown, got sat"
                    );
                }
            }
            Err(e) => {
                panic!("AY error on {name}: {e}");
            }
        }
    }

    // Verify Z3 agrees with expected results (if available).
    if z3_available() {
        for (name, smt, expected, _strict_match) in &cases {
            let z3_output =
                solve_with_z3(smt).unwrap_or_else(|e| panic!("z3 failed on {name}: {e}"));
            let z3_result = crate::common::sat_result(&z3_output)
                .unwrap_or_else(|| panic!("z3 produced no result for {name}: {z3_output}"));
            assert_eq!(
                z3_result, *expected,
                "Z3 result for {name} changed; expected={expected}, got={z3_result}"
            );
        }
    }
}

// ── Containment length bound axioms ────────────────────────────────────

#[test]
#[timeout(10_000)]
fn str_contains_length_bound_unsat() {
    // str.contains(x, "hello") ∧ str.len(x) < 5 is UNSAT:
    // "hello" has 5 chars, so x must be at least 5 long.
    let smt = r#"
(set-logic QF_SLIA)
(declare-const x String)
(assert (str.contains x "hello"))
(assert (< (str.len x) 5))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(result.trim(), "unsat");
}

#[test]
#[timeout(10_000)]
fn str_contains_length_bound_sat() {
    // str.contains(x, "hi") ∧ str.len(x) = 5 is SAT:
    // "hi" has 2 chars, x can be 5 chars and still contain "hi".
    let smt = r#"
(set-logic QF_SLIA)
(declare-const x String)
(assert (str.contains x "hi"))
(assert (= (str.len x) 5))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let answer = result.trim();
    assert!(
        matches!(answer, "sat" | "unknown"),
        "str.contains + len bound must not be unsat; got {answer}"
    );
}

#[test]
#[timeout(10_000)]
fn str_prefixof_length_bound_unsat() {
    // str.prefixof("hello", x) ∧ str.len(x) < 5 is UNSAT.
    // Skolem decomposition: x = "hello" ++ sk, so len(x) = 5 + len(sk) >= 5.
    let smt = r#"
(set-logic QF_SLIA)
(declare-const x String)
(assert (str.prefixof "hello" x))
(assert (< (str.len x) 5))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "str.prefixof length-bound case must be unsat, got {result}"
    );
}

#[test]
#[timeout(10_000)]
fn str_suffixof_length_bound_unsat() {
    // str.suffixof("world", x) ∧ str.len(x) = 3 is UNSAT.
    // Skolem decomposition: x = sk ++ "world", so len(x) = len(sk) + 5 >= 5 > 3.
    let smt = r#"
(set-logic QF_SLIA)
(declare-const x String)
(assert (str.suffixof "world" x))
(assert (= (str.len x) 3))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "str.suffixof length-bound case must be unsat, got {result}"
    );
}

// ── Prefix/suffix Skolem decomposition tests (#3715) ─────────────────

#[test]
#[timeout(10_000)]
fn str_prefixof_decomposition_sat() {
    // str.prefixof("ab", x) ∧ len(x) = 3 is SAT (x = "ab" ++ sk where len(sk) = 1).
    // Requires Skolem decomposition: prefixof("ab", x) => x = str.++("ab", sk_pfx_suf).
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.prefixof "ab" x))
(assert (= (str.len x) 3))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert!(
        result.trim() == "sat" || result.trim() == "unknown",
        "str.prefixof decomposition SAT case: got {result}"
    );
}

#[test]
#[timeout(10_000)]
fn str_suffixof_decomposition_sat() {
    // str.suffixof("cd", x) ∧ len(x) = 4 is SAT (x = sk ++ "cd" where len(sk) = 2).
    // Requires Skolem decomposition: suffixof("cd", x) => x = str.++(sk_sfx_pre, "cd").
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.suffixof "cd" x))
(assert (= (str.len x) 4))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert!(
        result.trim() == "sat" || result.trim() == "unknown",
        "str.suffixof decomposition SAT case: got {result}"
    );
}

#[test]
#[timeout(10_000)]
fn str_prefix_suffix_overlap_sat() {
    // str.prefixof("ab", x) ∧ str.suffixof("bc", x) ∧ len(x) = 3 is SAT (x = "abc").
    // Requires both prefix and suffix Skolem decomposition.
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.prefixof "ab" x))
(assert (str.suffixof "bc" x))
(assert (= (str.len x) 3))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert!(
        result.trim() == "sat" || result.trim() == "unknown",
        "prefix_suffix_overlap SAT case: got {result}"
    );
}

#[test]
#[timeout(10_000)]
fn str_prefixof_decomposition_unsat() {
    // str.prefixof("hello", x) ∧ len(x) = 3 is UNSAT (need at least 5 chars for "hello" prefix).
    // Skolem decomposition creates: x = "hello" ++ sk, so len(x) = 5 + len(sk) >= 5 > 3.
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.prefixof "hello" x))
(assert (= (str.len x) 3))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert!(
        result.trim() == "unsat" || result.trim() == "unknown",
        "str.prefixof decomposition UNSAT case — got: {}",
        result.trim()
    );
}

#[test]
#[timeout(10_000)]
fn str_suffixof_decomposition_unsat() {
    // str.suffixof("world", x) ∧ len(x) = 3 is UNSAT (need at least 5 chars).
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.suffixof "world" x))
(assert (= (str.len x) 3))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert!(
        result.trim() == "unsat" || result.trim() == "unknown",
        "str.suffixof decomposition UNSAT case — got: {}",
        result.trim()
    );
}

/// Two conflicting str.prefixof constants must not return SAT (#6326).
///
/// str.prefixof("ab", x) ∧ str.prefixof("ac", x) is UNSAT because
/// "ab" and "ac" differ at position 1. The Skolem decompositions create
/// x = "ab" ++ sk1 and x = "ac" ++ sk2, and the NF comparison of the
/// two concat terms must detect the 'b' vs 'c' conflict.
#[test]
#[timeout(10_000)]
fn str_prefixof_conflicting_constants_unsat_6326() {
    let smt = r#"
(set-logic QF_S)
(declare-const x String)
(assert (str.prefixof "ab" x))
(assert (str.prefixof "ac" x))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_ne!(
        result.trim(),
        "sat",
        "str.prefixof(\"ab\",x) ∧ str.prefixof(\"ac\",x) must not return SAT (#6326)"
    );
}

/// Conflicting suffix constants: str.suffixof("xy", x) ∧ str.suffixof("xz", x)
/// is UNSAT — the last characters differ.
#[test]
#[timeout(10_000)]
fn str_suffixof_conflicting_constants_unsat_6326() {
    let smt = r#"
(set-logic QF_S)
(declare-const x String)
(assert (str.suffixof "xy" x))
(assert (str.suffixof "xz" x))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_ne!(
        result.trim(),
        "sat",
        "str.suffixof(\"xy\",x) ∧ str.suffixof(\"xz\",x) must not return SAT (#6326)"
    );
}

#[test]
#[timeout(10_000)]
fn strings_phase_a_differential_smoke_vs_z3() {
    if !z3_available() {
        eprintln!("z3 not found; skipping strings differential smoke test");
        return;
    }

    let cases = [
        (
            "qf_s_unsat_conflicting_constants",
            r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x "a"))
(assert (= x "b"))
(check-sat)
"#,
        ),
        (
            "qf_s_sat_concat",
            r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= (str.++ x "") x))
(check-sat)
"#,
        ),
        (
            "qf_s_unsat_nonempty_prefix_self",
            r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= (str.++ "a" x) x))
(check-sat)
"#,
        ),
        (
            "qf_s_sat_empty_cycle_equivalent",
            r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= y ""))
(assert (= (str.++ y x) x))
(check-sat)
"#,
        ),
        (
            "qf_s_unsat_identical_concat_disequality",
            r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert (= z (str.++ x y)))
(assert (not (= z (str.++ x y))))
(check-sat)
"#,
        ),
        (
            "qf_slia_unsat_len_contradiction",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len x) 0))
(assert (> (str.len x) 0))
(check-sat)
"#,
        ),
        (
            "qf_slia_sat_contains",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.contains x x))
(check-sat)
"#,
        ),
        (
            "qf_slia_unsat_to_int_contradiction",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.to_int x) 0))
(assert (> (str.to_int x) 0))
(check-sat)
"#,
        ),
    ];

    for (name, smt) in cases {
        let ay_output = solve_or_error(smt).unwrap_or_else(|e| panic!("ay failed on {name}: {e}"));
        let z3_output = solve_with_z3(smt).unwrap_or_else(|e| panic!("z3 failed on {name}: {e}"));
        let ay_result = crate::common::sat_result(&ay_output)
            .unwrap_or_else(|| panic!("ay produced no sat-status line on {name}: {ay_output}"));
        let z3_result = crate::common::sat_result(&z3_output)
            .unwrap_or_else(|| panic!("z3 produced no sat-status line on {name}: {z3_output}"));
        assert!(
            matches!(z3_result, "sat" | "unsat"),
            "expected definite z3 result for {name}, got: {z3_result}"
        );
        // AY is incomplete on strings: unknown is always sound.
        // Only flag disagreements where AY gives a definite wrong answer.
        if ay_result != "unknown" {
            assert_eq!(
                ay_result, z3_result,
                "ay/z3 soundness mismatch on {name}\nay: {ay_output}\nz3: {z3_output}"
            );
        }
    }
}
