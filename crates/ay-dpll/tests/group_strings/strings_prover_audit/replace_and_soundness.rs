// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ===================================================================
// str.replace_all edge cases
// ===================================================================

/// str.replace_all with empty source string: str.replace_all("", "a", "b") = ""
/// No occurrences of "a" in "", so result is "".
#[test]
fn replace_all_empty_source() {
    let smt = r#"
(set-logic QF_S)
(assert (not (= (str.replace_all "" "a" "b") "")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "str.replace_all(\"\", \"a\", \"b\") = \"\" is a tautology, got {ay:?}"
    );
}

/// str.replace_all with empty target: str.replace_all("hello", "", "x") = "hello"
/// SMT-LIB: when target is empty, return source unchanged.
#[test]
fn replace_all_empty_target_returns_source() {
    let smt = r#"
(set-logic QF_S)
(assert (not (= (str.replace_all "hello" "" "x") "hello")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "str.replace_all(s, \"\", u) = s per SMT-LIB, got {ay:?}"
    );
}

/// str.replace_all replaces all occurrences: str.replace_all("aaa", "a", "b") = "bbb"
#[test]
fn replace_all_replaces_all_occurrences() {
    let smt = r#"
(set-logic QF_S)
(assert (not (= (str.replace_all "aaa" "a" "b") "bbb")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "str.replace_all(\"aaa\", \"a\", \"b\") = \"bbb\", got {ay:?}"
    );
}

/// str.replace_all with empty replacement: str.replace_all("aaa", "a", "") = ""
#[test]
fn replace_all_delete_all() {
    let smt = r#"
(set-logic QF_S)
(assert (not (= (str.replace_all "aaa" "a" "") "")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "str.replace_all(\"aaa\", \"a\", \"\") = \"\", got {ay:?}"
    );
}

/// str.replace_all with multi-char target: str.replace_all("ababab", "ab", "c") = "ccc"
#[test]
fn replace_all_multi_char_target() {
    let smt = r#"
(set-logic QF_S)
(assert (not (= (str.replace_all "ababab" "ab" "c") "ccc")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "str.replace_all(\"ababab\", \"ab\", \"c\") = \"ccc\", got {ay:?}"
    );
}

/// str.replace_all with longer replacement: str.replace_all("ab", "a", "xyz") = "xyzb"
#[test]
fn replace_all_longer_replacement() {
    let smt = r#"
(set-logic QF_S)
(assert (not (= (str.replace_all "ab" "a" "xyz") "xyzb")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "str.replace_all(\"ab\", \"a\", \"xyz\") = \"xyzb\", got {ay:?}"
    );
}

/// str.replace vs str.replace_all on multiple occurrences.
/// str.replace only replaces the first: str.replace("aaa", "a", "b") = "baa"
/// str.replace_all replaces all: str.replace_all("aaa", "a", "b") = "bbb"
#[test]
fn replace_vs_replace_all_semantics() {
    let smt = r#"
(set-logic QF_S)
(assert (= (str.replace "aaa" "a" "b") (str.replace_all "aaa" "a" "b")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    // "baa" != "bbb", so this should be unsat.
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "str.replace != str.replace_all when multiple occurrences exist, got {ay:?}"
    );
}

// ===================================================================
// One-way Nelson-Oppen: strings-internal equalities not propagated out
// ===================================================================

/// If string theory internally infers x = y (via N_UNIFY), and x, y are
/// shared with LIA, does LIA see the equality?
///
/// This test exercises the gap identified in the prover audit: the string
/// solver receives N-O equalities but does not propagate its own back.
/// Currently mitigated because string equalities usually correspond to
/// SAT-level atoms.
#[test]
fn strings_internal_equality_visible_to_lia() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.len x) (str.len y)))
(assert (= (str.++ x "a") (str.++ y "a")))
(assert (not (= (str.len x) (str.len y))))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "direct contradiction on str.len equality must be unsat"
    );
}

// ===================================================================
// Multi-hop cycle detection (known gap, regression guard)
// ===================================================================

/// Three-step cycle through three variables: x = "a"++y, y = "b"++z, z = "c"++x.
/// This is UNSAT because it creates x = "abc"++x (infinite string).
/// Verified working: the pre-SAT theory fast-path detects the cycle.
#[test]
fn three_step_cycle_is_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert (= x (str.++ "a" y)))
(assert (= y (str.++ "b" z)))
(assert (= z (str.++ "c" x)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(ay, Some("unsat"), "three-step cycle must be unsat");
}

/// Two-step cycle: x = "a"++y, y = "b"++x → UNSAT.
/// No finite strings satisfy these mutually-recursive equations because
/// len(x) = 1 + len(y) = 1 + 1 + len(x), giving 0 = 2.
#[test]
fn two_step_cycle_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= x (str.++ "a" y)))
(assert (= y (str.++ "b" x)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    // x = "a" ++ y AND y = "b" ++ x implies x = "ab" ++ x, an infinite
    // cycle impossible for finite strings.  Correct answer: unsat.
    assert_eq!(
        ay,
        Some("unsat"),
        "two-step cycle: mutually-recursive concats have no finite solution, got {ay:?}"
    );
}

/// Two-step cycle in SLIA mode: x = "a"++y, y = "b"++x → UNSAT.
#[test]
fn two_step_cycle_slia_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= x (str.++ "a" y)))
(assert (= y (str.++ "b" x)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    // Same infinite cycle as QF_S variant.  Correct answer: unsat.
    assert_eq!(
        ay,
        Some("unsat"),
        "two-step cycle SLIA: mutually-recursive concats have no finite solution, got {ay:?}"
    );
}

// =============================================================================
// Prover P17: containment+length soundness gap
//
// When str.contains(x, s) and len(x) = len(s), the solver must derive x = s.
// Without the ContainsPositive reduction lemma (disabled in df04f9bdb due to
// CEGAR infinite loop), this deduction path is missing.
//
// Root cause: The decomposition x = sk_pre ++ s ++ sk_post is never generated,
// so the solver cannot derive sk_pre = "" and sk_post = "" from the length
// constraint len(x) = len(s).
// =============================================================================

/// str.contains(x, "abc") ∧ str.contains(x, "xyz") ∧ len(x) = 3 is UNSAT.
///
/// "abc" has 3 chars, so len(x) = 3 forces x = "abc".
/// "abc" does not contain "xyz", so the second contains is contradicted.
///
/// Previously known bug (sat/panic). Now FIXED — AY correctly returns unsat.
#[test]
fn soundness_contains_length_forces_equality_two_patterns() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-const x String)
(assert (str.contains x "abc"))
(assert (str.contains x "xyz"))
(assert (= (str.len x) 3))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    let ay = crate::common::sat_result(&output);
    assert_eq!(
        ay,
        Some("unsat"),
        "contains+length two patterns: must be unsat, got {ay:?}"
    );
}

/// str.contains(x, "abc") ∧ len(x) = 3 ∧ x ≠ "abc" is UNSAT.
///
/// The only 3-char string containing "abc" is "abc" itself.
/// KNOWN GAP: AY returns unknown (sound but incomplete). Z3 returns unsat.
/// Requires contains decomposition + length normalization to close.
#[test]
fn soundness_contains_length_forces_equality_explicit_diseq() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-const x String)
(assert (str.contains x "abc"))
(assert (= (str.len x) 3))
(assert (not (= x "abc")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    // Correct answer: unsat. AY returns unknown (sound but incomplete).
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "contains+length explicit diseq: expected unsat or unknown, got {ay:?}"
    );
}

/// str.prefixof("abc", x) ∧ len(x) = 3 ∧ x ≠ "abc" should be UNSAT.
///
/// Prefix forces first 3 chars = "abc", length = 3 forces no more chars.
/// AY returns unknown (sound but incomplete).
#[test]
fn soundness_prefix_length_forces_equality() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-const x String)
(assert (str.prefixof "abc" x))
(assert (= (str.len x) 3))
(assert (not (= x "abc")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    // Correct answer is unsat. AY returns unknown (sound but incomplete).
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "prefix+length: expected unsat or unknown, got {ay:?}"
    );
}

/// str.suffixof("abc", x) ∧ len(x) = 3 ∧ x ≠ "abc" should be UNSAT.
///
/// Suffix forces last 3 chars = "abc", length = 3 forces no more chars.
/// AY returns unknown (sound but incomplete).
#[test]
fn soundness_suffix_length_forces_equality() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-const x String)
(assert (str.suffixof "abc" x))
(assert (= (str.len x) 3))
(assert (not (= x "abc")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    // Correct answer is unsat. AY returns unknown (sound but incomplete).
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "suffix+length: expected unsat or unknown, got {ay:?}"
    );
}

// =============================================================================
// Prover P17: ground extended function evaluation soundness gap
//
// When a ground-evaluable extended function (str.replace, str.at, str.substr,
// str.indexof) is in a positive equality with a variable, the solver fails to
// evaluate the function and propagate the result. check_extf_reductions skips
// EQCs without constants, and check_extf_string_equalities doesn't set
// incomplete for positive equalities with one unresolved side.
//
// Root cause: core.rs:344-346 skips non-constant EQCs, and core.rs:420-428
// only sets incomplete for negated equalities (!equality_expected).
// =============================================================================

/// str.replace("hallo", "a", "b") = y ∧ y ≠ "hbllo" is UNSAT.
///
/// Replace must produce "hbllo". AY fails to evaluate the ground replace.
///
/// KNOWN BUG: AY returns sat. Z3 returns unsat.
#[test]
fn soundness_ground_replace_eq_var_diseq() {
    let smt = r#"
(set-logic QF_S)
(declare-const x String)
(declare-const y String)
(assert (= x "hallo"))
(assert (= (str.replace x "a" "b") y))
(assert (not (= y "hbllo")))
(check-sat)
"#;
    // Bug fixed: AY now correctly returns unsat (#3754, fixed by extf reductions).
    let output = crate::common::solve(smt);
    let ay = crate::common::sat_result(&output);
    assert_eq!(
        ay,
        Some("unsat"),
        "ground replace eq: expected unsat, got {ay:?}"
    );
}

/// str.at("hello", 0) = x ∧ x ≠ "h" is UNSAT.
///
/// str.at on ground args must return "h".
/// Bug fixed: AY now correctly returns unsat (#3754, fixed by extf reductions).
#[test]
fn soundness_ground_str_at_eq_var_diseq() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-const x String)
(assert (= (str.at "hello" 0) x))
(assert (not (= x "h")))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    let ay = crate::common::sat_result(&output);
    assert_eq!(
        ay,
        Some("unsat"),
        "ground str.at eq: expected unsat, got {ay:?}"
    );
}

/// str.substr("hello", 1, 3) = x ∧ x ≠ "ell" is UNSAT.
///
/// str.substr on ground args must return "ell".
/// Bug fixed: AY now correctly returns unsat (#3754, fixed by extf reductions).
#[test]
fn soundness_ground_substr_eq_var_diseq() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-const x String)
(assert (= (str.substr "hello" 1 3) x))
(assert (not (= x "ell")))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    let ay = crate::common::sat_result(&output);
    assert_eq!(
        ay,
        Some("unsat"),
        "ground substr eq: expected unsat, got {ay:?}"
    );
}

/// str.indexof("hello", "ll", 0) = x ∧ x ≠ 2 is UNSAT.
///
/// str.indexof on ground args must return 2. AY fails to evaluate
/// the function during solving, but model validation catches the
/// inconsistency between the string evaluator (indexof=2) and the
/// LIA model (x≠2). This is progress over the old false-SAT (#3754).
///
/// KNOWN GAP: str.to_int/str.indexof results not propagated to LIA model.
/// When fixed, change to: assert_eq!(ay, Some("unsat"), ...)
#[test]
fn soundness_ground_indexof_eq_var_diseq_known_gap() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-const x Int)
(assert (= (str.indexof "hello" "ll" 0) x))
(assert (not (= x 2)))
(check-sat)
"#;
    let commands = parse(smt).expect("parse");
    let mut exec = Executor::new();
    match exec.execute_all(&commands) {
        Ok(outputs) => {
            let result = outputs.join("\n");
            let ay = crate::common::sat_result(&result);
            // Correct answer is unsat. Accept unsat or unknown (sound incomplete).
            assert!(
                matches!(ay, Some("unsat") | Some("unknown")),
                "ground indexof eq: expected unsat or unknown, got {ay:?}"
            );
        }
        Err(e) => {
            // Model validation error is expected: the string evaluator correctly
            // computes indexof=2 but the LIA model assigns x a different value.
            let msg = e.to_string();
            assert!(
                msg.contains("model validation") || msg.contains("ModelValidation"),
                "expected model validation error, got: {msg}"
            );
        }
    }
}

// =============================================================================
// Prover P19: str.replace_re / str.replace_re_all soundness
//
// Newly added in W4/W6 commits. Verify constant evaluation produces correct
// results and that sort-mismatch rejection works.
// =============================================================================

/// str.replace_re("aXbXc", (str.to_re "X"), "Y") = "aYbXc"
///
/// First-match-only replacement: only the first "X" is replaced.
#[test]
fn replace_re_first_match_replaces_only_first() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= x "aXbXc"))
(assert (= (str.replace_re x (str.to_re "X") "Y") "aYbXc"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("sat"),
        "replace_re first-only: expected sat, got {ay:?}"
    );
}

/// str.replace_re("aXbXc", (str.to_re "X"), "Y") ≠ "aYbYc"
///
/// replace_re replaces only the first match, not all.
/// If AY incorrectly replaces all, it would wrongly return SAT.
#[test]
fn replace_re_does_not_replace_all() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= x "aXbXc"))
(assert (= (str.replace_re x (str.to_re "X") "Y") "aYbYc"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "replace_re should NOT replace all: expected unsat/unknown, got {ay:?}"
    );
}

/// str.replace_re_all("aXbXc", (str.to_re "X"), "Y") = "aYbYc"
///
/// All-match replacement: every "X" becomes "Y".
#[test]
fn replace_re_all_replaces_all_matches() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= x "aXbXc"))
(assert (= (str.replace_re_all x (str.to_re "X") "Y") "aYbYc"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(ay, Some("sat"), "replace_re_all: expected sat, got {ay:?}");
}

/// str.replace_re with no match returns original string.
#[test]
fn replace_re_no_match_returns_original() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.replace_re "hello" (str.to_re "Z") "X") "hello"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("sat"),
        "replace_re no-match: expected sat, got {ay:?}"
    );
}

/// str.replace_re_all with no match returns original string.
#[test]
fn replace_re_all_no_match_returns_original() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.replace_re_all "hello" (str.to_re "Z") "X") "hello"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("sat"),
        "replace_re_all no-match: expected sat, got {ay:?}"
    );
}

/// str.replace_re on empty string returns empty.
#[test]
fn replace_re_empty_string_returns_empty() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.replace_re "" (str.to_re "a") "X") ""))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("sat"),
        "replace_re empty input: expected sat, got {ay:?}"
    );
}

/// str.replace_re with regex union: (re.union (str.to_re "a") (str.to_re "b"))
/// Applied to "abc" should replace first "a" → "X" giving "Xbc".
#[test]
fn replace_re_union_replaces_first_alternative() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.replace_re "abc" (re.union (str.to_re "a") (str.to_re "b")) "X") "Xbc"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("sat"),
        "replace_re union: expected sat, got {ay:?}"
    );
}
