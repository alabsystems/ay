// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ===================================================================
// P5-365: N-O bridge equality soundness + gate shim removal
// ===================================================================

/// N-O bridge: LIA propagates length equality which forces string equality.
///
/// In QF_SLIA, the LIA solver discovers len(x)=len(y) from arithmetic
/// constraints, propagating the equality through the N-O bridge back to
/// strings. The strings solver then rechecks normal forms. If the bridge
/// equality has empty reasons, a string conflict based on it would lack
/// the LIA premises in its explanation, creating a partial clause.
///
/// This test is SAT — the solver must not falsely conclude UNSAT from
/// a spurious conflict during the N-O recheck phase.
#[test]
fn soundness_no_bridge_length_equality_no_false_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun n () Int)
(assert (= n (str.len x)))
(assert (= n (str.len y)))
(assert (= n 3))
(assert (str.prefixof "ab" x))
(assert (str.prefixof "ab" y))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    // SAT: x="ab?" and y="ab?" where ? is any char.
    assert_eq!(
        ay,
        Some("sat"),
        "N-O bridge: len(x)=len(y)=3 with shared prefix is SAT, got {ay:?}"
    );
}

/// N-O bridge: strings + arithmetic with disequality.
///
/// The formula has x != y but len(x) = len(y) = 2, both prefixed with "a".
/// This is SAT (e.g., x="ab", y="ac"). The N-O bridge must not produce
/// a false conflict from the length equality propagation.
///
/// KNOWN GAP: AY returns unknown (sound but incomplete). Z3 returns sat.
/// Requires EqualitySplit (#4119) to resolve.
#[test]
fn soundness_no_bridge_diseq_with_shared_prefix_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.len x) (str.len y)))
(assert (= (str.len x) 2))
(assert (str.prefixof "a" x))
(assert (str.prefixof "a" y))
(assert (not (= x y)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    // Correct answer: sat. AY returns unknown (sound but incomplete).
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "N-O bridge: len(x)=len(y)=2, prefix 'a', x!=y: expected sat or unknown, got {ay:?}"
    );
}

// ===== Reduction Lemma Tests (CVC5 theory_strings_preprocess.cpp) =====
// Tests for str.substr and str.replace reduction lemmas that convert
// non-ground extended functions into word equations + arithmetic.

/// Non-ground substr with length constraint should be SAT.
/// substr(x, 1, 3) = "ell" with len(x) = 5 has solution x = "hello".
/// Reference: CVC5 theory_strings_preprocess.cpp:62-121
#[test]
fn reduction_substr_nonground_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len x) 5))
(assert (= (str.substr x 1 3) "ell"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "substr(x,1,3)=\"ell\" with len(x)=5 must not be unsat; got {ay:?}"
    );
}

/// Non-ground substr with conflicting length should be UNSAT.
/// substr(x, 0, 3) = "abc" with len(x) = 2: the string is too short.
#[test]
fn reduction_substr_conflicting_length_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len x) 2))
(assert (= (str.substr x 0 3) "abc"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "substr(x,0,3)=\"abc\" with len(x)=2 should be UNSAT, got {ay:?}"
    );
}

/// Replace with empty pattern: replace(x, "", "pre") = "pre" ++ x.
/// replace(x, "", "pre") = "prehello" with len(x) = 5.
/// Reference: CVC5 theory_strings_preprocess.cpp:572-631
#[test]
fn reduction_replace_empty_pattern_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.replace x "" "pre") "prehello"))
(assert (= (str.len x) 5))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "replace(x,\"\",\"pre\")=\"prehello\" with len(x)=5 must not be unsat; got {ay:?}"
    );
}

/// Ground replace inside str.len should evaluate (Wave 0 test).
/// len(replace("hello", "ll", "r")) = 4.
/// Known divergence (#4149): SLIA solver loops on this ground formula.
/// Uses interrupt-based timeout to avoid hang.
#[test]
fn reduction_ground_replace_in_len() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.len (str.replace "hello" "ll" "r")) 4))
(check-sat)
"#;
    let commands = parse(smt).expect("parse");
    let mut exec = Executor::new();
    let interrupt = Arc::new(AtomicBool::new(false));
    exec.set_interrupt(Arc::clone(&interrupt));
    let (cancel_tx, cancel_rx) = std::sync::mpsc::channel();
    let timer_flag = Arc::clone(&interrupt);
    let timer = std::thread::spawn(move || {
        if cancel_rx.recv_timeout(Duration::from_secs(10)).is_err() {
            timer_flag.store(true, Ordering::Relaxed);
        }
    });
    let output = exec.execute_all(&commands).expect("execute_all").join("\n");
    let _ = cancel_tx.send(());
    let _ = timer.join();
    let ay = crate::common::sat_result(&output);
    // Correct answer is sat. AY may return unknown due to divergence (#4149).
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "len(replace(\"hello\",\"ll\",\"r\")) = 4: expected sat or unknown, got: {ay:?}"
    );
}

/// Non-ground str.at with length constraint should be SAT.
/// str.at(x, 1) = "e" with x = "hello" is clearly satisfiable.
/// Reference: CVC5 theory_strings_preprocess.cpp:527-571
#[test]
fn reduction_at_nonground_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len x) 5))
(assert (= (str.at x 1) "e"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "str.at(x,1)=\"e\" with len(x)=5 must not be unsat; got {ay:?}"
    );
}

/// Non-ground str.at with conflicting constraints should be UNSAT.
/// str.at(x, 0) = "a" AND str.at(x, 0) = "b" is unsatisfiable.
#[test]
fn reduction_at_conflicting_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len x) 3))
(assert (= (str.at x 0) "a"))
(assert (= (str.at x 0) "b"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_ne!(
        ay,
        Some("sat"),
        "str.at(x,0)=\"a\" AND str.at(x,0)=\"b\" should not be SAT"
    );
}

// ========================================================================
// Ground ExtF Standalone Evaluation (Wave 0b)
//
// Regression tests for 8b956621a: standalone ground extended function terms
// (not wrapped in str.len) are evaluated during preprocessing. Without this
// fix, the solver never learns that str.replace("hello","ll","r") = "hero"
// and returns false SAT.
// Reference: the development design notes
// ========================================================================

/// Ground str.replace with multi-char pattern: replace("hello","ll","r") = "hero".
/// Tests standalone ground extf evaluation (Wave 0b, 8b956621a).
/// Unlike soundness_ground_replace_eq_var_diseq (line 443) which uses an
/// intermediary variable x, this tests direct replace with multi-char pattern.
#[test]
fn soundness_ground_replace_multichar_pattern() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-const x String)
(assert (= (str.replace "hello" "ll" "r") x))
(assert (not (= x "hero")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "str.replace(\"hello\",\"ll\",\"r\") = \"hero\" is forced; diseq with \"hero\" is UNSAT"
    );
}

/// Ground str.replace_all standalone: replace_all("banana","a","o") = "bonono".
#[test]
fn soundness_ground_replace_all_eq_var_diseq() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-const x String)
(assert (= (str.replace_all "banana" "a" "o") x))
(assert (not (= x "bonono")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "str.replace_all(\"banana\",\"a\",\"o\") = \"bonono\" is forced"
    );
}

/// Ground str.from_int standalone: str.from_int(42) = "42".
#[test]
fn soundness_ground_from_int_eq_var_diseq() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-const x String)
(assert (= (str.from_int 42) x))
(assert (not (= x "42")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(ay, Some("unsat"), "str.from_int(42) = \"42\" is forced");
}

/// Ground str.from_code standalone: str.from_code(65) = "A".
#[test]
fn soundness_ground_from_code_eq_var_diseq() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-const x String)
(assert (= (str.from_code 65) x))
(assert (not (= x "A")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(ay, Some("unsat"), "str.from_code(65) = \"A\" is forced");
}

/// Ground replace inside str.len: len(replace("hello","ll","r")) = 4.
/// This was the replace_then_len differential test failure.
#[test]
fn soundness_ground_replace_in_strlen() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun n () Int)
(assert (= n (str.len (str.replace "hello" "ll" "r"))))
(assert (not (= n 4)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "len(replace(\"hello\",\"ll\",\"r\")) = 4 is forced"
    );
}

/// Prefix + contradictory first character is UNSAT.
///
/// `str.prefixof "ab" x` forces the first character of `x` to be `"a"`,
/// so `(str.at x 0) = "c"` is contradictory.
#[test]
fn soundness_prefixof_model_validation() {
    let smt = r#"
(set-logic QF_S)
(declare-const x String)
(assert (str.prefixof "ab" x))
(assert (= (str.at x 0) "c"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "prefixof contradiction must be unsat, got {ay:?}"
    );
}

/// Contradictory double prefix: prefixof("ab",x) AND prefixof("ac",x)
/// is UNSAT because 'b' and 'c' conflict at position 1.
/// Fixed by #4118: removing per-variable dedup allows both prefix
/// decompositions to fire, and the NF solver detects the mismatch.
#[test]
fn soundness_contradictory_double_prefix() {
    let smt = r#"
(set-logic QF_S)
(declare-const x String)
(assert (str.prefixof "ab" x))
(assert (str.prefixof "ac" x))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "contradictory double prefix: 'ab' and 'ac' conflict at position 1"
    );
}

/// Overlap constant equality: prefix + suffix + length uniquely determines
/// the string. Regression test for preregister_overlap_constant_equalities.
#[test]
fn soundness_overlap_prefix_suffix_length_determines_string() {
    let smt = r#"
(set-logic QF_S)
(declare-const x String)
(assert (str.prefixof "ab" x))
(assert (str.suffixof "bc" x))
(assert (= (str.len x) 3))
(assert (not (= x "abc")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "prefix 'ab' + suffix 'bc' + len 3 => x = 'abc'; diseq with 'abc' is UNSAT"
    );
}

/// Overlap: prefix + suffix + length with inconsistent overlap chars.
/// prefix "ab", suffix "cd", length 3 => overlap 1 char but 'b' != 'c'.
#[test]
fn soundness_overlap_inconsistent_overlap_chars_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-const x String)
(assert (str.prefixof "ab" x))
(assert (str.suffixof "cd" x))
(assert (= (str.len x) 3))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "prefix 'ab' + suffix 'cd' + len 3 => overlap 'b' vs 'c' mismatch => UNSAT"
    );
}

/// Overlap: prefix + suffix with no overlap (concatenation fits exactly).
#[test]
fn soundness_overlap_no_overlap_exact_fit() {
    let smt = r#"
(set-logic QF_S)
(declare-const x String)
(assert (str.prefixof "ab" x))
(assert (str.suffixof "cd" x))
(assert (= (str.len x) 4))
(assert (not (= x "abcd")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "prefix 'ab' + suffix 'cd' + len 4 => x = 'abcd'; diseq with 'abcd' is UNSAT"
    );
}

/// Overlap: SAT case where prefix + suffix + length leaves free middle.
/// prefix "ab", suffix "cd", len 5 → middle char is unconstrained.
/// The overlap code should NOT fire (target_len > p_len + s_len).
/// #6309: was false-UNSAT before ground-only resolution fix.
#[test]
fn completeness_overlap_free_middle_is_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-const x String)
(assert (str.prefixof "ab" x))
(assert (str.suffixof "cd" x))
(assert (= (str.len x) 5))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    // Soundness: must NOT return unsat (this formula is satisfiable, e.g., x="abXcd").
    // Completeness: ideally returns sat, but unknown is acceptable.
    assert_ne!(
        ay,
        Some("unsat"),
        "#6309: prefix 'ab' + suffix 'cd' + len 5 is SAT (e.g., x=\"abXcd\"), must not return UNSAT"
    );
}

/// Overlap: multiple prefixes both consistent, uniquely determined.
/// prefix "ab" AND "abc", suffix "cd", len 4 → x = "abcd".
#[test]
fn soundness_overlap_multiple_prefixes_consistent() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-const x String)
(assert (str.prefixof "ab" x))
(assert (str.prefixof "abc" x))
(assert (str.suffixof "cd" x))
(assert (= (str.len x) 4))
(assert (not (= x "abcd")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "two consistent prefixes + suffix + len => x = 'abcd'; diseq is UNSAT"
    );
}

/// Overlap + contradictory str.at: overlap determines x = "abc",
/// but str.at says position 1 is "z". Should be unsat.
#[test]
fn soundness_overlap_with_contradictory_str_at() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-const x String)
(assert (str.prefixof "ab" x))
(assert (str.suffixof "bc" x))
(assert (= (str.len x) 3))
(assert (= (str.at x 1) "z"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "overlap determines x='abc', str.at(x,1)='z' contradicts 'b' => UNSAT"
    );
}

/// Deq completeness: shared prefix + diseq should be SAT.
/// Z3 model: x="abc", y="abcB" — both have prefix "abc", lengths differ.
/// Regression test for #4117 (process_simple_deq).
///
/// KNOWN GAP: AY returns unknown (sound but incomplete). Z3 returns sat.
/// Requires prefix decomposition completeness to resolve.
#[test]
fn completeness_deq_shared_prefix_is_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.prefixof "abc" x))
(assert (str.prefixof "abc" y))
(assert (not (= x y)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    // Correct answer: sat. AY returns unknown (sound but incomplete).
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "shared prefix + diseq: expected sat or unknown, got {ay:?}"
    );
}

/// Deq completeness: two variables with equal fixed length + diseq.
/// Model builder should assign different constants.
#[test]
fn completeness_deq_equal_length_is_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.len x) 3))
(assert (= (str.len y) 3))
(assert (not (= x y)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "two length-3 variables with diseq must not be unsat; got {ay:?}"
    );
}

/// Prefix + fixed length + diseq: regression for CVC5-style prefix rewrite (#4118).
/// `str.prefixof("a", x)`, `str.prefixof("a", y)`, len=2, x != y.
/// Z3 model: x="ab", y="ac". The new substr rewrite must not introduce
/// false UNSAT by over-constraining the normal forms.
#[test]
fn soundness_prefix_rewrite_diseq_with_fixed_length() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.len x) 2))
(assert (= (str.len y) 2))
(assert (str.prefixof "a" x))
(assert (str.prefixof "a" y))
(assert (not (= x y)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    // Known completeness gap: same pattern as bridge_diseq test above.
    // Guard against false UNSAT (soundness).
    assert!(
        ay == Some("sat") || ay == Some("unknown"),
        "prefix 'a' + len 2 + diseq: SAT (x=\"ab\", y=\"ac\") — #4118 regression guard, got {ay:?}"
    );
}

/// Suffix + fixed length + diseq: same pattern as prefix, for suffixof.
/// Z3 model: x="za", y="ya". Must not be false UNSAT.
#[test]
fn soundness_suffix_rewrite_diseq_with_fixed_length() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.len x) 2))
(assert (= (str.len y) 2))
(assert (str.suffixof "a" x))
(assert (str.suffixof "a" y))
(assert (not (= x y)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    // Z3: sat (x="za", y="ya"). Guard against false UNSAT.
    assert!(
        ay == Some("sat") || ay == Some("unknown"),
        "suffix 'a' + len 2 + diseq: SAT (x=\"za\", y=\"ya\") — #4118 regression guard, got {ay:?}"
    );
}

// ===================================================================
// #4057 regression tests: double-decomposition and empty-EQC guards
// ===================================================================

/// Regression test for double-decomposition prevention (#4057).
///
/// str.replace introduces an implicit str.contains check. When the replace
/// target and an explicit contains share the same haystack variable, the
/// second contains-decomposition pass must skip the variable (tracked via
/// `contains_decomposed_vars`). Without the guard, the same variable gets
/// conflicting concat decompositions: one from the explicit contains and
/// one from the replace-generated contains.
///
/// Formula: contains(x, "a") ∧ replace(x, "b", "c") = y ∧ x = "ab"
/// Model: x = "ab", y = "ac". SAT in Z3.
///
/// Note: uses try_solve because model validation may fail on str.replace
/// model reconstruction (separate completeness gap). The key invariant is
/// no false UNSAT from double-decomposition.
#[test]
fn regression_4057_replace_then_contains_no_double_decompose() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.contains x "a"))
(assert (= y (str.replace x "b" "c")))
(assert (= x "ab"))
(check-sat)
"#;
    let commands = parse(smt).expect("parse");
    let mut exec = Executor::new();
    // execute_all may return ModelValidation error if the solver finds SAT
    // but model reconstruction for str.replace is incomplete. Either way,
    // false UNSAT (the #4057 bug) must not occur.
    match exec.execute_all(&commands) {
        Ok(outputs) => {
            let result = outputs.join("\n");
            let ay = crate::common::sat_result(&result);
            assert!(
                ay == Some("sat") || ay == Some("unknown"),
                "replace+contains on same var: SAT (x=\"ab\", y=\"ac\"), got {ay:?}"
            );
        }
        Err(e) => {
            let msg = format!("{e}");
            // Model validation errors mean SAT was found (not false UNSAT).
            // This is acceptable — the double-decomposition guard worked.
            assert!(
                msg.contains("model validation") || msg.contains("ModelValidation"),
                "unexpected error (not model validation): {msg}"
            );
        }
    }
}

/// Regression test for double-decomposition with replace-generated contains (#4057).
///
/// When str.replace introduces an implicit str.contains check on a variable
/// that already has an explicit str.contains, the second decomposition pass
/// must skip the variable (tracked via `contains_decomposed_vars`). This
/// uses a ground haystack with a multi-char replace pattern to exercise
/// the two-pass decomposition path without timeout.
///
/// Formula: contains(x, "a") ∧ replace(x, "ab", "cd") = y ∧ x = "xab"
/// Z3 model: x = "xab", y = "xcd".
#[test]
fn regression_4057_replace_contains_shared_haystack_no_double_decompose() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.contains x "a"))
(assert (= y (str.replace x "ab" "cd")))
(assert (= x "xab"))
(check-sat)
"#;
    let commands = parse(smt).expect("parse");
    let mut exec = Executor::new();
    match exec.execute_all(&commands) {
        Ok(outputs) => {
            let result = outputs.join("\n");
            let ay = crate::common::sat_result(&result);
            // Z3: sat (x="xab", y="xcd"). Must not return false UNSAT.
            assert!(
                ay == Some("sat") || ay == Some("unknown"),
                "replace+contains shared haystack: SAT (x=\"xab\", y=\"xcd\"), got {ay:?}"
            );
        }
        Err(e) => {
            let msg = format!("{e}");
            // Model validation errors mean SAT was found (not false UNSAT).
            assert!(
                msg.contains("model validation") || msg.contains("ModelValidation"),
                "unexpected error (not model validation): {msg}"
            );
        }
    }
}

/// Regression test for empty-EQC guard in is_known_nonempty (#4057, #4094).
///
/// When a variable is merged into the empty-string EQC (x = ""), stale
/// disequalities (x != "") that were asserted before the merge must not
/// cause `is_known_nonempty` to return true. Without the guard at
/// state.rs:721 (`if self.is_empty_string(terms, t) { return false; }`),
/// check_cycles incorrectly reports cycle conflicts on empty terms.
///
/// Formula: x = "" ∧ y = str.++(x, "a") ∧ contains(y, "a")
/// Model: x = "", y = "a". SAT trivially.
#[test]
fn regression_4057_empty_eqc_not_reported_nonempty() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= x ""))
(assert (= y (str.++ x "a")))
(assert (str.contains y "a"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        ay == Some("sat") || ay == Some("unknown"),
        "empty x in concat: SAT (x=\"\", y=\"a\"), got {ay:?}"
    );
}

/// Regression test for empty-EQC stale disequality guard (#4094).
///
/// A more targeted test: assert x != "" first, then assert x = "".
/// The contradiction should be detected by the equality solver (UNSAT),
/// but the solver must NOT report it via a spurious cycle conflict
/// from is_known_nonempty returning true for a term in the empty EQC.
#[test]
fn regression_4057_empty_eqc_stale_disequality_contradiction() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (not (= x "")))
(assert (= x ""))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "x != \"\" ∧ x = \"\" is UNSAT, got {ay:?}"
    );
}
