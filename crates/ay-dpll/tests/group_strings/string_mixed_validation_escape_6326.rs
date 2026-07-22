// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression test for #6326: model validation skips Unknown string
//! evaluations, allowing false SAT in mixed string+arithmetic formulas.
//!
//! The bug: when a formula mixes string constraints with arithmetic,
//! the arithmetic assertions provide `checked` evidence while string
//! assertions silently increment `skipped_internal`. The zero-evidence
//! guard does not fire because `stats.checked > 0`, so string
//! constraints are invisible to validation.

/// Mixed QF_SLIA: conflicting str.prefixof with arithmetic.
/// "ab" and "ac" conflict at position 1 — no string can have both prefixes.
/// The arithmetic assertion `(= n 42)` provided checked evidence in the
/// broken code, masking the invisible string skip.
#[test]
fn test_mixed_slia_prefixof_conflict_not_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-const x String)
(declare-const n Int)
(assert (= n 42))
(assert (str.prefixof "ab" x))
(assert (str.prefixof "ac" x))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_ne!(
        result, "sat",
        "mixed string+arithmetic must not return sat for conflicting prefixes (#6326)"
    );
}

/// Pure string version (no arithmetic) — this already returned unknown
/// before the fix because the zero-evidence guard fired.
#[test]
fn test_pure_string_prefixof_conflict_not_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-const x String)
(assert (str.prefixof "ab" x))
(assert (str.prefixof "ac" x))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_ne!(
        result, "sat",
        "pure string prefixof conflict must not return sat"
    );
}

/// Mixed QF_SLIA with str.contains — another pattern where the
/// arithmetic evidence could mask string evaluation gaps.
#[test]
fn test_mixed_slia_contains_conflict_not_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-const x String)
(declare-const n Int)
(assert (= n 10))
(assert (= (str.len x) 1))
(assert (str.contains x "ab"))
(check-sat)
"#;
    // A string of length 1 cannot contain "ab" (length 2).
    let result = crate::common::solve(smt);
    assert_ne!(
        result, "sat",
        "length-1 string containing length-2 substring must not return sat"
    );
}
