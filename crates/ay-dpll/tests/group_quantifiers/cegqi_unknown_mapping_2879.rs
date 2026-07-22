// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #2879: CEGQI re-solve Unknown→SAT mapping is unsound when ground solver
//! returns Unknown for the category.
//!
//! When CEGQI's forall disambiguation re-solves the ground formula without CE
//! lemmas, the result may be Unknown (e.g., if the logic category is not
//! handled in the re-solve match). The old code mapped this to SAT via a
//! catch-all `_` arm. The fix maps Unknown/Err to Unknown.

use ntest::timeout;

/// A valid forall with LIRA ground should not return "unsat".
/// Before #2879 fix, the catch-all in the re-solve match mapped Unknown to
/// SAT. After the fix, it maps to Unknown. Both SAT and Unknown are
/// acceptable; UNSAT would be unsound.
#[test]
#[timeout(10000)]
fn test_cegqi_ground_unknown_does_not_become_unsat_2879() {
    // Ground: LIRA (mixed Int + Real)
    // Forall: z + 0 = z (trivially valid)
    // The CE lemma ~(e + 0 = e) is contradictory, so the full solve returns
    // UNSAT. The re-solve on ground-only hits the catch-all for LIRA category,
    // returning Unknown.
    let smt = r#"
(set-logic ALL)
(declare-fun a () Int)
(declare-fun b () Real)
(assert (> b 0.5))
(assert (>= a 0))
(assert (forall ((z Int)) (= (+ z 0) z)))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    // The formula is SAT (ground is SAT, forall is valid).
    // Must not return "unsat" — that would be unsound.
    assert!(
        !output.contains("unsat"),
        "LIRA ground + valid forall must not be UNSAT, got: {output}"
    );
}

/// A valid forall with LIA ground (handled in re-solve) should still produce
/// correct results. This verifies the fix doesn't regress the happy path.
#[test]
#[timeout(10000)]
fn test_cegqi_ground_sat_resolves_correctly_2879() {
    // Ground: pure LIA (handled in re-solve)
    // Forall: x + 0 = x (trivially valid)
    let smt = r#"
(set-logic ALL)
(declare-fun a () Int)
(assert (>= a 0))
(assert (forall ((z Int)) (= (+ z 0) z)))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    // With pure LIA ground, re-solve should find SAT, so final result is SAT.
    // Unknown is also acceptable (quantifier handling is incomplete).
    assert!(
        !output.contains("unsat"),
        "LIA ground + valid forall must not be UNSAT, got: {output}"
    );
}
