// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! D10 fix-up (2026-09-29): the two defects the scope-leak verifier found in
//! the branch's first design, pinned corpus-free with z3 5.1.0's answers.
//! H1 lived in the private query scope the fix-up withdrew; L1 in ay-sat's
//! original-clause ledger, fixed on main by 6c706d25ba. Both must stay decided.
//! And the defect 6c706d25ba exposed on main: a SAT frame the lazy split
//! loop's drift bail leaked, which let a scoped `false` outlive its pop.

use super::hunt_scope_leak_wrong_verdicts::{assert_decided_in_z3_mode, assert_never_wrong};

/// H1 (scope-leak verifier round 1, `probe/h1w3.smt2`): the branch solved a
/// window inside a user scope in a private scope of the session's lanes. The
/// private pop killed the activation of the window's assumption but left it
/// in the theory lane's encoded map; the plain check after the window cleared
/// the lane's re-activation flag, so when the same atom was asserted for real
/// it was taken for encoded and never activated. The third check was answered
/// on a model that violates it and the model gate turned it into `unknown`
/// (origin/main and the fix-up, whose windows never touch the session's
/// lanes, answer `unsat`). An atom asserted after a window must be active.
const H1_WINDOW_ATOM_ASSERTED_LATER: &str = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (>= (* y y x) 3))
(push 1)
(check-sat-assuming ((> (div x z) 4)))
(check-sat)
(assert (< (div x z) 2))
(assert (> (div x z) 4))
(check-sat)
(pop 1)
(check-sat)
"#;

/// H1, round-2 verifier `probe/w1_div0.smt2`: the same with a zero divisor.
const H1_DIVISOR_ZERO: &str = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (>= (* y y x) 3))
(assert (= z 0))
(push 1)
(check-sat-assuming ((> (div x z) 4)))
(check-sat)
(assert (< (div x z) 2))
(assert (> (div x z) 4))
(check-sat)
(pop 1)
(check-sat)
"#;

/// H1, round-2 verifier `probe/w6_nra_irr.smt2`: QF_NRA, irrational base.
const H1_NRA_IRRATIONAL: &str = r#"
(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= (* x x) 2.0))
(assert (> x 0.0))
(push 1)
(check-sat-assuming ((> (* x y) 3.0)))
(check-sat)
(assert (> (* x y) 3.0))
(assert (< y 1.0))
(check-sat)
(pop 1)
(check-sat)
"#;

/// H1 fixtures with z3 5.1.0's answers.
const H1_FIXTURES: [(&str, &str, &[&str]); 3] = [
    (
        "window atom asserted later",
        H1_WINDOW_ATOM_ASSERTED_LATER,
        &["sat", "sat", "unsat", "sat"],
    ),
    (
        "divisor zero",
        H1_DIVISOR_ZERO,
        &["sat", "sat", "unsat", "sat"],
    ),
    (
        "QF_NRA irrational base",
        H1_NRA_IRRATIONAL,
        &["sat", "sat", "unsat", "sat"],
    ),
];

#[test]
fn h1_a_window_atom_asserted_later_is_activated() {
    for (name, smt, expect) in H1_FIXTURES {
        assert_never_wrong(name, smt, expect);
        assert_decided_in_z3_mode(name, smt, expect);
    }
}

/// L1 (scope-leak verifier round 2, `probe/n796a_pw_min.smt2`): push/pop only.
/// A root asserted at depth 1 is first encoded at depth 2; its activation is
/// added for ancestor scope 1 (`add_clause_at_scope_depth`), which the SAT
/// solver's original-clause ledger recorded in scope 2's segment. The pop of
/// scope 2 truncated it from the ledger while it was still in force; the next
/// rebuild of the clause database from the ledger lost it, and the lane's
/// activation map still said "active at 1", so nothing re-added it: the second
/// check ran without the depth-1 roots (`--z3-mode` `sat unknown`, the model
/// gate refusing a model that violates them). ay-sat 6c706d25ba keeps such a
/// clause until scope 1 itself is popped.
const L1_ANCESTOR_ACTIVATION_AFTER_POP: &str = r#"
(set-logic QF_NIA)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(push 1)
(assert (not (= (mod x0 x2) 0)))
(assert (<= x0 1))
(push 1)
(assert (not (= (div x2 2) x1)))
(check-sat)
(pop 1)
(check-sat)
"#;

/// L1, the unreduced witness (`probe/n796a_pw.smt2`): three nested scopes.
const L1_NESTED_SCOPES: &str = r#"
(set-logic QF_NIA)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(assert (< (+ x0 (* 2 x1)) 2))
(push 1)
(assert (not (= (mod x0 x2) 0)))
(push 1)
(assert (<= x0 1))
(push 1)
(assert (not (= x1 (* x0 x1))))
(assert (not (= (div x2 2) x1)))
(check-sat)
(pop 1)
(check-sat)
(pop 1)
(check-sat)
"#;

/// L1 with a refutation to keep (round-2 verifier's `gen_l1.py` seed 40419,
/// `l1_nia_40419_00014`, cut after its second check): the two contradictory
/// depth-1 roots are first encoded at depth 2; after the pop the branch's
/// first design lost them and answered `unknown` where z3 answers `unsat`.
const L1_REFUTATION_AFTER_INNER_POP: &str = r#"
(set-logic QF_NIA)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(assert (or (<= (+ x0 (* 2 x0)) (- 15)) (<= (+ x0 (* 2 x0)) (- 15))))
(push 1)
(assert (and (<= (* x0 x1) (- 2)) (not (= x1 (* x1 x0)))))
(assert (not (<= (* x0 x1) (- 2))))
(push 1)
(assert (and (not (= x1 (* x1 x0))) (not (= x1 (* x1 x0)))))
(check-sat)
(pop 1)
(check-sat)
"#;

/// L1 through a symbolic `mod` (scope-leak fix-up probe `l1_p1`): the same
/// shape, the inner root introducing a `mod` the NIA route eliminates.
const L1_SYMBOLIC_MOD_AFTER_INNER_POP: &str = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(push 1)
(assert (> (* x y) 5))
(assert (< x 1))
(assert (> y 0))
(push 1)
(assert (= z (mod x y)))
(check-sat)
(pop 1)
(check-sat)
"#;

#[test]
fn l1_a_root_activated_for_its_own_scope_survives_an_inner_pop() {
    for (name, smt, expect) in [
        (
            "ancestor activation after pop",
            L1_ANCESTOR_ACTIVATION_AFTER_POP,
            &["sat", "sat"][..],
        ),
        (
            "nested scopes",
            L1_NESTED_SCOPES,
            &["sat", "sat", "sat"][..],
        ),
        (
            "refutation after inner pop",
            L1_REFUTATION_AFTER_INNER_POP,
            &["unsat", "unsat"][..],
        ),
        (
            "symbolic mod after inner pop",
            L1_SYMBOLIC_MOD_AFTER_INNER_POP,
            &["unsat", "unsat"][..],
        ),
    ] {
        assert_never_wrong(name, smt, expect);
        assert_decided_in_z3_mode(name, smt, expect);
    }
}

/// The lazy split loop's unbounded-drift bail (#1836) left its private SAT
/// frame on the session's persistent solver (every other exit pops it). The
/// next `(push 1)` then ran one frame deep, the scope's `(assert false)` was
/// guarded by the leaked frame, and the user's `(pop 1)` popped the wrong
/// selector: `--z3-mode` answered the last check `unsat` (origin/main
/// 9ea9b8b5dd). Delta-debugged from `leak_liadiv_9251_01603`; the plain
/// check's QF_NIA search (symbolic `div`) is the one that drifts.
const LEAKED_FRAME_AFTER_DRIFT: &str = r#"
(set-logic ALL)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun p0 () Bool)
(declare-fun p1 () Bool)
(assert (distinct (div (div x2 2) (* 3 x3)) 2))
(assert (>= (- (* (- 3) x3) (mod 1 x3)) 0))
(assert (=> p0 (= (+ (+ 3 x3) x0) (- 5))))
(assert (=> p1 (>= (mod 5 x1) 0)))
(check-sat-assuming ((not p1) p1))
(assert (>= (+ x3 (div (- 3) x2)) 0))
(check-sat)
(push 1)
(assert (>= (div (- 3) 2) (- 1)))
(check-sat)
(pop 1)
(check-sat)
"#;

#[test]
fn a_scope_refuted_after_a_drift_bail_does_not_outlive_its_pop() {
    assert_never_wrong(
        "leaked frame after drift",
        LEAKED_FRAME_AFTER_DRIFT,
        &["unsat", "sat", "unsat", "sat"],
    );
}
