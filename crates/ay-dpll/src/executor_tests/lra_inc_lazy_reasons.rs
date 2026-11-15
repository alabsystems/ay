// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lazy theory reasons on the session-persistent QF_LRA lane (#8467).
//!
//! The persistent SAT solver's assumption loop materialises the LRA
//! extension's lazy implied-bound reasons before 1UIP. Each script pins one
//! way a lazy reason went wrong: an unmaterialised one in the conflict's cone
//! made every analysis bail out, an unrebuildable one outside the cone
//! stalled every analysis, one citing its own atom livelocked the analyses
//! through it, and one citing a literal derived from the propagation made
//! 1UIP derive a non-resolvent. Verdicts are pinned to z3 and to the
//! from-scratch lane, and the engine lane's SAT conflicts to
//! [`super::lra_inc_dead_atoms`]'s counted canary, in both publication
//! postures.

use super::lra_inc_dead_atoms::{assert_engine_decides_in, Posture};

/// [`assert_engine_decides_in`] in the default posture and in competition
/// mode. A mishandled lazy reason can make 1UIP learn a non-resolvent, a
/// false `unsat` ([`CIRCULAR_REASON_SCRIPT`]); competition mode sheds the
/// internal proof cycle, so there the engine lane's verdict is published as
/// computed.
fn assert_decides_in_both_postures(script: &str, expected: &[&str], what: &str) {
    for posture in [Posture::Default, Posture::Competition] {
        assert_engine_decides_in(posture, script, expected, what);
    }
}

/// An unrebuildable lazy reason OUTSIDE the conflict's cone (adversarial
/// review fuzz, minimised; verdicts z3 4.8.12). Before ay-lra's explanation
/// fell through past a self-citing strategy, its self-reference guard rejected
/// routine implied-bound handles here and the assumption loop demoted them
/// before 1UIP. Arming the sticky failure flag on such a demotion aborted
/// every analysis at that level, cone or not: 363,646 bails and 7.6 s of CPU
/// (an `unknown` under a 5 s deadline) where 11 conflicts suffice. Only an
/// analysis that resolves into a demoted var may fail closed (ay-sat
/// `extension_tests` t4d); the counted canary pins the work. Either change
/// alone decides this script (3 conflicts with the explanation fixed, 8 with
/// only the flag disarmed); with neither the canary fails.
const OUT_OF_CONE_LAZY_SCRIPT: &str = "\
(set-logic QF_LRA)
(declare-const x0 Real)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const p0 Bool)
(declare-const p1 Bool)
(declare-const p2 Bool)
(assert (not (<= (* 2.0 x1) 2.0)))
(check-sat)
(push 1)
(push 1)
(check-sat)
(pop 1)
(push 1)
(check-sat)
(check-sat)
(pop 1)
(assert (< (+ (ite p2 x2 x1) (* 2.0 (ite p0 x1 x0))) (- 1.0)))
(push 1)
(assert (or (not (>= (+ x0 (ite p1 x1 x2)) x2)) (= (* 2.0 x2) 1.0) (= (+ x2 x1) 0.0)))
(assert (>= (* (- 1.0) (ite p1 x0 x2)) (ite p1 x0 x0)))
(assert (or (not (<= (* (- 1.0) x2) 1.0)) (not (distinct (+ x2 x2) x1))))
(push 1)
(check-sat)
(assert (>= x0 x1))
(check-sat)
(check-sat)
(pop 1)
(check-sat)
(pop 1)
(check-sat)
(pop 1)
(check-sat)
";

#[test]
fn an_unrebuildable_lazy_reason_outside_the_cone_does_not_stall_learning() {
    assert_decides_in_both_postures(
        OUT_OF_CONE_LAZY_SCRIPT,
        &[
            "sat", "sat", "sat", "sat", "sat", "unsat", "unsat", "sat", "sat", "sat",
        ],
        "unrebuildable lazy reason outside the 1UIP cone",
    );
}

/// A lazy implied bound in the conflict's cone (fuzz g3_70184, minimised;
/// verdict z3 4.8.12). Once the SAT core assigned it, the theory had asserted
/// the atom, which became its variable's own direct bound, and the
/// explanation cited the atom itself. That circular reason is refused, so the
/// literal was demoted and every analysis through it failed closed: the bail
/// loop ran 400,005 conflicts (9 s of CPU) before a random decision broke it.
/// The explanation now falls through to the row: 2 conflicts.
const SELF_CITING_REASON_SCRIPT: &str = "\
(set-logic QF_LRA)
(declare-const x0 Real)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const p0 Bool)
(declare-const p1 Bool)
(declare-const p2 Bool)
(assert (not (<= (* 2.0 x1) 2.0)))
(assert (< (+ (ite p2 x2 x1) (* 2.0 (ite p0 x1 x0))) (- 1.0)))
(push 1)
(assert (or (not (>= (+ x0 (ite p1 x1 x2)) x2)) (= (* 2.0 x2) 1.0) (= (+ x2 x1) 0.0)))
(assert (>= (* (- 1.0) (ite p1 x0 x2)) (ite p1 x0 x0)))
(assert (or (not (<= (* (- 1.0) x2) 1.0)) (not (distinct (+ x2 x2) x1))))
(assert (>= x0 x1))
(check-sat)
";

#[test]
fn a_lazy_reason_never_cites_its_own_atom() {
    assert_decides_in_both_postures(
        SELF_CITING_REASON_SCRIPT,
        &["unsat"],
        "lazy implied bound whose atom became its own direct bound",
    );
}

/// A circular lazy reason (fuzz g3_70341, minimised; verdicts z3 4.8.12).
/// Inside the push the theory propagated `x1 < 0` lazily, the scoped
/// `x1 = -3` was asserted after it, and the explanation taken under the
/// current bounds cited `x1 = -3`, itself derived through the propagation
/// (via `not p0`). 1UIP resolved the cycle as self-justifying, so what it
/// derived was no resolvent of the clause database, and after the pop the
/// engine lane refuted the satisfiable base: a false UNSAT that only the
/// strict certification stopped (`unknown (incomplete self-check-rejected)`).
const CIRCULAR_REASON_SCRIPT: &str = "\
(set-logic QF_LRA)
(declare-const x0 Real)
(declare-const x1 Real)
(declare-const p0 Bool)
(assert (= (+ (* 2.0 (ite p0 x1 x1)) (* 2.0 x0)) (- 2.0)))
(assert (or (>= (+ (* 2.0 (ite p0 x0 x0)) (ite p0 x1 x1)) x0) (not (<= (+ (* 2.0 x0) (* 2.0 x0)) x0))))
(assert (or (not (<= (+ (* 2.0 (ite p0 x1 x0)) x1) 1.0)) (= (+ (* 2.0 x0) (* 2.0 x1)) x0)))
(push 1)
(assert (>= (+ x1 (ite p0 x1 x0)) x1))
(assert (or p0 (= x1 (- 3.0)) p0))
(push 1)
(pop 1)
(check-sat)
(pop 1)
(check-sat)
";

#[test]
fn a_circular_lazy_reason_does_not_outlive_its_scope() {
    assert_decides_in_both_postures(
        CIRCULAR_REASON_SCRIPT,
        &["unsat", "sat"],
        "lazy reason through a literal derived from the propagation",
    );
}

/// A conflict whose 1UIP walk reaches a current-level lazy implied bound
/// (push/pop differential fuzz, seed 2026006146, shrunk; verdicts z3 4.16.0).
/// When the assumption loop did not materialise lazy reasons at all, analysis
/// met the opaque handle, backtracked to level 0 and learned nothing, and the
/// same assumptions, propagations and conflict recurred: the second check-sat
/// ran ~150k bailouts until its deadline and answered `unknown`, while z3 and
/// the from-scratch lane answer `unsat` at once.
const CONE_LAZY_REASON_SCRIPT: &str = "\
(set-logic QF_LRA)
(declare-fun x0 () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(push 1)
(assert (and (>= (+ (* 2 x0) (* (- 2) x2) x2) (+ (* (/ 1 2) x2) (* 3 x4) (* (/ 1 2) x3) 3)) (or (<= (+ (* 3 x0) (* 2 x2) (* (/ 1 2) x4)) 3) (>= (ite (>= x0 (/ 3 1)) (+ (* (- 1) x0) x4) (* (- 2) x1)) 4))))
(check-sat)
(assert (and (and (not (<= (+ (* 3 x0) (* 2 x2) (* (- 1) x4) (/ 6 4)) (+ x4 (* 3 x4) (* 2 x1) 0))) (not (= (ite (>= x4 5) (* (- 1) x4) (+ (* (/ 1 2) x1) (* (/ 1 2) x1) (* (/ 1 2) x3))) (+ (* (/ 1 2) x3) x1)))) (and (= (+ (* (/ 1 2) x2) (* 2 x2) x0) (+ (* (- 2) x2) x0 (* 3 x1))) (<= (+ (* (/ 1 2) x2) x1) 6))))
(assert (= x2 (- 3)))
(check-sat)
";

#[test]
fn a_conflict_through_a_lazy_reason_learns() {
    assert_decides_in_both_postures(
        CONE_LAZY_REASON_SCRIPT,
        &["sat", "unsat"],
        "conflict through a current-level lazy implied bound",
    );
}
