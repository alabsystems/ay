// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! D10: query-local facts outliving their query, pinned corpus-free.
//!
//! Nothing derived under a `check-sat-assuming` assumption or inside a push
//! scope may survive into a later query unless the permanent assertions imply
//! it. The persistent incremental SAT solver broke this two ways, both wrong
//! `unsat` under `--z3-mode` (the default posture's certification rejected the
//! refutation and answered `unknown`):
//!
//! # D10(a) — a scoped assumption solve made its assumptions permanent
//!
//! The QF_NIA / QF_NRA / QF_LRA arms retry an undecided direct assumption
//! solve through `solve_scoped_assumptions`, which merges the assumptions into
//! the assertion vector. The lane below encoded them into the session's
//! persistent SAT solver at the current depth — at depth 0 a permanent unit —
//! and every later query was solved under them (the 2026-09-23 linear hunt's
//! is_int witness, the NIA-soundness verifier's 57 incremental files; one of
//! them is an assumption unsatisfiable on its own, with no `div` in the base).
//! The window is now solved on fresh lanes in EVERY session; origin/main
//! ec28f5b4f8 did so only in incremental mode, and a script that never pushes
//! still leaked (`D10A_NO_PUSH`).
//!
//! # D10(c) — a scoped rewrite activated at depth 0
//!
//! The persistent SAT solver read each encoded term's push depth off its
//! POSITION in `ctx.assertions`, but routes install working windows there
//! (`solve_nia`: symbolic div/mod elimination and variable substitution). A
//! scoped `(= x 0)` substituted into the base `(> (* x y) 3)` gave `false` at
//! position 0 — activated at depth 0, permanent: every check after the pop was
//! `unsat` (the linear hunt's symbolic-division witness, the verifier's
//! push/pop witness).
//!
//! Every fixture runs in four postures: the plain and authored executors, the
//! fail-closed self-check, and the `--z3-mode` posture (proof cycle shed), the
//! only one in which these were wrong. z3 5.1.0's answers are in each
//! fixture's `EXPECT`.

use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;

/// D10(a), linear hunt M6 (`isintas`): the QF_LRA arm's scoped retry.
const D10A_IS_INT: &str = r#"
(set-logic QF_LIRA)
(declare-fun r0 () Real)
(declare-fun p1 () Bool)
(assert (is_int r0))
(check-sat-assuming (p1))
(check-sat-assuming ((not p1)))
"#;

/// D10(a), NIA-soundness verifier round 2: an assumption unsatisfiable on its
/// own, no `div` in the base, then a plain check.
const D10A_THEORY_ATOM: &str = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (>= (* y y x) 3))
(check-sat-assuming ((= (mod x 6) 6)))
(check-sat)
"#;

/// D10(a), verifier round 1: a fresh Boolean assumption, then its negation.
const D10A_FRESH_SELECTOR: &str = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun q () Bool)
(assert (> (div x 2) 0))
(assert (>= (* y y x) 3))
(check-sat-assuming (q))
(check-sat-assuming ((not q)))
"#;

/// D10(a), verifier round 2: the leaked assumption survives into a later push.
const D10A_THEN_PUSH: &str = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (> (div x 2) 0))
(assert (>= (* y y x) 3))
(declare-fun q () Bool)
(assert (=> q (< x 0)))
(check-sat-assuming (q))
(push 1)
(assert (> x 3))
(check-sat)
(pop 1)
(check-sat)
"#;

/// D10(a) inside a push: the assumption was activated at depth 1 and lived
/// until the pop, so the plain check in the same scope was refuted.
const D10A_INSIDE_PUSH: &str = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (>= (* y y x) 3))
(push 1)
(check-sat-assuming ((= (mod x 6) 6)))
(check-sat)
(pop 1)
(check-sat)
"#;

/// D10(a) in a session that never pushes (2026-09-29 scope-leak fix-up,
/// delta-debugged from the round-2 verifier's `niadiv_40417_00386`). origin/main
/// ec28f5b4f8 solves a scoped window on fresh lanes only in incremental mode,
/// which a script without `push` never enters; the lanes below still keep
/// their state across queries, so the first window's `(< (* x1 x0) (- 17))`
/// became a permanent unit and the second window, which assumes its negation,
/// was refuted (`--z3-mode` `sat unsat`).
const D10A_NO_PUSH: &str = r#"
(set-logic QF_NIA)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(assert (and (not (>= (div x1 x0) 3)) (not (>= (div x1 x0) 3))))
(check-sat-assuming ((not (>= (div x1 x0) 3)) (< (* x1 x0) (- 17))))
(check-sat-assuming ((not (= (mod x2 3) 1)) (not (< (* x1 x0) (- 17)))))
"#;

/// D10(a), QF_NRA: the NRA arm's scoped retry.
const D10A_NRA: &str = r#"
(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun q () Bool)
(assert (> (/ x 2.0) 0.0))
(assert (>= (* y y x) 3.0))
(check-sat-assuming (q))
(check-sat-assuming ((not q)))
"#;

/// D10(c), linear hunt M5 (`dzincr_31_00040`): a scoped equality on a
/// symbolic-divisor quotient became a substitution that rewrote the base.
const D10C_SYMBOLIC_DIV: &str = r#"
(set-logic ALL)
(declare-fun b () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (> (div b (- y z)) 2))
(assert (= y 0))
(push 1)
(assert (= (div b (- y z)) (- 1)))
(check-sat)
(pop 1)
(check-sat)
"#;

/// D10(c) at its smallest: a scoped `(= x 0)` substituted into the base.
const D10C_SCOPED_EQUALITY: &str = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (> (* x y) 3))
(push 1)
(assert (= x 0))
(check-sat)
(pop 1)
(check-sat)
"#;

/// D10(c), verifier round 1 §2b: a scoped false `mod` equality, symbolic
/// `mod` in the base.
const D10C_SCOPED_MOD: &str = r#"
(set-logic QF_NIA)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(assert (>= (mod (* x1 x1) x1) (- 1)))
(assert (<= (* x0 x1) 0))
(assert (<= (+ (* x0 x2 x1) x0) 0))
(assert (>= (+ x0 (* 3 x1)) 0))
(push 1)
(assert (= (mod x2 6) 6))
(check-sat)
(pop 1)
(check-sat)
"#;

/// D10(a) fixtures with z3 5.1.0's answers.
const D10A_FIXTURES: [(&str, &str, &[&str]); 7] = [
    ("is_int, selector flipped", D10A_IS_INT, &["sat", "sat"]),
    (
        "unsatisfiable theory atom",
        D10A_THEORY_ATOM,
        &["unsat", "sat"],
    ),
    (
        "fresh selector flipped",
        D10A_FRESH_SELECTOR,
        &["sat", "sat"],
    ),
    (
        "assumption then push",
        D10A_THEN_PUSH,
        &["unsat", "sat", "sat"],
    ),
    (
        "assumption inside a push",
        D10A_INSIDE_PUSH,
        &["unsat", "sat", "sat"],
    ),
    ("no push", D10A_NO_PUSH, &["sat", "sat"]),
    ("QF_NRA selector flipped", D10A_NRA, &["sat", "sat"]),
];

/// D10(c) fixtures with z3 5.1.0's answers.
const D10C_FIXTURES: [(&str, &str, &[&str]); 3] = [
    (
        "symbolic-divisor quotient",
        D10C_SYMBOLIC_DIV,
        &["unsat", "sat"],
    ),
    ("scoped equality", D10C_SCOPED_EQUALITY, &["unsat", "sat"]),
    ("scoped mod equality", D10C_SCOPED_MOD, &["unsat", "sat"]),
];

fn verdicts(results: &[String]) -> Vec<&str> {
    results
        .iter()
        .map(|line| line.trim())
        .filter(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .collect()
}

#[derive(Clone, Copy, Debug)]
enum Posture {
    /// `Executor::execute_all`, no flags.
    Plain,
    /// The caller-authored boundary the CLI uses.
    Authored,
    /// Fail-closed self-certification (`--self-check`).
    SelfCheck,
    /// The CLI's `--z3-mode` posture: the internal proof cycle is shed.
    Z3Mode,
}

const POSTURES: [Posture; 4] = [
    Posture::Plain,
    Posture::Authored,
    Posture::SelfCheck,
    Posture::Z3Mode,
];

/// Every wrong verdict pinned here was immediate on main.
const NEVER_WRONG_BUDGET: Duration = Duration::from_secs(5);
const DECIDED_BUDGET: Duration = Duration::from_secs(30);

fn solve(smt: &str, posture: Posture, budget: Duration) -> Vec<String> {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"));
    let mut exec = Executor::new();
    exec.set_timeout(Some(budget));
    match posture {
        Posture::SelfCheck => exec.set_self_check(true),
        Posture::Z3Mode => exec.set_competition_mode(true),
        Posture::Plain | Posture::Authored => {}
    }
    if matches!(posture, Posture::Authored) {
        let mut output = Vec::new();
        for command in &commands {
            if let Some(line) = exec
                .execute_authored(command)
                .unwrap_or_else(|err| panic!("execution failed: {err}\nSMT2:\n{smt}"))
            {
                output.push(line);
            }
        }
        output
    } else {
        exec.execute_all(&commands)
            .unwrap_or_else(|err| panic!("execution failed: {err}\nSMT2:\n{smt}"))
    }
}

/// A definite answer that contradicts z3 is wrong; `unknown` is not.
pub(super) fn assert_never_wrong(name: &str, smt: &str, expect: &[&str]) {
    for posture in POSTURES {
        let results = solve(smt, posture, NEVER_WRONG_BUDGET);
        let got = verdicts(&results);
        assert_eq!(
            got.len(),
            expect.len(),
            "{name} ({posture:?}): one verdict per check expected; got {results:?}"
        );
        for (index, (&got, &want)) in got.iter().zip(expect).enumerate() {
            assert!(
                got == want || got == "unknown",
                "WRONG VERDICT ({name}, {posture:?}, check {index}): z3 5.1.0 says `{want}`, \
                 got `{got}`; all answers {got_all:?}",
                got_all = verdicts(&results)
            );
        }
    }
}

/// The `--z3-mode` posture must DECIDE these, not merely stop being wrong: a
/// repair that bought soundness by answering `unknown` after every
/// assumption or pop would pass [`assert_never_wrong`]. Every query here is
/// decided in milliseconds; the budget only absorbs a loaded machine.
pub(super) fn assert_decided_in_z3_mode(name: &str, smt: &str, expect: &[&str]) {
    let results = solve(smt, Posture::Z3Mode, DECIDED_BUDGET);
    assert_eq!(
        verdicts(&results),
        expect,
        "{name} (Z3Mode): z3 5.1.0's answers expected; got {results:?}"
    );
}

#[test]
fn d10a_assumptions_do_not_outlive_their_query() {
    for (name, smt, expect) in D10A_FIXTURES {
        assert_never_wrong(name, smt, expect);
    }
    // The QF_NRA fixture stays `unknown` at its second query: not asserted.
    for (name, smt, expect) in &D10A_FIXTURES[..6] {
        assert_decided_in_z3_mode(name, smt, expect);
    }
}

#[test]
fn d10c_scoped_rewrites_do_not_outlive_their_scope() {
    for (name, smt, expect) in D10C_FIXTURES {
        assert_never_wrong(name, smt, expect);
        assert_decided_in_z3_mode(name, smt, expect);
    }
}

/// From the NIA-soundness verifier's `incr_nia_7001_0004`, a session that never
/// pushes: the window `(p2 p3)` is decided only warm (with the SAT state the
/// plain check before it left; on fresh lanes it is `unknown` under
/// `--z3-mode`). origin/main solved it on the session's lanes (its fresh-lane
/// helper returns early outside incremental mode) and kept `p2` as a permanent
/// unit, so the last check, which asserts `(not p2)`, was `unsat` under
/// `--z3-mode`. The window is now solved on a COPY of the session's lanes.
const D10A_WARM_SESSION: &str = r#"
(set-logic QF_NIA)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun p0 () Bool)
(declare-fun p1 () Bool)
(declare-fun p2 () Bool)
(declare-fun p3 () Bool)
(assert (not (<= (+ (* 3 x3) (* (- 2) x2)) 8)))
(assert (= (+ (* x1 x1) (* x2 x0) (* 7 x1)) 75))
(check-sat)
(assert (=> p0 (distinct (* x2 x3) (- 3))))
(assert (=> p1 (= (+ (* 7 (* x2 x3 x0)) (* (- 6) x2)) 123)))
(assert (=> p2 (not (<= (* x2 x0) 14))))
(assert (=> p3 (<= (* x1 x2) (- 15))))
(check-sat-assuming (p2 p3))
(assert (not p2))
(check-sat)
"#;

#[test]
fn d10a_a_window_in_a_session_without_push_does_not_outlive_its_query() {
    let expect = ["sat", "sat", "sat"];
    // 8b71d73999 and origin/main 1e4c7ed053 `--z3-mode`: `sat sat unsat`.
    assert_never_wrong("warm session", D10A_WARM_SESSION, &expect);
    // The window is decided (warm); the last check need not be.
    let results = solve(D10A_WARM_SESSION, Posture::Z3Mode, DECIDED_BUDGET);
    assert_eq!(
        verdicts(&results).get(..2),
        Some(&expect[..2]),
        "warm session (Z3Mode): z3 5.1.0's answers expected; got {results:?}"
    );
}

/// The same window solved twice in one query continues its lanes. From the
/// round-2 verifier's `niadiv_40417_00698` (its first query): under
/// `:produce-unsat-cores` the QF_NIA arm's scoped retry and then the
/// named-core rescue solve the same window; origin/main's second solve went on
/// from the lanes the first one left (the session's, outside incremental
/// mode) and decided it. The fix-up's second sub-solve continues the first
/// one's lanes too (fresh lanes each time left it `unknown`).
const D10A_SAME_WINDOW_TWICE: &str = r#"
(set-logic QF_NIA)
(set-option :produce-unsat-cores true)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun p0 () Bool)
(declare-fun p1 () Bool)
(declare-fun p2 () Bool)
(assert (<= x0 3))
(assert (! (not (= (mod x1 2) 1)) :named n1))
(assert (=> p0 (not (= (mod x0 6) 0))))
(assert (! (> (* x0 x0) 1) :named n2))
(assert (! (=> p0 (= (mod x0 6) 2)) :named n3))
(check-sat-assuming ((> (* x1 x0) 12) (= x1 8) p2))
"#;

#[test]
fn d10a_the_same_window_solved_twice_continues_its_lanes() {
    let expect = ["sat"];
    assert_never_wrong("same window twice", D10A_SAME_WINDOW_TWICE, &expect);
    assert_decided_in_z3_mode("same window twice", D10A_SAME_WINDOW_TWICE, &expect);
}

/// The session keeps what the permanent assertions taught it. From the
/// NIA-soundness verifier's round-2 corpus (`r2_incr_5200_0040`): the last
/// check is decided only warm (asked alone, with every assertion, it is
/// `unknown`), and the warm state it needs is what the permanent assertions
/// give: it is decided with the check-sat-assumings replaced by plain checks,
/// wrapped as `(push 1) (assert A) (check-sat) (pop 1)`, or removed. A depth-0
/// window that threw the session lanes away afterwards lost it; a window
/// solved on fresh lanes leaves them untouched.
const D10A_WARM_AFTER_WINDOWS: &str = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun s0 () Bool)
(declare-fun s1 () Bool)
(declare-fun s2 () Bool)
(assert (<= (* z y z) (- 9)))
(assert (>= (+ (* (- 2) x) z y) (- 9)))
(assert (= (mod z 6) 3))
(check-sat)
(assert (=> s0 (<= (* x z) 9)))
(check-sat-assuming (s0))
(check-sat)
(assert (=> s1 (distinct (* y x y) 7)))
(assert (=> s2 (>= (mod z 6) 1)))
(check-sat-assuming (s1 s2))
(check-sat)
"#;

#[test]
fn d10a_session_stays_warm_after_depth_zero_windows() {
    let expect = ["sat"; 5];
    assert_never_wrong("warm after windows", D10A_WARM_AFTER_WINDOWS, &expect);
    assert_decided_in_z3_mode("warm after windows", D10A_WARM_AFTER_WINDOWS, &expect);
}

/// A depth-0 window takes no scope. From the NIA-soundness verifier's
/// `incr_nia_7001_0107`: the first assumption query, after a plain check. In
/// a private scope of the session's lanes (the selector-composing SAT entry)
/// the NIA model check gives up on the SAT model it is handed (`unknown`); as
/// a plain depth-0 check on fresh lanes it is `sat`.
const D10A_DEPTH_ZERO_NO_SCOPE: &str = r#"
(set-logic QF_NIA)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun p0 () Bool)
(declare-fun p1 () Bool)
(assert (< (+ (* 7 (* x1 x1)) (* (- 6) x1) (* 4 x1)) 33))
(assert (distinct (div (* x2 x1) 3) 2))
(assert (not (<= (+ (* 5 x0) (* (- 3) x1) (* 2 x0)) 39)))
(check-sat)
(assert (=> p0 (< (+ (* 7 (* x1 x2)) (* (- 2) x0) (* 7 (* x1 x2))) 48)))
(assert (=> p1 (not (<= (* x0 x2) (- 11)))))
(check-sat-assuming ((not p0)))
"#;

#[test]
fn d10a_depth_zero_window_takes_no_scope() {
    let expect = ["sat", "sat"];
    assert_never_wrong("depth-0 window", D10A_DEPTH_ZERO_NO_SCOPE, &expect);
    assert_decided_in_z3_mode("depth-0 window", D10A_DEPTH_ZERO_NO_SCOPE, &expect);
}

/// Genuine Boolean SLS leaves must survive only in the query's typed model.
#[test]
fn nia_boolean_local_search_decides_the_two_warm_scope_regressions() {
    let warm_with_model = D10A_WARM_SESSION.replacen(
        "(check-sat-assuming (p2 p3))",
        "(check-sat-assuming (p2 p3))\n(get-value (p2 p3))",
        1,
    );
    for (name, script, expected) in [
        (
            "depth-zero Boolean window",
            D10A_DEPTH_ZERO_NO_SCOPE,
            vec!["sat", "sat"],
        ),
        (
            "warm Boolean windows",
            warm_with_model.as_str(),
            vec!["sat", "sat", "sat"],
        ),
    ] {
        for posture in [Posture::Plain, Posture::Z3Mode] {
            let results = solve(script, posture, DECIDED_BUDGET);
            assert_eq!(
                verdicts(&results),
                expected,
                "{name} ({posture:?}): {results:?}"
            );
            if name == "warm Boolean windows" {
                assert!(
                    results
                        .iter()
                        .any(|line| line.contains("(p2 true)") && line.contains("(p3 true)")),
                    "assumed leaves must be Boolean in the actual model: {results:?}"
                );
            }
        }
    }
    let contradictory = "(set-logic QF_NIA)(declare-const p Bool)(declare-const x Int)\n\
        (assert p)(assert (= x 1))(assert (=> p (= (* x x) 4)))(check-sat)";
    let results = solve(contradictory, Posture::Plain, DECIDED_BUDGET);
    assert_eq!(verdicts(&results), vec!["unsat"], "{results:?}");
}
