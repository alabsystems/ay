// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! AY-SMT-5: the top-level QF_NIA search under a wall deadline.
//!
//! - #nia-persist-until-deadline: the search may keep going to its deadline
//!   only when nothing waits for its `unknown`. In particular the
//!   post-dispatch partition rescue runs after an incomplete `unknown` while
//!   the deadline has not passed, so the policy must be OFF whenever the
//!   assertions split into two or more symbol-disjoint components (the
//!   rescue would otherwise be starved). The policy is reported as the
//!   statistic `nia.persist_until_deadline`.
//! - #nia-box-blast: before that search, growing boxes are bit-blasted for a
//!   small model (`nia.box_blast` statistic). A box without a model is never
//!   an `unsat`.

use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn solve(input: &str, budget: Option<Duration>) -> (String, Executor) {
    let commands = parse(input).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    exec.set_timeout(budget);
    exec.set_memory_limit(Some(4 << 30));
    let outputs = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}"));
    let answer = outputs
        .iter()
        .rev()
        .find(|out| matches!(out.as_str(), "sat" | "unsat" | "unknown"))
        .cloned()
        .unwrap_or_else(|| panic!("no check-sat answer in {outputs:?}"));
    (answer, exec)
}

/// `x^2 + y^2 = 7` has no integer solution (7 is 3 mod 4); `u^2 + v^2 = 7`
/// is the same over other symbols.
const ONE_COMPONENT: &str = "(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (+ (* x x) (* y y)) 7))
(check-sat)
";

const TWO_COMPONENTS: &str = "(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun u () Int)
(declare-fun v () Int)
(assert (= (+ (* x x) (* y y)) 7))
(assert (= (+ (* u u) (* v v)) 7))
(check-sat)
";

#[test]
#[timeout(60_000)]
fn persistence_is_on_for_one_component_under_a_deadline() {
    let (answer, exec) = solve(ONE_COMPONENT, Some(Duration::from_secs(3)));
    assert_ne!(answer, "sat", "the instance is unsat");
    assert_eq!(
        exec.statistics().get_int("nia.persist_until_deadline"),
        Some(1)
    );
}

#[test]
#[timeout(60_000)]
fn persistence_is_off_when_a_partition_rescue_may_follow() {
    let (answer, exec) = solve(TWO_COMPONENTS, Some(Duration::from_secs(3)));
    assert_ne!(answer, "sat", "the instance is unsat");
    assert_eq!(
        exec.statistics().get_int("nia.persist_until_deadline"),
        Some(0),
        "two symbol-disjoint components: the partition rescue may follow"
    );
}

/// `x*y*z = 30`, `x+y+z = 10`, all `>= 2`: the only models are the
/// permutations of `(2, 3, 5)`. The boxes at the proven lower bound 2 are
/// `[2, 4]` (r = 1), `[2, 2]` (r = 2), `[2, 4]` (r = 4) and `[2, 8]` (r = 8),
/// so the lane answers at r = 8.
#[test]
#[timeout(60_000)]
fn box_lane_finds_a_small_model() {
    let input = "(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (= (* x y z) 30))
(assert (= (+ x y z) 10))
(assert (>= x 2))
(assert (>= y 2))
(assert (>= z 2))
(check-sat)
";
    let (answer, exec) = solve(input, Some(Duration::from_secs(10)));
    assert_eq!(answer, "sat");
    assert_eq!(
        exec.statistics().get_string("nia.box_blast"),
        Some("sat r=8")
    );
}

/// `x*x = 4096` has its models at `x = +-64`, outside every box the lane
/// tries (r <= 32): every box is empty, and that must never become `unsat`.
#[test]
#[timeout(60_000)]
fn empty_boxes_never_answer_unsat() {
    let input = "(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (* x x) 4096))
(assert (= (* x y) (* 64 y)))
(check-sat)
";
    let (answer, exec) = solve(input, Some(Duration::from_secs(10)));
    assert_ne!(answer, "unsat", "x = 64 is a model");
    let lane = exec
        .statistics()
        .get_string("nia.box_blast")
        .map(str::to_owned);
    assert!(
        lane.as_deref().is_some_and(|s| s.starts_with("box-unsat")
            || s.starts_with("budget")
            || s.starts_with("declined")),
        "{lane:?}"
    );
}

/// The internal safety deadline of an untimed call never enables the
/// optional search, and the ordinary solver still answers this instance.
#[test]
#[timeout(60_000)]
fn a_solve_without_a_timeout_is_answered() {
    let input = "(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (* x y) 6))
(assert (>= x 2))
(assert (>= y 2))
(check-sat)
";
    let (answer, exec) = solve(input, None);
    assert_eq!(answer, "sat");
    assert_eq!(exec.statistics().get_string("nia.box_blast"), None);
    assert_ne!(
        exec.statistics().get_int("nia.persist_until_deadline"),
        Some(1)
    );
}
