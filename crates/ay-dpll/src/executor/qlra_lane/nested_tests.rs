// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Nested search (M2) against the REAL probe oracle: the FMSD'17 §6
//! Examples 10–12 as exact traces (LRA versions: the midpoint selection
//! replaces the paper's LIA one), plus the two exactness rules the paper's
//! grammar (4) hides — unsafe children first, and nested exactness from a
//! context-free UNSAT only.
//!
//! The traces follow the paper's tables step for step except that, after a
//! nested node logs an instance, the search re-asks only the parent's
//! counterexample query rather than the main query and every ancestor (see
//! `Search::rec`: with frozen instances those answers cannot have changed,
//! except for a child that is also a top node, which forces another round,
//! and for a node whose unsafe child grew since its check, which is asked
//! again).
//!
//! Trace notation: `M+`/`M-` main query sat/unsat; `C<n>c±` / `C<n>s±` a
//! counterexample query of node `n` in the main context / standalone;
//! `I<n>` an instance logged for node `n`; `X<n>` node `n` became exact.

use std::time::Duration;

use ay_core::time::Instant;
use ay_core::TermId;
use ay_frontend::{parse, Command};

use super::probe_oracle::{ExecutorQlraHost, OracleRoute};
use crate::cegqi::lra_nested::nested::{solve_nested_with, NestedCaps};
use crate::cegqi::lra_nested::{
    build_nested_tree, solve_nested, NestedRun, QlraDecline, QlraOutcome, TraceStep,
};
use crate::Executor;

struct Traced {
    run: NestedRun,
    steps: Vec<String>,
    /// Logged tuples, printed, in log order.
    tuples: Vec<(usize, Vec<String>)>,
}

fn trace(smt: &str) -> Traced {
    let commands: Vec<Command> = parse(smt)
        .expect("parse")
        .into_iter()
        .filter(|c| !matches!(c, Command::CheckSat))
        .collect();
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("execute");
    let roots: Vec<TermId> = exec.ctx.assertions.clone();
    let tree = build_nested_tree(&mut exec.ctx.terms, &roots).expect("nested tree");
    let deadline = Instant::now() + Duration::from_secs(30);
    let run = {
        let mut host = ExecutorQlraHost::with_route(&mut exec, deadline, OracleRoute::DirectQfLra);
        solve_nested(&mut host, &tree)
    };
    let mut steps = Vec::new();
    let mut tuples = Vec::new();
    for step in &run.trace {
        steps.push(match step {
            TraceStep::Main { sat } => format!("M{}", if *sat { '+' } else { '-' }),
            TraceStep::Check { node, context, sat } => format!(
                "C{node}{}{}",
                if *context { 'c' } else { 's' },
                if *sat { '+' } else { '-' }
            ),
            TraceStep::Instance { node, tuple } => {
                tuples.push((*node, tuple.iter().map(|&t| exec.format_term(t)).collect()));
                format!("I{node}")
            }
            TraceStep::Exact { node } => format!("X{node}"),
        });
    }
    Traced { run, steps, tuples }
}

fn assert_steps(name: &str, traced: &Traced, expected: &[&str]) {
    assert_eq!(
        traced.steps, expected,
        "{name}: trace (tuples {:?})",
        traced.tuples
    );
}

/// Example 10: `∀x. ¬(∀y. x > y ∨ 0 > y) ∨ x < 0` is SAT. The inner
/// universal is refined standalone once; its frozen instance makes the outer
/// counterexample query unsatisfiable on the second round.
#[test]
fn example_10_trace() {
    let traced = trace(
        "(set-logic LRA)(assert (forall ((x Real)) \
         (or (not (forall ((y Real)) (or (> x y) (> 0 y)))) (< x 0))))(check-sat)",
    );
    assert!(
        matches!(traced.run.outcome, QlraOutcome::Sat),
        "{:?}",
        traced.run.outcome
    );
    assert_steps("ex10", &traced, &["M+", "C0c+", "C1s+", "I1", "C0c-"]);
}

/// Example 11: `∀x. ¬(∀y. x > y) ∨ ¬(∀z. z < x)` is SAT, decided without
/// ever looking at the second inner universal (node 2).
#[test]
fn example_11_trace_never_visits_the_second_child() {
    let traced = trace(
        "(set-logic LRA)(assert (forall ((x Real)) \
         (or (not (forall ((y Real)) (> x y))) (not (forall ((z Real)) (< z x))))))(check-sat)",
    );
    assert!(
        matches!(traced.run.outcome, QlraOutcome::Sat),
        "{:?}",
        traced.run.outcome
    );
    assert_steps("ex11", &traced, &["M+", "C0c+", "C1s+", "I1", "C0c-"]);
    assert!(
        !traced.steps.iter().any(|s| s.starts_with("C2")),
        "node 2 is irrelevant"
    );
}

/// Example 12: `∀x y. ¬(∀z. z < x ∨ y < z) ∨ x < y + 5` is UNSAT. The inner
/// universal becomes exact (`⌊A3⌋ ⟺ x > y`) from a STANDALONE unsat, then
/// the outer instance `(6, 0)` refutes the main query.
#[test]
fn example_12_trace() {
    let traced = trace(
        "(set-logic LRA)(assert (forall ((x Real) (y Real)) \
         (or (not (forall ((z Real)) (or (< z x) (< y z)))) (< x (+ y 5)))))(check-sat)",
    );
    assert!(
        matches!(traced.run.outcome, QlraOutcome::Unsat),
        "{:?}",
        traced.run.outcome
    );
    assert_steps(
        "ex12",
        &traced,
        &["M+", "C0c+", "C1s+", "I1", "C0c+", "C1s-", "X1", "I0", "M-"],
    );
    let outer = traced
        .tuples
        .iter()
        .find(|(node, _)| *node == 0)
        .expect("outer instance");
    assert_eq!(outer.1, vec!["6.0".to_string(), "0.0".to_string()]);
}

/// An inner universal of the SAME effective kind as its parent
/// (`∀x. x > 0 ∨ ∀z. z < x`, UNSAT at x = 0) approximates as `⊤` while empty:
/// the parent's counterexample query is then unsat although the parent is
/// false. The parent may rely on that unsat only after the unsafe child is
/// exact.
#[test]
fn unsafe_child_is_made_exact_before_the_parent_is_trusted() {
    let traced = trace(
        "(set-logic LRA)(assert (forall ((x Real)) \
         (or (> x 0) (forall ((z Real)) (< z x)))))(check-sat)",
    );
    assert!(
        matches!(traced.run.outcome, QlraOutcome::Unsat),
        "{:?} {:?}",
        traced.run.outcome,
        traced.steps
    );
    assert_eq!(traced.steps[..3], ["M+", "C0c-", "C1s+"]);
}

/// Exactness only from a CONTEXT-FREE unsat. `∃x ∀y. x > y ∨ y > 5` is true
/// (x = 6), so `p` must be true and the problem is SAT. Under an iff the
/// existential is a both-polarity top node; while it is empty (`⊥`) the main
/// query `(= p ⊥) ∧ p` is UNSAT, so any check run IN that context is unsat
/// too and would freeze the node exact at `⊥` — a wrong UNSAT. The node's
/// standalone check instead finds the witness `x = 6`.
#[test]
fn nested_exactness_comes_from_a_context_free_unsat() {
    let traced = trace(
        "(set-logic LRA)(declare-const p Bool)\
         (assert (= p (exists ((x Real)) (forall ((y Real)) (or (> x y) (> y 5))))))\
         (assert p)(check-sat)",
    );
    assert!(
        matches!(traced.run.outcome, QlraOutcome::Sat),
        "{:?} {:?}",
        traced.run.outcome,
        traced.steps
    );
    assert_eq!(traced.steps[..3], ["M-", "C0s+", "C1s+"]);
    let witness = traced
        .tuples
        .iter()
        .find(|(node, _)| *node == 0)
        .expect("a witness for the existential");
    assert_eq!(witness.1, vec!["6.0".to_string()]);
}

/// A closed quantifier asserted on its own AND nested in another one is ONE
/// node (nodes are shared by term): `∀y. y > a` is false, so the problem is
/// UNSAT. The outer node's standalone recursion logs the shared node's
/// instance MID-ROUND; the round's main query does not contain it, and the
/// shared node's later in-context check (`stale main ∧ ⌊A⌋_new ∧ ¬ψ`) is
/// unsat. Answering Sat from that round was a wrong shadow `sat`; the round
/// must be re-asked, and the fresh main query is unsat.
#[test]
fn a_top_node_that_logs_mid_round_as_a_nested_child_forces_another_round() {
    let traced = trace(
        "(set-logic LRA)(declare-const a Real)\
         (assert (forall ((x Real)) (or (> x 0.0) (<= x 0.0) (forall ((y Real)) (> y a)))))\
         (assert (forall ((y Real)) (> y a)))(check-sat)",
    );
    assert!(
        matches!(traced.run.outcome, QlraOutcome::Unsat),
        "{:?} {:?}",
        traced.run.outcome,
        traced.steps
    );
    assert_steps(
        "shared",
        &traced,
        &[
            "M+", "C0c-", "C1s+", "I1", "C0c-", "C1s-", "X1", "C1c-", "M-",
        ],
    );
}

/// The same scheduling hazard on an ordinary shape: the shared node `Q` is a
/// SAFE child (under `=>`) of the outer universal, and `Q` (false) is also
/// asserted. Found by shape-targeted fuzzing against z3.
#[test]
fn a_shared_safe_child_asserted_at_top_level_is_not_a_wrong_sat() {
    let traced = trace(
        "(set-logic LRA)(declare-fun a () Real)(declare-fun b () Real)\
         (assert (forall ((o3 Real)) (=> (forall ((q1 Real)) (forall ((v2 Real)) \
           (>= (+ (* -2 a) (* (/ 1.0 2.0) v2)) (- 1.0)))) (> (+ b o3) 3.0))))\
         (assert (forall ((q1 Real)) (forall ((v2 Real)) \
           (>= (+ (* -2 a) (* (/ 1.0 2.0) v2)) (- 1.0)))))(check-sat)",
    );
    assert!(
        matches!(traced.run.outcome, QlraOutcome::Unsat),
        "{:?} {:?}",
        traced.run.outcome,
        traced.steps
    );
}

/// A node's UNSAT may be trusted only while its unsafe children are exact
/// AS THEY STOOD AT THE CHECK. Nodes are shared by term, so the closed
/// existential `D = ∃y. y > a` is an unsafe child of the outer node `A`
/// (under `¬`) AND a child of `A`'s other unsafe child `C = ∀z. z > x ∨ D`.
/// `A`'s in-context check is unsat while `⌊D⌋ = ⊥`; the recursion into `C`
/// then logs `D`'s instance, and `D` answers "exact" at once when `A` asks
/// it. Trusting `A`'s stale unsat was a wrong shadow `sat`: `A` is
/// `∀x. x > 0`, so the problem is UNSAT. `A` must be asked again.
#[test]
fn an_unsafe_child_grown_through_a_sibling_voids_the_parents_unsat() {
    let traced = trace(
        "(set-logic LRA)(declare-fun a () Real)\
         (assert (forall ((x Real)) (and (forall ((z Real)) (or (> z x) (exists ((y Real)) (> y a)))) \
           (or (> x 0.0) (not (exists ((y Real)) (> y a)))))))(check-sat)",
    );
    assert!(
        matches!(traced.run.outcome, QlraOutcome::Unsat),
        "{:?} {:?}",
        traced.run.outcome,
        traced.steps
    );
    // A = 0, C = 1, D = 2: after `X2` the check `C0c` is asked again.
    assert_steps(
        "stale-sat",
        &traced,
        &[
            "M+", "C0c-", "C1s+", "C2s+", "I2", "C1s-", "X1", "C2s-", "X2", "C0c+", "I0", "M-",
        ],
    );
}

/// The same staleness one level down makes a NESTED node wrongly exact (its
/// standalone unsat used `⌊D⌋ = ⊥`), so the outer universal's frozen
/// instance is too strong: a wrong shadow `unsat` on a SAT problem (the
/// nested universal is `∀x. x > 0`, false, so the outer body holds).
#[test]
fn an_unsafe_child_grown_through_a_sibling_voids_a_nested_exact_flag() {
    let traced = trace(
        "(set-logic LRA)(declare-fun a () Real)(declare-fun b () Real)\
         (assert (forall ((w Real)) (or (not (forall ((x Real)) (and (forall ((z Real)) \
           (or (> z x) (exists ((y Real)) (> y a)))) (or (> x 0.0) (not (exists ((y Real)) (> y a))))))) \
           (> w b))))(check-sat)",
    );
    assert!(
        matches!(traced.run.outcome, QlraOutcome::Sat),
        "{:?} {:?}",
        traced.run.outcome,
        traced.steps
    );
    // Node 1 is the nested `∀x`: after `X3` it is asked again standalone,
    // finds its counterexample and logs, instead of a wrong `X1`.
    assert_steps(
        "stale-exact",
        &traced,
        &[
            "M+", "C0c+", "C1s-", "C2s+", "C3s+", "I3", "C2s-", "X2", "C3s-", "X3", "C1s+", "I1",
            "C0c-",
        ],
    );
}

/// The main query's UNSAT refutes the roots only while every
/// both-polarity top node is exact AS IT STOOD IN THAT QUERY. Under
/// `p ⟺ B1`, `q ⟺ B2`, `p ⟺ q`, both `B1 = ∀x. x > 0 ∨ B2` and
/// `B2 = ∃y. y > a` are both-polarity top nodes, and `B2` is also nested in
/// `B1`. Both are true, so the problem is SAT; the first main query
/// (`p ⟺ ⊤`, `q ⟺ ⊥`, `p ⟺ q`) is unsat. Making `B1` exact logs
/// `B2`'s witness through the recursion, after which `B2` answers "exact"
/// at once; trusting the stale main unsat was a wrong shadow `unsat`.
#[test]
fn a_both_polarity_top_node_grown_after_the_main_unsat_forces_another_round() {
    let traced = trace(
        "(set-logic LRA)(declare-fun a () Real)\
         (declare-const p Bool)(declare-const q Bool)\
         (assert (= p (forall ((x Real)) (or (> x 0.0) (exists ((y Real)) (> y a))))))\
         (assert (= q (exists ((y Real)) (> y a))))(assert (= p q))(check-sat)",
    );
    assert!(
        matches!(traced.run.outcome, QlraOutcome::Sat),
        "{:?} {:?}",
        traced.run.outcome,
        traced.steps
    );
    // `B1` = 0, `B2` = 1: the main query is asked again after `X1`.
    assert_steps(
        "stale-main",
        &traced,
        &[
            "M-", "C0s+", "C1s+", "I1", "C0s-", "X0", "C1s-", "X1", "M+", "C0c-", "C1c-",
        ],
    );
}

/// Build the executor, tree and host for a cap/interrupt run.
fn run_with(smt: &str, caps: NestedCaps, budget: Duration) -> NestedRun {
    let commands: Vec<Command> = parse(smt)
        .expect("parse")
        .into_iter()
        .filter(|c| !matches!(c, Command::CheckSat))
        .collect();
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("execute");
    let roots: Vec<TermId> = exec.ctx.assertions.clone();
    let tree = build_nested_tree(&mut exec.ctx.terms, &roots).expect("nested tree");
    let deadline = Instant::now() + budget;
    let mut host = ExecutorQlraHost::with_route(&mut exec, deadline, OracleRoute::DirectQfLra);
    solve_nested_with(&mut host, &tree, caps)
}

const EXAMPLE_12: &str = "(set-logic LRA)(assert (forall ((x Real) (y Real)) \
     (or (not (forall ((z Real)) (or (< z x) (< y z)))) (< x (+ y 5)))))(check-sat)";

/// Every cap declines — never a truncated verdict.
#[test]
fn caps_decline_instead_of_answering() {
    let tight = |caps: NestedCaps| run_with(EXAMPLE_12, caps, Duration::from_secs(30)).outcome;
    let base = NestedCaps::default();
    for (caps, label) in [
        (
            NestedCaps {
                instances: 1,
                ..base
            },
            "cap-instances",
        ),
        (
            NestedCaps {
                instances_per_node: 0,
                ..base
            },
            "cap-instances-per-node",
        ),
        (NestedCaps { rounds: 1, ..base }, "cap-rounds"),
    ] {
        let outcome = tight(caps);
        assert!(
            matches!(outcome, QlraOutcome::Decline(QlraDecline::Cap(which)) if which == label),
            "{label}: {outcome:?}"
        );
    }
    assert!(matches!(tight(base), QlraOutcome::Unsat));
}

/// An expired deadline (or interrupt) declines before any verdict.
#[test]
fn an_expired_deadline_declines() {
    let outcome = run_with(EXAMPLE_12, NestedCaps::default(), Duration::ZERO).outcome;
    assert!(
        matches!(outcome, QlraOutcome::Decline(QlraDecline::Timeout)),
        "{outcome:?}"
    );
}
