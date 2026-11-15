// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! A ground problem solved again after every instance batch.
//!
//! The quantifier loop re-solves the ground problem each time E-matching adds
//! a batch of instances, and each re-solve starts in a new incremental state:
//! new SAT solver, new encoding. The lazy split loop finds a theory-consistent
//! assignment one theory conflict per round, so every re-solve used to pay for
//! the conflicts of the solve before it again. On the program-verification
//! queries this was reduced from, a re-solve that added three atoms took as
//! many rounds as the first solve, and no answer came in 60 CPU seconds where
//! z3 needs 0.03.
//!
//! The query below has that shape in small. Each of `VALUES` values is compared
//! with a bound twice: once as written, once through a box/unbox round trip
//! that only an axiom instance equates with it. A cold lazy solve needs one
//! round per value to learn that the two comparisons agree. A chain axiom puts
//! the refutation `LINKS` links away, so the instances arrive in batches and
//! the ground problem is solved once per batch. (Its pattern asks for the
//! ground term `(g x)` too, which stops the chain at the goal's last link.)
//!
//! The solves now hand their theory conflicts and their last assignment to the
//! next one (`ground_solve_carry`), so only the first pays.
//!
//! The query is AUFLIA. Written with a Real symbol in its signature (as the
//! carry's first fixture was) it takes the AUFLIRA route, which since
//! DR-stalls-6/7 (012e207c0, landed by f4d1b5de9) reads its window over the
//! representatives of its root congruence classes when no proof is published:
//! the instance `(= (h vi) (unbox (box (h vi))))` makes the two comparisons
//! one atom, no solve meets a theory conflict, and the carry has nothing to
//! carry (`the_auflira_spelling_pays_no_round_per_value` pins that).

use std::time::Duration;

use ntest::timeout;

/// Values compared with a bound in two spellings.
const VALUES: usize = 12;
/// Links of the chain between the asserted fact and the goal.
const LINKS: usize = 20;

/// The query; `goal` is its last assertion.
fn query(goal: &str) -> String {
    let mut smt = declarations_and_facts();
    smt.push_str(goal);
    smt.push_str("\n(check-sat)\n");
    smt
}

/// One session that decides each of `goals` in its own `push`/`pop` scope
/// over the same declarations and facts.
fn session(goals: &[String]) -> String {
    let mut smt = declarations_and_facts();
    for goal in goals {
        smt.push_str(&format!("(push 1)\n{goal}\n(check-sat)\n(pop 1)\n"));
    }
    smt
}

/// Everything but the goal.
fn declarations_and_facts() -> String {
    let mut smt = String::from(
        r#"
        (declare-sort Box 0)
        (declare-fun box (Int) Box)
        (declare-fun unbox (Box) Int)
        (declare-fun h (Int) Int)
        (declare-fun g (Int) Int)
        (declare-fun p (Int) Bool)
        (assert (forall ((x Int)) (! (= x (unbox (box x))) :pattern ((box x)))))
        (assert (forall ((x Int)) (! (=> (p x) (p (g x))) :pattern ((p x) (g x)))))
        (declare-const t Int)
        (assert (p t))
        "#,
    );
    for i in 0..VALUES {
        smt.push_str(&format!(
            "(declare-const v{i} Int)\n\
             (declare-const c{i} Int)\n\
             (declare-const w{i} Bool)\n\
             (assert (< (h v{i}) c{i}))\n\
             (assert (or (not (< (unbox (box (h v{i}))) c{i})) w{i}))\n"
        ));
    }
    smt
}

/// `(g (g ... t))`, `LINKS` deep.
fn end_of_chain() -> String {
    let mut term = String::from("t");
    for _ in 0..LINKS {
        term = format!("(g {term})");
    }
    term
}

/// The chain axiom reaches `p` of the last link, so denying it is refuted.
fn refuted_goal() -> String {
    format!("(assert (not (p {})))", end_of_chain())
}

struct Outcome {
    outputs: Vec<String>,
    round_trips: u64,
    carried: u64,
    replayed: u64,
}

/// Solve `smt`. `shed_proofs` selects the posture a verifier's z3-compatible
/// session runs in: no proof trace is recorded during the search. `budget`
/// bounds the solve; a query that runs into it answers `unknown`.
fn run(smt: &str, shed_proofs: bool, budget: Option<Duration>) -> Outcome {
    let commands = ay_frontend::parse(smt).expect("valid SMT-LIB input");
    let mut exec = ay_dpll::Executor::new();
    exec.set_competition_mode(shed_proofs);
    exec.set_timeout(budget);
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    let stats = exec.statistics();
    let stat = |key: &str| stats.get_int(key).unwrap_or(0);
    Outcome {
        outputs,
        round_trips: stat("all_lanes.round_trips"),
        carried: stat("split_loop.carried_conflicts"),
        replayed: stat("split_loop.carried_conflict_replays"),
    }
}

/// `smt` with a Real symbol in its signature, which routes it to AUFLIRA.
fn with_real_symbol(smt: &str) -> String {
    format!("(declare-fun r (Real) Real)\n{smt}")
}

/// The goal the chain never reaches: `p` of a term off the chain.
fn off_chain_goal() -> String {
    format!("(assert (not (p (h {}))))", end_of_chain())
}

/// z3: unsat. Each of the ground solves used to take a round per value; now
/// the first one does and the later ones start from its conflicts.
#[test]
#[timeout(120_000)]
fn a_re_solve_does_not_pay_for_the_conflicts_of_the_solve_before() {
    let outcome = run(&query(&refuted_goal()), true, None);
    assert_eq!(outcome.outputs, vec!["unsat"]);
    assert!(
        outcome.carried >= VALUES as u64,
        "{} conflicts carried, expected one per value ({VALUES})",
        outcome.carried
    );
    assert!(
        outcome.replayed >= VALUES as u64,
        "{} conflict clauses replayed: no later solve took them",
        outcome.replayed
    );
    // A cold solve is about `VALUES` rounds, and only the first solve starts
    // cold; two more follow. Paying for each again is more than three times
    // `VALUES` (44 round trips with the carry off, 20 with it, on fd4e00f75).
    let bound = 3 * VALUES as u64;
    assert!(
        outcome.round_trips <= bound,
        "{} DPLL(T) round trips, bound {bound}: the re-solves started cold",
        outcome.round_trips
    );
}

/// The same query in the AUFLIRA spelling pays no round per value in any of
/// its solves: the window is read over its root congruence classes, so the
/// two comparisons of a value are one atom (DR-stalls-6), and no solve has a
/// theory conflict to hand over (11 round trips on fd4e00f75). Before that
/// rewrite every solve paid: 39 round trips with the carry (b12ea8a0f, and
/// fd4e00f75 with the rewrite bypassed), 75 without it (9690cc622's count).
#[test]
#[timeout(120_000)]
fn the_auflira_spelling_pays_no_round_per_value() {
    let outcome = run(&with_real_symbol(&query(&refuted_goal())), true, None);
    assert_eq!(outcome.outputs, vec!["unsat"]);
    let bound = 2 * VALUES as u64;
    assert!(
        outcome.round_trips <= bound,
        "{} DPLL(T) round trips, bound {bound}: a solve paid a round per value",
        outcome.round_trips
    );
}

/// The twin differs in one line: its goal denies `p` of a term the chain
/// never reaches. It has a model (`p` true exactly on the chain), so the
/// conflicts its solves hand to each other must not refute it (z3 with MBQI
/// off: unknown). The budget ends the unknown retries a satisfiable query
/// goes through; the solves that replay conflicts come first.
#[test]
#[timeout(120_000)]
fn the_twin_whose_goal_is_off_the_chain_is_not_refuted() {
    let twin_goal = off_chain_goal();
    assert_ne!(twin_goal, refuted_goal());
    let outcome = run(&query(&twin_goal), true, Some(Duration::from_secs(20)));
    assert_eq!(outcome.outputs.len(), 1);
    assert_ne!(outcome.outputs[0], "unsat", "the twin is satisfiable");
    assert!(
        outcome.replayed > 0,
        "the twin's solves handed nothing over: it does not test the replay"
    );
}

/// A proof-tracked solve records where every clause came from, so nothing is
/// handed over there: the answer is the same and the store stays empty.
#[test]
#[timeout(120_000)]
fn a_proof_tracked_solve_carries_nothing() {
    let outcome = run(&query(&refuted_goal()), false, None);
    assert_eq!(outcome.outputs, vec!["unsat"]);
    assert_eq!(outcome.carried, 0);
    assert_eq!(outcome.replayed, 0);
}

/// The store serves one `check-sat`: a session that refutes the chain goal,
/// then asks the off-chain twin in another `push`/`pop` scope, then the chain
/// goal again, answers each as a fresh solver would. Nothing the first scope
/// learned (its conflicts, its last assignment) reaches the second, and the
/// twin's answer is not refuted by anything handed over (z3: unsat, then
/// unknown with MBQI off, then unsat).
#[test]
#[timeout(180_000)]
fn each_check_sat_of_a_session_starts_with_nothing_carried() {
    let goals = [refuted_goal(), off_chain_goal(), refuted_goal()];
    let outcome = run(&session(&goals), true, Some(Duration::from_secs(20)));
    assert_eq!(outcome.outputs.len(), 3, "{:?}", outcome.outputs);
    assert_eq!(outcome.outputs[0], "unsat");
    assert_ne!(outcome.outputs[1], "unsat", "the twin is satisfiable");
    assert_eq!(outcome.outputs[2], "unsat");
}
