// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Memory bound for E-matching on a multi-recursive definition.
//!
//! `fib` defined by a patterned universal, seeded with the symbolic calls
//! `fib(n)`, `fib(n-1)`, `fib(n-2)`, once minted `fib(n-1-1)`, `fib(n-1-2)`,
//! ... with no folding of the nested offsets, so the instances doubled every
//! round (2,028 instances, 4,065 `fib` applications). Eager BV congruence
//! then expanded all 8 million application pairs into CNF before search and
//! the process grew past 65 GB. z3 answers `unsat` on the concrete goal
//! after a handful of instances.
//!
//! Now `(x - c1) - c2` is built as `x - (c1 + c2)`, so a symbolic seed
//! unfolds linearly, and the congruence expansion stops at a clause budget
//! with a SAT degraded to `unknown`.

use ntest::timeout;
use std::time::{Duration, Instant};

const FIB_DEF: &str = r#"
    (set-logic ALL)
    (declare-const n (_ BitVec 32))
    (declare-fun fib ((_ BitVec 32)) (_ BitVec 32))
    (assert (forall ((x (_ BitVec 32)))
        (! (ite (= x #x00000000) (= (fib x) #x00000000)
             (ite (= x #x00000001) (= (fib x) #x00000001)
               (= (fib x) (bvadd (fib (bvsub x #x00000001)) (fib (bvsub x #x00000002))))))
           :pattern ((fib x)))))
    (assert (= (fib n) (bvadd (fib (bvsub n #x00000001)) (fib (bvsub n #x00000002)))))
"#;

/// Upper bound on E-matching instances for the queries below; the unfolded
/// runaway created 2,028 before its congruence expansion took the machine.
const MAX_INSTANCES: u64 = 400;

/// Wall-clock bound for each query. The `#[timeout]` above each test is a
/// backstop far past it.
const MAX_WALL: Duration = Duration::from_secs(30);

fn run(extra: &str) -> (Vec<String>, u64, Duration) {
    let smt = format!("{FIB_DEF}{extra}(check-sat)\n");
    let commands = ay_frontend::parse(&smt).expect("valid SMT-LIB input");
    let mut exec = ay_dpll::Executor::new();
    let started = Instant::now();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    let elapsed = started.elapsed();
    let instances = exec
        .statistics()
        .get_int("ematching_instances_created")
        .unwrap_or(0);
    (outputs, instances, elapsed)
}

/// The symbolic seed alone: satisfiable (the real Fibonacci function mod
/// 2^32 is a model) but not decided by E-matching, so `unknown`, reached
/// quickly with few instances. z3 does not finish on it either.
#[test]
#[timeout(120_000)]
fn fib_symbolic_seed_is_bounded_and_not_unsat() {
    let (outputs, instances, elapsed) = run("");
    assert_ne!(outputs, vec!["unsat"], "the formula is satisfiable");
    assert!(
        instances <= MAX_INSTANCES,
        "{instances} E-matching instances, bound {MAX_INSTANCES}"
    );
    assert!(elapsed <= MAX_WALL, "took {elapsed:?}, bound {MAX_WALL:?}");
}

/// The concrete goal z3 refutes: `fib(5) = 5` holds, so its negation is
/// UNSAT.
#[test]
#[timeout(120_000)]
fn fib_five_is_five_unsat_and_bounded() {
    let (outputs, instances, elapsed) = run("(assert (not (= (fib #x00000005) #x00000005)))\n");
    assert_eq!(outputs, vec!["unsat"]);
    assert!(
        instances <= MAX_INSTANCES,
        "{instances} E-matching instances, bound {MAX_INSTANCES}"
    );
    assert!(elapsed <= MAX_WALL, "took {elapsed:?}, bound {MAX_WALL:?}");
}

/// Refuted twin: `fib(5) = 6` is false, so asserting its negation must not
/// be UNSAT.
#[test]
#[timeout(120_000)]
fn fib_five_is_six_not_unsat() {
    let (outputs, _, elapsed) = run("(assert (not (= (fib #x00000005) #x00000006)))\n");
    assert_ne!(outputs, vec!["unsat"], "fib(5) = 6 is false");
    assert!(elapsed <= MAX_WALL, "took {elapsed:?}, bound {MAX_WALL:?}");
}
