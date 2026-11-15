// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sweep's limits: a call stops within one probe of its tick budget, a
//! raised stop ends it before its next environment or probe, and the
//! debug-build oracle stops at its own tick limit.

use super::*;
use crate::test_util::lit;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

/// The FP lane's CNF for a Float(2,3) division miter, reduced to the cone the
/// first environments see (`tests/data/fp_div_miter_cone.cnf`): two division
/// circuits over equal divisors, whose gates sweep proves equivalent.
fn fp_division_miter() -> (ClauseArena, usize) {
    let path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/fp_div_miter_cone.cnf");
    let text = std::fs::read_to_string(&path).expect("read fp_div_miter_cone.cnf");
    let formula = crate::parse_dimacs(&text).expect("parse fp_div_miter_cone.cnf");
    let num_vars = crate::dimacs::max_variable_count(&formula.clauses);
    let mut clauses = ClauseArena::new();
    for clause in &formula.clauses {
        clauses.add(clause, false);
    }
    (clauses, num_vars)
}

/// One `sweep_with_kitten` call with nothing assigned or frozen, and the
/// kitten ticks it spent.
fn sweep(
    sweeper: &mut Sweeper,
    clauses: &ClauseArena,
    num_vars: usize,
    budget: u64,
) -> (SweepOutcome, u64) {
    let vals = vec![0i8; num_vars * 2];
    let frozen = vec![0u32; num_vars];
    let start = sweeper.kitten.current_ticks();
    let outcome = sweeper.sweep_with_kitten(clauses, &vals, &frozen, budget);
    (outcome, sweeper.kitten.current_ticks() - start)
}

/// Ticks one probe pair may spend once the budget is crossed: two solves,
/// each ending at its first free decision after propagating the environment
/// (well under a hundred clauses here) and its assumptions.
const ONE_PROBE_TICKS: u64 = 1_000;

/// Each budget runs out while an environment is being probed. A kitten solve
/// stops only at its next free decision, so before the probes checked the
/// budget the environment's remaining probes all ran, each re-propagating
/// it: 2,013 to 2,286 ticks past these budgets on a51b675.
#[test]
fn a_sweep_call_stops_within_one_probe_of_its_tick_budget() {
    let (clauses, num_vars) = fp_division_miter();
    for budget in [1_500u64, 2_000, 3_000, 4_000] {
        let mut sweeper = Sweeper::new(num_vars);
        let (_, spent) = sweep(&mut sweeper, &clauses, num_vars, budget);
        assert!(
            spent <= budget + ONE_PROBE_TICKS,
            "budget {budget}: the call spent {spent} kitten ticks"
        );
        assert!(
            sweeper.stats().kitten_equivalences > 0,
            "budget {budget}: the sweep must have probed the miter"
        );
    }
}

/// A raised stop ends the call before its first environment; lowered, the
/// same call proves equivalences.
#[test]
fn a_raised_stop_ends_a_sweep_before_its_first_environment() {
    let (clauses, num_vars) = fp_division_miter();
    let flag = Arc::new(AtomicBool::new(true));
    let mut sweeper = Sweeper::new(num_vars);
    sweeper.set_terminator(Terminator::new(Some(Arc::clone(&flag)), None));
    let (outcome, spent) = sweep(&mut sweeper, &clauses, num_vars, u64::MAX);
    assert_eq!(spent, 0);
    assert_eq!(sweeper.stats().kitten_environments, 0);
    assert!(!outcome.unsat && outcome.lit_map.is_empty() && outcome.new_units.is_empty());

    flag.store(false, std::sync::atomic::Ordering::Relaxed);
    sweeper.set_terminator(Terminator::new(Some(flag), None));
    sweep(&mut sweeper, &clauses, num_vars, 20_000);
    assert!(sweeper.stats().kitten_equivalences > 0);
}

/// Tseitin clauses for `out ↔ a ⊕ b`.
#[cfg(debug_assertions)]
fn xor_gate(clauses: &mut ClauseArena, out: u32, a: u32, b: u32) {
    clauses.add(&[lit(out, false), lit(a, true), lit(b, true)], false);
    clauses.add(&[lit(out, false), lit(a, false), lit(b, false)], false);
    clauses.add(&[lit(out, true), lit(a, false), lit(b, true)], false);
    clauses.add(&[lit(out, true), lit(a, true), lit(b, false)], false);
}

/// The debug-build oracle checks a claim by solving the whole formula, so it
/// must stop at its tick limit: with none it ran for hours on a 334K-clause
/// FP formula (2026-10-02). Here `a ≡ b` needs a decision to refute either
/// direction, and the rest of the formula is PHP(12,11) over variables
/// kitten imports last and so decides first. Bounded, the oracle gives up and
/// the claim passes; unbounded, it stays in the pigeonhole instance and the
/// hang detector fails the test.
#[cfg(debug_assertions)]
#[test]
fn the_debug_oracle_gives_up_at_its_tick_limit() {
    let mut clauses = ClauseArena::new();
    // a ↔ x ⊕ y, b ↔ x' ⊕ y', x ≡ x', y ≡ y' (variables 0-5).
    xor_gate(&mut clauses, 0, 2, 3);
    xor_gate(&mut clauses, 1, 4, 5);
    for (x, y) in [(2, 4), (3, 5)] {
        clauses.add(&[lit(x, false), lit(y, true)], false);
        clauses.add(&[lit(x, true), lit(y, false)], false);
    }
    let (pigeons, holes) = (12u32, 11u32);
    let hole = |p: u32, h: u32| 6 + p * holes + h;
    for p in 0..pigeons {
        let row: Vec<Literal> = (0..holes).map(|h| lit(hole(p, h), true)).collect();
        clauses.add(&row, false);
    }
    for h in 0..holes {
        for p in 0..pigeons {
            for q in p + 1..pigeons {
                clauses.add(&[lit(hole(p, h), false), lit(hole(q, h), false)], false);
            }
        }
    }
    let num_vars = (6 + pigeons * holes) as usize;

    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let sweeper = Sweeper::new(num_vars);
        let vals = vec![0i8; num_vars * 2];
        let (a, b) = (lit(0, true).0, lit(1, true).0);
        let _ = tx.send(sweeper.debug_verify_equivalence_claim(a, b, &clauses, &vals));
    });
    let accepted = rx
        .recv_timeout(std::time::Duration::from_secs(60))
        .expect("the oracle ran for a minute: it has no tick limit");
    assert!(
        accepted,
        "a stopped oracle solve proves nothing, so the claim passes"
    );
}
