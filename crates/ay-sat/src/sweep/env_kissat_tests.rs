// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--sat-sweep-env-kissat`: Kissat's environment limits, the environment
//! they allow, and an equivalence only that environment holds.

use super::env_kissat::EnvLimits;
use super::*;
use crate::test_util::lit;

/// Auxiliary variables of `gadget`: more than AY's 48-variable environment.
const AUX: u32 = 60;

/// `x1 → x0`, `x0 → a` for each of 60 variables `a`, and
/// `(a_1 ∧ … ∧ a_60) → x1`. So `x0 ≡ x1`, but only an environment that holds
/// x0's 61 clauses and the long clause proves it.
fn gadget() -> (ClauseArena, usize) {
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, false)], false);
    for a in 2..2 + AUX {
        clauses.add(&[lit(0, false), lit(a, true)], false);
    }
    let mut long: Vec<Literal> = (2..2 + AUX).map(|a| lit(a, false)).collect();
    long.push(lit(1, true));
    clauses.add(&long, false);
    (clauses, (2 + AUX) as usize)
}

fn occurrences(clauses: &ClauseArena, num_vars: usize) -> OccList {
    let mut occ = OccList::new_occ_only(num_vars);
    for idx in clauses.indices() {
        occ.add_clause(idx, clauses.literals(idx));
    }
    occ
}

/// Kissat 4.0.4's table (sweep.c:107-137): variables and clauses double and
/// the depth grows by one with every completed pass, up to 8192, 32768 and
/// 3; the shift stops at 32 completed passes.
#[test]
fn kissat_limits_grow_with_completed_passes() {
    let limits = |completed| {
        let env = EnvLimits::kissat(completed);
        (env.vars, env.clauses, env.depth)
    };
    assert_eq!(limits(0), (256, 1024, 2));
    assert_eq!(limits(1), (512, 2048, 3));
    assert_eq!(limits(2), (1024, 4096, 3));
    assert_eq!(limits(3), (2048, 8192, 3));
    assert_eq!(limits(4), (4096, 16_384, 3));
    assert_eq!(limits(5), (8192, 32_768, 3));
    assert_eq!(limits(u64::MAX), (8192, 32_768, 3));
}

/// From x0, AY's environment stops at 48 variables after 47 of x0's
/// clauses. Kissat's first-pass environment takes all 61 of them and, one
/// layer out, the long clause.
#[test]
fn the_kissat_environment_holds_what_the_fixed_one_cuts_off() {
    let (clauses, num_vars) = gadget();
    let vals = vec![0i8; num_vars * 2];
    let occ = occurrences(&clauses, num_vars);
    let mut sweeper = Sweeper::new(num_vars);
    let fixed = sweeper.build_coi(0, &clauses, &occ, &vals);
    sweeper.clear_coi();
    assert_eq!(fixed, 47);
    let kissat = sweeper.build_coi_kissat(0, &clauses, &occ, &vals, EnvLimits::kissat(0));
    assert_eq!(sweeper.coi_vars.len(), num_vars);
    sweeper.clear_coi();
    assert_eq!(kissat, 62);
}

/// The sweep order puts the rank-2 variables (x1 and every `a`) before x0,
/// whose 61 occurrences rank last; x1's environment proves `x0 ≡ x1`, the
/// pass completes, and the next call's limits have grown.
#[test]
fn the_kissat_environment_proves_the_equivalence_and_completes_a_pass() {
    let (clauses, num_vars) = gadget();
    let vals = vec![0i8; num_vars * 2];
    let frozen = vec![0u32; num_vars];
    let occ = occurrences(&clauses, num_vars);
    let mut sweeper = Sweeper::new(num_vars);
    let order = sweeper.kissat_schedule(&occ, &vals, &frozen, EnvLimits::kissat(0));
    assert_eq!(order.first(), Some(&1));
    assert_eq!(order.last(), Some(&0));
    assert_eq!(order.len(), num_vars);

    sweeper.set_env_kissat(true);
    sweeper.set_charge_all_work(true);
    let outcome = sweeper.sweep_with_kitten(&clauses, &vals, &frozen, u64::MAX);
    assert!(!outcome.unsat);
    assert_eq!(outcome.contradiction, None);
    assert_eq!(outcome.new_units.len(), 0, "{:?}", outcome.new_units);
    assert_eq!(
        sweeper.stats.kitten_equivalences, 1,
        "later environments must not prove it again"
    );
    assert_eq!(outcome.lit_map.get(2), Some(&Literal(0)));
    assert_eq!(outcome.lit_map.get(3), Some(&Literal(1)));
    assert_eq!(sweeper.stats.completed_passes, 1);
}
