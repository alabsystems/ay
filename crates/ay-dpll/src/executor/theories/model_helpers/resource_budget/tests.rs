// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! P4a: the allowances a bit-blast solve chain runs under, and how a solve
//! is armed with them (the host-speed tests are in `host_tests.rs`).

use ay_sat::{Literal as SatLiteral, Variable as SatVariable};

use super::*;

const GROUND_DECISIONS: u64 = Executor::DEFAULT_GROUND_DECISION_ALLOWANCE;

#[test]
fn rlimit_carries_a_decision_allowance_beside_its_conflicts() {
    // The ground pipeline's decision allowance rides with an explicit :rlimit.
    assert_eq!(
        BitblastAllowances::for_limits(Some(100_000), None, true),
        BitblastAllowances {
            conflicts: Some(100_000),
            decisions: Some(GROUND_DECISIONS),
        }
    );
    // An explicit decision limit wins, as in `effective_decision_allowance`.
    assert_eq!(
        BitblastAllowances::for_limits(Some(100_000), Some(9), true),
        BitblastAllowances {
            conflicts: Some(100_000),
            decisions: Some(9),
        }
    );
    // Ground budget off and no decision limit: the ground ratio of the
    // :rlimit, never no decision bound at all.
    assert_eq!(
        BitblastAllowances::for_limits(Some(100_000), None, false),
        BitblastAllowances {
            conflicts: Some(100_000),
            decisions: Some(100_000 * DECISIONS_PER_CONFLICT),
        }
    );
    assert_eq!(
        BitblastAllowances::for_limits(Some(u64::MAX), None, false).decisions,
        Some(u64::MAX),
        "the ratio saturates"
    );
}

#[test]
fn without_rlimit_only_an_explicit_decision_limit_applies() {
    // The default ground allowances are deliberately not applied to
    // bit-blasting: that is the pre-P4a behaviour without :rlimit.
    assert_eq!(
        BitblastAllowances::for_limits(None, None, true),
        BitblastAllowances {
            conflicts: None,
            decisions: None,
        }
    );
    assert_eq!(
        BitblastAllowances::for_limits(None, Some(7), true),
        BitblastAllowances {
            conflicts: None,
            decisions: Some(7),
        }
    );
}

#[test]
fn arming_grants_what_the_chain_has_left_and_clears_without_a_budget() {
    let allowances = BitblastAllowances {
        conflicts: Some(10),
        decisions: Some(100),
    };
    let mut solver = SatSolver::new(4);
    allowances.arm(
        &mut solver,
        ChainSpend {
            conflicts: 3,
            decisions: 40,
        },
    );
    assert_eq!(solver.conflict_budget(), Some(7));
    assert_eq!(solver.decision_budget(), Some(60));
    assert!(
        solver.deterministic_inproc(),
        "a bounded solve runs ay-sat's counted schedules"
    );
    // An overspent chain arms a zero remainder, never "unlimited".
    allowances.arm(
        &mut solver,
        ChainSpend {
            conflicts: 30,
            decisions: 400,
        },
    );
    assert_eq!(solver.conflict_budget(), Some(0));
    assert_eq!(solver.decision_budget(), Some(0));
    // No budget clears what an earlier arming left, the counted schedules
    // included: the solver goes back to the process-wide setting.
    let unbounded = BitblastAllowances {
        conflicts: None,
        decisions: None,
    };
    assert!(!unbounded.bounded());
    unbounded.arm(&mut solver, ChainSpend::NONE);
    assert_eq!(solver.conflict_budget(), None);
    assert_eq!(solver.decision_budget(), None);
    assert_eq!(
        solver.deterministic_inproc(),
        ay_sat::deterministic_inproc_enabled()
    );
    // A decision limit alone is a count too.
    BitblastAllowances {
        conflicts: None,
        decisions: Some(5),
    }
    .arm(&mut solver, ChainSpend::NONE);
    assert!(solver.deterministic_inproc());
}

/// The pigeonhole principle for `holes + 1` pigeons, unsatisfiable: no probe
/// settles it, and CDCL needs far more than a few hundred conflicts.
fn pigeonhole(holes: u32) -> SatSolver {
    let pigeons = holes + 1;
    let var = |pigeon: u32, hole: u32| SatVariable::new(pigeon * holes + hole);
    let mut solver = SatSolver::new((pigeons * holes) as usize);
    // As the BV lanes configure theirs: no preprocessing or inprocessing,
    // whose conflicts the budget does not check, so a solve stops exactly at
    // its target.
    solver.set_preprocess_enabled(false);
    solver.disable_all_inprocessing();
    for pigeon in 0..pigeons {
        solver.add_clause(
            (0..holes)
                .map(|hole| SatLiteral::positive(var(pigeon, hole)))
                .collect(),
        );
    }
    for hole in 0..holes {
        for first in 0..pigeons {
            for second in first + 1..pigeons {
                solver.add_clause(vec![
                    SatLiteral::negative(var(first, hole)),
                    SatLiteral::negative(var(second, hole)),
                ]);
            }
        }
    }
    solver
}

#[test]
fn a_reused_solver_gets_the_remainder_on_every_solve_not_its_last_count_again() {
    // ay-sat zeroes its counters when a solve starts. A target of "count so
    // far + remainder" therefore granted a reused solver its previous solve's
    // work again on top of the allowance: 200, then 400, then 800 conflicts
    // under one allowance of 200.
    let allowances = BitblastAllowances {
        conflicts: Some(200),
        decisions: Some(1_000_000),
    };
    let mut solver = pigeonhole(9);
    for solve in 0..4 {
        allowances.arm(&mut solver, ChainSpend::NONE);
        assert_eq!(solver.conflict_budget(), Some(200), "solve {solve}");
        let result = solver.solve().into_inner();
        // Non-vacuity: the instance outlasts four allowances, so every solve
        // ends on its count, and a reused solver's extra grant would show.
        assert!(
            matches!(result, SatResult::Unknown)
                && solver.last_unknown_reason() == Some(ay_sat::SatUnknownReason::ResourceBudget),
            "solve {solve} ended on its count"
        );
        assert_eq!(
            solver.num_conflicts(),
            200,
            "solve {solve} spent its allowance, no more"
        );
    }
    // A chain of solves on one solver debits each solve once and arms what is
    // left: 200, then the other 300 of an allowance of 500.
    let chain = BitblastAllowances {
        conflicts: Some(500),
        decisions: None,
    };
    let mut spent = ChainSpend::NONE;
    let mut solver = pigeonhole(9);
    for (solve, remainder) in [(0, 200), (1, 300)] {
        if solve == 0 {
            BitblastAllowances {
                conflicts: Some(200),
                decisions: None,
            }
            .arm(&mut solver, spent);
        } else {
            chain.arm(&mut solver, spent);
        }
        assert_eq!(solver.conflict_budget(), Some(remainder));
        assert!(matches!(solver.solve().into_inner(), SatResult::Unknown));
        assert_eq!(solver.num_conflicts(), remainder);
        spent.debit(&solver);
    }
    assert_eq!(spent.conflicts, 500);
}

#[test]
fn a_chain_debits_every_solvers_conflicts_and_decisions() {
    let mut spent = ChainSpend::NONE;
    let mut solver = SatSolver::new(2);
    let a = SatLiteral::positive(SatVariable::new(0));
    let b = SatLiteral::positive(SatVariable::new(1));
    solver.add_clause(vec![a, b]);
    assert!(matches!(solver.solve().into_inner(), SatResult::Sat(_)));
    let (conflicts, decisions) = (solver.num_conflicts(), solver.num_decisions());
    spent.debit(&solver);
    spent.debit(&solver);
    assert_eq!(
        spent,
        ChainSpend {
            conflicts: 2 * conflicts,
            decisions: 2 * decisions,
        }
    );
}
