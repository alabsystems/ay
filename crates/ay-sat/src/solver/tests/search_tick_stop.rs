// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The caller's search-tick stop (`Solver::set_search_tick_stop`, GT-G6 item
//! 2 in the development design notes DR-36): it ends a search as `ResourceBudget` at a
//! count, and unset it changes nothing. Where it meets the parked
//! independent-support enumeration's head start is tested beside that
//! enumeration (`indep_enum/tests/tick_stop.rs`).

use super::*;

/// `pigeons` pigeons in one fewer holes, on the counted schedules: unsat, and
/// the search needs conflicts.
fn pigeonhole(pigeons: u32) -> Solver {
    let holes = pigeons - 1;
    let var = |pigeon: u32, hole: u32| Variable(pigeon * holes + hole);
    let mut solver = Solver::new((pigeons * holes) as usize);
    for pigeon in 0..pigeons {
        solver.add_clause(
            (0..holes)
                .map(|hole| Literal::positive(var(pigeon, hole)))
                .collect(),
        );
    }
    for hole in 0..holes {
        for first in 0..pigeons {
            for second in first + 1..pigeons {
                solver.add_clause(vec![
                    Literal::negative(var(first, hole)),
                    Literal::negative(var(second, hole)),
                ]);
            }
        }
    }
    solver.set_deterministic_inproc(true);
    solver
}

/// Where one solve ended: its verdict, its reason, and its search ticks,
/// conflicts and decisions.
type End = (&'static str, Option<SatUnknownReason>, u64, u64, u64);

fn solve_to_end(solver: &mut Solver) -> End {
    let verdict = match solver.solve().into_inner() {
        SatResult::Sat(_) => "sat",
        SatResult::Unsat(_) => "unsat",
        SatResult::Unknown => "unknown",
    };
    (
        verdict,
        solver.last_unknown_reason(),
        solver.total_search_ticks(),
        solver.num_conflicts(),
        solver.num_decisions(),
    )
}

const PIGEONS: u32 = 9;

/// A caller's stop ends the search as `ResourceBudget` once the search ticks
/// reach it, at the same count on every run of the same formula.
#[test]
fn a_caller_stop_ends_the_search_at_a_count() {
    let whole = solve_to_end(&mut pigeonhole(PIGEONS));
    assert_eq!(whole.0, "unsat", "{whole:?}");
    let stop = whole.2 / 4;
    assert!(stop > 0, "the search spent ticks: {whole:?}");

    let stopped = || {
        let mut solver = pigeonhole(PIGEONS);
        solver.set_search_tick_stop(Some(stop));
        solve_to_end(&mut solver)
    };
    let first = stopped();
    assert_eq!(
        (first.0, first.1),
        ("unknown", Some(SatUnknownReason::ResourceBudget)),
        "{first:?}"
    );
    assert!(
        first.2 >= stop && first.2 < whole.2,
        "stopped at {} ticks for a stop at {stop} (the whole search: {})",
        first.2,
        whole.2
    );
    assert_eq!(first, stopped(), "the same formula stops at the same count");
}

/// With no stop, or a cleared one, or one the search never reaches, the
/// search runs exactly as it did before the stop existed.
#[test]
fn an_unset_stop_changes_nothing() {
    let untouched = solve_to_end(&mut pigeonhole(PIGEONS));
    assert_eq!(untouched.0, "unsat", "{untouched:?}");

    let mut cleared = pigeonhole(PIGEONS);
    cleared.set_search_tick_stop(Some(1));
    cleared.set_search_tick_stop(None);
    assert_eq!(solve_to_end(&mut cleared), untouched);

    let mut unreached = pigeonhole(PIGEONS);
    unreached.set_search_tick_stop(Some(u64::MAX));
    assert_eq!(solve_to_end(&mut unreached), untouched);
}
