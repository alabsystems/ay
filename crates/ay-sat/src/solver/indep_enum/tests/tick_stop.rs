// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A caller's search-tick stop (`Solver::set_search_tick_stop`, GT-G6 item 2
//! in the development design notes DR-36) on a formula the parked enumeration is
//! admitted on, under the counted schedule: the head start sets and clears
//! its own tick stop, never the caller's, and does not read the caller's as
//! its own end.
//!
//! The solve budget is 9 ms. Its head start, 0.9 ms, is 0 whole milliseconds
//! and so 0 ticks: the head start is over at the first conflict of search.
//! Its slice is 4 ms of visits, which on this formula is spent without a
//! model, and search resumes and finds one.

use super::*;

/// What one counted solve of the 16-round, 32-input `mini_prng` did.
#[derive(Debug)]
struct Run {
    sat: bool,
    reason: Option<SatUnknownReason>,
    ticks: u64,
    blocks: u64,
}

fn counted_run(stop: Option<u64>) -> Run {
    let (num_vars, clauses, _) = mini_prng(32, 16, 0xDEAD_BEEF);
    let mut s = solver_from(num_vars, &clauses);
    s.set_deterministic_inproc(true);
    s.set_solve_budget_ms(Some(9));
    s.set_search_tick_stop(stop);
    let sat = s.solve().is_sat();
    assert_eq!(s.stats.indep_enum_admitted, 1, "the gate must admit");
    Run {
        sat,
        reason: s.last_unknown_reason(),
        ticks: s.total_search_ticks(),
        blocks: s.stats.indep_enum_blocks,
    }
}

/// A stop past the head start's end still ends the solve. Kept in the head
/// start's field, it would be overwritten and then cleared, and the solve
/// would run on to its model.
#[test]
fn a_caller_stop_survives_the_head_start() {
    let free = counted_run(None);
    assert!(free.sat && free.blocks > 0, "{free:?}");
    let first_conflict = counted_run(Some(1)).ticks;
    let stop = first_conflict + (free.ticks - first_conflict) / 2;

    let stopped = counted_run(Some(stop));
    assert!(!stopped.sat, "{stopped:?}");
    assert_eq!(stopped.reason, Some(SatUnknownReason::ResourceBudget));
    assert!(
        stopped.ticks >= stop && stopped.ticks < free.ticks,
        "stopped at {} ticks for a stop at {stop} (the free solve: {})",
        stopped.ticks,
        free.ticks
    );
    assert_eq!(
        stopped.blocks, free.blocks,
        "the head start ended and the slice ran before the stop"
    );
}

/// A stop reached at the conflict that ends the head start ends the solve
/// there: the enumeration does not run once the caller's budget is spent.
#[test]
fn a_caller_stop_reached_with_the_head_start_ends_the_solve() {
    let stopped = counted_run(Some(1));
    assert!(!stopped.sat, "{stopped:?}");
    assert_eq!(stopped.reason, Some(SatUnknownReason::ResourceBudget));
    assert_eq!(stopped.blocks, 0, "the enumeration ran after the stop");
    // Negative control: with no stop, the same conflict ends the head start
    // and the slice runs.
    let free = counted_run(None);
    assert!(free.blocks > 0, "{free:?}");
}

/// Every solve entry zeroes the per-solve tick count, so a caller that charges
/// a solve's search ticks to a budget (ay-chc's CHC run node, P4a slice 8)
/// reads `lifetime_search_ticks` around it: its difference is what the solve
/// spent, where the difference of two `total_search_ticks` readings is short
/// by the previous solve's count.
#[test]
fn lifetime_ticks_add_up_the_solves_a_fresh_entry_zeroes() {
    let (num_vars, clauses, _) = mini_prng(32, 16, 0xDEAD_BEEF);
    let mut s = solver_from(num_vars, &clauses);
    s.set_deterministic_inproc(true);
    assert_eq!(s.lifetime_search_ticks(), 0);
    assert!(s.solve().is_sat());
    let first = s.total_search_ticks();
    assert!(first > 0, "the first solve searched");
    assert_eq!(s.lifetime_search_ticks(), first);
    let _ = s.solve();
    let second = s.total_search_ticks();
    assert_eq!(
        s.lifetime_search_ticks(),
        first + second,
        "the second solve's count started from zero: {first} then {second}"
    );
}
