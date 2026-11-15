// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Charge `step` where no effort is open: such a charge never says stop.
fn charge_free(step: Step) {
    assert_eq!(
        charge(step),
        Ok(()),
        "a charge with no effort reads nothing"
    );
}

/// What a SAT solve of `cost` search ticks charges, through `sat_solve`'s
/// own accounting (its `charge_sat_ticks`).
fn charge_ticks(cost: u64) -> Result<(), Exhausted> {
    charge_sat_ticks(cost)
}

#[test]
fn a_run_charges_its_node_and_publishes_the_totals() {
    let meter = RunMeter::open(None, None);
    charge_free(Step::SmtEntry);
    charge_free(Step::TheoryRound);
    assert_eq!(charge_ticks(7), Ok(()));
    assert_eq!(charge_ticks(0), Ok(()));
    charge_free(Step::PdrIteration);
    charge_free(Step::Obligation);
    note_frames(4, 9);
    note_frames(5, 11);
    let work = meter.close().expect("the run is metered");
    assert_eq!(
        (
            work.ticks,
            work.sat_ticks,
            work.smt_entries,
            work.theory_rounds
        ),
        (11, 7, 1, 1)
    );
    assert_eq!((work.pdr_iterations, work.obligations), (1, 1));
    assert_eq!(
        (work.frames, work.lemmas),
        (5, 11),
        "the last reading stands"
    );
    assert_eq!((work.effort, work.stop), (None, None), "no effort");
}

#[test]
fn a_charge_outside_every_run_reaches_nothing_and_runs_nest() {
    charge_free(Step::SmtEntry);
    let outer = RunMeter::open(None, None);
    charge_free(Step::SmtEntry);
    let inner = RunMeter::open(None, None);
    charge_free(Step::SmtEntry);
    charge_free(Step::SmtEntry);
    let inner_work = inner.close().expect("the inner run is metered");
    assert_eq!((inner_work.ticks, inner_work.smt_entries), (2, 2));
    charge_free(Step::SmtEntry);
    let outer_work = outer.close().expect("the outer run is metered");
    assert_eq!(
        (outer_work.ticks, outer_work.smt_entries),
        (4, 2),
        "a nested run's ticks reach the outer ledger, not its counts"
    );
    charge_free(Step::SmtEntry);
}

#[test]
fn the_run_node_is_the_threads_current_node_and_hangs_below_the_last_one() {
    let around = Guard::root_child(ChildSpec::new(NodeLabel::Check));
    let _inside = around.enter();
    let meter = RunMeter::open(None, None);
    let current = current_guard().expect("the run is entered");
    assert!(current.is_within(&around));
    assert_eq!(current.poll(), None);
    ay_core::resource::work().add_sat_work(3, 4);
    charge_free(Step::SmtEntry);
    let work = meter.close().expect("the run is metered");
    assert_eq!(
        (work.ledger.sat_conflicts, work.ledger.sat_decisions),
        (3, 4)
    );
    assert!(
        current_guard().is_some_and(|node| around.is_within(&node)),
        "a closed run leaves its node: the thread is back in the node around it"
    );
    assert_eq!(
        around.ledger().sat_conflicts,
        3,
        "the run's work reached it"
    );
}

#[test]
fn the_run_is_not_a_check_so_a_lookup_for_the_check_passes_over_it() {
    let meter = RunMeter::open(None, None);
    let run = current_guard().expect("the run is entered");
    assert_eq!(run.label(), NodeLabel::Run);
    assert!(
        run.nearest(NodeLabel::Check).is_none(),
        "Certify's sizing finds no check in a run on a thread in none"
    );
    drop(meter);
    let around = Guard::root_child(ChildSpec::new(NodeLabel::Check));
    let _inside = around.enter();
    let _meter = RunMeter::open(None, None);
    let check = current_guard()
        .and_then(|node| node.nearest(NodeLabel::Check))
        .expect("the check around the run");
    assert!(around.is_within(&check) && check.is_within(&around));
}

#[test]
fn below_a_node_that_counts_the_run_opens_no_node_and_publishes_nothing() {
    let counted = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(100)));
    let _inside = counted.enter();
    let meter = RunMeter::open(None, None);
    let current = current_guard().expect("the counting node");
    assert!(
        current.is_within(&counted) && counted.is_within(&current),
        "no node is entered below it"
    );
    charge_free(Step::SmtEntry);
    assert_eq!(charge_ticks(40), Ok(()));
    assert!(!counting(), "a run that is not metered does not count");
    assert_eq!(
        meter.close(),
        None,
        "a run that was not metered has no work"
    );
    assert_eq!(
        (counted.ticks(), counted.remaining()),
        (0, Some(100)),
        "the charges reached nothing: the count decided nothing"
    );
}

#[test]
fn a_run_that_is_not_metered_charges_no_run_around_it() {
    let outer = RunMeter::open(None, None);
    let counted = current_guard()
        .expect("the outer run")
        .child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(100)));
    let inside = counted.enter();
    let inner = RunMeter::open(None, None);
    charge_free(Step::SmtEntry);
    assert_eq!(inner.close(), None);
    drop(inside);
    drop(counted);
    let work = outer.close().expect("the outer run is metered");
    assert_eq!(
        (work.ticks, work.smt_entries),
        (0, 0),
        "the unmetered run's charge went nowhere"
    );
}

#[test]
fn under_an_effort_the_run_stops_at_its_budget_and_publishes_the_stop() {
    let meter = RunMeter::open(Some(10), None);
    assert!(counting() && !run_stopped());
    assert_eq!(charge(Step::SmtEntry), Ok(()));
    assert_eq!(charge_ticks(7), Ok(()));
    assert_eq!(counted_ticks(), Some(8));
    assert_eq!(charge(Step::TheoryRound), Ok(()));
    assert_eq!(
        charge(Step::PdrIteration),
        Err(Exhausted::Rlimit),
        "the tenth tick reaches the budget"
    );
    assert!(run_stopped(), "is_cancelled reads the latched stop");
    assert_eq!(
        charge(Step::Obligation),
        Err(Exhausted::Rlimit),
        "it stays latched"
    );
    let work = meter.close().expect("the run is metered");
    assert_eq!(
        (work.effort, work.stop),
        (Some(10), Some(Exhausted::Rlimit))
    );
    assert_eq!((work.ticks, work.sat_ticks), (11, 7));
    assert!(
        !counting() && !run_stopped() && counted_ticks().is_none(),
        "closed: nothing counts"
    );
}

#[test]
fn an_effort_run_is_not_entered_so_an_executor_check_in_it_hangs_where_it_did() {
    let around = Guard::root_child(ChildSpec::new(NodeLabel::Check));
    let _inside = around.enter();
    let meter = RunMeter::open(Some(1_000), None);
    let current = current_guard().expect("the thread's node");
    assert!(
        current.is_within(&around) && around.is_within(&current),
        "the run's node is not the thread's current node"
    );
    let check = current.child(ChildSpec::new(NodeLabel::Check));
    assert_eq!(
        check.allotment(),
        None,
        "an executor check opened in the run is granted nothing of B"
    );
    drop(check);
    assert_eq!(charge(Step::SmtEntry), Ok(()));
    let work = meter.close().expect("the run is metered");
    assert_eq!((work.ticks, work.effort, work.stop), (1, Some(1_000), None));
    assert_eq!(
        around.ledger_ticks(),
        1,
        "its ticks reached the node above it"
    );
}

#[test]
fn an_effort_is_capped_by_a_node_that_counts_around_the_run() {
    let counted = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(5)));
    let _inside = counted.enter();
    let meter = RunMeter::open(Some(1_000), None);
    assert_eq!(charge_ticks(4), Ok(()));
    assert_eq!(charge(Step::SmtEntry), Err(Exhausted::Rlimit));
    let work = meter.close().expect("the run is metered");
    assert_eq!(
        (work.effort, work.stop),
        (Some(5), Some(Exhausted::Rlimit)),
        "a draw on the node around it"
    );
    assert_eq!(counted.ticks(), 5, "the closed run's spend is the node's");
}

#[test]
fn a_run_with_no_effort_inside_an_effort_run_draws_on_it() {
    let outer = RunMeter::open(Some(3), None);
    let inner = RunMeter::open(None, None);
    assert!(counting(), "the inner run counts on the outer one's node");
    assert_eq!(charge(Step::SmtEntry), Ok(()));
    assert_eq!(charge(Step::SmtEntry), Ok(()));
    assert_eq!(charge(Step::SmtEntry), Err(Exhausted::Rlimit));
    assert_eq!(inner.close(), None, "it has no node of its own");
    assert!(run_stopped(), "the outer run's budget is spent");
    let work = outer.close().expect("the outer run is metered");
    assert_eq!(
        (work.ticks, work.smt_entries, work.stop),
        (3, 0, Some(Exhausted::Rlimit)),
        "the inner run's charges are the outer run's ticks"
    );
}

/// A small satisfiable CNF with enough clauses that its search spends ticks.
fn pigeonhole_ish_solver() -> ay_sat::Solver {
    let mut sat = ay_sat::Solver::new(12);
    for a in 0..12u32 {
        for b in (a + 1)..12u32 {
            if (a + b) % 3 == 0 {
                sat.add_clause(vec![
                    ay_sat::Literal::negative(ay_sat::Variable::new(a)),
                    ay_sat::Literal::negative(ay_sat::Variable::new(b)),
                ]);
            }
        }
    }
    sat.add_clause(
        (0..12u32)
            .map(|v| ay_sat::Literal::positive(ay_sat::Variable::new(v)))
            .collect(),
    );
    sat
}

#[test]
fn a_sat_solve_under_an_effort_is_armed_and_put_back() {
    let mut sat = pigeonhole_ish_solver();
    let counted_before = sat.deterministic_inproc();
    sat.set_search_tick_stop(Some(123));
    let meter = RunMeter::open(Some(1 << 40), None);
    assert_eq!(charge(Step::SmtEntry), Ok(()));
    let mut armed = None;
    let _ = sat_solve(&mut sat, |sat| {
        armed = Some((sat.caller_search_tick_stop(), sat.deterministic_inproc()));
        sat.solve()
    });
    assert_eq!(
        armed,
        Some((Some((1 << 40) - 1), true)),
        "the solve ran with the run's remainder as its stop and the per-solver count on"
    );
    assert_eq!(
        (sat.caller_search_tick_stop(), sat.deterministic_inproc()),
        (Some(123), counted_before),
        "the solver's own stop and switch are put back"
    );
    let work = meter.close().expect("the run is metered");
    assert_eq!(work.sat_ticks, sat.lifetime_search_ticks());
    sat.set_search_tick_stop(None);
    let meter = RunMeter::open(None, None);
    let mut armed = None;
    let _ = sat_solve(&mut sat, |sat| {
        armed = Some(sat.deterministic_inproc());
        sat.solve()
    });
    assert_eq!(armed, Some(counted_before), "no effort: nothing is armed");
    let work = meter.close().expect("the run is metered");
    assert_eq!(
        work.sat_ticks,
        sat.total_search_ticks(),
        "a second solve's charge is what it spent, not the difference of two per-solve counts"
    );
}

#[test]
fn a_solve_that_unwinds_leaves_its_solver_as_it_was() {
    let mut sat = pigeonhole_ish_solver();
    let counted_before = sat.deterministic_inproc();
    let meter = RunMeter::open(Some(1_000), None);
    let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        sat_solve::<()>(&mut sat, |_| panic!("a solve that unwinds"))
    }));
    assert!(unwound.is_err());
    assert_eq!(
        (sat.caller_search_tick_stop(), sat.deterministic_inproc()),
        (None, counted_before),
        "a persistent solver is not left armed with a stale remainder"
    );
    drop(meter);
}

#[test]
fn a_backstop_that_ended_a_run_is_its_published_stop() {
    let past = Instant::now()
        .checked_sub(std::time::Duration::from_millis(1))
        .expect("a past instant");
    // A charge reads the clock on the stride (GT3): the next one after 1024
    // ticks latches the backstop, and the caller stops.
    let meter = RunMeter::open(Some(1 << 40), Some(past));
    assert_eq!(charge(Step::SmtEntry), Ok(()), "inside the stride");
    assert_eq!(charge_ticks(2_000), Err(Exhausted::Deadline));
    assert!(run_stopped());
    let work = meter.close().expect("the run is metered");
    assert_eq!(work.stop, Some(Exhausted::Deadline));
    // A run that ended after its last charge is settled at its close.
    let meter = RunMeter::open(Some(1 << 40), Some(past));
    assert_eq!(charge(Step::SmtEntry), Ok(()));
    meter.settle(false);
    let work = meter.close().expect("the run is metered");
    assert_eq!(work.stop, Some(Exhausted::Deadline));
    // The run's own token, which the node does not read.
    let meter = RunMeter::open(Some(1 << 40), None);
    meter.settle(true);
    assert_eq!(
        meter.close().map(|work| work.stop),
        Some(Some(Exhausted::Cancelled))
    );
    // A stop already latched stands, and a run nothing stopped settles to none.
    let meter = RunMeter::open(Some(1), Some(past));
    assert_eq!(charge(Step::SmtEntry), Err(Exhausted::Rlimit));
    meter.settle(true);
    assert_eq!(
        meter.close().map(|work| work.stop),
        Some(Some(Exhausted::Rlimit))
    );
    let meter = RunMeter::open(Some(1 << 40), None);
    meter.settle(false);
    assert_eq!(meter.close().map(|work| work.stop), Some(None));
    // Without an effort the backstop is not the node's, and nothing settles.
    let meter = RunMeter::open(None, Some(past));
    assert_eq!(charge_ticks(2_000), Ok(()));
    meter.settle(true);
    assert_eq!(meter.close().map(|work| work.stop), Some(None));
}
