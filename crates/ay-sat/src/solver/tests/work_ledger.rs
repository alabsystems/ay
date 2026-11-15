// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! When a solver's work reaches the work ledger (`solver/work_report.rs`):
//! each solve, an assumption solve and an IC3 query included, is charged in
//! full to the GuardTree node it ran in; a ceiling read at a stop poll counts
//! every conflict made before it; and an allowance the search never reaches
//! changes nothing.
//!
//! The solves that must be charged without a restart run on a schedule that
//! never restarts, so the restart report, the only one a solver made before,
//! can charge nothing there. The IC3 queries restart, on a loop whose
//! restarts never made that report.

use super::*;
use ay_core::resource::{current_guard, enter_work_ceiling, work_ceiling_reached};

/// `pigeons` pigeons in one fewer holes, each pigeon clause guarded by
/// `selector` when there is one: unsat (under the selector), and the search
/// needs conflicts. `first_var` places the copy's variables.
fn add_pigeonhole(solver: &mut Solver, pigeons: u32, first_var: u32, selector: Option<Literal>) {
    let holes = pigeons - 1;
    let var = |pigeon: u32, hole: u32| Variable(first_var + pigeon * holes + hole);
    for pigeon in 0..pigeons {
        let mut clause: Vec<Literal> = (0..holes)
            .map(|hole| Literal::positive(var(pigeon, hole)))
            .collect();
        clause.extend(selector.map(Literal::negated));
        solver.add_clause(clause);
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
}

fn pigeonhole(pigeons: u32) -> Solver {
    let mut solver = Solver::new((pigeons * (pigeons - 1)) as usize);
    add_pigeonhole(&mut solver, pigeons, 0, None);
    solver.set_deterministic_inproc(true);
    solver
}

/// Two copies of `pigeons` pigeons in one fewer holes in one solver, each
/// guarded by its own selector: unsat under either selector.
fn two_selected_pigeonholes(pigeons: u32) -> (Solver, Variable, Variable) {
    let copy = pigeons * (pigeons - 1);
    let first = Variable(2 * copy);
    let second = Variable(2 * copy + 1);
    let mut solver = Solver::new((2 * copy + 2) as usize);
    add_pigeonhole(&mut solver, pigeons, 0, Some(Literal::positive(first)));
    add_pigeonhole(&mut solver, pigeons, copy, Some(Literal::positive(second)));
    solver.set_deterministic_inproc(true);
    (solver, first, second)
}

/// A restart schedule that is never met.
fn never_restarting(mut solver: Solver) -> Solver {
    solver.cold.restart_min_conflicts = u64::MAX;
    solver
}

/// The CDCL conflicts the node this thread is in has recorded.
fn node_conflicts() -> u64 {
    current_guard()
        .expect("a counted node is entered")
        .ledger()
        .sat_conflicts
}

const PIGEONS: u32 = 9;

/// Two solves of one solver, each in a node of its own and neither
/// restarting: each node holds exactly its own solve's conflicts. Reported
/// only at restarts, both held none, and the first solve's tail would have
/// been charged to whichever node a later restart found the thread in.
#[test]
fn each_solve_is_charged_in_full_to_the_node_it_ran_in() {
    let (solver, first, second) = two_selected_pigeonholes(6);
    let mut solver = never_restarting(solver);

    let mut charged = Vec::new();
    for selector in [first, second] {
        let before = solver.total_num_conflicts();
        let node = enter_work_ceiling(None);
        let result = solver.solve_with_assumptions(&[Literal::positive(selector)]);
        assert!(result.is_unsat(), "{:?}", result.result());
        let spent = solver.total_num_conflicts() - before;
        assert_eq!(solver.num_restarts(), 0, "the schedule never restarted");
        charged.push((spent, node_conflicts()));
        drop(node);
    }
    for (spent, node) in charged {
        assert!(spent > 0, "each solve searched: {spent} conflicts");
        assert_eq!(node, spent, "the node holds its own solve's conflicts");
    }
}

/// Two incremental IC3 queries of one solver, each in a node of its own: each
/// node holds exactly its own query's conflicts, although the queries
/// restart. The IC3 loop's restarts never reported, so both nodes held none.
#[test]
fn each_ic3_query_is_charged_in_full_to_the_node_it_ran_in() {
    let (mut solver, first, second) = two_selected_pigeonholes(7);
    for selector in [first, second] {
        let before = solver.total_num_conflicts();
        let node = enter_work_ceiling(None);
        let result = solver.solve_incremental_ic3(&[Literal::positive(selector)]);
        assert!(result.is_unsat(), "{:?}", result.result());
        let spent = solver.total_num_conflicts() - before;
        assert!(spent > 0, "the query searched");
        // `num_restarts` counts the last solve's restarts.
        assert!(solver.num_restarts() > 0, "the query restarted");
        assert_eq!(
            node_conflicts(),
            spent,
            "the node holds its query's conflicts"
        );
        drop(node);
    }
}

/// The strict checker's local solve (`crate::solve_resolution_dag_counted_local`,
/// a SAT sweep's lemma, split leaf and closing refutation), which builds its
/// own solver and drops it: charged to the node it ran in exactly the
/// conflicts it reports to its caller. Reported only at restarts, each node
/// missed the conflicts its solve made after its last restart.
#[test]
fn a_local_resolution_solve_is_charged_to_the_node_it_ran_in() {
    for pigeons in [5, 6, 7] {
        let vars = (pigeons * (pigeons - 1)) as usize;
        let clauses = pigeonhole(pigeons).cold.original_ledger.to_vec_of_vecs();
        let limits = crate::ResolutionProofLimits {
            deadline: Some(ay_core::time::Instant::now() + std::time::Duration::from_secs(60)),
            ..crate::ResolutionProofLimits::default()
        };
        let node = enter_work_ceiling(None);
        let (outcome, conflicts) =
            crate::solve_resolution_dag_counted_local(vars, &clauses, &limits, &mut || true);
        assert!(
            matches!(outcome, Ok(crate::ResolutionSolveOutcome::Unsat(_))),
            "{pigeons} pigeons: {outcome:?}"
        );
        assert!(conflicts > 0, "{pigeons} pigeons: the refutation searched");
        assert_eq!(node_conflicts(), conflicts, "{pigeons} pigeons");
        drop(node);
    }
}

/// A caller's stop that reads a work ceiling stops a solve that never
/// restarts at the poll that reaches the allowance, at the same conflict on
/// every run, with the node holding exactly the conflicts made. Reported only
/// at restarts, the ceiling read zero and the solve ran to its verdict.
#[test]
fn a_ceiling_read_at_a_stop_poll_counts_every_conflict_before_it() {
    let allowance = 300;
    let mut probe = never_restarting(pigeonhole(PIGEONS));
    probe.set_conflict_budget(Some(4 * allowance));
    let probed = probe.solve();
    assert!(
        probed.is_unknown(),
        "the search needs more than four allowances: {:?}",
        probed.result()
    );

    let stopped = || {
        let owner = enter_work_ceiling(Some(allowance));
        let mut solver = never_restarting(pigeonhole(PIGEONS));
        let result = solver.solve_interruptible(work_ceiling_reached);
        assert!(result.is_unknown(), "{:?}", result.result());
        assert!(owner.spent(), "the allowance stopped it");
        assert_eq!(solver.num_restarts(), 0, "the schedule never restarted");
        (solver.total_num_conflicts(), node_conflicts())
    };
    let (conflicts, charged) = stopped();
    assert_eq!(charged, conflicts, "the node holds every conflict made");
    // The main loop polls at every 100th conflict and reports before the
    // caller's stop reads the ceiling, so the poll at the allowance (a
    // multiple of 100) stops it. Were it reported after the callback, every
    // poll would read the count of the poll before, and the stop come at 400.
    assert_eq!(
        conflicts, allowance,
        "the poll at the allowance stops it: {conflicts} for {allowance}"
    );
    assert_eq!(stopped(), (conflicts, charged), "the same count every run");
}

/// The negative twin: under an allowance the search never reaches, on the
/// default schedule (restart, stop-poll and end reports all made), the solve
/// ends with the same verdict, conflicts and decisions as with no ceiling,
/// and the node is charged each conflict exactly once.
#[test]
fn an_allowance_the_search_never_reaches_changes_nothing() {
    let solve = |solver: &mut Solver| {
        let result = solver.solve_interruptible(work_ceiling_reached);
        (
            result.is_unsat(),
            solver.total_num_conflicts(),
            solver.total_num_decisions(),
        )
    };
    let free = solve(&mut pigeonhole(PIGEONS));
    assert!(free.0, "unsat without a ceiling: {free:?}");

    let owner = enter_work_ceiling(Some(4 * free.1));
    let mut solver = pigeonhole(PIGEONS);
    let bounded = solve(&mut solver);
    assert_eq!(
        bounded, free,
        "the same search under an unreached allowance"
    );
    assert!(solver.num_restarts() > 0, "the default schedule restarted");
    assert!(!owner.spent());
    assert_eq!(node_conflicts(), free.1, "each conflict charged once");
}
