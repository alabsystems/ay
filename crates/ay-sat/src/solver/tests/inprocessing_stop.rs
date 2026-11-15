// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The search's stop inside inprocessing rounds: a restart's round sees it
//! at the settled points between its passes and ends at the first one after
//! it fired, the assumption solve's incremental round sees it too
//! (`assumptions`), and a stop wins over an UNSAT found after it.

use super::*;
use std::cell::Cell;

mod assumptions;

fn runs(solver: &Solver, pass: DiagnosticPass) -> u64 {
    let index = solver_stats::inprocessing_timing_index(pass).expect("timed pass");
    solver.stats.inprocessing_pass_runs[index]
}

/// A stop that fires on its `fire_at`-th poll and counts its polls.
fn stop_at(polls: &Cell<u32>, fire_at: u32) -> impl Fn() -> bool + '_ {
    move || {
        polls.set(polls.get() + 1);
        polls.get() >= fire_at
    }
}

/// A round with subsumption, both backbone paths and vivification due, in
/// this order: subsume, binary backbone, (elimination, all disabled),
/// bounded backbone, vivify, subsume after vivify, binary backbone again.
fn late_pass_round_solver() -> Solver {
    let mut solver: Solver = Solver::new(6);
    let pos = |v: u32| Literal::positive(Variable(v));
    let neg = |v: u32| Literal::negative(Variable(v));
    solver.add_clause_db(&[pos(0), pos(1)], false);
    solver.add_clause_db(&[pos(2), pos(3), pos(4)], false);
    solver.add_clause_db(&[neg(2), pos(3), pos(5)], false);
    solver.add_clause_db(&[pos(2), neg(4), neg(5)], false);
    solver.initialize_watches();
    solver.disable_all_inprocessing();
    solver.set_backbone_enabled(true);
    solver.set_vivify_enabled(true);
    solver.set_subsume_enabled(true);
    solver.cold.next_inprobe_conflict = 0;
    solver.inproc_ctrl.backbone.next_conflict = 0;
    solver.inproc_ctrl.vivify.next_conflict = 0;
    solver.inproc_ctrl.vivify_irred.next_conflict = 0;
    solver.inproc_ctrl.subsume.next_conflict = 0;
    solver.num_conflicts = BACKBONE_INTERVAL;
    solver
}

/// A stop the round sees ends it at its next checkpoint, between any two of
/// the binary backbone, the bounded backbone, vivification and the
/// subsumption after it. Before, nothing polled the stop after the
/// checkpoint that follows congruence and decompose: a stop that fired
/// after it was not seen until the whole back half (elimination, both
/// backbones, vivification, subsumption) had run, so the only states a
/// stop could leave were "before the binary backbone" and "round complete".
#[test]
fn a_stop_is_seen_between_each_late_pass_of_a_round() {
    let mut idle = late_pass_round_solver();
    let idle_polls = Cell::new(0_u32);
    assert!(idle
        .run_inprocessing_round_until(&stop_at(&idle_polls, u32::MAX), None)
        .is_none());
    let passes = |solver: &Solver| {
        (
            runs(solver, DiagnosticPass::Subsume),
            runs(solver, DiagnosticPass::Backbone),
            runs(solver, DiagnosticPass::Vivify),
        )
    };
    assert_eq!(passes(&idle), (2, 3, 1), "the fixture runs every late pass");

    let mut ended_after = Vec::new();
    for fire_at in 1..=idle_polls.get() {
        let mut solver = late_pass_round_solver();
        let polls = Cell::new(0_u32);
        let ended = solver.run_inprocessing_round_until(&stop_at(&polls, fire_at), None);
        assert!(
            matches!(ended, Some(SatResult::Unknown)),
            "{fire_at}: {ended:?}"
        );
        assert_eq!(polls.get(), fire_at, "a latched stop is not polled again");
        assert!(
            !solver.cold.inprocessing_caller_stop,
            "the round took the latch"
        );
        ended_after.push(passes(&solver));
    }
    for state in [(1, 1, 0), (1, 2, 0), (1, 2, 1)] {
        assert!(
            ended_after.contains(&state),
            "no stop ended the round after (subsume, backbone, vivify) runs {state:?}: {ended_after:?}"
        );
    }
}

/// A stop the round sees between the binary backbone and elimination keeps
/// elimination (here BVE) from starting, and one it sees right after
/// elimination keeps the bounded backbone from starting. Before, no
/// checkpoint sat on either side of `run_elimination_passes`.
#[test]
fn a_stop_is_seen_on_both_sides_of_elimination() {
    let fixture = || {
        let mut solver = late_pass_round_solver();
        solver.inproc_ctrl.bve.enabled = true;
        solver.inproc_ctrl.bve.next_conflict = 0;
        solver
    };
    let passes = |solver: &Solver| {
        (
            runs(solver, DiagnosticPass::Backbone),
            runs(solver, DiagnosticPass::BVE),
        )
    };
    let mut idle = fixture();
    let idle_polls = Cell::new(0_u32);
    assert!(idle
        .run_inprocessing_round_until(&stop_at(&idle_polls, u32::MAX), None)
        .is_none());
    assert_eq!(
        passes(&idle),
        (3, 1),
        "the fixture runs BVE and both backbones"
    );

    let mut ended_after = Vec::new();
    for fire_at in 1..=idle_polls.get() {
        let mut solver = fixture();
        let polls = Cell::new(0_u32);
        let ended = solver.run_inprocessing_round_until(&stop_at(&polls, fire_at), None);
        assert!(
            matches!(ended, Some(SatResult::Unknown)),
            "{fire_at}: {ended:?}"
        );
        ended_after.push(passes(&solver));
    }
    for state in [(1, 0), (1, 1)] {
        assert!(
            ended_after.contains(&state),
            "no stop ended the round after (backbone, bve) runs {state:?}: {ended_after:?}"
        );
    }
}

/// `count` binary clauses `(r_i v a_i)` over fresh variables: `2 * count`
/// probe candidates, none failing.
fn solver_with_probe_roots(count: u32) -> Solver {
    let mut solver: Solver = Solver::new(2 * count as usize);
    for root in 0..count {
        solver.add_clause(vec![
            Literal::positive(Variable(2 * root)),
            Literal::positive(Variable(2 * root + 1)),
        ]);
    }
    assert!(solver.process_initial_clauses().is_none());
    solver.initialize_watches();
    assert!(solver.propagate().is_none());
    solver
}

/// A round where probing (twenty candidates), intree probing, both backbone
/// paths and vivification are due.
fn probe_round_solver() -> Solver {
    let mut solver = solver_with_probe_roots(10);
    solver.disable_all_inprocessing();
    solver.inproc_ctrl.probe.enabled = true;
    solver.inproc_ctrl.probe.next_conflict = 0;
    solver.set_backbone_enabled(true);
    solver.set_vivify_enabled(true);
    solver.inproc_ctrl.backbone.next_conflict = 0;
    solver.inproc_ctrl.vivify.next_conflict = 0;
    solver.inproc_ctrl.vivify_irred.next_conflict = 0;
    solver.cold.next_inprobe_conflict = 0;
    solver.num_conflicts = BACKBONE_INTERVAL;
    solver
}

/// A stop seen while probing ends the round right after probing: no intree
/// probing (counted as a second probe-pass run), no backbone, no
/// vivification. Before, it ran on through intree probing, congruence and
/// decompose to the checkpoint after them.
#[test]
fn a_stop_probing_saw_ends_the_round_before_intree_probing() {
    let mut idle = probe_round_solver();
    assert!(idle.run_inprocessing_round_until(&|| false, None).is_none());
    assert_eq!(idle.inproc.prober.stats().probed, 20);
    assert_eq!(runs(&idle, DiagnosticPass::Probe), 2, "probe and intree");

    let mut cut_inside_probing = 0;
    for fire_at in 1..=40 {
        let mut solver = probe_round_solver();
        let polls = Cell::new(0_u32);
        let ended = solver.run_inprocessing_round_until(&stop_at(&polls, fire_at), None);
        let probed = solver.inproc.prober.stats().probed;
        if !(1..20).contains(&probed) {
            continue;
        }
        cut_inside_probing += 1;
        assert!(
            matches!(ended, Some(SatResult::Unknown)),
            "{fire_at}: {ended:?}"
        );
        assert_eq!(
            runs(&solver, DiagnosticPass::Probe),
            1,
            "stop at poll {fire_at}, {probed} candidates probed: intree probing ran"
        );
        assert_eq!(runs(&solver, DiagnosticPass::Backbone), 0);
        assert_eq!(runs(&solver, DiagnosticPass::Vivify), 0);
    }
    assert_eq!(
        cut_inside_probing, 19,
        "a stop at each candidate but the first"
    );
}

/// A probe round whose first candidate is the failed literal `p`
/// (`p -> q`, `q -> r`, `q -> s`, `r -> -s`), with decompose enabled under
/// `--sat-subst-kissat`, which skips the round-start decompose, so the
/// decompose after a probe that found a failed literal is due. Probing takes
/// candidates fewest binary occurrences first, the highest variable among
/// equals: `p` has one occurrence, like the twenty root literals, and is the
/// highest variable.
fn failed_literal_probe_round_solver() -> Solver {
    let roots = 10_u32;
    let var = |offset: u32| Variable(2 * roots + offset);
    let (q, r, s, p) = (var(0), var(1), var(2), var(3));
    let mut solver: Solver = Solver::new(2 * roots as usize + 4);
    for root in 0..roots {
        solver.add_clause(vec![
            Literal::positive(Variable(2 * root)),
            Literal::positive(Variable(2 * root + 1)),
        ]);
    }
    solver.add_clause(vec![Literal::negative(p), Literal::positive(q)]);
    solver.add_clause(vec![Literal::negative(q), Literal::positive(r)]);
    solver.add_clause(vec![Literal::negative(q), Literal::positive(s)]);
    solver.add_clause(vec![Literal::negative(r), Literal::negative(s)]);
    assert!(solver.process_initial_clauses().is_none());
    solver.initialize_watches();
    assert!(solver.propagate().is_none());
    solver.disable_all_inprocessing();
    solver.cold.subst_kissat = true;
    solver.inproc_ctrl.probe.enabled = true;
    solver.inproc_ctrl.probe.next_conflict = 0;
    solver.inproc_ctrl.decompose.enabled = true;
    solver.inproc_ctrl.decompose.next_conflict = 0;
    solver.cold.next_inprobe_conflict = 0;
    solver.num_conflicts = BACKBONE_INTERVAL;
    solver
}

/// A stop seen while probing skips the decompose that follows a probe that
/// found a failed literal: the round ends right after it anyway. Before,
/// that decompose (a pass over every clause) ran first, and only then did
/// the round see the stop.
#[test]
fn a_stop_probing_saw_skips_the_post_probe_decompose() {
    let mut idle = failed_literal_probe_round_solver();
    assert!(idle.run_inprocessing_round_until(&|| false, None).is_none());
    let total = idle.inproc.prober.stats().probed;
    assert_eq!(idle.inproc.prober.stats().failed, 1, "p fails");
    assert_eq!(
        runs(&idle, DiagnosticPass::Decompose),
        2,
        "after probing and after congruence"
    );

    let mut cut_after_a_failure = 0_u64;
    for fire_at in 1..=2 * total as u32 {
        let mut solver = failed_literal_probe_round_solver();
        let polls = Cell::new(0_u32);
        let ended = solver.run_inprocessing_round_until(&stop_at(&polls, fire_at), None);
        let stats = solver.inproc.prober.stats();
        let (probed, failed) = (stats.probed, stats.failed);
        if failed == 0 || !(1..total).contains(&probed) {
            continue;
        }
        cut_after_a_failure += 1;
        assert!(
            matches!(ended, Some(SatResult::Unknown)),
            "{fire_at}: {ended:?}"
        );
        assert_eq!(
            runs(&solver, DiagnosticPass::Decompose),
            0,
            "stop at poll {fire_at}, {probed} of {total} probed: decompose ran"
        );
    }
    assert_eq!(
        cut_after_a_failure,
        total - 1,
        "a stop at each candidate after p"
    );
}

/// The round's latch is read before its UNSAT: a stop it saw ends the solve
/// Unknown even when the round then derived the empty clause. Every
/// checkpoint returns as soon as it latches, so this order is what keeps a
/// refutation found after a latch (in probing's clean-up, say) from
/// answering a stopped solve; the latch is set here by hand.
#[test]
fn a_latched_stop_wins_over_the_unsat_the_round_finds() {
    let mut idle = solver_with_probe_roots(2);
    idle.cold.next_inprobe_conflict = 0;
    idle.num_conflicts = 1;
    idle.mark_empty_clause();
    let ended = idle.run_inprocessing_round_until(&|| false, None);
    assert!(matches!(ended, Some(SatResult::Unsat(_))), "{ended:?}");

    let mut stopped = solver_with_probe_roots(2);
    stopped.cold.next_inprobe_conflict = 0;
    stopped.num_conflicts = 1;
    stopped.mark_empty_clause();
    stopped.cold.inprocessing_caller_stop = true;
    let ended = stopped.run_inprocessing_round_until(&|| unreachable!("latched"), None);
    assert!(matches!(ended, Some(SatResult::Unknown)), "{ended:?}");
    assert_eq!(
        stopped.last_unknown_reason(),
        Some(SatUnknownReason::Interrupted)
    );
    assert!(!stopped.cold.inprocessing_caller_stop);
}

/// A stop seen past the solve deadline ends the solve as
/// `DeadlineExceeded`, from a restart's round and from the incremental one.
#[test]
fn a_round_ends_the_solve_as_deadline_exceeded_past_the_deadline() {
    let mut restart = solver_with_probe_roots(10);
    restart.cold.next_inprobe_conflict = 0;
    restart.num_conflicts = 1;
    restart.set_solve_deadline(Some(ay_core::time::Instant::now()));
    let ended = restart.run_inprocessing_round_until(&|| true, None);
    assert!(matches!(ended, Some(SatResult::Unknown)), "{ended:?}");
    assert_eq!(
        restart.last_unknown_reason(),
        Some(SatUnknownReason::DeadlineExceeded)
    );

    let mut incremental = solver_with_probe_roots(10);
    incremental.set_solve_deadline(Some(ay_core::time::Instant::now()));
    let ended = incremental.run_incremental_inprocessing_round_until(Some(&|| true));
    assert!(matches!(ended, Some(AssumeResult::Unknown)), "{ended:?}");
    assert_eq!(
        incremental.last_unknown_reason(),
        Some(SatUnknownReason::DeadlineExceeded)
    );
    assert!(!incremental.cold.inprocessing_caller_stop);
}

/// `holes + 1` pigeons in `holes` holes, and `roots` probe-root binaries
/// over fresh variables.
fn pigeonhole_with_probe_roots(holes: u32, roots: u32) -> Solver {
    let pigeons = holes + 1;
    let base = pigeons * holes;
    let mut solver: Solver = Solver::new((base + 2 * roots) as usize);
    let var = |pigeon: u32, hole: u32| Variable(pigeon * holes + hole);
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
    for root in 0..roots {
        solver.add_clause(vec![
            Literal::positive(Variable(base + 2 * root)),
            Literal::positive(Variable(base + 2 * root + 1)),
        ]);
    }
    // A conflict-budgeted first solve makes every pass due from the second
    // solve's first round on (`lifetime_conflicts > 0`), probing included.
    solver.set_conflict_budget(Some(50));
    assert!(solver.solve().into_inner().is_unknown());
    solver.set_conflict_budget(None);
    solver
}

/// Through `solve_interruptible`: a stop that fires while a restart's round
/// is probing ends the solve there, Unknown, with the round's candidates
/// left over, intree probing not run, and the stop not polled again.
#[test]
fn a_stop_that_fires_mid_probe_ends_solve_interruptible_there() {
    let mut idle = pigeonhole_with_probe_roots(6, 20);
    assert!(idle.solve_interruptible(|| false).into_inner().is_unsat());

    let mut checked = false;
    for fire_at in 1..=60 {
        let mut solver = pigeonhole_with_probe_roots(6, 20);
        let polls = Cell::new(0_u32);
        let result = solver
            .solve_interruptible(stop_at(&polls, fire_at))
            .into_inner();
        let probed = solver.inproc.prober.stats().probed;
        if probed == 0 || !solver.inproc.prober.has_probes() {
            continue;
        }
        assert!(result.is_unknown(), "{fire_at}: {result:?}");
        assert_eq!(
            solver.last_unknown_reason(),
            Some(SatUnknownReason::Interrupted)
        );
        assert_eq!(polls.get(), fire_at, "the stop was not polled again");
        assert_eq!(
            solver.stats.inprocessing_rounds, 0,
            "the probing round did not finish"
        );
        assert_eq!(
            solver.cold.intree_rounds, 0,
            "{fire_at}: intree probing ran after the stop"
        );
        checked = true;
        break;
    }
    assert!(checked, "no stop fired while a round was probing");
}
