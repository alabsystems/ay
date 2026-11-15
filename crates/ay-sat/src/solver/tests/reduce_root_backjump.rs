// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The backjump to level 0 that `reduce_db` takes to propagate out-of-order
//! units (CaDiCaL reduce.cpp:223) reaches the conflict-analysis backtrack
//! hook like every other backjump: an extension pops its scopes and the
//! assumption loop re-assumes; on the extension-conflict path the extension
//! itself hears it. Before this, only the analysis's own backjump was
//! announced, and an extension was left above the solver's decision level
//! (the CDCL(T) kernel's resyncs, K2).

use super::*;
use crate::extension::{ExtCheckResult, ExtPropagateResult, Extension, SolverContext};

fn pos(i: u32) -> Literal {
    Literal::positive(Variable(i))
}

fn neg(i: u32) -> Literal {
    Literal::negative(Variable(i))
}

/// x=0 at level 0; a=1 decided (level 1); b=2 decided (level 2); c=3 a
/// level-0 unit assigned out of order at level 2 (its reason's other literal
/// is x); d=4 decided (level 3) conflicts through e=5. Analysis backjumps to
/// level 2, keeping `c` above the first decision, and a reduction is due.
fn out_of_order_conflict() -> (Solver, ClauseRef) {
    let mut solver: Solver = Solver::new(6);
    solver.chrono_enabled = true;
    solver.add_clause(vec![neg(0), pos(3)]);
    let reason = ClauseRef(0);
    solver.add_clause(vec![neg(2), neg(4), pos(5)]);
    solver.add_clause(vec![neg(2), neg(4), neg(5)]);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    // `x` at level 0 without propagating it, so `c` is still free.
    solver.enqueue(pos(0), None);
    solver.qhead = solver.trail.len();
    solver.decide(pos(1));
    assert!(solver.search_propagate().is_none());
    solver.decide(pos(2));
    assert!(solver.search_propagate().is_none());
    solver.enqueue(pos(3), Some(reason));
    assert_eq!(solver.var_data[3].level, 0, "c is a level-0 unit");
    assert!(solver.search_propagate().is_none());
    solver.decide(pos(4));
    let conflict = solver.search_propagate().expect("d conflicts through e");
    solver.cold.next_reduce_db = 0;
    (solver, conflict)
}

#[test]
fn reduce_db_root_backjump_reaches_the_backtrack_hook() {
    let (mut solver, conflict) = out_of_order_conflict();
    let mut heard: Vec<u32> = Vec::new();
    solver.analyze_and_backtrack(conflict, "reduce_root_backjump", |_, level| {
        heard.push(level)
    });
    assert_eq!(
        solver.decision_level, 0,
        "the reduction backjumped to the root"
    );
    assert_eq!(
        heard.last().copied(),
        Some(0),
        "the hook heard {heard:?} but the solver ended at level 0"
    );
    assert_eq!(
        heard.first().copied(),
        Some(2),
        "the analysis backjump comes first"
    );
}

#[test]
fn reduce_db_announces_a_root_backjump_only_when_it_takes_one() {
    let (mut solver, _) = out_of_order_conflict();
    assert!(solver.reduce_db_backjumps_to_root());
    solver.chrono_enabled = false;
    assert!(!solver.reduce_db_backjumps_to_root());
    solver.chrono_enabled = true;
    solver.backtrack(0);
    assert!(
        !solver.reduce_db_backjumps_to_root(),
        "nothing above level 0"
    );
}

/// Every level `Extension::backtrack` announced.
#[derive(Default)]
struct Heard(Vec<u32>);

impl Extension for Heard {
    fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
        ExtPropagateResult::none()
    }

    fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
        ExtCheckResult::Sat
    }

    fn backtrack(&mut self, new_level: u32) {
        self.0.push(new_level);
    }
}

/// The extension-conflict path schedules reductions too: a theory conflict
/// over `b` (level 2) and `d` (level 3) backjumps to level 2, where `c` is
/// still out of order, and the due reduction's jump to level 0 reaches the
/// extension.
#[test]
fn reduce_db_root_backjump_reaches_the_extension_after_a_theory_conflict() {
    let (mut solver, _) = out_of_order_conflict();
    let mut heard = Heard::default();
    solver.handle_ext_conflict(vec![neg(2), neg(4)], &mut heard);
    assert_eq!(
        solver.decision_level, 0,
        "the reduction backjumped to the root"
    );
    assert_eq!(
        heard.0,
        vec![2, 0],
        "the extension heard {:?} but the solver ended at level 0",
        heard.0
    );
}
