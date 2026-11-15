// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The DPLL(T) loop honours a counted work grant
//! (`ay_core::resource::enter_work_grant`, #deterministic-probe-metering):
//! its loop-top solve controls and its SAT stop closure end it at the same
//! round trip every time, like a deadline.

use super::*;
use ay_core::resource::{enter_work_grant, thread_round_trips};

/// Rejects the first `conflicts_left` complete assignments it checks, each
/// with the conflict "exactly this assignment", then accepts: a solve needs
/// several split-loop round trips whatever the SAT solver picks.
struct RejectFirstAssignments {
    atoms: [TermId; 3],
    values: [Option<bool>; 3],
    conflicts_left: usize,
}

impl TheorySolver for RejectFirstAssignments {
    fn assert_literal(&mut self, literal: TermId, value: bool) {
        if let Some(slot) = self.atoms.iter().position(|&atom| atom == literal) {
            self.values[slot] = Some(value);
        }
    }

    fn check(&mut self) -> TheoryResult {
        let conflict: Vec<TheoryLit> = self
            .atoms
            .iter()
            .zip(self.values)
            .filter_map(|(&atom, value)| value.map(|value| TheoryLit::new(atom, value)))
            .collect();
        if self.conflicts_left == 0 || conflict.len() < self.atoms.len() {
            return TheoryResult::Sat;
        }
        self.conflicts_left -= 1;
        TheoryResult::Unsat(conflict)
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        vec![]
    }

    fn push(&mut self) {}

    fn pop(&mut self) {
        self.values = [None; 3];
    }

    fn reset(&mut self) {
        self.values = [None; 3];
    }
}

/// One DPLL(T) solve that rejects five assignments before it accepts one,
/// under `grant` if given: its result and the split-loop round trips it
/// started.
fn solve(grant: Option<u64>) -> (SatResult, u64) {
    let atoms = [TermId::new(11), TermId::new(12), TermId::new(13)];
    let theory = RejectFirstAssignments {
        atoms,
        values: [None; 3],
        conflicts_left: 5,
    };
    let mut dpll = DpllT::new(3, theory);
    for (var, atom) in (0u32..).zip(atoms) {
        dpll.register_theory_atom(atom, var);
    }
    let _grant = grant.map(enter_work_grant);
    let before = thread_round_trips();
    let result = dpll.solve().expect("the DPLL(T) loop answers");
    (result, thread_round_trips() - before)
}

#[test]
fn a_counted_grant_stops_the_dpll_loop_at_the_same_round_trip_every_time() {
    let (free, needed) = solve(None);
    assert!(
        matches!(free, SatResult::Sat(_)),
        "the ungranted loop accepts after its conflicts"
    );
    assert!(
        needed >= 4,
        "ANTI-VACUITY: the solve must need several round trips, or no grant \
         below it can be tested (needed {needed})"
    );
    let grant = needed - 2;
    let (cut, spent) = solve(Some(grant));
    assert!(
        matches!(cut, SatResult::Unknown),
        "a grant two round trips short of the answer must stop the loop"
    );
    assert_eq!(
        spent,
        grant + 1,
        "the loop runs exactly its granted round trips and stops at the next"
    );
    let (again, spent_again) = solve(Some(grant));
    assert!(matches!(again, SatResult::Unknown));
    assert_eq!(
        spent_again, spent,
        "the same grant stops at the same round trip"
    );
}

/// Negative twin: a grant covering the whole solve changes nothing.
#[test]
fn a_counted_grant_that_covers_the_dpll_loop_admits_its_answer() {
    let (free, needed) = solve(None);
    assert!(matches!(free, SatResult::Sat(_)));
    let (granted, spent) = solve(Some(needed));
    assert!(
        matches!(granted, SatResult::Sat(_)),
        "a grant of exactly the work needed admits the answer"
    );
    assert_eq!(spent, needed);
}
