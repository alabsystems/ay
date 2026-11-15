// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The terminator ends a solve within one poll, as an unknown answer.

use super::*;

/// PHP(pigeons, pigeons - 1): UNSAT, and exponential for kitten's CDCL.
fn pigeonhole(k: &mut Kitten, pigeons: u32) {
    let holes = pigeons - 1;
    let var = |p: u32, h: u32| (p * holes + h) * 2;
    let mut id = 0;
    for p in 0..pigeons {
        let clause: Vec<u32> = (0..holes).map(|h| var(p, h)).collect();
        k.add_clause_with_id(id, &clause, INVALID);
        id += 1;
    }
    for h in 0..holes {
        for p in 0..pigeons {
            for q in p + 1..pigeons {
                k.add_clause_with_id(id, &[var(p, h) ^ 1, var(q, h) ^ 1], INVALID);
                id += 1;
            }
        }
    }
    k.seal_original();
}

fn raised() -> Terminator {
    Terminator::new(Some(Arc::new(AtomicBool::new(true))), None)
}

/// The tick limit is only the test's backstop: without the terminator the
/// solve runs to it, and the tick assertion fails instead of hanging.
#[test]
fn raised_terminator_ends_a_solve_within_one_poll() {
    let mut k = Kitten::new();
    pigeonhole(&mut k, 10);
    k.set_ticks_limit(50_000_000);
    k.set_terminator(raised());
    assert_eq!(k.solve(), 0, "a stopped solve answers unknown");
    assert!(
        k.current_ticks() <= TERMINATOR_POLL_TICKS,
        "the solve ran {} ticks past a raised stop",
        k.current_ticks()
    );

    // The stop stays latched, so the next solve ends at once too.
    let before = k.current_ticks();
    assert_eq!(k.solve(), 0);
    assert!(k.current_ticks() - before <= TERMINATOR_POLL_TICKS);
}

/// An expired deadline stops a solve under assumptions, which are reset as
/// for any unknown answer; a new terminator clears the stop, and the solves
/// after it answer as before.
#[test]
fn expired_deadline_stops_a_solve_and_a_new_terminator_clears_it() {
    let mut k = Kitten::new();
    pigeonhole(&mut k, 5);
    k.set_terminator(Terminator::new(None, Some(ay_core::time::Instant::now())));
    k.assume(0);
    assert_eq!(k.solve(), 0);

    k.set_terminator(Terminator::default());
    k.assume(0);
    assert_eq!(k.solve(), 20, "PHP(5,4) is UNSAT");
}

/// A terminator that never fires changes no answer.
#[test]
fn unraised_terminator_changes_no_answer() {
    let flag = Arc::new(AtomicBool::new(false));
    let mut k = Kitten::new();
    pigeonhole(&mut k, 5);
    k.set_terminator(Terminator::new(Some(flag), None));
    assert_eq!(k.solve(), 20);

    let mut k = Kitten::new();
    k.add_clause_with_id(0, &[0, 2], INVALID);
    k.add_clause_with_id(1, &[1, 2], INVALID);
    k.seal_original();
    k.set_terminator(Terminator::new(
        Some(Arc::new(AtomicBool::new(false))),
        None,
    ));
    assert_eq!(k.solve(), 10);
    assert!(k.value(2) > 0, "x1 is forced once x0 is decided either way");
}

#[derive(Clone, Copy)]
enum TerminalInput {
    EmptySat,
    OriginalEmpty,
    ContradictoryUnits,
}

fn add_terminal_input(k: &mut Kitten, input: TerminalInput) -> i32 {
    let result = match input {
        TerminalInput::EmptySat => 10,
        TerminalInput::OriginalEmpty => {
            k.add_clause_with_id(0, &[], INVALID);
            20
        }
        TerminalInput::ContradictoryUnits => {
            k.add_clause_with_id(0, &[0], INVALID);
            k.add_clause_with_id(1, &[1], INVALID);
            20
        }
    };
    k.seal_original();
    result
}

fn terminal_inputs() -> [TerminalInput; 3] {
    [
        TerminalInput::EmptySat,
        TerminalInput::OriginalEmpty,
        TerminalInput::ContradictoryUnits,
    ]
}

#[test]
fn a_raised_stop_refuses_empty_sat_and_original_unit_refutations() {
    for input in terminal_inputs() {
        let mut k = Kitten::new();
        let expected = add_terminal_input(&mut k, input);
        k.set_terminator(raised());
        assert_eq!(k.solve(), 0);
        assert_eq!(k.current_ticks(), 0, "no search after an entry stop");
        // A NEW query explicitly rebound to a healthy terminator keeps the
        // original logical answer; the stop never erases the original input.
        k.set_terminator(Terminator::default());
        assert_eq!(k.solve(), expected);
    }
}

#[test]
fn an_expired_deadline_refuses_every_tiny_terminal_input() {
    for input in terminal_inputs() {
        let mut k = Kitten::new();
        let expected = add_terminal_input(&mut k, input);
        k.set_terminator(Terminator::new(None, Some(ay_core::time::Instant::now())));
        assert_eq!(k.solve(), 0);
        assert_eq!(k.current_ticks(), 0);
        k.set_terminator(Terminator::default());
        assert_eq!(k.solve(), expected);
    }
}

#[test]
fn a_latched_stop_survives_clear_for_empty_sat_and_refutations() {
    for input in terminal_inputs() {
        let flag = Arc::new(AtomicBool::new(true));
        let mut k = Kitten::new();
        k.set_terminator(Terminator::new(Some(Arc::clone(&flag)), None));
        assert_eq!(k.solve(), 0);
        k.clear();
        flag.store(false, Ordering::Relaxed);
        let expected = add_terminal_input(&mut k, input);
        assert_eq!(
            k.solve(),
            0,
            "clear/lowered raw flag cannot renew a latched owner"
        );
        k.set_terminator(Terminator::default());
        assert_eq!(k.solve(), expected);
    }
}

#[test]
fn an_early_stopped_solve_drops_assumptions_before_a_new_healthy_query() {
    let mut k = Kitten::new();
    k.add_clause_with_id(0, &[0, 2], INVALID);
    k.seal_original();
    k.assume(0);
    k.set_terminator(raised());
    assert_eq!(k.solve(), 0);
    assert!(k.assumptions.is_empty());
    k.set_terminator(Terminator::default());
    k.assume(1);
    assert_eq!(
        k.solve(),
        10,
        "stale x must not clash with the new query's not-x"
    );
    assert!(k.value(1) > 0);
    assert!(k.value(2) > 0);
}

#[test]
fn a_stop_after_a_previous_sat_answer_stays_unknown_and_rebinds_cleanly() {
    let mut k = Kitten::new();
    k.add_clause_with_id(0, &[0], INVALID);
    k.enable_antecedent_tracking();
    k.seal_original();
    assert_eq!(k.solve(), 10);
    k.assume(1);
    k.set_terminator(raised());
    assert_eq!(
        k.solve(),
        0,
        "an assumption refutation cannot escape the stop"
    );
    assert!(k.assumptions.is_empty());
    assert_eq!(k.failing, INVALID);
    assert!(k.failed.iter().all(|failed| !failed));
    assert!(k.core.is_empty());
    k.set_terminator(Terminator::default());
    k.assume(0);
    assert_eq!(k.solve(), 10, "no stale failed assumption after the stop");
}
