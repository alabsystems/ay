// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! D10(c): the push depths of the scope-tracked roots are captured once per
//! query (`with_scope_root_depths`), never read off positions in whatever
//! working window a route installed in `ctx.assertions`. (D10(a), the scoped
//! assumption solve on fresh lanes, is pinned in
//! `check_sat_assuming/stateless_subsolve_tests.rs`.)

use std::cell::RefCell;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::Arc;

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::TermId;
use ay_frontend::parse;

use super::Executor;
use crate::incremental_state::IncrementalTheoryState;

thread_local! {
    static FIRST_CAPTURE: RefCell<Option<Arc<HashMap<TermId, usize>>>> =
        const { RefCell::new(None) };
}

/// Test builds only: `with_scope_root_depths` reports every outermost
/// capture here, and the FIRST one since the last [`take_first_capture`] is
/// kept — the capture of the entry a test called, not of a nested executor.
pub(super) fn record_first_capture(depths: &Arc<HashMap<TermId, usize>>) {
    FIRST_CAPTURE.with(|slot| {
        slot.borrow_mut().get_or_insert_with(|| Arc::clone(depths));
    });
}

fn take_first_capture() -> Option<Arc<HashMap<TermId, usize>>> {
    FIRST_CAPTURE.with(|slot| slot.borrow_mut().take())
}

fn executor_with_assertion() -> Executor {
    let commands = parse(
        r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        "#,
    )
    .expect("test SMT should parse");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("test SMT setup should execute");
    exec
}

/// D10(c): the roots' depths are read off the frames once, before any
/// route installs a working window in `ctx.assertions`; a nested entry
/// keeps the outer capture, and nothing outlives the query.
#[test]
fn scope_root_depths_are_captured_at_the_outermost_entry_only() {
    let commands = parse(
        r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (> x 0))
        (push 1)
        (assert (< x 5))
        "#,
    )
    .expect("test SMT should parse");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("test SMT setup should execute");
    let roots = exec.ctx.assertions.clone();
    assert_eq!(roots.len(), 2, "two roots expected, got {roots:?}");
    let (base, scoped) = (roots[0], roots[1]);
    assert!(
        exec.activation_root_depths().is_empty(),
        "no query, no roots"
    );

    exec.with_scope_root_depths(|outer| {
        let depths = outer.activation_root_depths();
        assert_eq!(depths.get(&base), Some(&0));
        assert_eq!(depths.get(&scoped), Some(&1));
        // A route installs a working window whose positions say nothing
        // about the frames: the nested entry must not re-read them.
        outer.ctx.assertions = vec![scoped, base];
        outer.with_scope_root_depths(|inner| {
            assert!(Arc::ptr_eq(&inner.activation_root_depths(), &depths));
        });
        outer.ctx.assertions = vec![base, scoped];
    });
    assert!(
        exec.scope_root_depths.is_none(),
        "the capture must be released when the outermost entry returns"
    );
}

/// D10(c): with `:produce-unsat-cores`, the named-core entry moves the named
/// roots out of `ctx.assertions` into the assumptions before it solves. Read
/// off that stripped vector, the root asserted inside the push sits where the
/// depth-0 frame's count says depth 0, and any lane encoding it would make a
/// scoped root permanent. The entry captures before its redirect.
#[test]
fn named_core_entry_captures_before_the_redirect_strips_named_roots() {
    let commands = parse(
        r#"
        (set-option :produce-unsat-cores true)
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (! (> x 0) :named n0))
        (push 1)
        (assert (< x 5))
        "#,
    )
    .expect("test SMT should parse");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("test SMT setup should execute");
    let roots = exec.ctx.assertions.clone();
    assert_eq!(roots.len(), 2, "two roots expected, got {roots:?}");
    let (named, scoped) = (roots[0], roots[1]);

    let _ = take_first_capture();
    let result = exec
        .check_sat_assuming_with_named_cores(&[])
        .expect("the query should run");
    assert!(!result.is_unsat(), "x = 1 satisfies both roots");
    let captured = take_first_capture().expect("the query captured its roots");
    assert_eq!(
        captured.get(&named),
        Some(&0),
        "the named root is permanent"
    );
    assert_eq!(
        captured.get(&scoped),
        Some(&1),
        "the scoped root dies at the pop; captured {captured:?}"
    );
    assert_eq!(
        exec.ctx.assertions, roots,
        "the redirect restores the stack"
    );
}

#[test]
fn scope_root_depths_are_released_after_panic() {
    let mut exec = executor_with_assertion();
    let panic = catch_unwind(AssertUnwindSafe(|| {
        exec.with_scope_root_depths(|_| panic!("sentinel capture panic"));
    }));
    assert!(panic.is_err(), "test panic should propagate");
    assert!(
        exec.scope_root_depths.is_none(),
        "a panicking query must not leave its roots for the next one"
    );
}

/// Derived-assertion provenance describes one query's roots: the next
/// query must not activate a term at a depth an earlier query computed.
#[test]
fn derived_assertion_provenance_is_dropped_at_the_query_boundary() {
    let mut exec = executor_with_assertion();
    let term = *exec.ctx.assertions.first().expect("setup asserts one term");
    let mut state = IncrementalTheoryState::new();
    state.replace_lia_derived_assertions([(term, 0, vec![term])]);
    exec.incr_theory_state = Some(state);
    exec.with_scope_root_depths(|this| {
        assert!(this
            .incr_theory_state
            .as_ref()
            .is_some_and(|state| state.lia_derived_assertions.is_empty()));
    });
}

/// The LIA route's derived-assertion depths come from the captured roots,
/// not from positions in the window installed in `ctx.assertions`: with the
/// scoped root first, a positional read would give it depth 0 — a
/// permanent activation for an assertion that dies at the next pop.
#[test]
fn lia_derived_assertion_depths_come_from_the_captured_roots() {
    let commands = parse(
        r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (> x 0))
        (push 1)
        (assert (< x 5))
        "#,
    )
    .expect("test SMT should parse");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("test SMT setup should execute");
    let roots = exec.ctx.assertions.clone();
    let (base, scoped) = (roots[0], roots[1]);
    exec.with_scope_root_depths(|this| {
        this.ctx.assertions = vec![scoped, base];
        // The provenance is installed before the solve; its verdict is
        // not what this pins.
        let _ = this.solve_lia_incremental();
        let depth_of = |term| {
            this.incr_theory_state.as_ref().and_then(|state| {
                state
                    .lia_derived_assertions
                    .get(&term)
                    .map(|meta| meta.activation_depth)
            })
        };
        assert_eq!(depth_of(scoped), Some(1), "the scoped root dies at the pop");
        assert_eq!(depth_of(base), Some(0), "the base root is permanent");
        this.ctx.assertions = vec![base, scoped];
    });
}

/// `leak_liadiv_9251_01603` (2026-09-29 scope-leak fix-up), delta-debugged. z3
/// 5.1.0: `unsat sat unsat sat`. The plain check's QF_NIA lazy split loop
/// bails on unbounded drift; the `(assert false)` scope then must not outlive
/// its pop.
const LEAKED_FRAME_WITNESS: &str = r#"
(set-logic ALL)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun p0 () Bool)
(declare-fun p1 () Bool)
(assert (distinct (div (div x2 2) (* 3 x3)) 2))
(assert (>= (- (* (- 3) x3) (mod 1 x3)) 0))
(assert (=> p0 (= (+ (+ 3 x3) x0) (- 5))))
(assert (=> p1 (>= (mod 5 x1) 0)))
(check-sat-assuming ((not p1) p1))
(assert (>= (+ x3 (div (- 3) x2)) 0))
(check-sat)
(push 1)
(assert false)
(check-sat)
(pop 1)
(check-sat)
"#;

/// The lazy split loops (the lazy arm of `solve_nia` / `solve_lia`, and the
/// assume arm) run inside ONE private frame of the session's persistent SAT
/// solver per check-sat, and every exit must pop it. The unbounded-drift bail
/// (#1836) did not: the solver's selectors then ran one level deeper than the
/// session's scopes, a root activated for its own scope was guarded by the
/// leaked frame, and the user's `(pop 1)` popped the wrong selector — the
/// scoped `false` stayed active and `--z3-mode` refuted the last check. After
/// every command the persistent solver must be exactly as deep as the session.
#[test]
fn persistent_sat_frames_stay_in_step_with_the_session_scopes() {
    let commands = parse(LEAKED_FRAME_WITNESS).expect("test SMT should parse");
    let mut exec = Executor::new();
    exec.set_timeout(Some(std::time::Duration::from_secs(10)));
    exec.set_competition_mode(true);
    let mut verdicts = Vec::new();
    for (index, command) in commands.iter().enumerate() {
        let output = exec.execute(command).expect("test SMT should execute");
        verdicts.extend(output.filter(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown")));
        let depths = exec.incr_theory_state.as_ref().and_then(|state| {
            state
                .persistent_sat
                .as_ref()
                .map(|sat| (sat.scope_depth(), state.scope_depth))
        });
        if let Some((sat_depth, session_depth)) = depths {
            assert_eq!(
                sat_depth, session_depth,
                "after command {index} ({command:?}) the persistent SAT solver is {sat_depth} \
                 frames deep but the session {session_depth}: a check-sat left a private frame"
            );
        }
    }
    assert_eq!(verdicts.len(), 4, "four answers expected: {verdicts:?}");
    assert_ne!(
        verdicts[1], "unsat",
        "the plain check is sat (z3): {verdicts:?}"
    );
    assert_ne!(
        verdicts[3], "unsat",
        "the check after the pop is sat (z3): {verdicts:?}"
    );
}
