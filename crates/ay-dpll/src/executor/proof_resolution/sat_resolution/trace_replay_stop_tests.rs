// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The executor hands its assembly stop to the SAT-trace replay rung.

use std::sync::atomic::AtomicBool;
use std::sync::Arc;

use ay_core::{time::Instant, Proof, Sort};
use ay_sat::{ClauseTrace, Literal, Variable};

use crate::executor::Executor;

/// An executor holding the trace of `p`, `(not p)` and the hinted empty
/// clause, and the proof with those two leaves.
fn primed() -> (Executor, Proof) {
    let mut exec = Executor::new();
    let p = exec.ctx.terms.mk_var("replay_wire_p", Sort::Bool);
    let not_p = exec.ctx.terms.mk_not(p);
    let mut proof = Proof::new();
    proof.add_assume(p, None);
    proof.add_assume(not_p, None);
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable::new(0))], true);
    trace.add_clause(2, vec![Literal::negative(Variable::new(0))], true);
    trace.add_clause_with_hints(3, Vec::new(), false, vec![1, 2]);
    exec.last_clause_trace = Some(trace);
    exec.last_var_to_term = Some([(0, p)].into_iter().collect());
    exec.last_negations = Some(Default::default());
    (exec, proof)
}

/// The rung is called directly, past the ladder's own per-rung poll, so only
/// the replay's poll can stop it: an interrupt, or an expired certification
/// deadline.
#[test]
fn a_fired_stop_reaches_the_trace_replay_rung() {
    let (mut unstopped, mut proof) = primed();
    assert!(
        unstopped.try_derive_empty_via_sat_resolution(&mut proof),
        "the unstopped rung replays the trace to the empty clause"
    );

    let stops = [
        (Some(Arc::new(AtomicBool::new(true))), None),
        (None, Some(Instant::now())),
    ];
    for (interrupt, deadline) in stops {
        let (mut exec, mut proof) = primed();
        exec.set_solve_controls(interrupt, deadline);
        assert!(
            !exec.try_derive_empty_via_sat_resolution(&mut proof),
            "the executor must hand its stop to the replay"
        );
        assert_eq!(
            proof.steps.len(),
            2,
            "no trace entry was replayed: {proof:?}"
        );
    }
}
