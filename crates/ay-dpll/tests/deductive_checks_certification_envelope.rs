// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #certification-envelope-isolation — the consumer-shaped pin.
//!
//! THE DEFECT. `Executor::set_deadline` is the COMMAND-level deadline: it
//! moves both the search wall (`solve_deadline`) and the certification
//! envelope (`certification_deadline`). Five search lanes — the CEGQI
//! per-universal refutation, the ground-witness legs, the
//! constant-interpretation certificate and the quantified model-gate arms —
//! claimed their 300 ms / per-arm slices through that same setter and
//! restored through it from a snapshot of `solve_deadline` alone. Whenever
//! such a lane ran while another lane held the search wall narrowed, the
//! restore wrote that narrowed value into the certification envelope, and
//! from then on every mandatory-certification lane that polls the envelope
//! (`TrustClauseDischargeControls::stop_requested`, step (4)'s
//! `resources_live`) read "expired" while the command still had seconds
//! left. Measured on deductive-checks's `replay_push_appends_entailed` obligation
//! (ay `501caafdf`, deductive-checks `e152f1b9`):
//!
//! ```text
//! RECONFIRM(4) ENTER: certification_deadline_remaining_ms=Some(0)
//!                     solve_deadline_remaining_ms=Some(11094)
//! computed UNSAT rejected by mandatory strict certification: strict UNSAT
//!   proof validation failed: step t5 uses unverified trust rule;
//!   deferred-trust discharge failed: no collected trust clause is a
//!   standalone theory tautology (collected 5) AND the authored assertions
//!   could not be independently re-solved as UNSAT
//! ```
//!
//! The funnel started reading `certification_deadline` in `f704330f29`
//! ("harden MODEL_CHECKER_CONSUMER scale ghost solving"), which is the commit deductive-checks
//! bisected the regression to; before it, step (4) inherited
//! `solve_deadline`, which those lanes DO restore correctly, so the clobber
//! was invisible. The fix is `Executor::set_search_deadline`, which narrows
//! and restores the search wall only; the certification envelope now moves
//! only at the command boundary.
//!
//! WHAT IS PINNED HERE. The captured deductive-checks query certifies under the
//! consumer's posture — `unsat`, never the DECIDED-then-WITHHELD class. The
//! contract halves (the setter leaves the envelope alone; an expired search
//! slice does not starve the corroborating re-solve) and the negative control
//! (an injected trust step over a satisfiable problem is still refused) live
//! beside the funnel in `executor/unsat_cert.rs`'s test module.
//!
//! POSTURE. The fixture is a byte-exact `--dump-query-dir` capture of the
//! query deductive-checks's `ay_refutation_loop_realbody::replay_push_appends_entailed`
//! sends, option set included. deductive-checks drives it through
//! `Solver::set_timeout(30_000)`; the dump does not serialise that, so
//! `solve()` re-installs a wall via `(set-option :timeout …)` the way
//! `deductive_checks_seq_length_frame_withholding.rs` does. The wall here is 60 s
//! rather than 30 s: measured at the fix, one solve of this query costs
//! 18.2-18.9 s on an idle box (six consecutive runs), and a loaded box would
//! turn a 30 s replay into a `Timeout` that says nothing about the class
//! this test exists to pin. A `Timeout` still FAILS the test — it is reported
//! as a cost problem, not as the withholding regression.

use std::path::PathBuf;
use std::time::Instant;

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

const FIXTURE: &str = "refutation_loop_push_appends_entailed.smt2";

/// `UnknownReason` spellings that mean ay DECIDED and then WITHHELD.
const DECIDED_THEN_WITHHELD: &[&str] = &["SelfCheckRejected", "ProofTrusted", "InternalError"];

fn fixture(name: &str) -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/deductive_checks_certification_envelope")
        .join(name);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

fn solve(name: &str) -> (String, Option<String>, f64) {
    let script = format!("(set-option :timeout 60000)\n{}", fixture(name));
    let commands = parse(&script).unwrap_or_else(|e| panic!("parse {name}: {e}"));
    let mut executor = Executor::new();
    let started = Instant::now();
    let outputs = executor
        .execute_all(&commands)
        .unwrap_or_else(|e| panic!("execute {name}: {e}"));
    let elapsed = started.elapsed().as_secs_f64();
    let verdict = outputs
        .iter()
        .find(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
        .cloned()
        .unwrap_or_else(|| "<no verdict>".into());
    let reason = executor.unknown_reason().map(|r| format!("{r:?}"));
    (verdict, reason, elapsed)
}

/// The captured deductive-checks obligation certifies: the deferred-trust funnel
/// runs its lanes under a LIVE certification envelope and publishes `unsat`.
#[test]
#[timeout(180_000)]
fn deductive_checks_push_appends_entailed_query_certifies_under_a_live_envelope() {
    let (verdict, reason, elapsed) = solve(FIXTURE);
    eprintln!("{FIXTURE}: {verdict} ({reason:?}) in {elapsed:.2}s");
    let withheld = verdict == "unknown"
        && reason
            .as_deref()
            .is_some_and(|r| DECIDED_THEN_WITHHELD.iter().any(|w| r.contains(w)));
    assert!(
        !withheld,
        "{FIXTURE} was DECIDED and then WITHHELD ({reason:?}): the certification \
         envelope was narrowed by a search lane again — see \
         `Executor::set_search_deadline`"
    );
    assert_eq!(
        verdict, "unsat",
        "{FIXTURE} must certify as unsat; got {verdict} ({reason:?}) after {elapsed:.2}s — \
         a Timeout here is a cost regression, not the withholding class"
    );
}
