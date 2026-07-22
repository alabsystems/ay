// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! COMPILE-TIME lock for the primal worker-return split (design §3.2 of
//! the development design notes).
//!
//! The parallel optimization portfolio spawns its PRIMAL workers (LNS / SLS)
//! through `portfolio::spawn_primal_optimization_worker`, whose SIGNATURE makes
//! a primal verdict structurally impossible: the run type
//! (`portfolio::PrimalWorkerRun`) returns `()` — not a `PbSolution` — and the
//! only channel handle it receives is a `portfolio::PrimalSender`, whose sole
//! public emit surface is `send_improvement` (the already-verdict-free
//! incumbent stream). The coordinator's `WorkerMsg::Done` (the carrier of
//! `OptimumFound`/`Unsatisfiable`) is a private type a primal run cannot name,
//! construct, or send.
//!
//! These UI cases pin that property AT COMPILE TIME: if a refactor ever lets a
//! primal run return a solution or reach a verdict channel, the compile-fail
//! expectations below break the build. The `pass` case is the non-vacuity
//! control (the compile-fails must fail for the RIGHT reason, not because the
//! legitimate surface broke).

#[test]
fn primal_worker_is_structurally_verdict_incapable() {
    let t = trybuild::TestCases::new();
    // Non-vacuity: a legitimate improvement-only primal run COMPILES.
    t.pass("tests/ui/primal_run_improvement_only_ok.rs");
    // A primal run cannot RETURN a verdict-carrying `PbSolution`.
    t.compile_fail("tests/ui/primal_run_cannot_return_solution.rs");
    // A primal run cannot SEND a verdict: `PrimalSender` has no such method,
    // and the `WorkerMsg::Done` carrier is private and unnameable.
    t.compile_fail("tests/ui/primal_sender_cannot_send_done.rs");
}

/// COMPILE-TIME lock for the SharedBounds lb TYPED-BY-SOURCE rule (design
/// §2.7 of the same doc): `publish_lb` accepts only a `GlobalSoundFloor`,
/// whose constructors are all `pub(crate)` and exist solely for AUDITED
/// globally-sound floor derivations. Un-audited code can READ the bus (the
/// prune-only surface) but cannot fabricate a floor to feed the `ub == lb`
/// OPTIMUM upgrade.
#[test]
fn shared_bounds_lb_is_typed_by_source() {
    let t = trybuild::TestCases::new();
    // Non-vacuity: the unprivileged read-only surface COMPILES.
    t.pass("tests/ui/shared_bounds_read_only_ok.rs");
    // A floor cannot be forged by struct literal or constructor call.
    t.compile_fail("tests/ui/shared_bounds_lb_requires_audited_source.rs");
}
