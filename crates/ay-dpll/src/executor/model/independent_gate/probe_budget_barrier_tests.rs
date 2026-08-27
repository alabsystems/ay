// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Barriers for the quantified model gate's query-owned wall envelope,
// included in `independent_gate::tests` so their fully-qualified test names
// remain stable and the `solved`/`loaded` fixtures are in scope.
//
// Every assertion here is an ACCOUNTING read, never a clock read. The host
// these run on sits at load 30+, so "the gate took N ms" is not a stable
// quantity; "the gate opened N arms and was granted M ms" is decided entirely
// by `probe_budget.rs` and is stable.

/// THE CONVERSION, as a wiring assertion.
///
/// The gate's ground obligation used to be handed a flat `500` at the
/// `checked_ground_solve` call site. On `Inc Equality_MachineArith`'s
/// `exp_loop_true-unreach-call.c.smt2` the positive-existential FP obligation
/// DECIDES `sat`, but needs 1,579-2,426 ms to do it (73 in-situ samples, 73/73
/// decided, zero undecided even at a 60 s budget). Under 500 ms it returned
/// `None`, the gate reported `Indeterminate("nested solve undecided")`, and a
/// `sat` AY had genuinely computed published as `unknown (incomplete)`.
///
/// Restoring `500` at that call site — the exact mutation this barrier exists
/// to kill — puts the cap back below the whole measured band.
#[test]
fn the_gate_ground_probe_asks_for_the_budgeted_cap_not_a_flat_constant() {
    let mut exec = Executor::new();
    let contradiction = exec.ctx.terms.false_term();
    assert!(
        exec.quantified_gate_checked_ground_solve(vec![contradiction])
            .is_some(),
        "the fixture obligation must reach the checked ground solve"
    );

    let asked = exec.quantified_gate_probe_budget.last_probe_cap_ms();
    assert_eq!(
        asked,
        probe_budget::GATE_PROBE_CAP_MS,
        "the gate obligation handed {asked}ms to checked_ground_solve; it must \
         hand the budgeted per-probe cap"
    );
    assert!(
        asked >= 2_426,
        "the gate obligation asks for {asked}ms, below the measured p100 need \
         of 2426ms — every query in the model-gate bucket would still publish \
         `unknown` for a `sat` the nested solve decides"
    );
}

/// THE PUBLICATION ARM IS WIRED TO THE ENVELOPE.
///
/// `apply_quantified_model_failclosed_gate` used to arm a FRESH
/// `Instant::now() + Duration::from_secs(2)` window. Restoring that constant
/// leaves `arms_opened` at zero: the arm no longer draws from the query's
/// envelope, so nothing bounds it across the gate's two arm sites and four
/// publication callers.
#[test]
fn the_publication_gate_arm_draws_its_window_from_the_query_envelope() {
    let mut exec = loaded(
        r#"
            (set-logic AUFLIA)
            (define-fun a ((x Int)) Bool (= x 0))
            (define-fun A () (Array Int Int) ((as const (Array Int Int)) 1))
            (assert (forall ((x Int))
                (=> (a x)
                    (forall ((y Int)) (not (= (select A y) x))))))
        "#,
    );
    exec.begin_external_decision_query(false);
    exec.set_produce_proofs(true);
    exec.last_model = Some(Model::empty());
    assert_eq!(exec.quantified_gate_probe_budget.arms_opened(), 0);

    assert_eq!(
        exec.apply_quantified_model_failclosed_gate(SolveResult::Sat),
        SolveResult::Sat,
        "the fixture must reach — and pass — the gate's candidate loop"
    );
    assert_eq!(
        exec.last_statistics
            .get_string("model_check_gate.quantified"),
        Some("confirmed"),
    );

    assert_eq!(
        exec.quantified_gate_probe_budget.arms_opened(),
        1,
        "the publication gate arm must draw its wall window from the \
         query-owned envelope, not from a fresh per-arm constant"
    );
}

/// THE RESTORATION ARM IS THE SECOND ARM SITE, AND IT SHARES THE ENVELOPE.
///
/// `quantified_model_gate_confirms_current_assertions` runs on the same public
/// `check-sat` as — and BEFORE — the publication gate, and it too used to arm a
/// fresh 2 s window. With both arming fresh constants, one query could pay the
/// gate's ground probes twice over; raising the per-probe cap multiplies that.
/// A revert here leaves `arms_opened` at 1 instead of 2.
#[test]
fn the_restoration_arm_and_the_publication_arm_share_one_envelope() {
    let mut exec = loaded(
        r#"
            (set-logic AUFLIA)
            (define-fun a ((x Int)) Bool (= x 0))
            (define-fun A () (Array Int Int) ((as const (Array Int Int)) 1))
            (assert (forall ((x Int))
                (=> (a x)
                    (forall ((y Int)) (not (= (select A y) x))))))
        "#,
    );
    exec.begin_external_decision_query(false);
    exec.set_produce_proofs(true);
    exec.last_model = Some(Model::empty());

    let _ = exec.quantified_model_gate_confirms_current_assertions();
    let after_restoration = exec.quantified_gate_probe_budget.arms_opened();
    let _ = exec.apply_quantified_model_failclosed_gate(SolveResult::Sat);

    assert_eq!(
        after_restoration, 1,
        "the SAT-restoration confirmation is a gate arm and must draw from the \
         query envelope"
    );
    assert_eq!(
        exec.quantified_gate_probe_budget.arms_opened(),
        2,
        "both gate arm sites on one query must be metered by the SAME envelope"
    );
    assert!(
        exec.quantified_gate_probe_budget.granted_ms() <= probe_budget::QUERY_GATE_BUDGET_MS,
        "two arms were granted {}ms against a {}ms query envelope",
        exec.quantified_gate_probe_budget.granted_ms(),
        probe_budget::QUERY_GATE_BUDGET_MS,
    );
}

/// THE FAN-OUT BARRIER.
///
/// This is the assertion that must hold no matter how many arm sites the gate
/// grows, because it is exactly what `9e5793ba81` violated on the
/// consequence-replay lane: a per-call budget is a MULTIPLIER when nothing caps
/// the call count. It holds for arm counts that do not exist today, so a future
/// edit that adds a fifth publication caller or a third arm site cannot
/// reintroduce the regression without failing here.
#[test]
fn no_number_of_gate_arms_can_exceed_one_query_envelope() {
    let mut exec = Executor::new();
    exec.begin_external_decision_query(false);

    let mut handed_out = 0;
    for _ in 0..64 {
        let arm = exec.quantified_gate_probe_budget.open_arm(None);
        handed_out += arm.window_ms();
        // An arm that burns its whole slice refunds nothing.
        exec.quantified_gate_probe_budget
            .close_arm(arm, arm.window_ms());
    }

    assert_eq!(
        handed_out,
        probe_budget::QUERY_GATE_BUDGET_MS,
        "64 gate arms were handed {handed_out}ms; one query's total gate wall \
         must be the envelope, not the per-arm window times the arm count"
    );
    assert_eq!(exec.quantified_gate_probe_budget.arms_opened(), 64);
}

/// ONLY THE EXTERNAL BOUNDARY REPLENISHES.
///
/// The gate's own probes build disposable executors and the outer query
/// restarts lanes internally; both run `begin_public_solve`. Replenishing
/// there would hand every nested solve a fresh envelope — which is the
/// per-call constant this replaced, wearing a new name.
#[test]
fn a_nested_public_solve_does_not_replenish_the_gate_envelope() {
    let mut exec = Executor::new();
    exec.begin_external_decision_query(false);
    let arm = exec.quantified_gate_probe_budget.open_arm(None);
    exec.quantified_gate_probe_budget
        .close_arm(arm, arm.window_ms());
    assert_eq!(exec.quantified_gate_probe_budget.remaining_ms(), 0);

    exec.begin_public_solve(false);
    assert_eq!(
        exec.quantified_gate_probe_budget.remaining_ms(),
        0,
        "an internal solve boundary must not replenish the query's gate envelope"
    );

    exec.begin_external_decision_query(false);
    assert_eq!(
        exec.quantified_gate_probe_budget.remaining_ms(),
        probe_budget::QUERY_GATE_BUDGET_MS,
        "the external decision-query boundary is what re-arms the envelope"
    );
}

/// THE DEADLINE-SHARE GUARD, WHICH THE GATE DID NOT HAVE.
///
/// `ConsequenceReplayProbeBudget::claim` caps a probe at half the caller's
/// remaining deadline precisely so the lane cannot consume a short caller
/// timeout down to zero. The gate arm had no such rule: under `-T` with 2.5 s
/// left it could take a 2 s window and leave nothing for `check_scope.finish`,
/// model emission, or a following `(get-model)`. That is the `9e5793ba81`
/// failure mode transplanted, so the guard is barriered here on a real
/// executor deadline rather than only in the module's own unit tests.
#[test]
fn a_gate_arm_leaves_the_caller_half_its_remaining_deadline() {
    let mut exec = Executor::new();
    exec.begin_external_decision_query(false);
    let deadline = ay_core::time::Instant::now() + std::time::Duration::from_millis(2_000);
    exec.set_deadline(Some(deadline));

    let arm = exec
        .quantified_gate_probe_budget
        .open_arm(exec.solve_deadline.get());

    assert!(
        arm.window_ms() <= 1_000,
        "a gate arm claimed {}ms of a 2000ms remaining deadline; publication \
         needs a share of that clock too",
        arm.window_ms()
    );
    assert!(
        arm.deadline() < deadline,
        "the arm window must end strictly before the caller's own deadline"
    );
}
