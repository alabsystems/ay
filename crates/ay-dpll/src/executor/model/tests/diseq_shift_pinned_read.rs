// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #qf-auflia-diseq-shift / #subst-key-no-default / #repair-fallback-unrepaired
//! / #qfax-sk-witness-route: a model repair may never falsify an assertion the
//! candidate already satisfies, and a correct search model must not be thrown
//! away by the gate.
//!
//! ROOT CAUSE (measured on the SMT-COMP `storecomm_invalid_*_pp_sf_*` family,
//! 0/108 solved while z3 answers `sat` in 0.02 s, and on the 6-assertion
//! minimum below): on the LIA-less array+EUF lane the element aliases
//! `x = A[i]`, `y = B[i]` are recorded substitution KEYS with no model slot;
//! the evaluator fabricated 0 for both, so completion's fill-only derivation
//! never replaced them with their reads, the asserted `(not (= x y))` looked
//! violated, the `#qf-auflia-diseq-shift` repair (whose own collision test
//! read absent slots as 0) moved `x` to the `1_000_003` sentinel and pushed
//! the phantom 0 into the array, and the strict arrays oracle refuted
//! `(= x (select A i))` — a pin the search's model satisfied.
//!
//! Fixes pinned here:
//!   1. `evaluate_var` no longer fabricates 0 for a substitution key when no
//!      arithmetic model exists — the key is derived from its RHS by model
//!      completion (the same contract the BitVec branch already had);
//!   2. the diseq-shift's collision test uses `evaluate_term` (the strict
//!      oracle's own value semantics) and never moves a side it can see
//!      differs from its peer;
//!   3. fail-closed fallback: when the REPAIRED witness is refuted, the
//!      identical strict oracle re-runs on the candidate the repair started
//!      from, and the full validation pipeline still decides acceptance;
//!   4. `#qfax-isolated-lane-retry`: a gate refutation of a model PUBLISHED by
//!      the LIA-less isolated array+EUF ladder arms one combiner re-solve
//!      (`check_sat_guarded`), so the SMT-COMP shape is decided by
//!      `solve_auf_lia` — whose `has_substantive_int_constraints` clause
//!      `is_int_uf_app_with_array_arg` already classifies `(sk A B)` as
//!      needing LIA — and gate-confirmed. Reconciling the two routing
//!      predicates up front instead was MEASURED to cost three files the
//!      isolated route decides in under 0.25 s, so the disagreement is
//!      resolved reactively: the first pass is unchanged for every file and
//!      only an already-rejected verdict pays a second solve.
//!
//! Every `sat` below is re-established two independent ways: AY's own
//! validation pipeline must have ACCEPTED the witness
//! (`last_model_validated`), and the separate `ay-model-check` gate must
//! `ConfirmedSat` it concretely.

use super::*;
use ay_frontend::parse;
use ay_model_check::GateVerdict;

/// Solve `input` through the full executor pipeline (independent gate included).
fn solve(input: &str) -> (Executor, String) {
    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute succeeds");
    let verdict = outputs.into_iter().next().expect("a check-sat verdict");
    (exec, verdict)
}

/// The verdict must be `sat` AND the emitted witness must validate, checked
/// two independent ways:
///
///  1. `last_model_validated` — AY's OWN postcondition that the full
///     fail-closed validation pipeline (strict definitive-false oracles, the
///     coverage policy, the array/EUF gates) accepted the emitted witness. A
///     `sat` published with this false is the #7912 violation these tests
///     exist to catch, and it is exactly what a repair that falsifies an
///     already-satisfied assertion produces.
///  2. `confirm_sat_with_independent_gate` — the SEPARATE `ay-model-check`
///     evaluator, which must ground-confirm every assertion concretely.
///
/// Deliberately NOT a third pass with `Executor::evaluate_term`: that
/// evaluator answers `Bool(false)` for a satisfied ARRAY equality whose sides
/// are a model array value and a `store` chain over another one (measured on
/// `(= r1 (store a1 3 e3))` in `storecomm_pp_sf_shape_is_sat_with_validated_model`,
/// whose emitted model gives both sides the identical
/// `(store (store ((as const (Array Int Int)) 8) 4 1000003) 3 0)`), so it
/// raises false alarms the two real gates correctly reject. Both gates below
/// are the ones that actually license publication.
fn assert_sat_with_validated_witness(exec: &Executor, verdict: &str, what: &str) {
    assert_eq!(verdict, "sat", "{what}: z3 answers sat; got {verdict}");
    assert!(
        exec.last_model_validated,
        "{what}: sat was published WITHOUT the validation pipeline accepting \
         the witness (`last_model_validated == false`)"
    );
    assert!(
        exec.last_model.is_some(),
        "{what}: sat was published with no model at all"
    );
    match exec.confirm_sat_with_independent_gate() {
        GateVerdict::ConfirmedSat => {}
        GateVerdict::ModelViolates { assertion } => panic!(
            "{what}: sat shipped an INVALID model — the independent gate \
             ground-refuted assertion {assertion:?}"
        ),
        GateVerdict::CannotConfirm { reason } => panic!(
            "{what}: sat shipped a model the independent gate could not \
             concretely confirm ({reason})"
        ),
    }
}

/// The 6-assertion minimum of the storecomm `pp_sf` defect with a FREE Int
/// witness index (no Skolem at all): `A` and `B` are same-base store chains
/// that differ at index 1 (`A[1] = e1`, `B[1] = a1[1]`) and at 3. Pre-fix the
/// search found `i = 1, x = 0, y = 4`, the shift moved `x` to the sentinel
/// because its lookup read `y` as 0, and `(= x (select A i))` was refuted.
#[test]
fn free_index_read_pins_survive_the_diseq_shift() {
    let (exec, verdict) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a1 () (Array Int Int))
        (declare-fun e1 () Int)
        (declare-fun e2 () Int)
        (declare-fun e3 () Int)
        (declare-fun i () Int)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun A () (Array Int Int))
        (declare-fun B () (Array Int Int))
        (assert (= A (store (store a1 1 e1) 2 e2)))
        (assert (= B (store (store a1 2 e2) 3 e3)))
        (assert (= x (select A i)))
        (assert (= y (select B i)))
        (assert (not (= x y)))
        (check-sat)
        "#,
    );
    assert_sat_with_validated_witness(&exec, &verdict, "free-index read pins");
}

/// Same shape with the SMT-COMP skolemized-extensionality witness
/// `(= i (sk A B))` — the `pp_sf` encoding proper. This is the shape the
/// isolated LIA-less ladder answers with a model the gates refute; the
/// `#qfax-isolated-lane-retry` combiner re-solve is what makes it `sat`.
#[test]
fn skolem_witness_read_pins_survive_the_diseq_shift() {
    let (exec, verdict) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a1 () (Array Int Int))
        (declare-fun e1 () Int)
        (declare-fun e2 () Int)
        (declare-fun e3 () Int)
        (declare-fun i () Int)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun A () (Array Int Int))
        (declare-fun B () (Array Int Int))
        (declare-fun sk ((Array Int Int) (Array Int Int)) Int)
        (assert (= A (store (store a1 1 e1) 2 e2)))
        (assert (= B (store (store a1 2 e2) 3 e3)))
        (assert (= x (select A i)))
        (assert (= y (select B i)))
        (assert (= i (sk A B)))
        (assert (not (= x y)))
        (check-sat)
        "#,
    );
    assert_sat_with_validated_witness(&exec, &verdict, "skolem-witness read pins");
}

/// `storecomm_invalid_*_pp_sf_*` at size 4: two sf-flattened (aliased) store
/// chains over one base, the right chain a permutation of the left plus ONE
/// extra write (index 4), the witness index skolemized, and the element
/// aliases compared for disequality. z3: sat. At the SMT-COMP sizes (10..60)
/// this was an instant `unknown` (`strict model-validation oracle arrays
/// rejected assertion N`); at THIS size the pre-fix binary still answered
/// `sat` — measured with `--model-reject-dump`: `[diseq-shift] el := 1000003
/// (was 0, collided with er ...)` fired and the pin re-route rescued it. It
/// is therefore the live "shift fires, witness still validates" pin: it must
/// keep answering `sat` with a validated model whether or not the shift runs.
#[test]
fn storecomm_pp_sf_shape_is_sat_with_validated_model() {
    let (exec, verdict) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a1 () (Array Int Int))
        (declare-fun e1 () Int)
        (declare-fun e2 () Int)
        (declare-fun e3 () Int)
        (declare-fun e4 () Int)
        (declare-fun l1 () (Array Int Int))
        (declare-fun l2 () (Array Int Int))
        (declare-fun l3 () (Array Int Int))
        (declare-fun r1 () (Array Int Int))
        (declare-fun r2 () (Array Int Int))
        (declare-fun r3 () (Array Int Int))
        (declare-fun r4 () (Array Int Int))
        (declare-fun el () Int)
        (declare-fun er () Int)
        (declare-fun i () Int)
        (declare-fun sk ((Array Int Int) (Array Int Int)) Int)
        (assert (= l1 (store a1 1 e1)))
        (assert (= l2 (store l1 2 e2)))
        (assert (= l3 (store l2 3 e3)))
        (assert (= r1 (store a1 3 e3)))
        (assert (= r2 (store r1 4 e4)))
        (assert (= r3 (store r2 1 e1)))
        (assert (= r4 (store r3 2 e2)))
        (assert (= el (select l3 i)))
        (assert (= er (select r4 i)))
        (assert (= i (sk l3 r4)))
        (assert (not (= el er)))
        (check-sat)
        "#,
    );
    assert_sat_with_validated_witness(&exec, &verdict, "storecomm pp_sf size 4");
}

/// The shape the shift was written for: store-chain indices that appear ONLY
/// in stores (never in a read pin) and are asserted distinct, so that a
/// completion default could collide them on `(not (= i1 i2))`. This is the
/// `(None, None)` arm of the rewritten side selection (both sides unvalued —
/// separate them). Must be `sat` with a validated witness before and after.
#[test]
fn store_only_index_disequality_is_still_separated() {
    let (exec, verdict) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i1 () Int)
        (declare-fun i2 () Int)
        (declare-fun e1 () Int)
        (declare-fun e2 () Int)
        (declare-fun l () (Array Int Int))
        (declare-fun r () (Array Int Int))
        (assert (= l (store (store a i1 e1) i2 e2)))
        (assert (= r (store (store a i2 e2) i1 e1)))
        (assert (not (= i1 i2)))
        (assert (= l r))
        (check-sat)
        "#,
    );
    assert_sat_with_validated_witness(&exec, &verdict, "store-only index disequality");
}

/// The `(Some, Some)` arm: a var-var disequality whose both sides the
/// evaluator values. Equal values are a genuine collision (the candidate is
/// doomed on that assertion, so shifting one side is allowed); distinct
/// values must never be touched. Either way the answer is `sat` with a
/// validated witness.
#[test]
fn concrete_collision_on_free_int_pair_still_shifts_to_a_validated_model() {
    let (exec, verdict) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun p () Int)
        (declare-fun q () Int)
        (declare-fun e () Int)
        (declare-fun l () (Array Int Int))
        (assert (= l (store (store a p e) q e)))
        (assert (not (= p q)))
        (assert (= (select l p) (select l q)))
        (check-sat)
        "#,
    );
    assert_sat_with_validated_witness(&exec, &verdict, "concrete collision shift");
}
