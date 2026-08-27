// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::api::{Logic, Solver, Sort};
#[cfg(feature = "proof-checker")]
use crate::executor::proof::check::EmptyClauseDerivation;
#[cfg(feature = "proof-checker")]
use ay_core::AletheRule;
use std::cell::Cell;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

#[test]
fn aggregate_meter_refuses_cross_call_limit_and_overflow() {
    let mut meter = StrictCheckMeter::with_limits(10, 8);
    assert!(meter.charge(6, 5));
    assert!(meter.charge(4, 3));
    assert!(!meter.charge(1, 0));

    let mut overflow = StrictCheckMeter::with_limits(usize::MAX, usize::MAX);
    assert!(overflow.charge(usize::MAX, usize::MAX));
    assert!(!overflow.charge(1, 0));
    assert!(!overflow.charge(0, 1));
}

#[test]
fn control_is_polled_on_every_charge_including_zero_delta() {
    let polls = Cell::new(0usize);
    let mut meter = StrictCheckMeter::with_limits(10, 10);
    assert!(meter.charge_while_running(
        1,
        1,
        || {
            polls.set(polls.get() + 1);
            false
        },
        || "test".to_string()
    ));
    assert!(!meter.charge_while_running(
        0,
        0,
        || {
            polls.set(polls.get() + 1);
            true
        },
        || "test".to_string()
    ));
    assert_eq!(polls.get(), 2);
}

/// The cancel limb has to tell interrupt from deadline from memory. It used
/// to print the disjunction of all three, so the one question a reader has
/// -- WHICH one stopped it -- was the one it would not answer, and
/// diagnosing the model-checker-consumer `dyn_ptr` certification gap needed four
/// hand-instrumented sites and a rebuild to establish "the deadline, 233
/// times out of 233".
#[test]
fn stop_signal_description_names_the_signal_that_fired() {
    let mut interrupted = Executor::new();
    interrupted.set_solve_controls(Some(Arc::new(AtomicBool::new(true))), None);
    let described = describe_stop_signal(&interrupted);
    assert!(
        described.contains("interrupt"),
        "a raised interrupt must be named, got {described:?}"
    );

    let mut expired = Executor::new();
    let now = std::time::Instant::now();
    let expired_deadline = match now.checked_sub(std::time::Duration::from_millis(50)) {
        Some(deadline) => deadline,
        None => now,
    };
    expired.set_solve_controls(None, Some(expired_deadline));
    let described = describe_stop_signal(&expired);
    assert!(
        described.starts_with("deadline expired by"),
        "a passed deadline must be named and quantified, got {described:?}"
    );
    assert!(
        !described.contains("interrupt"),
        "an unset interrupt must not be reported, got {described:?}"
    );

    // Neither signal set: say so rather than name an innocent one.
    let quiet = Executor::new();
    let described = describe_stop_signal(&quiet);
    assert!(
        described.starts_with("none-now"),
        "no live signal must report none-now, got {described:?}"
    );
}

#[test]
fn executor_strict_derivation_check_polls_active_interrupt() {
    let mut executor = Executor::new();
    executor.set_solve_controls(Some(Arc::new(AtomicBool::new(true))), None);

    assert_eq!(
        executor.check_proof_strict_derivation_with_datatypes(&Proof::new()),
        Err(ProofCheckError::Cancelled)
    );
}

#[test]
fn executor_strict_check_polls_active_interrupt() {
    let mut executor = Executor::new();
    executor.set_solve_controls(Some(Arc::new(AtomicBool::new(true))), None);

    assert_eq!(
        executor.check_proof_strict_with_datatypes(&Proof::new()),
        Err(ProofCheckError::Cancelled)
    );
}

#[test]
fn executor_strict_derivation_check_polls_active_deadline() {
    let mut executor = Executor::new();
    executor.set_solve_controls(None, Some(ay_core::time::Instant::now()));

    assert_eq!(
        executor.check_proof_strict_derivation_with_datatypes(&Proof::new()),
        Err(ProofCheckError::Cancelled)
    );
}

#[test]
fn executor_strict_derivation_check_polls_executor_memory_limit() {
    let mut executor = Executor::new();
    executor.set_memory_limit(Some(1));

    assert_eq!(
        executor.check_proof_strict_derivation_with_datatypes(&Proof::new()),
        Err(ProofCheckError::Cancelled)
    );
}

/// #diagnostic-envelope AMENDMENT. A cancelled resolution-chain check must
/// report that the ENVELOPE refused, not merely that "something went
/// wrong". `build_unsat_assembly` repairs the proof on a defect, and a
/// repair entered because we ran out of time is unbounded post-stop work of
/// exactly the kind this envelope exists to remove.
#[cfg(feature = "proof-checker")]
#[test]
fn cancelled_partial_check_names_the_envelope_as_the_refusing_party() {
    let mut exec = Executor::new();
    let proof = valid_empty_clause_proof(&mut exec);
    exec.set_solve_controls(Some(Arc::new(AtomicBool::new(true))), None);

    let outcome = check_partial_with_executor_progress(&exec, &proof, WantQuality::No);
    assert_eq!(outcome.error, Some(ProofCheckError::Cancelled));
    assert!(
        outcome.envelope_refused(),
        "a cancelled walk must be attributable to the envelope, not to the proof"
    );
    assert_eq!(
        outcome.envelope_refusal,
        Some(StrictCheckRefusal::Cancelled),
        "and to the CANCELLED limb: the stop signal was raised"
    );
}

/// The three states must be genuinely three: a proof the checker accepted,
/// a proof it rejected, and a proof it never got to look at.
#[cfg(feature = "proof-checker")]
#[test]
fn empty_clause_derivation_separates_defect_from_cancellation() {
    let mut accepted = Executor::new();
    let good = valid_empty_clause_proof(&mut accepted);
    assert_eq!(
        accepted.empty_clause_derivation_status(&good),
        EmptyClauseDerivation::Valid
    );
    assert!(accepted.proof_derives_valid_empty_clause(&good));

    // A genuine defect: the resolution pivot occurs in neither premise, so
    // the checker REACHES a verdict and the verdict is "broken". This is
    // the one state a repair may act on.
    let mut defective = Executor::new();
    let bad = broken_empty_clause_proof(&mut defective);
    assert_eq!(
        defective.empty_clause_derivation_status(&bad),
        EmptyClauseDerivation::Invalid
    );
    assert!(!defective.proof_derives_valid_empty_clause(&bad));

    // Same proof as the accepted one, but the caller has already asked us
    // to stop. NOTHING is known about it, so it is neither certifiable nor
    // repairable.
    let mut cancelled = Executor::new();
    let good = valid_empty_clause_proof(&mut cancelled);
    cancelled.set_solve_controls(Some(Arc::new(AtomicBool::new(true))), None);
    assert_eq!(
        cancelled.empty_clause_derivation_status(&good),
        EmptyClauseDerivation::Undetermined,
        "a cancelled check must not be reported as a broken resolution chain"
    );
    assert!(
        !cancelled.proof_derives_valid_empty_clause(&good),
        "self-certification must still fail closed on a check that never ran"
    );
}

/// A structurally empty-clause-free proof is a DEFECT, not a refusal, and
/// it is decided without walking anything.
#[cfg(feature = "proof-checker")]
#[test]
fn absent_empty_clause_is_invalid_even_under_an_active_interrupt() {
    let mut exec = Executor::new();
    let p = exec.ctx.terms.mk_var("p", Sort::Bool);
    let mut proof = Proof::new();
    proof.add_assume(p, None);
    exec.set_solve_controls(Some(Arc::new(AtomicBool::new(true))), None);

    assert_eq!(
        exec.empty_clause_derivation_status(&proof),
        EmptyClauseDerivation::Invalid
    );
}

/// The quality-discarding callers must not pay for the fused walk's
/// unmetered `validate_sko_forall_uniqueness` tail: `WantQuality::No` takes
/// the quality-free entry point and returns no quality at all.
#[cfg(feature = "proof-checker")]
#[test]
fn want_quality_selects_which_walk_runs() {
    let mut exec = Executor::new();
    let proof = valid_empty_clause_proof(&mut exec);

    let without = check_partial_with_executor_progress(&exec, &proof, WantQuality::No);
    assert!(without.error.is_none());
    assert!(!without.envelope_refused());
    assert!(without.quality.is_none());

    let with = check_partial_with_executor_progress(&exec, &proof, WantQuality::Yes);
    assert!(with.error.is_none());
    assert!(with.quality.is_some());
    // The step accounting is the same walk either way.
    assert_eq!(without.summary, with.summary);
}

/// `p` and `not p` assumed, resolved to the empty clause by a
/// `th_resolution` STEP: the partial checker accepts the chain and it
/// terminates in the empty clause.
///
/// The RULE matters. `ProofStep::Resolution` is validated by
/// `validate_resolution_step`, which takes no progress meter at all, so a
/// proof built only from those charges nothing and can never be stopped —
/// harmless on three steps, and a real remaining hole on a large one.
/// `AletheRule::ThResolution` routes through `validate_resolution_rule`,
/// which IS metered, and that is the rule deductive-checks's proofs are built from.
///
/// The two leaves are `assume` rather than theory lemmas on purpose: a bare
/// `Proof::add_theory_lemma` records a `Generic`/trust step, and the
/// `explicit_trust_call_site_census` ratchet counts those per source file
/// WITHOUT stripping inline `#[cfg(test)]` modules. A fixture is no reason
/// to spend a vetted trust site, and none is needed here.
#[cfg(feature = "proof-checker")]
fn valid_empty_clause_proof(exec: &mut Executor) -> Proof {
    let p = exec.ctx.terms.mk_var("p", Sort::Bool);
    let not_p = exec.ctx.terms.mk_not(p);
    let mut proof = Proof::new();
    let positive = proof.add_assume(p, None);
    let negative = proof.add_assume(not_p, None);
    proof.add_rule_step(
        AletheRule::ThResolution,
        Vec::new(),
        vec![positive, negative],
        Vec::new(),
    );
    proof
}

/// As above, but both `th_resolution` premises are `p`, which does not
/// resolve to the empty clause. The proof still ENDS in an empty clause,
/// which is what makes this a checker VERDICT about the chain rather than a
/// structural observation about the proof's shape.
#[cfg(feature = "proof-checker")]
fn broken_empty_clause_proof(exec: &mut Executor) -> Proof {
    let p = exec.ctx.terms.mk_var("p", Sort::Bool);
    let mut proof = Proof::new();
    let first = proof.add_assume(p, None);
    let second = proof.add_assume(p, None);
    proof.add_rule_step(
        AletheRule::ThResolution,
        Vec::new(),
        vec![first, second],
        Vec::new(),
    );
    proof
}

/// Regression for the verification condition `(x & 15) <u 16` over a free
/// 64-bit `x`, as emitted by the proof-IR frontend.
///
/// The generated three-step proof contains one proof-producing
/// `BvBitBlast` lemma. Its published 768 MiB conservative precharge used to
/// exceed this caller's entire 512 MiB envelope, so 29 proof-surgery and
/// publication probes all rejected the same valid proof as `ResourceLimit`
/// (the old pre-mint statistics snapshot reported only 28).
#[test]
fn strict_publication_admits_one_wide_bv_bitblast_lemma() {
    let mut solver = Solver::try_new(Logic::All).expect("solver construction");
    solver.set_produce_proofs(true);
    let x = solver.declare_const("resource_mask_x", Sort::bitvec(64));
    let mask = solver.bv_const(15, 64);
    let bound = solver.bv_const(16, 64);
    let masked = solver.bvand(x, mask);
    let comparison = solver.bvult(masked, bound);

    // Match the proof-IR frontend's canonical Bool -> BV1 -> Bool schema
    // normalization.
    let one = solver.bv_const(1, 1);
    let zero = solver.bv_const(0, 1);
    let encoded = solver.ite(comparison, one, zero);
    let holds = solver.eq(encoded, one);
    let negated = solver.not(holds);
    solver.assert_term(negated);

    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "the mask theorem must publish UNSAT, not {:?}: {:?}",
        solver.unknown_reason(),
        solver.statistics()
    );
    assert!(
        result.was_unsat_strictly_verified(),
        "publication must consume the strict proof capability, not an independent fallback"
    );
    assert!(!result.was_unsat_independently_verified());
    assert_eq!(
        solver.last_proof().map(|proof| proof.len()),
        Some(3),
        "the regression must continue exercising the wide BV lemma proof"
    );
    let invocations = solver
        .statistics()
        .get_int("proof.strict_check_invocations")
        .expect("strict-check invocation counter");
    // The final published snapshot includes the bounded BV-authored repair
    // path, its fixed post-repair gates, and certificate minting. Before the
    // envelope fix, the all-member rejection storm took 29 checks and never
    // published UNSAT; successful promotion stays within the current
    // 17-check bound while permitting future removal of redundant gates.
    assert!(
        invocations <= 17,
        "accepted proof exceeded the bounded publication pipeline: {invocations}"
    );
}

/// BUDGET limb coverage — the half of the envelope where publication stays
/// LIVE. No stop signal is raised anywhere in this test: the walk refuses
/// purely on the injected aggregate work budget, and the three facts the
/// two-limb design rests on are asserted — the limb is named, the error is
/// NOT laundered into `Cancelled`, and the classification is
/// `Undetermined` ("never repair"), not `Invalid` ("repair").
#[cfg(feature = "proof-checker")]
#[test]
fn budget_refusal_names_the_budget_and_stays_undetermined() {
    let mut exec = Executor::new();
    let proof = valid_empty_clause_proof(&mut exec);

    let outcome = check_partial_with_executor_progress_and_meter(
        &exec,
        &proof,
        WantQuality::No,
        StrictCheckMeter::with_limits(1, usize::MAX),
    );
    assert_eq!(
        outcome.envelope_refusal,
        Some(StrictCheckRefusal::BudgetRefused),
        "no stop signal exists in this test; only the injected budget can refuse"
    );
    assert_eq!(
        outcome.error,
        Some(ProofCheckError::ResourceLimit),
        "a budget refusal must surface as ResourceLimit, not be laundered into Cancelled"
    );
    assert_eq!(
        crate::executor::proof::check::classify_empty_clause_walk(
            outcome.error.as_ref(),
            outcome.envelope_refused(),
        ),
        EmptyClauseDerivation::Undetermined,
        "BudgetRefused learned nothing about the chain; a repair may not act on it"
    );
}

/// MUTATION-SENSITIVE map of the classifier, every limb pinned. The two
/// mutants this kills are exactly the two historical misreadings: mapping
/// `BudgetRefused` back to `Invalid` re-enters the repair on "I never
/// looked" (the trackA2 regression this amendment exists to close), and
/// keying on the ERROR KIND instead of the refusing party would move the
/// checker's own in-checker `ResourceLimit` budgets (`checker::lra_farkas`,
/// `checker::nia_*`) out of their historical `Invalid` reading.
#[cfg(feature = "proof-checker")]
#[test]
fn classifier_separates_verdicts_from_both_refusal_limbs() {
    use crate::executor::proof::check::classify_empty_clause_walk as classify;
    assert_eq!(classify(None, false), EmptyClauseDerivation::Valid);
    assert_eq!(
        classify(Some(&ProofCheckError::ResourceLimit), false),
        EmptyClauseDerivation::Invalid,
        "in-checker resource budgets are a property of the PROOF and keep Invalid"
    );
    assert_eq!(
        classify(Some(&ProofCheckError::Cancelled), true),
        EmptyClauseDerivation::Undetermined
    );
    assert_eq!(
        classify(Some(&ProofCheckError::ResourceLimit), true),
        EmptyClauseDerivation::Undetermined,
        "BudgetRefused must not read as a defect: the repair it would trigger is \
             the exact post-refusal work the envelope exists to eliminate"
    );
}
