// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The strict checker admits a wide arithmetic identity through a swept
//! refutation, which it replays itself; a false one is never admitted. The
//! sweep's work is counted, and an exhausted allowance ends it.

use crate::bv_blast_solver::{self as solver, cnf::BvExprCnf, BvExpr, BvExprProofLimits};
use crate::sat_sweep::SweepLimits;
use ay_core::{Sort, Symbol, TermStore};
use ay_sat::{Literal, ResolutionDag, ResolutionProofError, ResolutionProofResource};
use std::time::{Duration, Instant};

/// The CNF of `lhs != rhs` and its clauses, with the conservative external
/// limits of at most `steps` resolution steps.
fn miter(
    lhs: &BvExpr,
    rhs: &BvExpr,
    steps: usize,
) -> (BvExprCnf, Vec<Vec<Literal>>, BvExprProofLimits) {
    let deadline = Instant::now() + Duration::from_secs(30);
    let limits = BvExprProofLimits::conservative_external(deadline, steps);
    let cnf = solver::cnf::build_bv_expr_cnf(lhs, rhs, &limits, &mut || true).unwrap();
    let clauses = solver::materialize_sat_clauses_with_cancellation(
        &cnf.clauses,
        &limits.resolution,
        &mut || true,
    )
    .unwrap();
    (cnf, clauses, limits)
}

fn identity_cnf() -> (BvExprCnf, Vec<Vec<Literal>>, BvExprProofLimits) {
    let a = BvExpr::leaf("a", 1);
    miter(&a, &a, 100)
}

/// `(x + y) * z` against `(y + x) * z` at 8 bits, whose adders line up bit by
/// bit, or, `false_by` one, against `(y + x) * z + 1`: no refutation exists.
fn commuted_sum_product(false_by: Option<u128>) -> (BvExprCnf, Vec<Vec<Literal>>) {
    let (x, y, z) = (
        BvExpr::leaf("x", 8),
        BvExpr::leaf("y", 8),
        BvExpr::leaf("z", 8),
    );
    let lhs = BvExpr::mul(BvExpr::add(x.clone(), y.clone()), z.clone());
    let mut rhs = BvExpr::mul(BvExpr::add(y, x), z);
    if let Some(offset) = false_by {
        rhs = BvExpr::add(rhs, BvExpr::const_val(offset, 8));
    }
    let (cnf, clauses, _) = miter(&lhs, &rhs, 100);
    (cnf, clauses)
}

/// `total_work` literals, the checker's lemma cap, no conflict cap and a
/// deadline an hour away.
fn within(total_work: u64) -> SweepLimits {
    SweepLimits {
        lemma_conflicts: super::LEMMA_CONFLICTS,
        total_conflicts: u64::MAX,
        total_work,
        deadline: Instant::now() + Duration::from_hours(1),
    }
}

/// The checker's sweep of `cnf` [`within`] `total_work` and under a caller
/// that never stops it: the refutation, and the conflicts and the work it
/// spent.
fn sweep_within(
    cnf: &BvExprCnf,
    clauses: &[Vec<Literal>],
    total_work: u64,
) -> (Option<ResolutionDag>, u64, u64) {
    let limits = within(total_work);
    let (dag, spent) = crate::sat_sweep::refute_counted(
        super::sweep_gates(cnf).unwrap(),
        clauses,
        &super::disequality_roots(cnf),
        false,
        limits,
        &mut || true,
    );
    (dag, spent.conflicts, spent.work)
}

/// A false identity's sweep is doomed: no refutation exists. With its
/// deadline out of reach and no conflict cap, a quarter of the work its
/// candidates would read ends it, on the count.
#[test]
fn a_doomed_sweep_stops_once_its_work_is_spent() {
    let (cnf, clauses) = commuted_sum_product(Some(1));
    let (refuted, _, unbounded) = sweep_within(&cnf, &clauses, u64::MAX);
    assert!(refuted.is_none() && unbounded >= 4, "{unbounded}");
    let allowance = unbounded / 4;
    let (refuted, _, read) = sweep_within(&cnf, &clauses, allowance);
    assert!(refuted.is_none());
    // It read its allowance and at most the candidate that crossed it.
    assert!(
        read >= allowance && read < unbounded / 2,
        "{read} read of {allowance}; {unbounded} without a cap"
    );
}

/// Each of the sweep's solver calls is a local solve, whose solver begins no
/// build of ay-sat's parked support enumeration (`sat_sweep/solve.rs`): the
/// enumeration waits for a head start no lemma solve reaches. Its twin, the
/// monolithic producer's counted solve of the same CNF, begins one.
#[test]
fn the_sweeps_solver_calls_begin_no_support_enumeration_build() {
    let (cnf, clauses) = commuted_sum_product(None);
    let builds = ay_sat::Solver::support_enumeration_builds();
    let (refuted, conflicts, _) = sweep_within(&cnf, &clauses, u64::MAX);
    assert!(
        refuted.is_some() && conflicts > 0,
        "the sweep called its solver"
    );
    assert_eq!(ay_sat::Solver::support_enumeration_builds(), builds);
    let limits = ay_sat::ResolutionProofLimits {
        deadline: Some(Instant::now() + Duration::from_secs(30)),
        max_conflicts: Some(100),
        ..ay_sat::ResolutionProofLimits::default()
    };
    let _ = ay_sat::solve_resolution_dag_counted(cnf.vars.len(), &clauses, &limits, &mut || true);
    assert_eq!(ay_sat::Solver::support_enumeration_builds(), builds + 1);
}

/// The cap's twin: a sweep that closes within its allowance closes exactly as
/// without one, and one literal short it ends before its closing refutation.
#[test]
fn a_sweep_within_its_work_closes_unchanged_and_one_literal_short_declines() {
    let (cnf, clauses) = commuted_sum_product(None);
    let (free, free_conflicts, needed) = sweep_within(&cnf, &clauses, u64::MAX);
    let free = free.expect("the adders line up, so the sweep closes");
    let (capped, conflicts, work) = sweep_within(&cnf, &clauses, needed + 1);
    assert_eq!(
        (capped.as_ref(), conflicts, work),
        (Some(&free), free_conflicts, needed)
    );
    let (short, short_conflicts, short_work) = sweep_within(&cnf, &clauses, needed);
    assert!(short.is_none());
    assert_eq!(short_work, needed);
    assert!(
        short_conflicts < free_conflicts,
        "{short_conflicts} of {free_conflicts}"
    );
}

/// The checker's split-then-sweep spends its work as the sweep alone does: a
/// split of a root with no open guard reads nothing, so the sweep keeps the
/// whole allowance, closes within what it needs and declines one literal
/// short.
#[test]
fn the_checkers_split_leaves_its_sweep_the_whole_work_it_did_not_spend() {
    let (cnf, clauses) = commuted_sum_product(None);
    let (_, _, needed) = sweep_within(&cnf, &clauses, u64::MAX);
    let checked = |work: u64| super::split_then_sweep(&cnf, &clauses, within(work), &mut || true).0;
    checked(needed + 1)
        .expect("the split declines and the sweep closes within its work")
        .validate()
        .expect("the swept DAG is an ordinary RUP refutation of the same CNF");
    assert!(checked(needed).is_none());
}

/// The split gets half of every count and of the time left; the sweep after
/// it keeps what the split did not spend, and nothing once either count is
/// spent.
#[test]
fn the_split_takes_half_of_each_count_and_the_sweep_what_is_left() {
    let now = Instant::now();
    let limits = SweepLimits {
        lemma_conflicts: super::LEMMA_CONFLICTS,
        total_conflicts: 1_000,
        total_work: 5_000,
        deadline: now + Duration::from_secs(10),
    };
    let share = super::split_share(limits, now);
    assert_eq!(
        (
            share.lemma_conflicts,
            share.total_conflicts,
            share.total_work
        ),
        (super::LEMMA_CONFLICTS, 500, 2_500)
    );
    assert_eq!(share.deadline, now + Duration::from_secs(5));
    let spent = |spent: u64, worked: u64| crate::sat_sweep::split::Outcome {
        refutation: None,
        spent,
        worked,
        deferred: false,
    };
    let left = super::left_after(limits, &spent(300, 4_000)).expect("both counts are left");
    assert_eq!((left.total_conflicts, left.total_work), (700, 1_000));
    assert_eq!(left.deadline, limits.deadline);
    assert!(super::left_after(limits, &spent(300, 5_000)).is_none());
    assert!(super::left_after(limits, &spent(1_000, 0)).is_none());
}

/// After a monolithic attempt that stopped on a proof-size cap, the sweep
/// has the envelope's whole conflict budget, however many the attempt spent;
/// after one that stopped on the conflict cap itself, nothing is swept.
#[test]
fn a_proof_size_stop_leaves_the_sweep_the_whole_envelope() {
    let (cnf, clauses) = commuted_sum_product(None);
    let (_, needed, _) = sweep_within(&cnf, &clauses, u64::MAX);
    assert!(needed > 0);
    let mut limits =
        BvExprProofLimits::conservative_external(Instant::now() + Duration::from_secs(30), 100)
            .resolution;
    limits.max_conflicts = Some(needed + 1_000);
    let stopped_on = |resource| ResolutionProofError::LimitExceeded {
        resource,
        limit: 1,
        actual: 2,
    };
    let swept = |error: &ResolutionProofError| {
        super::after_counted_cap(&cnf, &clauses, error, &limits, &mut || true)
    };
    swept(&stopped_on(ResolutionProofResource::ProofOutputBytes))
        .expect("the whole envelope closes the sweep")
        .validate()
        .expect("the swept DAG is an ordinary RUP refutation of the same CNF");
    assert!(swept(&stopped_on(ResolutionProofResource::Conflicts)).is_none());
}

/// Through [`super::bounded_refutation`] itself: the commuted product's
/// monolithic attempt refutes it after thousands of conflicts and then stops
/// on its 100-step cap. An envelope one conflict short of the attempt's
/// spend plus the sweep's need still closes, because the sweep is not
/// charged what the attempt spent (562aac51de charged it, and this envelope
/// then refused; external-codegen's corpus9 row 0644 is that case). An envelope of
/// one conflict stops the attempt on the conflict cap, and nothing is swept.
#[test]
fn bounded_refutation_sweeps_with_the_whole_envelope() {
    let (cnf, clauses) = commuted_sum_product(None);
    let (_, needed, _) = sweep_within(&cnf, &clauses, u64::MAX);
    let mut limits =
        BvExprProofLimits::conservative_external(Instant::now() + Duration::from_secs(30), 100);
    limits.sweep = true;
    limits.resolution.max_conflicts = Some(10_000_000);
    let (monolithic, spent) = ay_sat::prove_unsat_resolution_dag_counted_work(
        cnf.vars.len(),
        &clauses,
        &limits.resolution,
        &mut || true,
    );
    assert!(matches!(
        monolithic,
        Err(ResolutionProofError::LimitExceeded { ref resource, .. })
            if *resource != ResolutionProofResource::Conflicts
    ));
    assert!(spent > 1 && needed > 1);
    limits.resolution.max_conflicts = Some(spent + needed - 1);
    assert!(super::bounded_refutation(&cnf, &clauses, &limits, &mut || true).is_ok());
    limits.resolution.max_conflicts = Some(1);
    assert!(super::bounded_refutation(&cnf, &clauses, &limits, &mut || true).is_err());
}

#[test]
fn monolithic_validation_reports_existing_work_without_an_extra_replay() {
    let (cnf, clauses, limits) = identity_cnf();
    let mut measured_calls = 0;
    let measured = super::bounded_refutation(&cnf, &clauses, &limits, &mut || {
        measured_calls += 1;
        true
    })
    .unwrap();
    let mut original_calls = 0;
    let original = ay_sat::prove_unsat_resolution_dag_with_limits_and_cancellation_work(
        cnf.vars.len(),
        &clauses,
        &limits.resolution,
        &mut || {
            original_calls += 1;
            true
        },
    )
    .unwrap();
    assert!(original.1 > 0);
    assert_eq!(measured, (original.0, Some(original.1)));
    assert_eq!(measured_calls, original_calls);
}

#[test]
fn swept_candidate_never_fabricates_monolithic_validation_work() {
    let (cnf, clauses, mut limits) = identity_cnf();
    limits.sweep = true;
    limits.resolution.max_codec_bytes = 0;
    let (dag, work) = super::bounded_refutation(&cnf, &clauses, &limits, &mut || true).unwrap();
    assert_eq!(work, None);
    dag.validate_with_limits(&limits.resolution.validation)
        .unwrap();
}

fn constant_product_identity(terms: &mut TermStore, constant: u64) -> ay_core::TermId {
    let width = 64;
    let sort = Sort::bitvec(width);
    let x = terms.mk_var("x", sort.clone());
    let literal = terms.mk_bitvec(constant.into(), width);
    let product = terms.mk_app(Symbol::named("bvmul"), [literal, x], sort.clone());
    let seven = terms.mk_bitvec(7_u64.into(), width);
    let shifted = terms.mk_app(Symbol::named("bvshl"), [x, seven], sort.clone());
    let difference = terms.mk_app(Symbol::named("bvsub"), [shifted, x], sort);
    terms.mk_app(Symbol::named("="), [product, difference], Sort::Bool)
}

/// external-codegen's `ConstMul_Shift_Sub_I64 a=7`: the 64-bit multiplier against a
/// shift-and-subtract. Measured 2026-09-29, its monolithic refutation
/// surfaced past the proof-size caps; the checker's lowering now refutes it
/// monolithically. The swept route is pinned on the multiplier blasted whole,
/// past a counted cap the monolithic attempt cannot meet: the producer sweeps
/// it within the checker's own envelope, [`super::SWEEP_WORK`] included
/// (about 20.6M literals and 64,000 conflicts), and the DAG replays.
#[test]
fn a_sixty_four_bit_constant_product_identity_is_admitted_through_a_sweep() {
    let mut terms = TermStore::new();
    let identity = constant_product_identity(&mut terms, 127);
    assert!(crate::recognize_bv_bitblast(&terms, &[identity]));
    let x = BvExpr::leaf("x", 64);
    let product = BvExpr::mul(BvExpr::const_val(127, 64), x.clone());
    let difference = BvExpr::sub(BvExpr::shl(x.clone(), BvExpr::const_val(7, 64)), x);
    let (cnf, clauses, mut limits) = miter(&product, &difference, 250_000);
    limits.sweep = true;
    limits.resolution.max_codec_bytes = 0;
    let (dag, work) = super::bounded_refutation(&cnf, &clauses, &limits, &mut || true)
        .expect("the swept refutation closes within the envelope");
    assert_eq!(work, None);
    dag.validate_with_limits(&limits.resolution.validation)
        .unwrap();
}

#[test]
fn a_false_sixty_four_bit_constant_product_identity_is_never_admitted() {
    let mut terms = TermStore::new();
    let wrong = constant_product_identity(&mut terms, 126);
    assert!(!crate::recognize_bv_bitblast(&terms, &[wrong]));
}

/// Inside an exact-division attempt under a proof build's memo
/// (`crate::exact_division_sweeps`), only a sweep that spent its whole
/// envelope without closing is remembered, and the next attempt with that
/// divider obligation skips its sweep, even one that would close; a sweep
/// that ends short of its envelope, or closes, is not remembered.
#[test]
fn a_build_remembers_only_a_sweep_that_spent_its_whole_envelope() {
    use crate::exact_division_sweeps::{exact_division, ExactDivisionSweepMemo};
    let (doomed, doomed_clauses) = commuted_sum_product(Some(1));
    let (closing, closing_clauses) = commuted_sum_product(None);
    let (_, conflicts, _) = sweep_within(&doomed, &doomed_clauses, u64::MAX);
    assert!(conflicts >= 4, "{conflicts}");
    let stopped = ResolutionProofError::LimitExceeded {
        resource: ResolutionProofResource::ProofOutputBytes,
        limit: 1,
        actual: 2,
    };
    let envelope = |max_conflicts: u64| {
        let deadline = Instant::now() + Duration::from_secs(30);
        let mut limits = BvExprProofLimits::conservative_external(deadline, 100).resolution;
        limits.max_conflicts = Some(max_conflicts);
        limits
    };
    let mut terms = TermStore::new();
    let mut in_range = |k: u64| {
        let x = terms.mk_var("swept-dividend", Sort::bitvec(64));
        let divisor = terms.mk_bitvec(k.into(), 64);
        let remainder = terms.mk_app(Symbol::named("bvurem"), [x, divisor], Sort::bitvec(64));
        vec![terms.mk_app(Symbol::named("bvult"), [remainder, divisor], Sort::Bool)]
    };
    let (obligation, other) = (in_range(1_000_003), in_range(1_000_033));
    let swept =
        |clause: &[ay_core::TermId], cnf: &BvExprCnf, clauses: &[Vec<Literal>], conflicts: u64| {
            exact_division(&terms, clause, Some(true), 1, || {
                super::after_counted_cap(cnf, clauses, &stopped, &envelope(conflicts), &mut || true)
            })
        };
    let mut memo = ExactDivisionSweepMemo::new();
    let _build = memo.begin_build();
    assert!(swept(&obligation, &doomed, &doomed_clauses, conflicts * 10).is_none());
    assert_eq!(memo.failed_signatures(), 0, "short of its envelope");
    assert!(swept(&obligation, &doomed, &doomed_clauses, conflicts / 2).is_none());
    assert_eq!(memo.failed_signatures(), 1, "its whole envelope");
    assert!(swept(&obligation, &closing, &closing_clauses, 1_000_000).is_none());
    assert_eq!(memo.skipped_sweeps(), 1);
    swept(&other, &closing, &closing_clauses, 1_000_000)
        .expect("another obligation sweeps, and closes")
        .validate()
        .expect("the swept DAG is an ordinary RUP refutation of the same CNF");
    assert_eq!(
        memo.failed_signatures(),
        1,
        "a closed sweep is not remembered"
    );
}
