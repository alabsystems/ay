// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The producer-input refusal memo: what it remembers, what it never
//! remembers, and that a hit is exactly the refusal a search would return.

use super::super::super::retained::producer_test_counter;
use super::super::super::{
    cancellation, cnf, map_bounded_resolution_error, preflight_bv_equality, BvExpr,
};
use super::super::validate_bv_expr_compact;
use super::*;
use crate::exact_division_sweeps::{self as sweeps, ExactDivisionSweepMemo};
use ay_core::{Sort, Symbol, TermId, TermStore};
use ay_sat::{ResolutionProofError, ResolutionProofResource};

fn limits(conflicts: u64) -> BvExprProofLimits {
    let mut limits =
        BvExprProofLimits::conservative_external(Instant::now() + Duration::from_secs(30), 100_000);
    limits.resolution.max_conflicts = Some(conflicts);
    limits
}

fn replay(limits: &BvExprProofLimits) -> BvBlastValidateLimits {
    BvBlastValidateLimits {
        deadline: limits.resolution.deadline,
        max_vars: 1 << 16,
        max_bit_lemmas: 1 << 16,
        max_clauses: 1 << 18,
        max_clause_literals: 64,
        max_original_literals: 1 << 20,
        max_resolution_steps: 1 << 20,
        max_derived_literals: 1 << 22,
        max_work: 1 << 30,
    }
}

/// `x * y = y * x` over `width`-bit leaves named `x` and `y`.
fn commuted(x: &str, y: &str, width: u32) -> (BvExpr, BvExpr) {
    (
        BvExpr::mul(BvExpr::leaf(x, width), BvExpr::leaf(y, width)),
        BvExpr::mul(BvExpr::leaf(y, width), BvExpr::leaf(x, width)),
    )
}

/// One strict-checker decision of `lhs = rhs`, and whether it ran the
/// producer.
fn decide(
    (lhs, rhs): &(BvExpr, BvExpr),
    limits: &BvExprProofLimits,
) -> (Result<(), BvExprExportError>, bool) {
    let before = producer_test_counter::count();
    let outcome = validate_bv_expr_compact(lhs, rhs, limits, &replay(limits), &mut || true);
    (outcome, producer_test_counter::count() > before)
}

fn input((lhs, rhs): &(BvExpr, BvExpr), limits: &BvExprProofLimits) -> BvExprCnf {
    let preflight = preflight_bv_equality(lhs, rhs, limits, &mut || true).unwrap();
    cnf::build(lhs, rhs, Some((limits, preflight)), &mut || true).unwrap()
}

fn capped() -> BvExprExportError {
    BvExprExportError::ResourceLimit {
        resource: "resolution conflicts",
        limit: 1,
        actual: 2,
    }
}

#[test]
fn a_counted_refusal_is_repeated_for_the_same_input_without_a_search() {
    let tight = limits(1);
    let base = remembered();
    let (first, searched) = decide(&commuted("x", "y", 8), &tight);
    assert!(searched);
    let Err(refusal @ BvExprExportError::ResourceLimit { .. }) = first else {
        panic!("one conflict cannot refute 8-bit commutativity: {first:?}");
    };
    assert_eq!(remembered(), base + 1);
    // The same obligation again, and over other leaves: the CNF names no
    // leaf, so both are the same input, refused exactly as before.
    for (x, y) in [("x", "y"), ("p", "q")] {
        let (again, searched) = decide(&commuted(x, y, 8), &tight);
        assert!(!searched, "{x}*{y} searched again");
        assert_eq!(again, Err(refusal.clone()));
    }
    assert_eq!(remembered(), base + 1);
}

#[test]
fn another_input_or_other_caps_are_decided_afresh() {
    let tight = limits(1);
    let base = remembered();
    assert!(decide(&commuted("x", "y", 8), &tight).1);
    // Another width is another CNF.
    assert!(decide(&commuted("x", "y", 9), &tight).1);
    // The same CNF under another conflict cap is another question.
    assert!(decide(&commuted("x", "y", 8), &limits(2)).1);
    assert_eq!(remembered(), base + 3);
}

#[test]
fn an_acceptance_is_never_remembered() {
    let ample = limits(200_000);
    let base = remembered();
    for _ in 0..2 {
        let (outcome, searched) = decide(&commuted("x", "y", 4), &ample);
        assert_eq!(outcome, Ok(()));
        assert!(searched, "every acceptance is searched and replayed");
    }
    assert_eq!(remembered(), base);
}

#[test]
fn a_model_is_remembered_as_no_refutation() {
    let ample = limits(200_000);
    let false_claim = (BvExpr::leaf("a", 4), BvExpr::leaf("b", 4));
    assert_eq!(
        decide(&false_claim, &ample),
        (Err(BvExprExportError::NoRefutation), true)
    );
    assert_eq!(
        decide(&false_claim, &ample),
        (Err(BvExprExportError::NoRefutation), false)
    );
}

/// Run `deciding` over a fixed input with a stub decision that refuses with
/// `refusal` after calling `during` with the poll, made sticky as the
/// producer makes it (`cancellation::run`).
fn stubbed(
    limits: &BvExprProofLimits,
    refusal: BvExprExportError,
    keep_going: &mut dyn FnMut() -> bool,
    during: impl FnOnce(&mut dyn FnMut() -> bool),
) {
    let input = input(&commuted("x", "y", 6), &self::limits(200_000));
    let outcome = cancellation::run(keep_going, |poll| {
        deciding(input, limits, &replay(limits), poll, |input, poll| {
            during(poll);
            (Err(refusal.clone()), Some(input))
        })
    });
    assert_eq!(outcome, Err(refusal));
}

#[test]
fn a_refusal_a_stop_a_wall_or_a_withheld_sweep_may_have_shaped_is_not_remembered() {
    let ample = limits(200_000);
    let base = remembered();
    // Not the producer's verdict.
    for refusal in [
        BvExprExportError::Cancelled,
        BvExprExportError::SolverUnknown,
        BvExprExportError::Malformed("shape".into()),
        BvExprExportError::ResourceLimit {
            resource: "resolution proof deadline",
            limit: 0,
            actual: 1,
        },
        BvExprExportError::ResourceLimit {
            resource: "expression construction bytes",
            limit: 1,
            actual: 2,
        },
    ] {
        stubbed(&ample, refusal, &mut || true, |_| ());
    }
    // A poll refused during the decision: a stop can end a search early and
    // come back as a cap.
    let mut calls = 0;
    stubbed(
        &ample,
        capped(),
        &mut || {
            calls += 1;
            calls != 1
        },
        |poll| assert!(!poll()),
    );
    // A caller that stopped by the end of the decision.
    let mut calls = 0;
    stubbed(
        &ample,
        capped(),
        &mut || {
            calls += 1;
            calls != 1
        },
        |_| (),
    );
    // At its deadline: no wall is out of reach.
    let mut near = ample.clone();
    near.resolution.deadline = Some(Instant::now());
    stubbed(&near, capped(), &mut || true, |_| ());
    // A failure the environment may have decided: a sweep's solver call
    // interrupted, or an allocation the producer could not make, which is
    // reported as a `resolution ...` cap.
    stubbed(&ample, capped(), &mut || true, |_| note_uncounted_failure());
    let allocation = || {
        map_bounded_resolution_error(
            ResolutionProofError::AllocationFailed {
                resource: ResolutionProofResource::ProofOutputBytes,
            },
            &ample.resolution,
        )
    };
    stubbed(&ample, allocation(), &mut || true, |_| drop(allocation()));
    // A withheld exact-division sweep: the envelope did not run in full.
    let (terms, clause) = divider_clause();
    let mut memo = ExactDivisionSweepMemo::new();
    let _build = memo.begin_build();
    sweeps::exact_division(&terms, &clause, Some(true), 7, sweeps::sweep_failed);
    stubbed(&ample, capped(), &mut || true, |_| {
        assert!(sweeps::exact_division(
            &terms,
            &clause,
            Some(true),
            7,
            sweeps::skips_sweep
        ));
    });
    assert_eq!(remembered(), base);
    // The negative twin: the same stub, clear of all of these, is remembered.
    stubbed(&ample, capped(), &mut || true, |_| ());
    assert_eq!(remembered(), base + 1);
}

/// `x % 1000003 < 1000003` over a 64-bit `x`: one division to sign.
fn divider_clause() -> (TermStore, [TermId; 1]) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("dividend", Sort::bitvec(64));
    let divisor = terms.mk_bitvec(1_000_003u64.into(), 64);
    let remainder = terms.mk_app(Symbol::named("bvurem"), [x, divisor], Sort::bitvec(64));
    let clause = [terms.mk_app(Symbol::named("bvult"), [remainder, divisor], Sort::Bool)];
    (terms, clause)
}

#[test]
fn an_allocation_failure_reads_as_a_cap_and_is_noted() {
    let ample = limits(200_000);
    let noted = uncounted_failures();
    let refusal = map_bounded_resolution_error(
        ResolutionProofError::AllocationFailed {
            resource: ResolutionProofResource::ProofOutputBytes,
        },
        &ample.resolution,
    );
    // Its resource and its sentinel are a counted cap's ...
    assert!(counted(&refusal), "{refusal:?}");
    // ... so it is noted where it is mapped, and an overflow, which the
    // input decides, is not.
    assert_eq!(uncounted_failures(), noted + 1);
    let overflow = map_bounded_resolution_error(
        ResolutionProofError::AccountingOverflow {
            resource: ResolutionProofResource::ProofOutputBytes,
        },
        &ample.resolution,
    );
    assert!(counted(&overflow));
    assert_eq!(uncounted_failures(), noted + 1);
}

/// One proof build's exact-division attempt at [`divider_clause`] decides
/// `input` (built at `width`) with a stub that refuses it by a cap, having
/// remembered a failed sweep when `swept`; then another build, whose memo
/// starts afresh, meets the same input.
#[test]
fn a_hit_remembers_the_failed_sweep_its_decision_remembered() {
    let ample = limits(200_000);
    let (terms, clause) = divider_clause();
    for (swept, width) in [(true, 5), (false, 7)] {
        let input = || input(&commuted("x", "y", width), &ample);
        let mut first = ExactDivisionSweepMemo::new();
        {
            let _build = first.begin_build();
            sweeps::exact_division(&terms, &clause, Some(true), 7, || {
                let outcome = deciding(input(), &ample, &replay(&ample), &mut || true, |cnf, _| {
                    if swept {
                        sweeps::sweep_failed();
                    }
                    (Err(capped()), Some(cnf))
                });
                assert_eq!(outcome, Err(capped()));
            });
        }
        assert_eq!(first.failed_signatures(), usize::from(swept));
        let mut second = ExactDivisionSweepMemo::new();
        let _build = second.begin_build();
        sweeps::exact_division(&terms, &clause, Some(true), 7, || {
            let outcome = deciding(input(), &ample, &replay(&ample), &mut || true, |_, _| {
                panic!("a remembered input is decided again")
            });
            assert_eq!(outcome, Err(capped()));
        });
        // The second build learned the divider from the hit exactly when
        // deciding the input again would have taught it.
        assert_eq!(
            second.failed_signatures(),
            usize::from(swept),
            "swept: {swept}"
        );
    }
}

/// The `k`-th of many distinct inputs: `a = b + shift` at one of 64 widths.
fn distinct(k: u32, limits: &BvExprProofLimits) -> BvExprCnf {
    let width = 1 + k % 64;
    let shift = u128::from(k / 64) % (1u128 << width.min(64));
    let rhs = BvExpr::add(BvExpr::leaf("b", width), BvExpr::const_val(shift, width));
    input(&(BvExpr::leaf("a", width), rhs), limits)
}

#[test]
fn equal_inputs_encode_equal_and_different_inputs_differently() {
    let ample = limits(200_000);
    let encoded = |x, y, width| encode(&input(&commuted(x, y, width), &ample)).unwrap();
    assert_eq!(encoded("x", "y", 8), encoded("p", "q", 8));
    assert_ne!(encoded("x", "y", 8), encoded("x", "y", 9));
    // Swapping the factors on one side changes the circuit's wiring.
    let skewed = (
        BvExpr::mul(BvExpr::leaf("x", 8), BvExpr::leaf("y", 8)),
        BvExpr::mul(BvExpr::leaf("x", 8), BvExpr::leaf("y", 8)),
    );
    assert_ne!(
        encoded("x", "y", 8),
        encode(&input(&skewed, &ample)).unwrap()
    );
}

#[test]
fn the_memo_keeps_to_its_bounds() {
    let ample = limits(200_000);
    let caps = || caps(&ample, &replay(&ample));
    let entry = |k: u32| {
        let input = distinct(k, &ample);
        Entry {
            shape: Shape::of(&input),
            caps: caps(),
            input: encode(&input).unwrap(),
            refusal: BvExprExportError::NoRefutation,
            swept_out: false,
        }
    };
    let held = |k: u32| {
        let input = distinct(k, &ample);
        refused(Shape::of(&input), &input, caps).is_some()
    };
    let last = MAX_ENTRIES as u32 + 3;
    for k in 0..=last {
        remember(entry(k));
    }
    assert_eq!(remembered(), MAX_ENTRIES, "the oldest inputs make room");
    assert!(!held(0) && !held(3) && held(4) && held(last));
    // An input past the byte bound is not remembered at all.
    let mut huge = entry(last + 1);
    huge.caps = "x".repeat(MAX_BYTES);
    remember(huge);
    assert!(!held(last + 1) && held(last));
    MEMO.with(|memo| assert!(memo.borrow().bytes <= MAX_BYTES));
}
