// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Whole public Expr bridge controls; DATA checks, not CHC proof credentials.

use super::*;

const MODES: [RoundingMode; 5] = [
    RoundingMode::RNE,
    RoundingMode::RNA,
    RoundingMode::RTP,
    RoundingMode::RTN,
    RoundingMode::RTZ,
];

fn word(bits: u64, width: u32) -> Expr {
    let fraction = if width == 32 { 23 } else { 52 };
    let exponent = width - fraction - 1;
    Expr::fp_from_bvs(
        Expr::bitvec_const(bits >> (width - 1), 1),
        Expr::bitvec_const((bits >> fraction) & ((1u64 << exponent) - 1), exponent),
        Expr::bitvec_const(bits & ((1u64 << fraction) - 1), fraction),
    )
}

fn exact(actual: Expr, expected: Expr, budget: &mut WorkBudget<'_>) {
    // Check the entire structural FP result and its negation, not sampled bits.
    let correct = actual.eq(expected);
    let problem = ChcProblem::new();
    for (root, expected) in [(correct.clone(), true), (correct.not(), false)] {
        let roots = [root];
        let output = relation(&roots, &[], &problem, budget);
        let (body, source) = output.into_parts().unwrap();
        assert_eq!(units::consistent(&body, budget), expected);
        assert!(std::ptr::eq(source.roots(), roots.as_slice()));
        drop(body);
        drop(source);
        budget.charge(0).unwrap();
    }
}

fn attempt(roots: &[Expr], budget: &mut WorkBudget<'_>) -> Result<(), FpAdapterError> {
    let problem = ChcProblem::new();
    let output = lower_fp_expr_clause(roots, &[], &problem, budget)?;
    let (body, source) = output.into_body(ClauseBody::empty())?.into_parts()?;
    drop(body);
    drop(source);
    budget.charge(0)?;
    Ok(())
}

fn simple(fused: bool) -> Expr {
    let one = word(0x3f800000, 32);
    if fused {
        one.clone()
            .fp_fma(RoundingMode::RNE, one.clone(), one)
            .fp_is_normal()
    } else {
        one.fp_sqrt(RoundingMode::RNE).fp_is_normal()
    }
}

#[test]
fn literal_modes_keep_all_original_unary_and_ternary_children_in_order() {
    with_owner(|budget| {
        for width in [32, 64] {
            let (a, _) = input(width);
            let b = Expr::var("original_y", a.sort().clone());
            let c = Expr::var("original_z", a.sort().clone());
            for (index, mode) in MODES.into_iter().enumerate() {
                let originals = [&a, &b, &c];
                for (name, expr, arity) in [
                    ("fp.sqrt", a.clone().fp_sqrt(mode), 1),
                    ("fp.fma", a.clone().fp_fma(mode, b.clone(), c.clone()), 3),
                ] {
                    budget.admit(4096, 4096).unwrap();
                    let shape = typed::describe(&expr).unwrap();
                    assert!(matches!(shape.op, typed::Operator::Apply(n, Some(m))
                        if n == name && m == index));
                    let children = shape.children.collect::<Vec<_>>();
                    assert_eq!(children.len(), arity);
                    for (child, original) in children.iter().zip(&originals[..arity]) {
                        assert!(std::ptr::eq(child.value(), original.value()));
                    }
                    drop(children);
                    budget.charge(0).unwrap();
                }
            }
        }
    });
}

#[test]
fn complete_square_root_results_keep_manual_irrational_words_for_all_modes() {
    with_owner(|budget| {
        for (width, two, down, nearest_up) in [
            (32, 0x40000000u64, 0x3fb504f3u64, false),
            (64, 0x4000000000000000, 0x3ff6a09e667f3bcc, true),
        ] {
            for mode in MODES {
                let up = match mode {
                    RoundingMode::RNE | RoundingMode::RNA => nearest_up,
                    RoundingMode::RTP => true,
                    _ => false,
                };
                exact(
                    word(two, width).fp_sqrt(mode),
                    word(down + u64::from(up), width),
                    budget,
                );
            }
        }
    });
}

#[test]
fn complete_fused_results_preserve_product_cancellation_lost_by_two_roundings() {
    with_owner(|budget| {
        for (width, x, y, z, expected) in [
            (32, 0x3f800001u64, 0x3f7ffffe, 0xbf800000, 0xa8800000),
            (
                64,
                0x3ff0000000000001,
                0x3feffffffffffffe,
                0xbff0000000000000,
                0xb970000000000000,
            ),
        ] {
            // (1+2^-p)*(1-2^-p)-1 = -2^(-2p), p=23/52, exactly representable.
            for mode in MODES {
                exact(
                    word(x, width).fp_fma(mode, word(y, width), word(z, width)),
                    word(expected, width),
                    budget,
                );
            }
        }
    });
}

#[test]
fn rounded_special_values_keep_signed_zero_and_only_nan_class_promises() {
    with_owner_until(|budget, end| {
        let enclosing = ay_core::resource::current_check_stop().unwrap();
        let stopped = std::sync::atomic::AtomicBool::new(false);
        let _stop = ay_core::resource::enter_check_stop(std::sync::Arc::new(move || {
            use std::sync::atomic::Ordering;
            if stopped.load(Ordering::Acquire) {
                return true;
            }
            let requested = Instant::now() >= end || enclosing.as_ref().is_some_and(|stop| stop());
            if requested {
                stopped.store(true, Ordering::Release);
            }
            requested
        }));
        for (width, sign, one, infinity) in [
            (32, 1u64 << 31, 0x3f800000u64, 0x7f800000u64),
            (64, 1u64 << 63, 0x3ff0000000000000, 0x7ff0000000000000),
        ] {
            exact(
                word(sign, width).fp_sqrt(RoundingMode::RNE),
                word(sign, width),
                budget,
            );
            let bad =
                word(0, width).fp_fma(RoundingMode::RNE, word(infinity, width), word(one, width));
            for (root, expected) in [
                (bad.clone().fp_is_nan(), true),
                (bad.clone().fp_eq(bad), false),
            ] {
                // General native SAT checks every clause; the fixed constant
                // unit-check helper and its 4096 bounds are unchanged.
                truncating::native::check(root, expected, budget, end);
                assert!(!ay_core::resource::check_stop_requested());
            }
        }
    });
}

#[test]
fn zero_factors_and_unchosen_roots_cannot_hide_omitted_or_unsupported_operands() {
    let sort = crate::Sort::fp(8, 24);
    let zero = Expr::fp_plus_zero(&sort);
    let missing = Expr::var("omitted", sort.clone());
    let unsupported = zero.clone().fp_round_to_integral(RoundingMode::RNE);
    let problem = ChcProblem::new();
    with_owner(|budget| {
        for value in [
            missing.clone().fp_sqrt(RoundingMode::RNE),
            zero.clone()
                .fp_fma(RoundingMode::RNE, missing.clone(), zero.clone()),
            zero.clone()
                .fp_fma(RoundingMode::RNE, zero.clone(), missing.clone()),
        ] {
            let selected = Expr::ite(Expr::true_(), zero.clone(), value);
            assert!(matches!(
                lower_fp_expr_clause(&[selected.fp_is_zero()], &[], &problem, budget),
                Err(FpAdapterError::Invalid(_))
            ));
        }
        for value in [
            unsupported.clone().fp_sqrt(RoundingMode::RNE),
            zero.clone()
                .fp_fma(RoundingMode::RNE, unsupported.clone(), zero.clone()),
            zero.clone()
                .fp_fma(RoundingMode::RNE, zero.clone(), unsupported),
        ] {
            let selected = Expr::ite(Expr::true_(), zero.clone(), value);
            assert!(matches!(
                lower_fp_expr_clause(&[selected.fp_is_zero()], &[], &problem, budget),
                Err(FpAdapterError::Unsupported(_))
            ));
        }
    });
}

#[test]
fn unsupported_rounded_formats_never_create_free_or_partial_outputs() {
    let problem = ChcProblem::new();
    with_owner(|budget| {
        for (e, s) in [(5, 11), (15, 113)] {
            let x = Expr::fp_plus_zero(&crate::Sort::fp(e, s));
            for value in [
                x.clone().fp_sqrt(RoundingMode::RNE),
                x.clone().fp_fma(RoundingMode::RNE, x.clone(), x),
            ] {
                assert!(matches!(
                    lower_fp_expr_clause(&[value.fp_is_zero()], &[], &problem, budget),
                    Err(FpAdapterError::Unsupported(_))
                ));
            }
        }
    });
}

#[test]
fn rounded_total_work_and_bytes_have_exact_one_short_sticky_refusals() {
    let end = Instant::now() + Duration::from_secs(20);
    for fused in [false, true] {
        let roots = [simple(fused)];
        let paid = Cell::new(0usize);
        let stored = Cell::new(0usize);
        let mut count = |work: usize, bytes: usize| {
            if Instant::now() >= end {
                return Err(QueryError::Interrupted(StopReason::Deadline));
            }
            paid.set(paid.get().checked_add(work).unwrap());
            stored.set(stored.get().checked_add(bytes).unwrap());
            Ok(())
        };
        let mut baseline = WorkBudget::with_admission(WORK, &mut count);
        attempt(&roots, &mut baseline).unwrap();
        drop(baseline);
        assert!(paid.get() > 0 && stored.get() > 0);
        let mut permit = |_: usize, _: usize| {
            if Instant::now() >= end {
                Err(QueryError::Interrupted(StopReason::Deadline))
            } else {
                Ok(())
            }
        };
        let mut short = WorkBudget::with_admission((paid.get() - 1) as u64, &mut permit);
        assert_eq!(
            attempt(&roots, &mut short).err(),
            Some(FpAdapterError::Owner(QueryError::Exhausted))
        );
        assert_eq!(short.charge(0), Err(QueryError::Exhausted));
        drop(short);
        let mut remaining = stored.get() - 1;
        let mut permit = |_: usize, bytes: usize| {
            if Instant::now() >= end {
                return Err(QueryError::Interrupted(StopReason::Deadline));
            }
            remaining = remaining.checked_sub(bytes).ok_or(QueryError::Exhausted)?;
            Ok(())
        };
        let mut short = WorkBudget::with_admission(WORK, &mut permit);
        assert_eq!(
            attempt(&roots, &mut short).err(),
            Some(FpAdapterError::Owner(QueryError::Exhausted))
        );
        assert_eq!(short.charge(0), Err(QueryError::Exhausted));
    }
}

#[test]
fn consuming_rounded_data_keeps_the_original_late_stop_after_reset() {
    let end = Instant::now() + Duration::from_secs(20);
    for fused in [false, true] {
        let roots = [simple(fused)];
        let problem = ChcProblem::new();
        let permit = Cell::new(true);
        let mut owner = |_: usize, _: usize| {
            if Instant::now() >= end {
                return Err(QueryError::Interrupted(StopReason::Deadline));
            }
            if permit.get() {
                Ok(())
            } else {
                Err(QueryError::Interrupted(StopReason::Cancelled))
            }
        };
        let mut budget = WorkBudget::with_admission(WORK, &mut owner);
        let body = lower_fp_expr_clause(&roots, &[], &problem, &mut budget)
            .unwrap()
            .into_body(ClauseBody::empty())
            .unwrap();
        permit.set(false);
        assert!(matches!(
            body.into_parts(),
            Err(FpAdapterError::Owner(QueryError::Interrupted(
                StopReason::Cancelled
            )))
        ));
        permit.set(true);
        assert_eq!(
            budget.charge(0),
            Err(QueryError::Interrupted(StopReason::Cancelled))
        );
    }
}
