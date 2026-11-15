// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Native Bool/BV checks of every emitted clause and complete original roots.
use super::*;
use ay_chc::{SmtContext, SmtResult};
use std::sync::Arc;

fn with_native_owner(run: impl FnOnce(&mut WorkBudget<'_>, Instant)) {
    let end = Instant::now() + Duration::from_secs(20);
    let original = ay_core::resource::current_check_stop().unwrap();
    let enclosing = original.clone();
    let _scope = ay_core::resource::enter_check_stop(Arc::new(move || {
        Instant::now() >= end || enclosing.as_ref().is_some_and(|stop| stop())
    }));
    let (mut left_work, mut left_bytes) = (WORK, BYTES);
    let mut owner = |w: usize, b: usize| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        if original.as_ref().is_some_and(|stop| stop()) {
            return Err(QueryError::Invalid("original enclosing stop"));
        }
        left_work = left_work
            .checked_sub(w as u64)
            .ok_or(QueryError::Exhausted)?;
        left_bytes = left_bytes
            .checked_sub(b as u64)
            .ok_or(QueryError::Exhausted)?;
        Ok(())
    };
    let mut budget = WorkBudget::with_admission(WORK, &mut owner);
    run(&mut budget, end);
    budget.charge(0).unwrap();
    drop(budget);
    owner(0, 0).unwrap();
}

pub(in crate::fp::tests) fn check(
    value: Expr,
    truth: bool,
    budget: &mut WorkBudget<'_>,
    end: Instant,
) {
    budget.admit(1_048_576, 1_048_576).unwrap();
    let roots = [value];
    let problem = ChcProblem::new();
    let output = relation(&roots, &[], &problem, budget);
    let (body, source) = output.into_parts().unwrap();
    assert!(std::ptr::eq(source.roots(), roots.as_slice()));
    let mut native = SmtContext::new();
    native.set_term_memory_budget(Some(128 * 1024 * 1024));
    budget.charge(0).unwrap();
    let remaining = end.saturating_duration_since(Instant::now());
    assert!(!remaining.is_zero());
    let result = native.check_sat_with_timeout(body.constraint.as_ref().unwrap(), remaining);
    if truth {
        assert!(matches!(result, SmtResult::Sat(_)));
    } else {
        assert!(result.is_unsat());
    }
    drop(result);
    drop(native);
    drop(body);
    drop(source);
    budget.charge(0).unwrap();
}

#[test]
fn native_truncating_words_and_wrong_word_exclusion_cover_both_dividend_signs() {
    with_native_owner(|budget, end| {
        for (width, three, two, one) in [
            (32, 0x40400000u64, 0x40000000u64, 0x3f800000u64),
            (
                64,
                0x4008000000000000,
                0x4000000000000000,
                0x3ff0000000000000,
            ),
        ] {
            let sign = 1u64 << (width - 1);
            for (a, b, result) in [
                (three, two, one),
                (three | sign, two, one | sign),
                (three, two | sign, one),
                (three | sign, two | sign, one | sign),
            ] {
                let value = word(a, width).fp_truncating_rem(word(b, width));
                let root = value.eq(word(result, width));
                check(root.clone(), true, budget, end);
                check(root.not(), false, budget, end);
            }
        }
    });
}

#[test]
fn native_truncating_subnormals_exact_multiples_and_full_exponent_gap_keep_zero_sign() {
    with_native_owner(|budget, end| {
        for (width, two, one, max, sign) in [
            (
                32,
                0x40000000u64,
                0x3f800000u64,
                0x7f7fffffu64,
                0x80000000u64,
            ),
            (
                64,
                0x4000000000000000,
                0x3ff0000000000000,
                0x7fefffffffffffff,
                0x8000000000000000,
            ),
        ] {
            for (a, b, result) in [
                (5, 3, 2),
                (5 | sign, 3, 2 | sign),
                (two | sign, one, sign),
                (max, 1, 0),
                (1, 3, 1),
            ] {
                let root = word(a, width)
                    .fp_truncating_rem(word(b, width))
                    .eq(word(result, width));
                check(root.clone(), true, budget, end);
                check(root.not(), false, budget, end);
            }
        }
    });
}

#[test]
fn native_truncating_infinities_and_invalid_operands_promise_nan_class_only() {
    with_native_owner(|budget, end| {
        for (width, one, inf, nan) in [
            (32, 0x3f800000u64, 0x7f800000u64, 0x7fc00001u64),
            (
                64,
                0x3ff0000000000000,
                0x7ff0000000000000,
                0x7ff8000000000001,
            ),
        ] {
            let finite = word(one, width)
                .fp_truncating_rem(word(inf, width))
                .eq(word(one, width));
            check(finite.clone(), true, budget, end);
            check(finite.not(), false, budget, end);
            for (a, b) in [(inf, one), (one, 0), (nan, one), (one, nan)] {
                let value = word(a, width).fp_truncating_rem(word(b, width));
                let class = value.clone().fp_is_nan();
                check(class.clone(), true, budget, end);
                check(class.not(), false, budget, end);
                check(value.clone().fp_eq(value), false, budget, end);
            }
        }
    });
}
