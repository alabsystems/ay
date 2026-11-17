// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Intended native Bool/BV checks of complete attached DATA, not CHC verdicts.

use super::*;
use ay_chc::{SmtContext, SmtResult};
use std::sync::Arc;

pub(in crate::fp::tests) fn original_owner<T>(
    run: impl FnOnce(&mut WorkBudget<'_>, Instant) -> T,
) -> T {
    let end = Instant::now() + Duration::from_secs(20);
    let enclosing = ay_core::resource::current_check_stop().unwrap();
    let original = enclosing.clone();
    let _stop = ay_core::resource::enter_check_stop(Arc::new(move || {
        Instant::now() >= end || enclosing.as_ref().is_some_and(|stop| stop())
    }));
    let mut work = WORK;
    let mut bytes = BYTES;
    let mut owner = |w: usize, b: usize| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        if original.as_ref().is_some_and(|stop| stop()) {
            return Err(QueryError::Invalid("original enclosing check-stop"));
        }
        work = work.checked_sub(w as u64).ok_or(QueryError::Exhausted)?;
        bytes = bytes.checked_sub(b as u64).ok_or(QueryError::Exhausted)?;
        Ok(())
    };
    let mut budget = WorkBudget::with_admission(WORK, &mut owner);
    let result = run(&mut budget, end);
    budget.charge(0).unwrap();
    result
}

fn check(
    roots: &[Expr],
    word: &Expr,
    target: &ChcVar,
    raw: (u64, u32),
    expected: bool,
    budget: &mut WorkBudget<'_>,
    end: Instant,
) {
    // Fixed fixture/scratch fee on the SAME per-test ledger before copying.
    // Native SMT work has its separate native caps, not prepaid solver credit.
    budget.admit(1_048_576, 1_048_576).unwrap();
    let problem = ChcProblem::new();
    let bindings = [FpExprInputBinding {
        source: word,
        target,
    }];
    let pin = ChcExpr::Op(
        ChcOp::Eq,
        vec![
            Arc::new(ChcExpr::Var(target.clone())),
            Arc::new(ChcExpr::BitVec(u128::from(raw.0), raw.1)),
        ],
    );
    let old = ClauseBody::constraint(pin);
    {
        let output = lower_fp_expr_clause(roots, &bindings, &problem, budget).unwrap();
        let (body, source) = output.into_body(old).unwrap().into_parts().unwrap();
        assert!(std::ptr::eq(source.roots(), roots));
        budget.charge(0).unwrap();
        let mut native = SmtContext::new();
        native.set_term_memory_budget(Some(128 * 1024 * 1024));
        let remaining = end.saturating_duration_since(Instant::now());
        assert!(!remaining.is_zero());
        let result = native.check_sat_with_timeout(body.constraint.as_ref().unwrap(), remaining);
        if expected {
            assert!(matches!(result, SmtResult::Sat(_)));
        } else {
            assert!(result.is_unsat());
        }
        drop(result);
        drop(native);
        drop(body);
    }
    budget.charge(0).unwrap();
}

#[test]
fn original_raw_words_have_native_classifications_and_wrong_roots_refuse() {
    original_owner(|budget, end| {
        for (width, one, minus_zero, inf, nan) in [
            (32, 0x3f800000u64, 0x80000000, 0x7f800000, 0x7fc00001),
            (
                64,
                0x3ff0000000000000u64,
                0x8000000000000000,
                0x7ff0000000000000,
                0x7ff8000000000001,
            ),
        ] {
            let (word, target) = raw_input(width);
            let fp = fields(word.clone(), width);
            let cases = [
                (one, fp.clone().fp_is_normal()),
                (
                    minus_zero,
                    fp.clone().fp_is_zero().and(fp.clone().fp_is_negative()),
                ),
                (inf, fp.clone().fp_is_infinite()),
                (nan, fp.clone().fp_is_nan()),
                (
                    nan,
                    fp.clone()
                        .eq(fp.clone())
                        .and(fp.clone().fp_eq(fp.clone()).not()),
                ),
            ];
            for (bits, root) in cases {
                check(
                    &[root.clone()],
                    &word,
                    &target,
                    (bits, width),
                    true,
                    budget,
                    end,
                );
                check(
                    &[root.not()],
                    &word,
                    &target,
                    (bits, width),
                    false,
                    budget,
                    end,
                );
            }
        }
    });
}

#[test]
fn all_five_literal_modes_keep_the_same_raw_word_and_full_arithmetic_relation() {
    original_owner(|budget, end| {
        for (width, bits) in [(32, 0x3f800000u64), (64, 0x3ff0000000000000u64)] {
            let (word, target) = raw_input(width);
            let fp = fields(word.clone(), width);
            let sort = fp.sort().clone();
            for mode in [
                RoundingMode::RNE,
                RoundingMode::RNA,
                RoundingMode::RTP,
                RoundingMode::RTN,
                RoundingMode::RTZ,
            ] {
                let sum = fp.clone().fp_add(mode, Expr::fp_plus_zero(&sort));
                let equality = sum.eq(fp.clone());
                check(
                    &[equality.clone(), fp.clone().fp_is_normal()],
                    &word,
                    &target,
                    (bits, width),
                    true,
                    budget,
                    end,
                );
                check(
                    &[equality.not(), fp.clone().fp_is_normal()],
                    &word,
                    &target,
                    (bits, width),
                    false,
                    budget,
                    end,
                );
            }
        }
    });
}
