// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_chc::{SmtContext, SmtResult};

fn original_owner<T>(run: impl FnOnce(&mut WorkBudget<'_>, Instant) -> T) -> T {
    let end = Instant::now() + Duration::from_secs(20);
    let enclosing = ay_core::resource::current_check_stop().unwrap();
    let original = enclosing.clone();
    let _scope = ay_core::resource::enter_check_stop(Arc::new(move || {
        Instant::now() >= end || enclosing.as_ref().is_some_and(|stop| stop())
    }));
    let mut work = WORK;
    let mut bytes = BYTES;
    let mut owner = |w: usize, b: usize| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        if original.as_ref().is_some_and(|stop| stop()) {
            return Err(QueryError::Invalid("enclosing guard owner"));
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
    words: &[Expr; 2],
    targets: &[ChcVar; 2],
    raw: [u64; 2],
    expected: bool,
    budget: &mut WorkBudget<'_>,
    end: Instant,
) {
    // Fixed bounded test scratch, distinct from the production circuit fee.
    budget.admit(1_048_576, 1_048_576).unwrap();
    let bindings = links(words, targets);
    let namespace = ChcProblem::new();
    let mut pins = Vec::new();
    for (target, bits) in targets.iter().zip(raw) {
        budget.charge(1024).unwrap();
        let ChcSort::BitVec(width) = &target.sort else {
            panic!()
        };
        pins.push(Arc::new(ChcExpr::Op(
            ChcOp::Eq,
            vec![
                Arc::new(ChcExpr::Var(target.clone())),
                Arc::new(ChcExpr::BitVec(u128::from(bits), *width)),
            ],
        )));
    }
    let output = lower_fp_expr_clause(roots, &bindings, &namespace, budget).unwrap();
    let original = ClauseBody::constraint(ChcExpr::Op(ChcOp::And, pins));
    let (body, source) = output.into_body(original).unwrap().into_parts().unwrap();
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
    drop(source);
    budget.charge(0).unwrap();
}

#[test]
fn all_relations_equality_and_distinct_keep_signed_and_unsigned_width_boundaries() {
    original_owner(|budget, end| {
        for width in [1, 8, 32, 64] {
            let (words, targets) = inputs(width);
            let [a, b] = words.clone();
            let maximum = if width == 64 {
                u64::MAX
            } else {
                (1u64 << width) - 1
            };
            let root = Expr::and_many(vec![
                a.clone().bvult(b.clone()).not(),
                a.clone().bvule(b.clone()).not(),
                a.clone().bvugt(b.clone()),
                a.clone().bvuge(b.clone()),
                a.clone().bvslt(b.clone()),
                a.clone().bvsle(b.clone()),
                a.clone().bvsgt(b.clone()).not(),
                a.clone().bvsge(b.clone()).not(),
                a.clone().eq(b.clone()).not(),
                Expr::distinct(vec![a, b]),
            ]);
            check(
                &[root.clone()],
                &words,
                &targets,
                [maximum, 0],
                true,
                budget,
                end,
            );
            check(
                &[root.not()],
                &words,
                &targets,
                [maximum, 0],
                false,
                budget,
                end,
            );
            let equal = words[0]
                .clone()
                .eq(words[1].clone())
                .and(Expr::distinct(words.to_vec()).not());
            check(
                &[equal.clone()],
                &words,
                &targets,
                [0, 0],
                true,
                budget,
                end,
            );
            check(&[equal.not()], &words, &targets, [0, 0], false, budget, end);
        }
    });
}

#[test]
fn mixed_or_and_fp_selection_share_the_original_word_cache_in_both_branches() {
    original_owner(|budget, end| {
        for (width, one, minus_one) in [
            (32, 0x3f800000u64, 0xbf800000u64),
            (64, 0x3ff0000000000000u64, 0xbff0000000000000u64),
        ] {
            let (words, targets) = inputs(width);
            let guard = words[0].clone().bvult(words[1].clone());
            let selected = Expr::ite(
                guard.clone(),
                fields(words[0].clone(), width),
                fields(words[1].clone(), width),
            );
            let expected = fields(Expr::bitvec_const(one, width), width);
            let identity = selected.eq(expected);
            let root = identity.and(guard.or(fields(words[0].clone(), width).fp_is_normal()));
            for raw in [[one, minus_one], [minus_one, one]] {
                check(&[root.clone()], &words, &targets, raw, true, budget, end);
                check(
                    &[root.clone().not()],
                    &words,
                    &targets,
                    raw,
                    false,
                    budget,
                    end,
                );
            }
        }
    });
}

#[test]
fn direct_extract_and_constant_guards_retain_full_nan_and_infinity_word_links() {
    original_owner(|budget, end| {
        for (width, nan, inf) in [
            (32, 0x7fc00001u64, 0x7f800000u64),
            (64, 0x7ff8000000000001u64, 0x7ff0000000000000u64),
        ] {
            let (words, targets) = inputs(width);
            let fraction = if width == 32 { 23 } else { 52 };
            let exponent = words[0].clone().extract(width - 2, fraction);
            let exponent_width = width - 1 - fraction;
            let maximum = (1u64 << exponent_width) - 1;
            let guard = exponent.eq(Expr::bitvec_const(maximum, exponent_width));
            let root = guard
                .and(fields(words[0].clone(), width).fp_is_nan())
                .and(fields(words[1].clone(), width).fp_is_infinite());
            check(
                &[root.clone()],
                &words,
                &targets,
                [nan, inf],
                true,
                budget,
                end,
            );
            check(
                &[root.not()],
                &words,
                &targets,
                [nan, inf],
                false,
                budget,
                end,
            );
        }
    });
}
