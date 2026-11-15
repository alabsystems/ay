// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::executor::model::{eval_guard, tests::empty_model};
use crate::executor_types::UnknownOrigin;

const BITS: u128 = 0x3fff_8000_0000_0000_0000_0000_0000_0001;
const FRACTION: u128 = (1u128 << 111) + 1;

#[derive(Clone, Copy)]
enum Spelling {
    Constructor,
    Reinterpret,
}

fn literal(executor: &mut Executor, spelling: Spelling) -> TermId {
    let terms = &mut executor.ctx.terms;
    let args = match spelling {
        Spelling::Constructor => vec![
            terms.mk_bitvec(BigInt::from(0), 1),
            terms.mk_bitvec(BigInt::from(0x3fff), 15),
            terms.mk_bitvec(BigInt::from(FRACTION), 112),
        ],
        Spelling::Reinterpret => vec![terms.mk_bitvec(BigInt::from(BITS), 128)],
    };
    let name = match spelling {
        Spelling::Constructor => "fp",
        Spelling::Reinterpret => "to_fp",
    };
    terms.mk_app(Symbol::named(name), args, Sort::FloatingPoint(15, 113))
}

fn refuses_child_then_recovers(spelling: Spelling, visits: usize) {
    let mut executor = Executor::new();
    let term = literal(&mut executor, spelling);
    let model = empty_model();
    let read = executor.begin_external_evaluation_read();
    // The application itself enters first. This budget is exhausted by an
    // actual field child, after evaluate_fp_app has captured its poison stamp.
    let budget = eval_guard::EvalWorkBudget::new(visits);
    assert!(matches!(
        executor.evaluate_term(&model, term),
        EvalValue::Unknown
    ));
    assert!(budget.exhausted(), "a field child must actually be refused");
    assert_eq!(
        executor.evaluation_stop_origin(),
        Some(UnknownOrigin::DeterministicResourceBudget)
    );
    drop(budget);
    assert!(matches!(
        executor.evaluate_term(&model, term),
        EvalValue::Unknown
    ));
    assert_eq!(
        executor.evaluation_stop_origin(),
        Some(UnknownOrigin::DeterministicResourceBudget)
    );
    drop(read);

    let _fresh = executor.begin_external_evaluation_read();
    assert_eq!(executor.evaluation_stop_origin(), None);
    let EvalValue::Fp(value) = executor.evaluate_term(&model, term) else {
        panic!("fresh read must decode the original complete binary128 value");
    };
    assert_eq!(value.to_ieee_bv(), (BigInt::from(BITS), 128));
    assert_eq!(executor.evaluation_stop_origin(), None);
}

#[test]
fn constructor_field_work_refusal_is_sticky_until_a_fresh_read() {
    // Refuse sign, exponent, and fraction separately; no earlier decoded
    // prefix licenses a fabricated or reconstructed FP result.
    for visits in [1, 2, 3] {
        refuses_child_then_recovers(Spelling::Constructor, visits);
    }
}

#[test]
fn reinterpret_field_work_refusal_is_sticky_until_a_fresh_read() {
    refuses_child_then_recovers(Spelling::Reinterpret, 1);
}

#[test]
fn malformed_model_fields_are_not_truncated_or_reconstructed() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let sign = terms.mk_bitvec(BigInt::from(0), 1);
    let exponent = terms.mk_bitvec(BigInt::from(0x3fff), 15);
    let fraction = terms.mk_var("fraction", Sort::bitvec(112));
    let packed = terms.mk_var("packed", Sort::bitvec(128));
    let constructor = terms.mk_app(
        Symbol::named("fp"),
        [sign, exponent, fraction],
        Sort::FloatingPoint(15, 113),
    );
    let reinterpret = terms.mk_app(
        Symbol::named("to_fp"),
        [packed],
        Sort::FloatingPoint(15, 113),
    );
    for (term, field, width, good) in [
        (constructor, fraction, 112, FRACTION),
        (reinterpret, packed, 128, BITS),
    ] {
        // Model-owned field pins are deliberately malformed test inputs. The
        // checked decoder must reject both payload and evaluated-width errors.
        for (value, actual_width) in [
            (BigInt::from(-1), width),
            (BigInt::from(1) << width as usize, width),
            (BigInt::from(good), width + 1),
        ] {
            let mut model = empty_model();
            model.dt_pins.insert(
                field,
                EvalValue::BitVec {
                    value,
                    width: actual_width,
                },
            );
            let _read = executor.begin_external_evaluation_read();
            assert!(matches!(
                executor.evaluate_term(&model, term),
                EvalValue::Unknown
            ));
            assert_eq!(executor.evaluation_stop_origin(), None);
        }
        let mut model = empty_model();
        model.dt_pins.insert(
            field,
            EvalValue::BitVec {
                value: BigInt::from(good),
                width,
            },
        );
        let _read = executor.begin_external_evaluation_read();
        let EvalValue::Fp(value) = executor.evaluate_term(&model, term) else {
            panic!("the exact-width positive field control must decode");
        };
        assert_eq!(value.to_ieee_bv(), (BigInt::from(BITS), 128));
    }

    let terms = &mut executor.ctx.terms;
    let bad_sign = terms.mk_bitvec(BigInt::from(0), 2);
    let bad_packed = terms.mk_bitvec(BigInt::from(0), 127);
    let malformed_constructor = terms.mk_app(
        Symbol::named("fp"),
        [bad_sign, exponent, fraction],
        Sort::FloatingPoint(15, 113),
    );
    let malformed_reinterpret = terms.mk_app(
        Symbol::named("to_fp"),
        [bad_packed],
        Sort::FloatingPoint(15, 113),
    );
    let model = empty_model();
    let _read = executor.begin_external_evaluation_read();
    for term in [malformed_constructor, malformed_reinterpret] {
        assert!(matches!(
            executor.evaluate_term(&model, term),
            EvalValue::Unknown
        ));
        assert_eq!(executor.evaluation_stop_origin(), None);
    }
}
