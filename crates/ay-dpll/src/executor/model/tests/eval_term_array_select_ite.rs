// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Model-time reads through array conditionals. Raw ITEs avoid constructor
//! folding, and direct evaluate_select calls exercise the structural walker.

use super::*;

fn constant(executor: &mut Executor, number: i64) -> TermId {
    let value = executor.ctx.terms.mk_int(BigInt::from(number));
    executor.ctx.terms.mk_const_array(Sort::Int, value)
}

#[test]
fn conditional_array_read_uses_each_exact_boolean_branch() {
    for (choice, expected) in [(true, 11), (false, 99)] {
        let mut executor = Executor::new();
        let guard = executor.ctx.terms.mk_var("guard", Sort::Bool);
        let yes = constant(&mut executor, 11);
        let no = constant(&mut executor, 99);
        let array = executor.ctx.terms.mk_ite_raw(guard, yes, no);
        let index = executor.ctx.terms.mk_int(BigInt::from(3));
        let model = model_with_sat_assignments(&[(guard, choice)]);
        assert_eq!(
            executor.evaluate_select(&model, array, index),
            EvalValue::Rational(BigRational::from(BigInt::from(expected)))
        );
    }
}

#[test]
fn conditional_array_read_peels_store_and_scopes_a_selected_lambda() {
    let mut executor = Executor::new();
    let guard = executor.ctx.terms.mk_var("guard", Sort::Bool);
    let x = executor.ctx.terms.mk_var("lambda_index", Sort::Int);
    let one = executor.ctx.terms.mk_int(BigInt::from(1));
    let body = executor.ctx.terms.mk_add(vec![x, one]);
    let lambda = executor.ctx.terms.mk_lambda_array(x, body);
    let five = executor.ctx.terms.mk_int(BigInt::from(5));
    let forty_two = executor.ctx.terms.mk_int(BigInt::from(42));
    let selected = executor.ctx.terms.mk_store(lambda, five, forty_two);
    let no = constant(&mut executor, 99);
    let conditional = executor.ctx.terms.mk_ite_raw(guard, selected, no);
    let seven = executor.ctx.terms.mk_int(BigInt::from(7));
    let eighty = executor.ctx.terms.mk_int(BigInt::from(80));
    let array = executor.ctx.terms.mk_store(conditional, seven, eighty);
    let mut model = model_with_sat_assignments(&[(guard, true)]);
    let mut values = HashMap::default();
    values.insert(x, BigInt::from(99));
    model.lia_model = Some(LiaModel { values });
    for (address, expected) in [(3, 4), (5, 42), (7, 80)] {
        let index = executor.ctx.terms.mk_int(BigInt::from(address));
        assert_eq!(
            executor.evaluate_select(&model, array, index),
            EvalValue::Rational(BigRational::from(BigInt::from(expected)))
        );
    }
    assert_eq!(
        executor.evaluate_term(&model, body),
        EvalValue::Rational(BigRational::from(BigInt::from(100))),
        "the selected lambda must restore the ambient binder value"
    );
}

#[test]
fn conditional_array_read_keeps_the_full_width_symbolic_address() {
    for (address, expected) in [(u64::MAX, 63u8), (0, 0)] {
        let mut executor = Executor::new();
        let guard = executor.ctx.terms.mk_var("guard", Sort::Bool);
        let index = executor.ctx.terms.mk_var("address", Sort::bitvec(64));
        let last = executor.ctx.terms.mk_bitvec(BigInt::from(u64::MAX), 64);
        let zero = executor.ctx.terms.mk_bitvec(BigInt::from(0), 8);
        let sixty_three = executor.ctx.terms.mk_bitvec(BigInt::from(63), 8);
        let nine = executor.ctx.terms.mk_bitvec(BigInt::from(9), 8);
        let base = executor.ctx.terms.mk_const_array(Sort::bitvec(64), zero);
        let selected = executor.ctx.terms.mk_store(base, last, sixty_three);
        let no = executor.ctx.terms.mk_const_array(Sort::bitvec(64), nine);
        let array = executor.ctx.terms.mk_ite_raw(guard, selected, no);
        let mut model = model_with_sat_assignments(&[(guard, true)]);
        let mut values = HashMap::default();
        values.insert(index, BigInt::from(address));
        model.bv_model = Some(BvModel {
            values,
            term_to_bits: HashMap::default(),
            bool_overrides: HashMap::default(),
        });
        assert_eq!(
            executor.evaluate_select(&model, array, index),
            EvalValue::BitVec {
                value: BigInt::from(expected),
                width: 8,
            }
        );
    }
}

#[test]
fn conditional_array_read_does_not_guess_an_undecidable_guard_from_sat_or_array_rows() {
    let mut executor = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let a = executor.ctx.terms.mk_var("a", array_sort.clone());
    let b = executor.ctx.terms.mk_var("b", array_sort);
    let guard = executor.ctx.terms.mk_eq_coerce_no_ite_expand(a, b);
    let yes = constant(&mut executor, 11);
    let no = constant(&mut executor, 99);
    let array = executor.ctx.terms.mk_ite_raw(guard, yes, no);
    let index = executor.ctx.terms.mk_int(BigInt::from(3));
    let mut model = model_with_sat_assignments(&[(guard, true)]);
    model.array_model = Some(ArrayModel {
        array_values: HashMap::from_iter([(
            array,
            ay_arrays::ArrayInterpretation {
                default: Some("11".to_owned()),
                stores: vec![],
                index_sort: Some(Sort::Int),
                element_sort: Some(Sort::Int),
            },
        )]),
        ..Default::default()
    });
    assert_eq!(executor.evaluate_term(&model, guard), EvalValue::Unknown);
    assert_eq!(
        executor.evaluate_select(&model, array, index),
        EvalValue::Unknown,
        "a partial ITE interpretation must not resolve its unknown guard"
    );
}

#[test]
fn conditional_array_read_does_not_evaluate_an_unselected_incomplete_array() {
    for (choice, expected) in [
        (
            true,
            EvalValue::Rational(BigRational::from(BigInt::from(11))),
        ),
        (false, EvalValue::Unknown),
    ] {
        let mut executor = Executor::new();
        let guard = executor.ctx.terms.mk_var("guard", Sort::Bool);
        let yes = constant(&mut executor, 11);
        let no = executor
            .ctx
            .terms
            .mk_var("incomplete", Sort::array(Sort::Int, Sort::Int));
        let array = executor.ctx.terms.mk_ite_raw(guard, yes, no);
        let index = executor.ctx.terms.mk_int(BigInt::from(3));
        let model = model_with_sat_assignments(&[(guard, choice)]);
        assert_eq!(executor.evaluate_select(&model, array, index), expected);
    }
}

#[test]
fn conditional_array_read_restores_guards_depending_on_an_outer_lambda_index() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("outer_index", Sort::Int);
    let five = executor.ctx.terms.mk_int(BigInt::from(5));
    let guard = executor.ctx.terms.mk_lt(x, five);
    let yes = constant(&mut executor, 11);
    let no = constant(&mut executor, 99);
    let array = executor.ctx.terms.mk_ite_raw(guard, yes, no);
    let body = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), vec![array, x], Sort::Int);
    let lambda = executor.ctx.terms.mk_lambda_array(x, body);
    let mut values = HashMap::default();
    values.insert(x, BigInt::from(99));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values });
    for (address, expected) in [(3, 11), (7, 99), (3, 11)] {
        let index = executor.ctx.terms.mk_int(BigInt::from(address));
        assert_eq!(
            executor.evaluate_select(&model, lambda, index),
            EvalValue::Rational(BigRational::from(BigInt::from(expected)))
        );
    }
    assert_eq!(
        executor.evaluate_term(&model, guard),
        EvalValue::Bool(false)
    );
}
