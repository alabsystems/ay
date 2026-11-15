// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Clone, Copy)]
enum Level {
    Element,
    Vector,
    Data,
    Cell,
}

fn at_level(level: Level, data: ModelValue) -> ModelValue {
    match level {
        Level::Element => element(data),
        Level::Vector => vector(data),
        Level::Data => data,
        Level::Cell => bv(5, 40),
    }
}

#[test]
fn whole_record_vector_and_array_requirements_keep_defaults_and_last_store() {
    for level in [Level::Element, Level::Vector, Level::Data] {
        for expected in [5, 6] {
            let mut terms = TermStore::new();
            let f = Fixture::new(&mut terms);
            let [element, vector, data_term, cell] = f.read(&mut terms, f.a, f.outer, f.inner);
            let (target, sort) = match level {
                Level::Element => (element, f.element.clone()),
                Level::Vector => (vector, f.vector.clone()),
                Level::Data => (data_term, f.data.clone()),
                Level::Cell => unreachable!(),
            };
            let pin = terms.mk_var("parent_value", sort);
            let parent = eq(&mut terms, target, pin);
            let observed = eq_bv(&mut terms, cell, expected, 40);
            let mut model = Model::default();
            model
                .leaves
                .insert(pin, Arc::new(at_level(level, data(9, &[(33, 4), (33, 5)]))));
            if expected != 5 {
                refused(&terms, &model, &[parent, observed]);
                continue;
            }
            let roots = [parent, observed];
            let assignments = complete(&terms, &model, &roots);
            model.install(&terms, assignments);
            assert_confirmed(&confirm_completed_model(&terms, &model, &roots));
            let EvalOutcome::Value(ModelValue::Array(recovered)) =
                evaluate_term(&terms, &model, data_term)
            else {
                panic!("full parent array must survive");
            };
            assert_eq!(recovered.store.len(), 2);
            assert!(value_eq(&recovered.default, &bv(9, 40)).unwrap());
            assert!(value_eq(&recovered.store[0].1, &bv(4, 40)).unwrap());
            assert!(value_eq(&recovered.store[1].1, &bv(5, 40)).unwrap());
            let absent = terms.mk_bitvec(BigInt::from(99), 64);
            let [_, _, _, default_read] = f.read(&mut terms, f.a, f.outer, absent);
            assert_bv(&terms, &model, default_read, 9, 40);
        }
    }
}

#[test]
fn committed_whole_parent_and_terminal_pins_only_narrow_aliased_requirements() {
    for level in [Level::Element, Level::Vector, Level::Data, Level::Cell] {
        let mut terms = TermStore::new();
        let f = Fixture::new(&mut terms);
        let chain = f.read(&mut terms, f.a, f.outer, f.inner);
        let [_, _, _, other] = f.read(&mut terms, f.b, f.outer, f.inner);
        let target = match level {
            Level::Element => chain[0],
            Level::Vector => chain[1],
            Level::Data => chain[2],
            Level::Cell => chain[3],
        };
        let mut model = Model::default();
        let pinned = at_level(level, data(9, &[(33, 4), (33, 5)]));
        match level {
            Level::Element | Level::Cell => {
                model.selects.insert(target, pinned);
            }
            Level::Vector | Level::Data => {
                model.applications.insert(target, pinned);
            }
        }
        assert_bv(&terms, &model, chain[3], 5, 40);
        let alias = eq(&mut terms, f.a, f.b);
        let committed = eq_bv(&mut terms, chain[3], 5, 40);
        let same = eq_bv(&mut terms, other, 5, 40);
        let different = eq_bv(&mut terms, other, 6, 40);
        refused(&terms, &model, &[committed, alias, different]);
        let roots = [committed, alias, same];
        let assignments = complete(&terms, &model, &roots);
        model.install(&terms, assignments);
        assert_confirmed(&confirm_completed_model(&terms, &model, &roots));
        assert_bv(&terms, &model, other, 5, 40);
    }
}

#[test]
fn unselected_true_or_arm_still_conserves_its_committed_inner_read() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let [_, _, _, pinned] = f.read(&mut terms, f.a, f.outer, f.inner);
    let [_, _, _, other] = f.read(&mut terms, f.b, f.outer, f.inner);
    let yes = terms.mk_bool(true);
    let pinned_false = eq_bv(&mut terms, pinned, 6, 40);
    let already_true = app(&mut terms, "or", &[yes, pinned_false], Sort::Bool);
    let alias = eq(&mut terms, f.a, f.b);
    let same = eq_bv(&mut terms, other, 5, 40);
    let conflict = eq_bv(&mut terms, other, 6, 40);
    let mut model = Model::default();
    model.selects.insert(pinned, bv(5, 40));
    assert_confirmed(&confirm_completed_model(&terms, &model, &[already_true]));
    refused(&terms, &model, &[already_true, alias, conflict]);
    let roots = [already_true, alias, same];
    let assignments = complete(&terms, &model, &roots);
    model.install(&terms, assignments);
    assert_confirmed(&confirm_completed_model(&terms, &model, &roots));
    assert_bv(&terms, &model, other, 5, 40);
}

#[test]
fn an_evaluable_pin_under_an_unlocalizable_array_receiver_stays_refused() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let [_, _, data_term, _] = f.read(&mut terms, f.a, f.outer, f.inner);
    let [_, _, _, other] = f.read(&mut terms, f.b, f.outer, f.inner);
    let yes = terms.mk_bool(true);
    let unrelated = terms.mk_var("other_data", f.data.clone());
    let conditional = terms.mk_ite_raw(yes, data_term, unrelated);
    let pinned = app(
        &mut terms,
        "select",
        &[conditional, f.inner],
        Sort::bitvec(40),
    );
    let already_true = eq_bv(&mut terms, pinned, 5, 40);
    let alias = eq(&mut terms, f.a, f.b);
    let requirement = eq_bv(&mut terms, other, 5, 40);
    let mut model = Model::default();
    model.selects.insert(pinned, bv(5, 40));
    assert_bv(&terms, &model, pinned, 5, 40);
    assert_confirmed(&confirm_completed_model(&terms, &model, &[already_true]));
    refused(&terms, &model, &[already_true, alias, requirement]);
}

#[test]
fn malformed_parent_defaults_overwritten_values_and_keys_are_not_ignored() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let [_, _, data_term, cell] = f.read(&mut terms, f.a, f.outer, f.inner);
    let parent = terms.mk_var("parent", f.data.clone());
    let parent_eq = eq(&mut terms, data_term, parent);
    let observed = eq_bv(&mut terms, cell, 5, 40);
    for array in [
        ArrayValue {
            default: ModelValue::Bool(false),
            store: vec![(bv(33, 64), bv(5, 40))],
        },
        ArrayValue {
            default: bv(0, 40),
            store: vec![
                (bv(33, 64), ModelValue::Bool(false)),
                (bv(33, 64), bv(5, 40)),
            ],
        },
        ArrayValue {
            default: bv(0, 40),
            store: vec![(bv(99, 32), bv(7, 40)), (bv(33, 64), bv(5, 40))],
        },
    ] {
        let mut model = Model::default();
        model
            .leaves
            .insert(parent, Arc::new(ModelValue::Array(Box::new(array))));
        refused(&terms, &model, &[parent_eq, observed]);
    }
}

#[test]
fn an_inner_array_cell_can_be_a_record_with_distinct_observed_fields() {
    let mut terms = TermStore::new();
    let lit = record(
        "PbLit",
        "mkPbLit",
        vec![
            DatatypeField::new("var", Sort::bitvec(32)),
            DatatypeField::new("negated", Sort::Bool),
        ],
    );
    let data_sort = Sort::array(Sort::bitvec(64), lit.clone());
    let outer_sort = record(
        "Unpacked",
        "mkUnpacked",
        vec![DatatypeField::new("data", data_sort.clone())],
    );
    let array = terms.mk_var(
        "unpacked",
        Sort::array(Sort::bitvec(64), outer_sort.clone()),
    );
    let zero = terms.mk_bitvec(BigInt::from(0), 64);
    let one = terms.mk_bitvec(BigInt::from(1), 64);
    let outer = app(&mut terms, "select", &[array, zero], outer_sort);
    let data = app(&mut terms, "data", &[outer], data_sort);
    let first = app(&mut terms, "select", &[data, zero], lit.clone());
    let second = app(&mut terms, "select", &[data, one], lit);
    let variable = app(&mut terms, "var", &[first], Sort::bitvec(32));
    let next_variable = app(&mut terms, "var", &[second], Sort::bitvec(32));
    let negative = app(&mut terms, "negated", &[first], Sort::Bool);
    let yes = terms.mk_bool(true);
    let no = terms.mk_bool(false);
    let first_variable = eq_bv(&mut terms, variable, 7, 32);
    let second_variable = eq_bv(&mut terms, next_variable, 8, 32);
    let negative_true = eq(&mut terms, negative, yes);
    let negative_false = eq(&mut terms, negative, no);
    let mut model = Model::default();
    refused(&terms, &model, &[negative_true, negative_false]);
    let roots = [first_variable, second_variable, negative_true];
    let assignments = complete(&terms, &model, &roots);
    model.install(&terms, assignments);
    assert_confirmed(&confirm_completed_model(&terms, &model, &roots));
    assert_bv(&terms, &model, variable, 7, 32);
    assert_bv(&terms, &model, next_variable, 8, 32);
}
