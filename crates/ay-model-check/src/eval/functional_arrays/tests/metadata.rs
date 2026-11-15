// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn rich_case() -> Case {
    let mut case = case(false, 3);
    let TermData::App(_, lambda) = case.terms.get(case.lambda).clone() else {
        panic!("lambda")
    };
    let TermData::Ite(condition, positive, negative) = case.terms.get(lambda[1]).clone() else {
        panic!("body")
    };
    let TermData::App(_, read) = case.terms.get(positive).clone() else {
        panic!("read")
    };
    let zero = case.terms.mk_bitvec(0.into(), 64);
    let shifted = app(&mut case.terms, "bvadd", &[read[1], zero], Sort::bitvec(64));
    let positive = app(
        &mut case.terms,
        "select",
        &[read[0], shifted],
        Sort::bitvec(8),
    );
    let body = app(
        &mut case.terms,
        "ite",
        &[condition, positive, negative],
        Sort::bitvec(8),
    );
    let sort = case.terms.sort(case.target).clone();
    case.lambda = app(&mut case.terms, "lambda-array", &[lambda[0], body], sort);
    case.definition = app(
        &mut case.terms,
        "=",
        &[case.target, case.lambda],
        Sort::Bool,
    );
    assert!(matches!(
        confirm_completed_model(&case.terms, &case.view, &[case.definition]),
        GateVerdict::ConfirmedSat
    ));
    case
}

fn occurrences(terms: &TermStore, root: TermId, name: &str) -> Vec<TermId> {
    let mut result = Vec::new();
    let mut pending = vec![root];
    while let Some(term) = pending.pop() {
        if let TermData::App(symbol, _) = terms.get(term) {
            if symbol.name() == name {
                result.push(term);
            }
        }
        pending.extend(terms.children(term));
    }
    result
}

fn replace(terms: &mut TermStore, root: TermId, original: TermId, changed: TermId) -> TermId {
    if root == original {
        return changed;
    }
    let sort = terms.sort(root).clone();
    match terms.get(root).clone() {
        TermData::App(symbol, args) => {
            let args: Vec<_> = args
                .iter()
                .map(|child| replace(terms, *child, original, changed))
                .collect();
            terms.mk_app(symbol, &args, sort)
        }
        _ => root,
    }
}

fn refuses_original(case: &mut Case, lambda: TermId) {
    assert!(recognize_range_lambda(&case.terms, lambda).is_none());
    assert!(Evaluator::new(&case.terms, &case.view)
        .capture_array_snapshot(lambda)
        .is_err());
    let equality = app(&mut case.terms, "=", &[case.target, lambda], Sort::Bool);
    assert!(!matches!(
        confirm_completed_model(&case.terms, &case.view, &[equality]),
        GateVerdict::ConfirmedSat
    ));
}

#[test]
fn every_indexed_range_operator_refuses_canonical_grammar_and_whole_equality_credit() {
    for name in [
        "lambda-array",
        "ite",
        "and",
        "bvule",
        "bvult",
        "select",
        "bvsub",
        "bvadd",
    ] {
        let original = rich_case();
        let nodes = occurrences(&original.terms, original.lambda, name);
        assert!(!nodes.is_empty(), "actual occurrence of {name}");
        for index in 0..nodes.len() {
            let mut case = rich_case();
            let node = occurrences(&case.terms, case.lambda, name)[index];
            let TermData::App(_, args) = case.terms.get(node).clone() else {
                panic!("actual operator")
            };
            let sort = case.terms.sort(node).clone();
            let indexed = case
                .terms
                .mk_app(Symbol::indexed(name, vec![0]), &args, sort);
            let root = case.lambda;
            let lambda = replace(&mut case.terms, root, node, indexed);
            refuses_original(&mut case, lambda);
        }
    }
}

#[test]
fn every_malformed_range_result_sort_refuses_literal_semantics_and_equality_credit() {
    for name in [
        "lambda-array",
        "ite",
        "and",
        "bvule",
        "bvult",
        "select",
        "bvsub",
        "bvadd",
    ] {
        let original = rich_case();
        for index in 0..occurrences(&original.terms, original.lambda, name).len() {
            let mut case = rich_case();
            let node = occurrences(&case.terms, case.lambda, name)[index];
            let TermData::App(symbol, args) = case.terms.get(node).clone() else {
                panic!("operator")
            };
            let wrong = match case.terms.sort(node) {
                Sort::Bool => Sort::bitvec(64),
                Sort::Array(_) => Sort::array(Sort::bitvec(64), Sort::bitvec(16)),
                _ => Sort::Bool,
            };
            let changed = case.terms.mk_app(symbol, &args, wrong);
            let root = case.lambda;
            let lambda = replace(&mut case.terms, root, node, changed);
            refuses_original(&mut case, lambda);
        }
    }
}

#[test]
fn indexed_store_and_constant_constructors_never_acquire_snapshot_or_equality_credit() {
    for name in ["store", "const-array"] {
        let mut case = case(false, 3);
        let dst = recognize_range_lambda(&case.terms, case.lambda)
            .expect("recipe")
            .destination;
        let index = case.terms.mk_bitvec(0.into(), 64);
        let value = case.terms.mk_bitvec(9.into(), 8);
        let args = if name == "store" {
            vec![dst, index, value]
        } else {
            vec![value]
        };
        let sort = case.terms.sort(dst).clone();
        let literal = case.terms.mk_app(Symbol::named(name), &args, sort.clone());
        let snapshot = Evaluator::new(&case.terms, &case.view)
            .capture_array_snapshot(literal)
            .expect("canonical constructor");
        case.view.arrays.insert(case.target, snapshot);
        let indexed = case
            .terms
            .mk_app(Symbol::indexed(name, vec![0]), &args, sort);
        assert!(Evaluator::new(&case.terms, &case.view)
            .capture_array_snapshot(indexed)
            .is_err());
        let equality = app(&mut case.terms, "=", &[case.target, indexed], Sort::Bool);
        assert!(!matches!(
            confirm_completed_model(&case.terms, &case.view, &[equality]),
            GateVerdict::ConfirmedSat
        ));
    }
}

#[test]
fn malformed_store_result_base_index_and_cell_sorts_cannot_become_complete_arrays() {
    for mutation in 0..4 {
        let mut case = case(false, 3);
        let dst = recognize_range_lambda(&case.terms, case.lambda)
            .expect("recipe")
            .destination;
        let key = case.terms.mk_bitvec(0.into(), 64);
        let cell = case.terms.mk_bitvec(9.into(), 8);
        let mut args = vec![dst, key, cell];
        let mut sort = case.terms.sort(dst).clone();
        match mutation {
            0 => sort = Sort::array(Sort::bitvec(64), Sort::bitvec(16)),
            1 => {
                args[0] = case.terms.mk_var(
                    "wrong_base",
                    Sort::array(Sort::bitvec(64), Sort::bitvec(16)),
                )
            }
            2 => args[1] = case.terms.mk_bool(false),
            _ => args[2] = case.terms.mk_bool(true),
        }
        let bad = case.terms.mk_app(Symbol::named("store"), &args, sort);
        assert!(Evaluator::new(&case.terms, &case.view)
            .capture_array_snapshot(bad)
            .is_err());
        let equality = app(&mut case.terms, "=", &[case.target, bad], Sort::Bool);
        assert!(!matches!(
            confirm_completed_model(&case.terms, &case.view, &[equality]),
            GateVerdict::ConfirmedSat
        ));
    }
}

#[test]
fn constant_cell_metadata_and_equality_operand_sorts_are_exact_before_any_true() {
    let mut case = case(false, 3);
    let eight = case.terms.mk_bitvec(7.into(), 8);
    let wrong = Sort::array(Sort::bitvec(64), Sort::bitvec(16));
    let constant = case
        .terms
        .mk_app(Symbol::named("const-array"), &[eight], wrong.clone());
    assert!(Evaluator::new(&case.terms, &case.view)
        .capture_array_snapshot(constant)
        .is_err());
    let array = case.terms.mk_var("wrong_sort_owned", wrong);
    case.view.arrays.insert(array, base(7));
    let equality = app(&mut case.terms, "=", &[case.target, array], Sort::Bool);
    assert!(!matches!(
        confirm_completed_model(&case.terms, &case.view, &[equality]),
        GateVerdict::ConfirmedSat
    ));
}

#[test]
fn malformed_bv64_capture_cannot_enter_unsigned_empty_interval_shortcut() {
    let mut case = case(true, 3);
    case.view.scalars.insert(
        case.lo,
        ModelValue::BitVec {
            value: BigInt::from(1) << 66,
            width: 64,
        },
    );
    case.view.scalars.insert(
        case.hi,
        ModelValue::BitVec {
            value: BigInt::from(1) << 65,
            width: 64,
        },
    );
    assert!(Evaluator::new(&case.terms, &case.view)
        .capture_array_snapshot(case.lambda)
        .is_err());
    assert!(!matches!(
        confirm_completed_model(&case.terms, &case.view, &[case.definition]),
        GateVerdict::ConfirmedSat
    ));
}
