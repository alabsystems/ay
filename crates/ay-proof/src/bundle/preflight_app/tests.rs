// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{ArraySort, BitVecSort};

use super::*;

mod floating_point;
mod indexed;
mod progress;

fn bv(width: u32) -> Sort {
    Sort::BitVec(BitVecSort::new(width))
}
fn array() -> Sort {
    Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Bool)))
}

fn entries() -> Vec<(TermData, Sort)> {
    [
        Sort::Bool,
        Sort::Int,
        Sort::Real,
        bv(8),
        bv(16),
        array(),
        Sort::FloatingPoint(8, 24),
        bv(1),
        bv(8),
        bv(23),
    ]
    .into_iter()
    .enumerate()
    .map(|(index, sort)| (TermData::Var(format!("app_{index}"), index as u32), sort))
    .collect()
}

fn run(
    entries: &[(TermData, Sort)],
    symbol: &Symbol,
    args: &[TermId],
    result: &Sort,
) -> Result<(), ProofCheckError> {
    validate_app_signature_with_progress(
        entries,
        entries.len(),
        symbol,
        args,
        result,
        &mut |_, _| true,
    )
}

fn compare(entries: &[(TermData, Sort)], symbol: &Symbol, args: &[TermId], result: &Sort) -> bool {
    let old = validate_app_signature(entries, entries.len(), symbol, args, result);
    let new = run(entries, symbol, args, result);
    assert_eq!(
        old.is_ok(),
        new.is_ok(),
        "symbol {symbol:?}, args {args:?}, result {result:?}: old={old:?}, new={new:?}"
    );
    if new.is_err() {
        assert!(matches!(
            new,
            Err(ProofCheckError::MalformedProofBundle { .. })
        ));
    }
    old.is_ok()
}

fn compare_group(names: &[&str], args: &[u32], result: Sort) {
    let entries = entries();
    let args: Vec<_> = args.iter().copied().map(TermId).collect();
    for &name in names {
        let symbol = Symbol::named(name);
        assert!(
            compare(&entries, &symbol, &args, &result),
            "positive {name}"
        );
        for bad_args in [
            vec![],
            vec![TermId(0)],
            vec![TermId(1), TermId(2)],
            vec![TermId(0); 4],
        ] {
            compare(&entries, &symbol, &bad_args, &result);
        }
        for other_result in [Sort::Bool, Sort::Int, bv(16), array()] {
            compare(&entries, &symbol, &args, &other_result);
        }
    }
}

#[test]
fn boolean_and_array_builtins_match_legacy_positive_and_malformed_signatures() {
    compare_group(&["="], &[1, 1], Sort::Bool);
    compare_group(&["distinct"], &[1, 1, 1], Sort::Bool);
    compare_group(&["not"], &[0], Sort::Bool);
    compare_group(&["and", "or", "xor", "=>"], &[0, 0], Sort::Bool);
    compare_group(&["ite"], &[0, 1, 1], Sort::Int);
    compare_group(&["select"], &[5, 1], Sort::Bool);
    compare_group(&["store"], &[5, 1, 0], array());
    compare_group(&["const-array"], &[0], array());
}

#[test]
fn all_named_bv_operations_match_the_legacy_table() {
    compare_group(&["bvnot", "bvneg"], &[3], bv(8));
    compare_group(
        &[
            "bvand", "bvor", "bvxor", "bvnand", "bvnor", "bvxnor", "bvadd", "bvsub", "bvmul",
            "bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod", "bvshl", "bvlshr", "bvashr",
        ],
        &[3, 3],
        bv(8),
    );
    compare_group(
        &[
            "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge",
        ],
        &[3, 3],
        Sort::Bool,
    );
    compare_group(&["concat"], &[3, 3], bv(16));
}

#[test]
fn all_named_fp_operations_match_the_legacy_table() {
    compare_group(&["fp"], &[7, 8, 9], Sort::FloatingPoint(8, 24));
    compare_group(&["fp.abs", "fp.neg"], &[6], Sort::FloatingPoint(8, 24));
    compare_group(
        &[
            "fp.isNaN",
            "fp.isInfinite",
            "fp.isZero",
            "fp.isNormal",
            "fp.isSubnormal",
            "fp.isPositive",
            "fp.isNegative",
        ],
        &[6],
        Sort::Bool,
    );
    compare_group(
        &["fp.eq", "fp.lt", "fp.leq", "fp.gt", "fp.geq"],
        &[6, 6],
        Sort::Bool,
    );
}

#[test]
fn zero_and_one_argument_boolean_forms_keep_legacy_semantics() {
    let entries = entries();
    for name in ["distinct", "and", "or", "xor"] {
        assert!(compare(&entries, &Symbol::named(name), &[], &Sort::Bool));
        let id = if name == "distinct" {
            TermId(1)
        } else {
            TermId(0)
        };
        assert!(compare(&entries, &Symbol::named(name), &[id], &Sort::Bool));
    }
    assert!(!compare(
        &entries,
        &Symbol::named("=>"),
        &[TermId(0)],
        &Sort::Bool
    ));
}

#[test]
fn unsupported_uf_and_named_arithmetic_signatures_are_not_newly_authenticated_or_restricted() {
    let entries = entries();
    for name in ["arbitrary_function", "+", "*", "<", "str.len"] {
        assert!(compare(
            &entries,
            &Symbol::named(name),
            &[TermId(0), TermId(2)],
            &Sort::RegLan
        ));
    }
    assert!(compare(
        &entries,
        &Symbol::indexed("arbitrary_indexed", vec![u32::MAX; 100]),
        &[TermId(1)],
        &Sort::Bool
    ));
}

#[test]
fn missing_child_handles_are_rejected_even_for_unknown_uf_heads() {
    let entries = entries();
    for symbol in [
        Symbol::named("="),
        Symbol::named("unknown"),
        Symbol::indexed("repeat", vec![2]),
        Symbol::indexed("unknown", vec![]),
    ] {
        for missing in [TermId(entries.len() as u32), TermId(u32::MAX)] {
            assert!(matches!(
                run(&entries, &symbol, &[missing], &Sort::Bool),
                Err(ProofCheckError::MalformedProofBundle { .. })
            ));
        }
    }
}
