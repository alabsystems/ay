// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn declines(terms: &TermStore, source: TermId) {
    let mut progress = |_, _| true;
    assert!(Reference::build(terms, source, &mut progress).is_err());
}

#[test]
fn exact_live_source_arity_sort_named_identity_and_operands_are_required() {
    let mut f = Fixture::new(8, 24);
    let TermData::App(_, args) = f.terms.get(f.source) else {
        panic!("source fixture");
    };
    let args = args.clone();
    declines(&f.terms, TermId::SENTINEL);
    let missing = f.terms.mk_app(
        Symbol::named("fp.mul"),
        [f.rm, args[1], TermId::SENTINEL],
        Sort::FloatingPoint(8, 24),
    );
    declines(&f.terms, missing);
    let wrong_op = f.terms.mk_app(
        Symbol::named("fp.add"),
        args.clone(),
        Sort::FloatingPoint(8, 24),
    );
    declines(&f.terms, wrong_op);
    let indexed = f.terms.mk_app(
        Symbol::indexed("fp.mul", vec![8, 24]),
        args.clone(),
        Sort::FloatingPoint(8, 24),
    );
    declines(&f.terms, indexed);
    let short = f.terms.mk_app(
        Symbol::named("fp.mul"),
        &args[..2],
        Sort::FloatingPoint(8, 24),
    );
    declines(&f.terms, short);
    let wrong_sort = f
        .terms
        .mk_app(Symbol::named("fp.mul"), args, Sort::FloatingPoint(11, 53));
    declines(&f.terms, wrong_sort);
}

#[test]
fn malformed_or_indexed_rounding_modes_are_never_assumed_rne() {
    let mut f = Fixture::new(8, 24);
    let TermData::App(_, args) = f.terms.get(f.source) else {
        panic!("source fixture");
    };
    let args = args.clone();
    for symbol in [Symbol::named("unknown_rm"), Symbol::indexed("RNE", vec![0])] {
        let rm = f
            .terms
            .mk_app(symbol, [], Sort::Uninterpreted("RoundingMode".into()));
        let source = f.terms.mk_app(
            Symbol::named("fp.mul"),
            [rm, args[1], args[2]],
            Sort::FloatingPoint(8, 24),
        );
        declines(&f.terms, source);
    }
    let rm = f.terms.mk_var("looks_like_rm", Sort::Bool);
    let source = f.terms.mk_app(
        Symbol::named("fp.mul"),
        [rm, args[1], args[2]],
        Sort::FloatingPoint(8, 24),
    );
    declines(&f.terms, source);
}

#[test]
fn imported_noncanonical_constants_and_hidden_cycles_decline_before_abstracting() {
    let f = Fixture::new(8, 24);
    for data in [
        TermData::Const(Constant::BitVec {
            value: BigInt::from(-1i8),
            width: 1,
        }),
        TermData::Const(Constant::BitVec {
            value: BigInt::from(2u8),
            width: 1,
        }),
        TermData::Const(Constant::BitVec {
            value: BigInt::from(0u8),
            width: 2,
        }),
        TermData::App(Symbol::named("bvnot"), vec![f.x.sign]),
    ] {
        let mut entries = f.terms.entries_snapshot();
        entries[f.x.sign.index()] = (data, Sort::bitvec(1));
        let imported = TermStore::from_entries(entries, None, None, f.terms.var_counter());
        declines(&imported, f.source);
    }
}

#[test]
fn arbitrary_fp_variables_are_not_a_caller_asserted_decomposition() {
    let mut f = Fixture::new(8, 24);
    let x = f.terms.mk_var(
        "original_float_without_registered_bits",
        Sort::FloatingPoint(8, 24),
    );
    let source = f.terms.mk_app(
        Symbol::named("fp.mul"),
        [f.rm, x, x],
        Sort::FloatingPoint(8, 24),
    );
    declines(&f.terms, source);
}

#[test]
fn exact_source_field_identity_shares_only_actual_repeated_occurrences() {
    let mut f = Fixture::new(3, 4);
    let TermData::App(_, args) = f.terms.get(f.source) else {
        panic!("source fixture");
    };
    let x = args[1];
    let source = f.terms.mk_app(
        Symbol::named("fp.mul"),
        [f.rm, x, x],
        Sort::FloatingPoint(3, 4),
    );
    let mut progress = |_, _| true;
    let mut reference =
        Reference::build(&f.terms, source, &mut progress).expect("actual repeated occurrence");
    let inputs = f.assignments(raw(0, 3, 1), raw(1, 0, 0), 0);
    let (actual, _) = reference
        .evaluate(&inputs)
        .expect("source IDs, not supplied order");
    assert_eq!(
        actual,
        oracle::multiply((3, 4), raw(0, 3, 1), raw(0, 3, 1), 0)
    );
    let leaves = reference
        .nodes
        .iter()
        .filter(|node| matches!(node.operation, graph::Operation::Input(_)))
        .count();
    assert_eq!(leaves, 4, "one actual RM plus three shared actual fields");
}

#[test]
fn checked_host_widths_decline_before_precision_sized_construction() {
    assert_eq!(Format::checked(1, 24).err(), Some(ReferenceError::Source));
    assert_eq!(Format::checked(8, 1).err(), Some(ReferenceError::Source));
    assert_eq!(
        Format::checked(8, u32::MAX).err(),
        Some(ReferenceError::Width)
    );
    assert_eq!(
        Format::checked(u32::MAX - 2, 2).err(),
        Some(ReferenceError::Width)
    );
}

#[test]
fn a_free_variable_displayed_rne_is_not_silently_a_rounding_literal() {
    let mut f = Fixture::new(3, 4);
    let TermData::App(_, args) = f.terms.get(f.source) else {
        panic!("mul fixture");
    };
    let args = args.clone();
    let rm = f
        .terms
        .mk_var("RNE", Sort::Uninterpreted("RoundingMode".into()));
    let source = f.terms.mk_app(
        Symbol::named("fp.mul"),
        [rm, args[1], args[2]],
        Sort::FloatingPoint(3, 4),
    );
    let mut progress = |_, _| true;
    let mut reference =
        Reference::build(&f.terms, source, &mut progress).expect("free actual RM input");
    let x = raw(0, 3, 2);
    let mut inputs = f.assignments(x, x, 0);
    inputs.push((rm, BigUint::from(1u8))); // actual RNA, despite the leaf's display spelling
    let (actual, domain) = reference
        .evaluate(&inputs)
        .expect("actual variable binding");
    assert!(domain);
    assert_eq!(actual, oracle::multiply((3, 4), x, x, 1));
    assert_ne!(actual, oracle::multiply((3, 4), x, x, 0));
}
