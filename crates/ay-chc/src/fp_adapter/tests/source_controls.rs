// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn refusal(terms: &TermStore, root: TermId, inputs: &[FpInputBinding<'_>]) -> FpAdapterError {
    let namespace = ChcProblem::new();
    let mut checkpoint = || ControlFlow::Continue(());
    let mut budget = WorkBudget::new(10_000_000_000, &mut checkpoint);
    match lower_fp_clause(terms, &[root], inputs, &namespace, &mut budget) {
        Ok(_) => panic!("negative source must refuse"),
        Err(error) => error,
    }
}

#[test]
fn unsupported_fp_and_raw_nan_payload_conversion_never_become_free_words() {
    for op in ["fp.roundToIntegral", "fp.min", "fp.max", "user_fp"] {
        let mut terms = TermStore::new();
        let x = fp_constant(&mut terms, 0x3f800000, 32);
        let mode = terms.mk_app(
            Symbol::named("RNE"),
            [],
            Sort::Uninterpreted("RoundingMode".into()),
        );
        let args = match op {
            "fp.roundToIntegral" => vec![mode, x],
            "fp.min" | "fp.max" => vec![x, x],
            _ => vec![mode, x, x],
        };
        let result = terms.mk_app(Symbol::named(op), args, Sort::FloatingPoint(8, 24));
        let root = predicate(&mut terms, "fp.isNaN", &[result]);
        assert!(matches!(
            refusal(&terms, root, &[]),
            FpAdapterError::Unsupported(_)
        ));
    }
    let mut terms = TermStore::new();
    let x = fp_constant(&mut terms, 0x3f800000, 32);
    let mode = terms.mk_app(
        Symbol::named("RNE"),
        [],
        Sort::Uninterpreted("RoundingMode".into()),
    );
    let div = terms.mk_app(
        Symbol::named("fp.div"),
        [mode, x, x],
        Sort::FloatingPoint(8, 24),
    );
    let root = predicate(&mut terms, "fp.isNormal", &[div]);
    let namespace = ChcProblem::new();
    let mut checkpoint = || ControlFlow::Continue(());
    let mut budget = WorkBudget::new(10_000_000_000, &mut checkpoint);
    assert!(lower_fp_clause(&terms, &[root], &[], &namespace, &mut budget).is_ok());
    let mut terms = TermStore::new();
    let x = fp_constant(&mut terms, 0x7fc00001, 32);
    let raw = terms.mk_app(Symbol::named("fp.to_ieee_bv"), [x], Sort::bitvec(32));
    let bits = terms.mk_bitvec(0x7fc00000u64.into(), 32);
    let root = predicate(&mut terms, "=", &[raw, bits]);
    assert!(matches!(
        refusal(&terms, root, &[]),
        FpAdapterError::Unsupported(_)
    ));
}

#[test]
fn wrong_symbolic_or_spoofed_rounding_mode_and_mixed_formats_refuse() {
    for sort in [Sort::Bool, Sort::Uninterpreted("RoundingMode".into())] {
        let mut terms = TermStore::new();
        let x = fp_constant(&mut terms, 0x3f800000, 32);
        let mode = if sort == Sort::Bool {
            terms.mk_app(Symbol::named("RNE"), [], sort)
        } else {
            terms.mk_var("RNE", sort)
        };
        let result = terms.mk_app(
            Symbol::named("fp.add"),
            [mode, x, x],
            Sort::FloatingPoint(8, 24),
        );
        let root = predicate(&mut terms, "fp.isZero", &[result]);
        assert!(matches!(
            refusal(&terms, root, &[]),
            FpAdapterError::Unsupported(_)
        ));
    }
    let mut terms = TermStore::new();
    let x = fp_constant(&mut terms, 0, 32);
    let y = fp_constant(&mut terms, 0, 64);
    let root = predicate(&mut terms, "fp.eq", &[x, y]);
    assert!(matches!(
        refusal(&terms, root, &[]),
        FpAdapterError::Unsupported(_)
    ));
}

#[test]
fn missing_cycles_malformed_sort_constants_and_indexed_format_are_rejected() {
    for child in [TermId(0), TermId(999)] {
        let terms =
            TermStore::from_entries(vec![(TermData::Not(child), Sort::Bool)], None, None, 0);
        assert!(matches!(
            refusal(&terms, TermId(0), &[]),
            FpAdapterError::Invalid(_)
        ));
    }
    let terms = TermStore::from_entries(
        vec![
            (TermData::Not(TermId(1)), Sort::Bool),
            (
                TermData::Const(ay_core::term::Constant::Bool(true)),
                Sort::bitvec(32),
            ),
        ],
        None,
        None,
        0,
    );
    assert!(matches!(
        refusal(&terms, TermId(0), &[]),
        FpAdapterError::Invalid(_)
    ));
    let mut terms = TermStore::new();
    let bv = terms.mk_bitvec(0u8.into(), 32);
    let malformed = terms.mk_app(
        Symbol::indexed("to_fp", vec![11, 53]),
        [bv],
        Sort::FloatingPoint(8, 24),
    );
    let root = predicate(&mut terms, "fp.isZero", &[malformed]);
    assert!(matches!(
        refusal(&terms, root, &[]),
        FpAdapterError::Invalid(_)
    ));
}

#[test]
fn unbound_wrong_name_wrong_sort_and_duplicate_input_links_refuse() {
    let mut terms = TermStore::new();
    let (input, root, correct) = simple(&mut terms);
    assert!(matches!(
        refusal(&terms, root, &[]),
        FpAdapterError::Invalid(_)
    ));
    for target in [
        ChcVar::new("not_original_x", crate::ChcSort::BitVec(64)),
        ChcVar::new("original_x", crate::ChcSort::BitVec(32)),
    ] {
        assert!(matches!(
            refusal(&terms, root, &bindings(input, &target)),
            FpAdapterError::Invalid(_)
        ));
    }
    let inputs = [FpInputBinding {
        source: input,
        target: &correct,
    }; 2];
    assert!(matches!(
        refusal(&terms, root, &inputs),
        FpAdapterError::Invalid("duplicate or aliased input")
    ));
    let alias = terms.mk_fresh_named_var("original_x", Sort::FloatingPoint(11, 53));
    let inputs = [
        FpInputBinding {
            source: input,
            target: &correct,
        },
        FpInputBinding {
            source: alias,
            target: &correct,
        },
    ];
    assert!(matches!(
        refusal(&terms, root, &inputs),
        FpAdapterError::Invalid("duplicate or aliased input")
    ));
}

#[test]
fn unused_declarations_and_nonselected_body_children_are_not_skipped() {
    let mut terms = TermStore::new();
    let false_term = terms.mk_bool(false);
    let unbound = terms.mk_var("unselected", Sort::Bool);
    let root = predicate(&mut terms, "and", &[false_term, unbound]);
    assert!(matches!(
        refusal(&terms, root, &[]),
        FpAdapterError::Invalid(_)
    ));
    let mut namespace = ChcProblem::new();
    namespace.declare_predicate("__ay_fp_bits_unused", Vec::new());
    let mut checkpoint = || ControlFlow::Continue(());
    let mut budget = WorkBudget::new(10_000_000_000, &mut checkpoint);
    assert!(matches!(
        lower_fp_clause(&terms, &[false_term], &[], &namespace, &mut budget),
        Err(FpAdapterError::Invalid(
            "reserved auxiliary namespace collision"
        ))
    ));
}

#[test]
fn depth_and_raw_repeated_dag_expansion_are_bounded_before_circuit_entry() {
    let mut terms = TermStore::new();
    let mut deep = terms.mk_bool(true);
    for _ in 0..64 {
        deep = terms.mk_not_raw(deep);
    }
    assert!(matches!(
        refusal(&terms, deep, &[]),
        FpAdapterError::Invalid(_)
    ));
    let mut shared = terms.mk_bool(true);
    for _ in 0..13 {
        shared = predicate(&mut terms, "and", &[shared, shared]);
    }
    assert!(matches!(
        refusal(&terms, shared, &[]),
        FpAdapterError::Unsupported(_)
    ));
}

#[test]
fn repeated_roots_expand_the_prepaid_cost_not_a_new_allowance() {
    let mut terms = TermStore::new();
    let (input, root, target) = simple(&mut terms);
    let inputs = bindings(input, &target);
    let mut checkpoint = || ControlFlow::Continue(());
    let mut budget = WorkBudget::new(10_000_000_000, &mut checkpoint);
    let one = source::plan(&terms, &[root], &inputs, &mut budget).unwrap();
    let two = source::plan(&terms, &[root, root], &inputs, &mut budget).unwrap();
    assert_eq!(two.occurrences, one.occurrences * 2);
    assert_eq!(two.gates - 64, (one.gates - 64) * 2);
    let before = budget.remaining();
    one.prepay(&mut budget).unwrap();
    two.prepay(&mut budget).unwrap();
    assert_eq!(
        before - budget.remaining(),
        ((one.gates + two.gates) * 1024) as u64
    );
}
