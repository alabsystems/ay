// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Wide comparisons must agree with a separately lowered narrow reference.

use super::*;

const OPERATORS: [&str; 8] = [
    "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge",
];
const WIDTHS: [u32; 6] = [129, 191, 256, 257, 511, 1024];

fn extended(terms: &mut TermStore, value: TermId, width: u32) -> TermId {
    terms.mk_app(
        Symbol::indexed("sign_extend", vec![width - 128]),
        [value],
        Sort::bitvec(width),
    )
}

fn comparison_query(terms: &mut TermStore, name: &str, width: u32, inverted: bool) -> TermId {
    let a = terms.mk_var("a", Sort::bitvec(128));
    let b = terms.mk_var("b", Sort::bitvec(128));
    let ae = extended(terms, a, width);
    let be = extended(terms, b, width);
    let wide = terms.mk_app(Symbol::named(name), [ae, be], Sort::Bool);
    // Sign extension preserves both unsigned bit-pattern ordering and signed
    // ordering. The native narrow route computes this reference separately.
    let narrow = terms.mk_app(Symbol::named(name), [a, b], Sort::Bool);
    assert_ne!(wide, narrow);
    let expected = if inverted {
        terms.mk_not_raw(narrow)
    } else {
        narrow
    };
    let equal = terms.mk_app(Symbol::named("="), [wide, expected], Sort::Bool);
    terms.mk_not_raw(equal)
}

#[test]
fn wide_comparisons_preserve_sign_extended_order_and_exact_request_census() {
    for width in WIDTHS {
        for name in OPERATORS {
            let mut terms = TermStore::new();
            let root = comparison_query(&mut terms, name, width, false);
            let mut lowerer =
                ProofProducingLowerer::new(&terms, Instant::now() + Duration::from_secs(60));
            let result = lowerer.lower_bool(root);
            assert!(result.is_ok(), "{name}, width {width}: {result:?}");
            lowerer.audit_census();
            let evidence = authenticate_bool_bv_unsat_query(&terms, &[root], None)
                .unwrap_or_else(|error| panic!("{name}, width {width}: {error}"));
            assert!(evidence.is_current_for(&terms, &[root]));
        }
    }
}

#[test]
fn inverted_wide_comparison_flags_are_satisfiable() {
    for width in WIDTHS {
        for name in OPERATORS {
            let mut terms = TermStore::new();
            let root = comparison_query(&mut terms, name, width, true);
            let result = authenticate_bool_bv_unsat_query(&terms, &[root], None);
            assert!(
                matches!(result, Err(BoolBvUnsatAuthenticationError::Satisfiable)),
                "{name}, width {width}: {result:?}"
            );
        }
    }
}

#[test]
fn comparison_partition_bounds_a_word_of_one_bit_fields() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(1));
    let b = terms.mk_var("b", Sort::bitvec(1));
    let mut lhs = a;
    let mut rhs = b;
    for width in 2..=MAX_WIDE_WIDTH {
        lhs = terms.mk_app(Symbol::named("concat"), [a, lhs], Sort::bitvec(width));
        rhs = terms.mk_app(Symbol::named("concat"), [b, rhs], Sort::bitvec(width));
    }
    let slices = planning::plan(&terms, lhs, rhs, Partition::Limbs, &mut || Ok(()))
        .expect("canonical limbs remain bounded for distinct concat trees");
    assert_eq!(slices.len(), (MAX_WIDE_WIDTH / SLICE) as usize);
    assert!(slices
        .iter()
        .all(|(a, b)| a.width() == SLICE && b.width() == SLICE));
}

#[test]
fn wide_comparisons_refuse_malformed_and_unsupported_sources() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(128));
    let good = extended(&mut terms, a, 129);
    let malformed = terms.mk_app(
        Symbol::indexed("sign_extend", vec![2]),
        [a],
        Sort::bitvec(129),
    );
    let unsupported = terms.mk_app(
        Symbol::named("unsupported_function"),
        [a],
        Sort::bitvec(128),
    );
    let hidden = extended(&mut terms, unsupported, 129);
    for name in OPERATORS {
        for (lhs, rhs) in [(good, malformed), (good, a), (hidden, hidden)] {
            let root = terms.mk_app(Symbol::named(name), [lhs, rhs], Sort::Bool);
            let error = authenticate_bool_bv_unsat_query(&terms, &[root], None)
                .expect_err("order reflexivity must not bypass source validation");
            assert!(error.is_unsupported_fragment(), "{name}: {error:?}");
        }
    }
}
