// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::eval::quantifier::domain_support::GuardedDomain;
use crate::eval::quantifier::QuantifierKind;
use crate::eval::Evaluator;
use crate::{ModelValue, ModelView};
use ay_core::term::Symbol;
use ay_core::{TermId, TermStore};
use num_traits::ToPrimitive;
use std::cell::Cell;

struct EmptyModel;

impl ModelView for EmptyModel {
    fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
        None
    }
}

fn app(terms: &mut TermStore, operator: &str, args: &[TermId]) -> TermId {
    terms.mk_app(Symbol::named(operator), args, Sort::Bool)
}

fn signed(raw: u16, width: u32) -> i32 {
    let value = i32::from(raw);
    if raw & (1 << (width - 1)) != 0 {
        value - (1 << width)
    } else {
        value
    }
}

fn host_comparison(operator: &str, left: i32, right: i32) -> bool {
    match operator {
        "bvslt" => left < right,
        "bvsle" => left <= right,
        "bvsgt" => left > right,
        "bvsge" => left >= right,
        _ => panic!("test oracle only accepts the four signed relations"),
    }
}

/// This oracle uses host signed arithmetic, not AY's comparison evaluator or
/// the implementation's interval conversion. Every carrier value is checked.
fn assert_small_support(
    terms: &TermStore,
    width: u32,
    body: TermId,
    kind: QuantifierKind,
    expected: impl Fn(u16) -> bool,
) {
    let model = EmptyModel;
    let evaluator = Evaluator::new(terms, &model);
    evaluator.quantifier_state.nesting.set(1);
    let size = 1usize << width;
    let sort = Sort::bitvec(width);
    let domain = GuardedDomain::derive(
        &evaluator,
        kind,
        &[("i".to_owned(), sort.clone())],
        body,
        0,
        size,
    )
    .expect("small source support fits")
    .expect("source contains a bound comparison");
    let mut seen = vec![false; size];
    let mut previous = None;
    for ordinal in 0..domain.count {
        let ModelValue::BitVec {
            width: actual_width,
            value,
        } = domain.value_at(&evaluator, &sort, ordinal).unwrap()
        else {
            panic!("support changed the binder carrier");
        };
        assert_eq!(actual_width, width);
        let value = value.to_usize().unwrap();
        assert!(value < size);
        assert!(!seen[value], "split ranges must not duplicate values");
        assert!(previous.is_none_or(|previous| previous < value));
        previous = Some(value);
        seen[value] = true;
    }
    for (raw, included) in seen.into_iter().enumerate() {
        assert_eq!(included, expected(raw as u16), "width={width} raw={raw}");
    }
}

#[test]
fn signed_support_exhaustive_bv1_through_bv4_all_endpoints_orders_and_polarities() {
    for width in 1..=4 {
        let mut terms = TermStore::new();
        let variable = terms.mk_var("i", Sort::bitvec(width));
        for operator in ["bvslt", "bvsle", "bvsgt", "bvsge"] {
            for raw in 0u16..(1 << width) {
                let endpoint = terms.mk_bitvec(BigInt::from(raw), width);
                for args in [[variable, endpoint], [endpoint, variable]] {
                    let atom = app(&mut terms, operator, &args);
                    let not = terms.mk_not_raw(atom);
                    for (body, negated) in [(atom, false), (not, true)] {
                        for kind in [QuantifierKind::Forall, QuantifierKind::Exists] {
                            assert_small_support(&terms, width, body, kind, |value| {
                                let left = signed(value, width);
                                let right = signed(raw, width);
                                let actual = if args[0] == variable {
                                    host_comparison(operator, left, right)
                                } else {
                                    host_comparison(operator, right, left)
                                };
                                (actual != negated) == kind.decisive_value()
                            });
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn signed_support_exhaustive_ranges_preserve_unknown_body_polarity() {
    let mut terms = TermStore::new();
    let variable = terms.mk_var("i", Sort::bitvec(4));
    let unknown = terms.mk_var("unknown", Sort::Bool);
    for lower in 0u16..16 {
        let lower_term = terms.mk_bitvec(BigInt::from(lower), 4);
        let from = app(&mut terms, "bvsge", &[variable, lower_term]);
        for upper in 0u16..16 {
            let upper_term = terms.mk_bitvec(BigInt::from(upper), 4);
            let to = app(&mut terms, "bvslt", &[variable, upper_term]);
            let guard = app(&mut terms, "and", &[from, to]);
            for (operator, kind) in [
                ("=>", QuantifierKind::Forall),
                ("and", QuantifierKind::Exists),
            ] {
                let body = app(&mut terms, operator, &[guard, unknown]);
                assert_small_support(&terms, 4, body, kind, |raw| {
                    signed(raw, 4) >= signed(lower, 4) && signed(raw, 4) < signed(upper, 4)
                });
            }
        }
    }
}

#[test]
fn signed_and_unsigned_disjunction_keeps_the_negative_tail() {
    let mut terms = TermStore::new();
    let variable = terms.mk_var("i", Sort::bitvec(4));
    let zero = terms.mk_bitvec(BigInt::zero(), 4);
    let one = terms.mk_bitvec(BigInt::one(), 4);
    let negative = app(&mut terms, "bvslt", &[variable, zero]);
    let small_unsigned = app(&mut terms, "bvule", &[variable, one]);
    let guard = app(&mut terms, "or", &[negative, small_unsigned]);
    let unknown = terms.mk_var("unknown", Sort::Bool);
    for (operator, kind) in [
        ("=>", QuantifierKind::Forall),
        ("and", QuantifierKind::Exists),
    ] {
        let body = app(&mut terms, operator, &[guard, unknown]);
        assert_small_support(&terms, 4, body, kind, |raw| signed(raw, 4) < 0 || raw <= 1);
    }
}

#[test]
fn signed_bv128_min_max_minus_one_zero_keep_exact_canonical_values() {
    let width = 128;
    let half = BigInt::one() << 127usize;
    for expected in [
        BigInt::zero(),
        &half - 1u8,
        half,
        (BigInt::one() << 128usize) - 1u8,
    ] {
        let mut terms = TermStore::new();
        let sort = Sort::bitvec(width);
        let variable = terms.mk_var("i", sort.clone());
        let endpoint = terms.mk_bitvec(expected.clone(), width);
        let from = app(&mut terms, "bvsge", &[variable, endpoint]);
        let to = app(&mut terms, "bvsle", &[variable, endpoint]);
        let guard = app(&mut terms, "and", &[from, to]);
        let model = EmptyModel;
        let evaluator = Evaluator::new(&terms, &model);
        evaluator.quantifier_state.nesting.set(1);
        let domain = GuardedDomain::derive(
            &evaluator,
            QuantifierKind::Exists,
            &[("i".to_owned(), sort.clone())],
            guard,
            0,
            1,
        )
        .unwrap()
        .unwrap();
        assert_eq!(domain.count, 1);
        assert!(matches!(domain.value_at(&evaluator, &sort, 0).unwrap(),
            ModelValue::BitVec { width: 128, value } if value == expected));
    }
}

#[test]
fn signed_conversion_refuses_before_work_and_shares_sticky_allowance() {
    let terms = TermStore::new();
    let model = EmptyModel;
    let evaluator = Evaluator::new(&terms, &model);
    evaluator.quantifier_state.nesting.set(1);
    let sort = Sort::bitvec(128);
    let analysis = SupportAnalysis {
        evaluator: &evaluator,
        name: "i",
        sort: &sort,
        unavailable: &[],
        eval_depth: 0,
        saw_bound_comparison: Cell::new(false),
    };
    let initial = evaluator.quantifier_state.work_left.get();
    assert!(analysis
        .signed_comparison("bvslt", BigInt::zero(), true)
        .is_ok());
    let used = initial - evaluator.quantifier_state.work_left.get();
    assert!(used >= 32 * 3, "the 129-bit exclusive endpoint is charged");
    evaluator.quantifier_state.work_left.set(used);
    assert!(analysis
        .signed_comparison("bvslt", BigInt::zero(), true)
        .is_ok());
    assert_eq!(evaluator.quantifier_state.work_left.get(), 0);
    evaluator.quantifier_state.work_left.set(used - 1);
    assert!(analysis
        .signed_comparison("bvslt", BigInt::zero(), true)
        .is_err());
    assert_eq!(evaluator.quantifier_state.work_left.get(), 0);
    assert!(analysis
        .signed_comparison("bvslt", BigInt::zero(), true)
        .is_err());
    let fresh = Evaluator::new(&terms, &model);
    fresh.quantifier_state.nesting.set(1);
    let fresh_analysis = SupportAnalysis {
        evaluator: &fresh,
        ..analysis
    };
    assert!(fresh_analysis
        .signed_comparison("bvslt", BigInt::zero(), true)
        .is_ok());
}
