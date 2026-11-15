// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::original_query::FiniteAdmissionGrant;
use num_bigint::BigInt;
use std::sync::Arc;

mod borrowed_fp;
mod existing;
mod resources;
mod signatures;

fn owner(work: u64, bytes: usize) -> CountedAdmission {
    CountedAdmission::new(
        FiniteAdmissionGrant::new(work, bytes),
        None,
        Arc::new(|| false),
    )
    .unwrap()
}

fn ample() -> CountedAdmission {
    owner(100_000_000, 256 * 1024 * 1024)
}

#[test]
fn counted_integer_products_preserve_carries_sign_zero_and_original_refusal() {
    let wide = (BigInt::from(1u8) << 97usize) - 1u8;
    for (a, b) in [
        (wide.clone(), wide.clone()),
        (-wide.clone(), wide),
        (0.into(), (-7).into()),
    ] {
        let expected = &a * &b;
        let mut store = TermStore::new();
        let left = store.mk_int(a);
        let right = store.mk_int(b);
        let admission = ample();
        let mut builder = CountedTermBuilder::new(&mut store, &admission).unwrap();
        let product = builder.integer_product(left, right).unwrap();
        assert!(
            matches!(builder.terms().get(product), TermData::Const(Constant::Int(value)) if value == &expected)
        );
    }
    let mut store = TermStore::new();
    let variable = store.mk_var("n", Sort::Int);
    let three = store.mk_int(3.into());
    let two = store.mk_int(2.into());
    let nested = store.mk_app_structural(Symbol::named("*"), [variable, two], Sort::Int);
    let bad = store.mk_bool(true);
    let admission = ample();
    let mut builder = CountedTermBuilder::new(&mut store, &admission).unwrap();
    let product = builder.integer_product(variable, three).unwrap();
    assert!(
        matches!(builder.terms().get(product), TermData::App(Symbol::Named(head), args) if head == "*" && args == &[three, variable])
    );
    assert!(builder.integer_product(variable, bad).is_err());
    let normalized = builder.integer_product(nested, three).unwrap();
    let TermData::App(_, args) = builder.terms().get(normalized) else {
        panic!("product required")
    };
    assert_eq!(args.len(), 2);
    assert_eq!(args[1], variable);
    assert!(
        matches!(builder.terms().get(args[0]), TermData::Const(Constant::Int(value)) if value == &6.into())
    );
    drop(builder);
    store.register_declared_function("*");
    let admission = ample();
    let mut builder = CountedTermBuilder::new(&mut store, &admission).unwrap();
    assert!(builder.integer_product(variable, three).is_err());
    let mut store = TermStore::new();
    let left = store.mk_int((BigInt::from(1u8) << 65536usize) - 1u8);
    let right = store.mk_int(3.into());
    let admission = owner(1 << 20, 4096);
    let mut builder = CountedTermBuilder::new(&mut store, &admission).unwrap();
    assert!(builder.integer_product(left, right).is_err());
    assert!(
        builder.integer_product(right, right).is_err(),
        "same original refusal stays sticky"
    );
}

#[test]
fn counted_ring_numbers_cover_signed_carry_rationals_and_original_refusal() {
    use num_rational::BigRational;
    let mut store = TermStore::new();
    let n = (BigInt::from(1u8) << 129usize) - 1u8;
    let a = store.mk_int(-n.clone());
    let b = store.mk_int(n - 1u8);
    let admission = ample();
    let mut builder = CountedTermBuilder::new(&mut store, &admission).unwrap();
    let sum = builder.number_add(a, b).unwrap();
    assert!(
        matches!(builder.terms().get(sum), TermData::Const(Constant::Int(v)) if v == &(-1).into())
    );
    let a = builder
        .rational(&BigRational::new(3.into(), 5.into()))
        .unwrap();
    let b = builder
        .rational(&BigRational::new((-7).into(), 10.into()))
        .unwrap();
    let sum = builder.number_add(a, b).unwrap();
    let product = builder.number_product(a, b).unwrap();
    let inverse = builder.number_reciprocal(b).unwrap();
    for (id, expected) in [
        (sum, BigRational::new((-1).into(), 10.into())),
        (product, BigRational::new((-21).into(), 50.into())),
        (inverse, BigRational::new((-10).into(), 7.into())),
    ] {
        assert!(
            matches!(builder.terms().get(id), TermData::Const(Constant::Rational(v)) if v.0 == expected)
        );
    }
    let zero = builder.number_like(0, a).unwrap();
    assert!(builder.number_reciprocal(zero).is_err());
    assert!(builder.number_add(a, sum).is_ok());
    drop(builder);
    let mut store = TermStore::new();
    let huge = store.mk_int((BigInt::from(1u8) << 65536usize) - 1u8);
    let small = store.mk_int(1.into());
    let admission = owner(1 << 20, 4096);
    let mut builder = CountedTermBuilder::new(&mut store, &admission).unwrap();
    assert!(builder.number_add(huge, huge).is_err());
    assert!(
        builder.number_add(small, small).is_err(),
        "original storage refusal remains sticky"
    );
}

#[test]
fn counted_ring_construction_enforces_types_and_generated_namespace() {
    let mut store = TermStore::new();
    let i = store.mk_var("i", Sort::Int);
    let r = store.mk_var("r", Sort::Real);
    let two = store.mk_int(2.into());
    let admission = ample();
    let mut builder = CountedTermBuilder::new(&mut store, &admission).unwrap();
    assert!(builder
        .ring_apply(CountedRingBuiltin::Add, &[i, r])
        .is_err());
    assert!(builder
        .ring_apply(CountedRingBuiltin::ToReal, &[r])
        .is_err());
    let real_power = builder
        .ring_apply(CountedRingBuiltin::Power, &[i, two])
        .unwrap();
    assert_eq!(builder.terms().sort(real_power), &Sort::Real);
    let integral = builder
        .ring_apply(CountedRingBuiltin::ToInt, &[real_power])
        .unwrap();
    assert_eq!(builder.terms().sort(integral), &Sort::Int);
    drop(builder);
    store.register_declared_function("+");
    let admission = ample();
    let mut builder = CountedTermBuilder::new(&mut store, &admission).unwrap();
    assert!(builder
        .ring_apply(CountedRingBuiltin::Add, &[i, i])
        .is_err());
}

#[test]
fn counted_sequence_constructors_enforce_sorts_namespace_and_empty_cost() {
    let mut store = TermStore::new();
    let empty = store.mk_string(String::new());
    let word = store.mk_string("ab".into());
    let seq = store.mk_var("xs", Sort::seq(Sort::Int));
    let other = store.mk_var("bs", Sort::seq(Sort::Bool));
    let original = ample();
    let mut builder = CountedTermBuilder::new(&mut store, &original).unwrap();
    assert_eq!(builder.string_repeat(empty, u32::MAX).unwrap(), empty);
    assert!(builder.sequence_concat(seq, other).is_err());
    assert!(builder.sequence_concat(seq, word).is_err());
    let repeated = builder.string_repeat(word, 3).unwrap();
    assert!(
        matches!(builder.terms().get(repeated), TermData::Const(Constant::String(s)) if s == "ababab")
    );
    builder.finish().unwrap();
}

#[test]
fn counted_field_constructor_preserves_domain_and_presence() {
    let original = ample();
    let mut store = TermStore::new();
    let f = crate::FiniteFieldSort::new(7).unwrap();
    let g = crate::FiniteFieldSort::new(5).unwrap();
    let mut builder = CountedTermBuilder::new(&mut store, &original).unwrap();
    let a = builder.finite_field(3, f).unwrap();
    let b = builder.finite_field(4, f).unwrap();
    let other = builder.finite_field(4, g).unwrap();
    assert!(builder.finite_field(7, f).is_err());
    assert!(builder
        .field_apply(CountedFieldBuiltin::Mul, &[a, other])
        .is_err());
    assert!(builder
        .field_apply(CountedFieldBuiltin::Neg, &[a, b])
        .is_err());
    let sum = builder
        .field_apply(CountedFieldBuiltin::Add, &[a, b])
        .unwrap();
    let equation = builder.apply(CountedBuiltin::Eq, &[sum, a]).unwrap();
    let array = builder.constant_array(&Sort::Bool, a).unwrap();
    assert_eq!(builder.terms().finite_field_presence(a), Some(true));
    assert_eq!(builder.terms().finite_field_presence(equation), Some(true));
    assert_eq!(builder.terms().finite_field_presence(array), Some(true));
    builder.finish().unwrap();
    assert_eq!(store.mk_ff_app("ff.add", &[a, b]), Some(sum));
}

#[test]
fn closed_builtin_publication_cannot_reuse_a_declared_function_identity() {
    for declared in [false, true] {
        let mut store = TermStore::new();
        let field = crate::FiniteFieldSort::new(7).unwrap();
        let a = store.mk_finite_field(0, field);
        let b = store.mk_finite_field(1, field);
        let p = store.mk_var("p", Sort::Bool);
        let q = store.mk_var("q", Sort::Bool);
        let u = store.mk_var("u", Sort::bitvec(8));
        let v = store.mk_var("v", Sort::bitvec(8));
        if declared {
            for name in ["=", "and", "bvadd", "ff.mul"] {
                store.register_declared_function(name);
            }
        }
        let original = ample();
        let mut builder = CountedTermBuilder::new(&mut store, &original).unwrap();
        let count = builder.terms().len();
        for result in [
            builder.apply(CountedBuiltin::Eq, &[a, b]),
            builder.apply(CountedBuiltin::And, &[p, q]),
            builder.apply(CountedBuiltin::BvAdd, &[u, v]),
            builder.field_apply(CountedFieldBuiltin::Mul, &[a, b]),
        ] {
            if declared {
                assert_eq!(result, Err(CountedTermError::InvalidInput));
            } else {
                assert!(result.is_ok());
            }
        }
        if declared {
            assert_eq!(builder.terms().len(), count);
        }
        // Structural Not has its own node identity and remains usable when
        // the Named operator spellings above belong to declared functions.
        assert!(builder.apply(CountedBuiltin::Not, &[p]).is_ok());
        builder.finish().unwrap();
    }
}

#[test]
fn counted_exact_integer_literals_share_the_native_typed_interner() {
    let original = ample();
    let mut store = TermStore::new();
    let wide: BigInt = (BigInt::from(1u32) << 4096usize) + 17u32;
    let existing = store.mk_int(wide.clone());
    let x = store.mk_var("integer_x", Sort::Int);
    let one = store.mk_int(1.into());
    let sum = store.mk_app_structural(Symbol::named("+"), &[x, one], Sort::Int);
    let mut builder = CountedTermBuilder::new(&mut store, &original).unwrap();
    assert_eq!(builder.integer(&wide).unwrap(), existing);
    for value in [BigInt::from(0), -wide] {
        let literal = builder.integer(&value).unwrap();
        assert_eq!(
            builder.terms().get(literal),
            &TermData::Const(Constant::Int(value.clone()))
        );
        assert_eq!(builder.terms().sort(literal), &Sort::Int);
        assert_eq!(builder.terms().finite_field_presence(literal), Some(false));
        let rebuilt = builder.rebuild_existing(sum, &[literal, one]).unwrap();
        assert_eq!(
            builder.terms().get(rebuilt),
            &TermData::App(Symbol::named("+"), vec![literal, one])
        );
    }
    builder.finish().unwrap();
}

#[test]
fn counted_integer_literal_refusal_precedes_copy_and_remains_original() {
    use std::sync::atomic::{AtomicBool, Ordering};
    let stop = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&stop);
    let original = CountedAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 1 << 20),
        None,
        Arc::new(move || observed.load(Ordering::Relaxed)),
    )
    .unwrap();
    let mut store = TermStore::new();
    let mut builder = CountedTermBuilder::new(&mut store, &original).unwrap();
    let count = builder.terms().len();
    let wide = BigInt::from(1u32) << 4096usize;
    stop.store(true, Ordering::Relaxed);
    assert!(builder.integer(&wide).is_err());
    stop.store(false, Ordering::Relaxed);
    assert!(builder.integer(&wide).is_err());
    assert_eq!(builder.terms().len(), count);
}

#[test]
fn counted_rational_normalization_preserves_native_value_identity_and_rejects_zero_denominators() {
    use num_rational::BigRational;
    let mut store = TermStore::new();
    let half = store.mk_rational(BigRational::new(1.into(), 2.into()));
    let zero = store.mk_rational(BigRational::from_integer(0.into()));
    let original = ample();
    let mut builder = CountedTermBuilder::new(&mut store, &original).unwrap();
    for (numerator, denominator) in [(2, 4), (-2, -4), (1000, 2000)] {
        assert_eq!(
            builder
                .rational(&BigRational::new_raw(numerator.into(), denominator.into()))
                .unwrap(),
            half
        );
    }
    assert_eq!(
        builder
            .rational(&BigRational::new_raw(0.into(), (-7).into()))
            .unwrap(),
        zero
    );
    let before = builder.terms().len();
    assert_eq!(
        builder.rational(&BigRational::new_raw(1.into(), 0.into())),
        Err(CountedTermError::InvalidInput)
    );
    assert_eq!(builder.terms().len(), before);
    let negative = builder
        .rational(&BigRational::new_raw(1.into(), (-3).into()))
        .unwrap();
    assert_eq!(
        builder.terms().get(negative),
        &TermData::Const(Constant::Rational(
            BigRational::new((-1).into(), 3.into()).into()
        ))
    );
    assert_eq!(builder.terms().sort(negative), &Sort::Real);
    assert_eq!(builder.terms().finite_field_presence(negative), Some(false));
    builder.finish().unwrap();
}

#[test]
fn counted_rational_refusal_precedes_copy_and_remains_original() {
    use std::sync::atomic::{AtomicBool, Ordering};
    let stop = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&stop);
    let original = CountedAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 1 << 20),
        None,
        Arc::new(move || observed.load(Ordering::Relaxed)),
    )
    .unwrap();
    let mut store = TermStore::new();
    let mut builder = CountedTermBuilder::new(&mut store, &original).unwrap();
    let count = builder.terms().len();
    let wide = num_rational::BigRational::new_raw(BigInt::from(1u32) << 4096usize, 3.into());
    stop.store(true, Ordering::Relaxed);
    assert!(builder.rational(&wide).is_err());
    stop.store(false, Ordering::Relaxed);
    assert!(builder.rational(&wide).is_err());
    assert_eq!(builder.terms().len(), count);
}

#[test]
fn raw_construction_preserves_nodes_and_native_interning_after_session() {
    let original = ample();
    let mut store = TermStore::try_new_with_admission(&original).unwrap();
    let mut builder = CountedTermBuilder::new(&mut store, &original).unwrap();
    let yes = builder.boolean(true).unwrap();
    let no = builder.boolean(false).unwrap();
    let conjunction = builder.apply(CountedBuiltin::And, &[no, yes]).unwrap();
    let negated = builder.apply(CountedBuiltin::Not, &[yes]).unwrap();
    assert!(matches!(builder.store.get(conjunction), TermData::App(_, args) if args == &[no, yes]));
    assert_eq!(builder.store.get(negated), &TermData::Not(yes));
    assert_eq!(
        builder.apply(CountedBuiltin::And, &[no, yes]).unwrap(),
        conjunction
    );
    builder.finish().unwrap();
    assert_eq!(
        store.mk_app(Symbol::named("and"), [no, yes], Sort::Bool),
        conjunction
    );
    assert_eq!(store.mk_not_raw(yes), negated);
    assert_eq!(original.deadline(), None);
}

#[test]
fn full_typed_variable_identity_is_stable_with_long_names() {
    let original = ample();
    let mut store = TermStore::new();
    let name = "a".repeat(4096);
    let mut builder = CountedTermBuilder::new(&mut store, &original).unwrap();
    let boolean = builder.variable(&name, &Sort::Bool).unwrap();
    let bits = builder.variable(&name, &Sort::bitvec(257)).unwrap();
    assert_ne!(boolean, bits);
    assert_eq!(builder.variable(&name, &Sort::Bool).unwrap(), boolean);
    assert_eq!(builder.variable(&name, &Sort::bitvec(257)).unwrap(), bits);
    builder.finish().unwrap();
    assert_eq!(store.mk_var(name, Sort::bitvec(257)), bits);
    assert_eq!(store.sort(boolean), &Sort::Bool);
    assert_eq!(store.sort(bits), &Sort::bitvec(257));
}

#[test]
fn new_session_reuses_visible_binding_but_does_not_resurrect_hidden_identity() {
    let original = ample();
    let mut store = TermStore::new();
    let mut first = CountedTermBuilder::new(&mut store, &original).unwrap();
    let hidden = first.variable("same", &Sort::Bool).unwrap();
    let visible = first.variable("same", &Sort::bitvec(8)).unwrap();
    first.finish().unwrap();
    let mut second = CountedTermBuilder::new(&mut store, &original).unwrap();
    assert_eq!(second.variable("same", &Sort::bitvec(8)).unwrap(), visible);
    let recreated = second.variable("same", &Sort::Bool).unwrap();
    assert_ne!(recreated, hidden);
    assert_eq!(second.variable("same", &Sort::Bool).unwrap(), recreated);
    assert_eq!(second.store.sort(hidden), second.store.sort(recreated));
    second.finish().unwrap();
    assert_eq!(store.mk_var("same", Sort::Bool), recreated);
}

#[test]
fn native_array_keys_values_and_indexed_bv_payload_are_not_special_cased() {
    let original = ample();
    let mut store = TermStore::new();
    let mut builder = CountedTermBuilder::new(&mut store, &original).unwrap();
    let value = builder.bitvector(&BigInt::from(7), 257).unwrap();
    let index = builder.bitvector(&BigInt::from(3), 13).unwrap();
    let array = builder.constant_array(&Sort::bitvec(13), value).unwrap();
    let stored = builder
        .apply(CountedBuiltin::Store, &[array, index, value])
        .unwrap();
    let read = builder
        .apply(CountedBuiltin::Select, &[stored, index])
        .unwrap();
    assert_eq!(builder.store.sort(read), &Sort::bitvec(257));
    assert!(matches!(builder.store.get(read), TermData::App(name, _) if name.name() == "select"));
    let high = builder
        .apply(CountedBuiltin::BvExtract(256, 128), &[read])
        .unwrap();
    assert_eq!(builder.store.sort(high), &Sort::bitvec(129));
    assert!(
        matches!(builder.store.get(high), TermData::App(Symbol::Indexed(name, indices), args)
        if name == "extract" && indices == &[256, 128] && args == &[read])
    );
    let outer = builder.constant_array(&Sort::Bool, array).unwrap();
    let yes = builder.boolean(true).unwrap();
    let inner = builder
        .apply(CountedBuiltin::Select, &[outer, yes])
        .unwrap();
    assert_eq!(builder.store.sort(inner), builder.store.sort(array));
    builder.finish().unwrap();
}

#[test]
fn large_arity_preserves_every_original_edge_without_folding_or_a_small_cap() {
    let original = ample();
    let mut store = TermStore::new();
    let mut builder = CountedTermBuilder::new(&mut store, &original).unwrap();
    let yes = builder.boolean(true).unwrap();
    let args = vec![yes; 4096];
    let conjunction = builder.apply(CountedBuiltin::And, &args).unwrap();
    assert!(
        matches!(builder.store.get(conjunction), TermData::App(_, children) if children == &args)
    );
    builder.finish().unwrap();
}

#[test]
fn hash_bucket_selection_is_not_term_or_sort_authority() {
    let original = ample();
    let mut store = TermStore::new();
    let mut builder = CountedTermBuilder::new(&mut store, &original).unwrap();
    let yes = builder.boolean(true).unwrap();
    let no = builder.boolean(false).unwrap();
    let candidate = TermData::App(Symbol::named("and"), vec![yes, no]);
    let hash = TermStore::compute_hash(&candidate);
    builder.terms.insert(hash, yes, &original).unwrap();
    let actual = builder.apply(CountedBuiltin::And, &[yes, no]).unwrap();
    assert_ne!(actual, yes);
    assert_eq!(builder.store.get(actual), &candidate);
    assert_eq!(
        builder.apply(CountedBuiltin::And, &[yes, no]).unwrap(),
        actual
    );
}

#[test]
fn ordered_index_handles_monotone_reverse_and_duplicate_hashes() {
    for reverse in [false, true] {
        let original = ample();
        let mut index = index::Index::default();
        for step in 0..4096u32 {
            let key = if reverse { 4095 - step } else { step };
            index
                .insert(u64::from(key), TermId(key), &original)
                .unwrap();
        }
        for key in 0..4096u32 {
            assert_eq!(
                index.get(u64::from(key), &original).unwrap(),
                Some([TermId(key)].as_slice())
            );
        }
        index.insert(17, TermId(9000), &original).unwrap();
        assert_eq!(
            index.get(17, &original).unwrap(),
            Some([TermId(17), TermId(9000)].as_slice())
        );
        assert!(original.usage().unwrap().work_admitted < 1_000_000);
    }
}
