// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The original external-codegen checked-i128 predicates: 128-bit inputs and wrapping
//! value, exact 129-bit arithmetic on the specification side, independently
//! encoded overflow flag on the machine side, and a 129-bit packed result.

use super::*;

#[derive(Clone, Copy, Debug)]
enum Kind {
    SignedAdd,
    SignedSub,
    UnsignedAdd,
    UnsignedSub,
}

#[derive(Clone, Copy)]
enum Flag {
    Intended,
    Inverted,
}

const KINDS: [Kind; 4] = [
    Kind::SignedAdd,
    Kind::SignedSub,
    Kind::UnsignedAdd,
    Kind::UnsignedSub,
];

fn word(terms: &mut TermStore, op: &str, args: &[TermId], width: u32) -> TermId {
    terms.mk_app(Symbol::named(op), args, Sort::bitvec(width))
}

fn predicate(terms: &mut TermStore, op: &str, args: &[TermId]) -> TermId {
    terms.mk_app(Symbol::named(op), args, Sort::Bool)
}

fn indexed(terms: &mut TermStore, op: &str, indices: &[u32], arg: TermId, width: u32) -> TermId {
    terms.mk_app(
        Symbol::indexed(op, indices.to_vec()),
        [arg],
        Sort::bitvec(width),
    )
}

fn pack(terms: &mut TermStore, flag: TermId, value: TermId) -> TermId {
    let one = terms.mk_bitvec(1.into(), 1);
    let zero = terms.mk_bitvec(0.into(), 1);
    let flag = terms.mk_ite(flag, one, zero);
    word(terms, "concat", &[flag, value], 129)
}

fn machine_flag(terms: &mut TermStore, kind: Kind, a: TermId, b: TermId, value: TermId) -> TermId {
    match kind {
        Kind::UnsignedAdd => predicate(terms, "bvult", &[value, a]),
        Kind::UnsignedSub => predicate(terms, "bvult", &[a, b]),
        Kind::SignedAdd | Kind::SignedSub => {
            let sa = indexed(terms, "extract", &[127, 127], a, 1);
            let sb = indexed(terms, "extract", &[127, 127], b, 1);
            let sv = indexed(terms, "extract", &[127, 127], value, 1);
            let same_inputs = predicate(terms, "=", &[sa, sb]);
            let input_signs = match kind {
                Kind::SignedAdd => same_inputs,
                _ => terms.mk_not_raw(same_inputs),
            };
            let same_result = predicate(terms, "=", &[sa, sv]);
            let changed_result = terms.mk_not_raw(same_result);
            predicate(terms, "and", &[input_signs, changed_result])
        }
    }
}

fn original_query(terms: &mut TermStore, kind: Kind, flag: Flag) -> TermId {
    let a = terms.mk_var("a", Sort::bitvec(128));
    let b = terms.mk_var("b", Sort::bitvec(128));
    let op = match kind {
        Kind::SignedAdd | Kind::UnsignedAdd => "bvadd",
        _ => "bvsub",
    };
    let extension = match kind {
        Kind::SignedAdd | Kind::SignedSub => "sign_extend",
        _ => "zero_extend",
    };
    let value = word(terms, op, &[a, b], 128);
    let a_ext = indexed(terms, extension, &[1], a, 129);
    let b_ext = indexed(terms, extension, &[1], b, 129);
    let exact = word(terms, op, &[a_ext, b_ext], 129);
    let wrapped = indexed(terms, extension, &[1], value, 129);
    let same = predicate(terms, "=", &[exact, wrapped]);
    let spec_flag = terms.mk_not_raw(same);
    let actual_flag = machine_flag(terms, kind, a, b, value);
    let actual_flag = match flag {
        Flag::Intended => actual_flag,
        Flag::Inverted => terms.mk_not_raw(actual_flag),
    };
    let spec = pack(terms, spec_flag, value);
    let actual = pack(terms, actual_flag, value);
    assert_ne!(
        spec, actual,
        "a structurally identical obligation grants no credit"
    );
    let equality = predicate(terms, "=", &[spec, actual]);
    terms.mk_not_raw(equality)
}

#[test]
fn original_checked_i128_predicates_authenticate_without_widening_words() {
    assert_eq!(MAX_PROOF_PRODUCING_INTERNAL_BV_WIDTH, 128);
    for kind in KINDS {
        let mut terms = TermStore::new();
        let root = original_query(&mut terms, kind, Flag::Intended);
        let mut lowerer =
            ProofProducingLowerer::new(&terms, Instant::now() + Duration::from_secs(60));
        lowerer
            .lower_bool(root)
            .expect("complete original query must lower");
        lowerer.audit_census();
        let result = authenticate_bool_bv_unsat_query(&terms, &[root], None);
        assert!(result.is_ok(), "{kind:?}: {result:?}");
        assert!(result.unwrap().is_current_for(&terms, &[root]));
    }
}

#[test]
fn original_overflow_words_also_authenticate_across_unaligned_concat_slices() {
    for kind in KINDS {
        for padding in [1, 7, 63] {
            let mut terms = TermStore::new();
            let original = original_query(&mut terms, kind, Flag::Intended);
            let TermData::Not(equality) = terms.get(original) else {
                panic!("negated equality")
            };
            let TermData::App(_, args) = terms.get(*equality) else {
                panic!("packed equality")
            };
            let (left, right) = (args[0], args[1]);
            let pad = terms.mk_var("padding", Sort::bitvec(padding));
            let lhs = word(&mut terms, "concat", &[left, pad], 129 + padding);
            let rhs = word(&mut terms, "concat", &[right, pad], 129 + padding);
            let equality = predicate(&mut terms, "=", &[lhs, rhs]);
            let root = terms.mk_not_raw(equality);
            let result = authenticate_bool_bv_unsat_query(&terms, &[root], None);
            assert!(result.is_ok(), "{kind:?}, padding {padding}: {result:?}");
        }
    }
}

#[test]
fn padded_inverted_overflow_flags_remain_satisfiable() {
    for kind in KINDS {
        for padding in [1, 7, 63] {
            let mut terms = TermStore::new();
            let original = original_query(&mut terms, kind, Flag::Inverted);
            let TermData::Not(equality) = terms.get(original) else {
                panic!("negated equality")
            };
            let TermData::App(_, args) = terms.get(*equality) else {
                panic!("packed equality")
            };
            let (left, right) = (args[0], args[1]);
            let pad = terms.mk_var("padding", Sort::bitvec(padding));
            let lhs = word(&mut terms, "concat", &[left, pad], 129 + padding);
            let rhs = word(&mut terms, "concat", &[right, pad], 129 + padding);
            let equality = predicate(&mut terms, "=", &[lhs, rhs]);
            let root = terms.mk_not_raw(equality);
            let result = authenticate_bool_bv_unsat_query(&terms, &[root], None);
            assert!(
                matches!(result, Err(BoolBvUnsatAuthenticationError::Satisfiable)),
                "{kind:?}, padding {padding}: {result:?}"
            );
        }
    }
}

fn widened_value_query(terms: &mut TermStore, kind: Kind, flag: Flag, padding: u32) -> TermId {
    let op = match kind {
        Kind::UnsignedAdd => "bvadd",
        Kind::UnsignedSub => "bvsub",
        _ => panic!("unsigned value identity"),
    };
    let a = terms.mk_var("a", Sort::bitvec(128));
    let b = terms.mk_var("b", Sort::bitvec(128));
    let value = word(terms, op, &[a, b], 128);
    let ae = indexed(terms, "zero_extend", &[1], a, 129);
    let be = indexed(terms, "zero_extend", &[1], b, 129);
    let wide = word(terms, op, &[ae, be], 129);
    let carry = machine_flag(terms, kind, a, b, value);
    let carry = match flag {
        Flag::Intended => carry,
        Flag::Inverted => terms.mk_not_raw(carry),
    };
    let one = terms.mk_bitvec(1.into(), 1);
    let zero = terms.mk_bitvec(0.into(), 1);
    let carry = terms.mk_ite(carry, one, zero);
    let pad = terms.mk_var("padding", Sort::bitvec(padding));
    // Deliberately different concat boundaries: the arithmetic itself is
    // requested through unaligned windows, rather than isolated by a common
    // outer field. Correctness includes the complete carry/borrow bit.
    let lhs = word(terms, "concat", &[wide, pad], 129 + padding);
    let lower = word(terms, "concat", &[value, pad], 128 + padding);
    let rhs = word(terms, "concat", &[carry, lower], 129 + padding);
    let equality = predicate(terms, "=", &[lhs, rhs]);
    terms.mk_not_raw(equality)
}

#[test]
fn widened_values_preserve_carry_and_borrow_across_different_field_partitions() {
    for kind in [Kind::UnsignedAdd, Kind::UnsignedSub] {
        for padding in [1, 7, 63] {
            let mut terms = TermStore::new();
            let root = widened_value_query(&mut terms, kind, Flag::Intended, padding);
            let result = authenticate_bool_bv_unsat_query(&terms, &[root], None);
            assert!(result.is_ok(), "{kind:?}, padding {padding}: {result:?}");
            let mut wrong_terms = TermStore::new();
            let wrong = widened_value_query(&mut wrong_terms, kind, Flag::Inverted, padding);
            let result = authenticate_bool_bv_unsat_query(&wrong_terms, &[wrong], None);
            assert!(
                matches!(result, Err(BoolBvUnsatAuthenticationError::Satisfiable)),
                "wrong {kind:?}, padding {padding}: {result:?}"
            );
        }
    }
}

#[test]
fn inverted_original_i128_flags_are_satisfiable_not_certified() {
    for kind in KINDS {
        let mut terms = TermStore::new();
        let root = original_query(&mut terms, kind, Flag::Inverted);
        let result = authenticate_bool_bv_unsat_query(&terms, &[root], None);
        assert!(
            matches!(result, Err(BoolBvUnsatAuthenticationError::Satisfiable)),
            "{kind:?}: {result:?}"
        );
    }
}

#[test]
fn constant_padding_matches_wide_zero_extension_across_limb_boundaries() {
    for width in [257, 511, 512, 1023, 1024] {
        for kind in [Kind::UnsignedAdd, Kind::UnsignedSub] {
            let mut terms = TermStore::new();
            let a = terms.mk_var("a", Sort::bitvec(128));
            let b = terms.mk_var("b", Sort::bitvec(128));
            let op = match kind {
                Kind::UnsignedAdd => "bvadd",
                _ => "bvsub",
            };
            let value = word(&mut terms, op, &[a, b], 128);
            // The proof surface expands zero_extend to a concat with a
            // constant. At 257 bits that padding itself exceeds 128 bits.
            let zero = terms.mk_bitvec(0.into(), width - 128);
            let ae = word(&mut terms, "concat", &[zero, a], width);
            let be = word(&mut terms, "concat", &[zero, b], width);
            let exact = word(&mut terms, op, &[ae, be], width);
            let flag = machine_flag(&mut terms, kind, a, b, value);
            let one = terms.mk_bitvec(1.into(), 1);
            let zero = terms.mk_bitvec(0.into(), 1);
            let bit = terms.mk_ite(flag, one, zero);
            let extension = match kind {
                Kind::UnsignedAdd => "zero_extend",
                _ => "sign_extend",
            };
            let prefix = indexed(&mut terms, extension, &[width - 129], bit, width - 128);
            let expected = word(&mut terms, "concat", &[prefix, value], width);
            let equal = predicate(&mut terms, "=", &[exact, expected]);
            let root = terms.mk_not_raw(equal);
            let result = authenticate_bool_bv_unsat_query(&terms, &[root], None);
            assert!(result.is_ok(), "{kind:?}, width {width}: {result:?}");
        }
    }
}
