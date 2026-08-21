// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

// #8529: Use deterministic hash maps in all builds.
use super::*;
use ay_bv::BvModel;
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::Symbol;
use ay_core::{Sort, TermStore};
use num_bigint::BigInt;

#[test]
fn test_evaluate_bv_expr_sign_extend_negative() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(4));
    // sign_extend by 4 bits: 4-bit -> 8-bit
    let sext = terms.mk_app(
        Symbol::indexed("sign_extend", vec![4]),
        vec![x],
        Sort::bitvec(8),
    );
    let mut values = HashMap::default();
    // 0b1100 = 12, but in 4-bit signed = -4
    values.insert(x, BigInt::from(0b1100u8));
    let result = Executor::evaluate_bv_expr(&terms, sext, &values);
    // sign_extend(-4, 8 bits) = 0b11111100 = 252
    assert_eq!(result, Some(BigInt::from(0b11111100u8)));
}

#[test]
fn test_evaluate_bv_expr_sign_extend_positive() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(4));
    let sext = terms.mk_app(
        Symbol::indexed("sign_extend", vec![4]),
        vec![x],
        Sort::bitvec(8),
    );
    let mut values = HashMap::default();
    // 0b0101 = 5 (positive in 4-bit signed)
    values.insert(x, BigInt::from(0b0101u8));
    let result = Executor::evaluate_bv_expr(&terms, sext, &values);
    // sign_extend(5, 8 bits) = 0b00000101 = 5
    assert_eq!(result, Some(BigInt::from(0b00000101u8)));
}

#[test]
fn test_evaluate_bv_expr_sign_extend_named_symbol() {
    // The model evaluator tests use Symbol::named — verify this path works too
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(4));
    let sext = terms.mk_app(Symbol::named("sign_extend"), vec![x], Sort::bitvec(8));
    let mut values = HashMap::default();
    values.insert(x, BigInt::from(0b1100u8));
    let result = Executor::evaluate_bv_expr(&terms, sext, &values);
    assert_eq!(result, Some(BigInt::from(0b11111100u8)));
}

#[test]
fn test_evaluate_bv_expr_zero_extend() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(4));
    let zext = terms.mk_app(Symbol::named("zero_extend"), vec![x], Sort::bitvec(8));
    let mut values = HashMap::default();
    values.insert(x, BigInt::from(0b1100u8));
    let result = Executor::evaluate_bv_expr(&terms, zext, &values);
    // zero_extend(0b1100) = 0b00001100 = 12
    assert_eq!(result, Some(BigInt::from(0b00001100u8)));
}

#[test]
fn test_evaluate_bv_expr_repeat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(4));
    // repeat 3 times: 4-bit -> 12-bit
    let rep = terms.mk_app(
        Symbol::indexed("repeat", vec![3]),
        vec![x],
        Sort::bitvec(12),
    );
    let mut values = HashMap::default();
    // 0b1010
    values.insert(x, BigInt::from(0b1010u8));
    let result = Executor::evaluate_bv_expr(&terms, rep, &values);
    // repeat(0b1010, 3) = 0b1010_1010_1010 = 0xAAA = 2730
    assert_eq!(result, Some(BigInt::from(0b1010_1010_1010u16)));
}

#[test]
fn test_evaluate_bv_expr_ite_with_boolean_condition_11928() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(8));
    let y = terms.mk_var("y", Sort::bitvec(8));
    let one = terms.mk_bitvec(BigInt::from(1u8), 8);
    let two = terms.mk_bitvec(BigInt::from(2u8), 8);
    let three = terms.mk_bitvec(BigInt::from(3u8), 8);
    let ten = terms.mk_bitvec(BigInt::from(10u8), 8);
    let x_lt_ten = terms.mk_bvult(x, ten);
    let y_eq_two = terms.mk_eq_coerce(y, two);
    let cond = terms.mk_and(vec![x_lt_ten, y_eq_two]);
    let ite = terms.mk_ite(cond, one, three);

    let mut values = HashMap::default();
    values.insert(x, BigInt::from(4u8));
    values.insert(y, BigInt::from(2u8));
    assert_eq!(
        Executor::evaluate_bv_expr(&terms, ite, &values),
        Some(BigInt::from(1u8))
    );

    values.insert(y, BigInt::from(5u8));
    assert_eq!(
        Executor::evaluate_bv_expr(&terms, ite, &values),
        Some(BigInt::from(3u8))
    );
}

#[test]
fn test_nested_bv1_store_chain_array_model_recovery_11936() {
    let mut terms = TermStore::new();
    let array_sort = Sort::array(Sort::bitvec(32), Sort::bitvec(8));
    let mem0 = terms.mk_var("mem0", array_sort.clone());
    let mem1 = terms.mk_var("mem1", array_sort);
    let t_store = terms.mk_var("t_store", Sort::bitvec(1));

    let idx = terms.mk_bitvec(BigInt::from(3u8), 32);
    let value = terms.mk_bitvec(BigInt::from(0xaau8), 8);
    let store = terms.mk_store(mem0, idx, value);
    let array_eq = terms.mk_eq_coerce_no_ite_expand(mem1, store);

    let one = terms.mk_bitvec(BigInt::from(1u8), 1);
    let zero = terms.mk_bitvec(BigInt::from(0u8), 1);
    let array_eq_as_bv = terms.mk_ite(array_eq, one, zero);
    let guard_eq = terms.mk_eq_coerce(t_store, array_eq_as_bv);
    let guard_eq_as_bv = terms.mk_ite(guard_eq, one, zero);
    let asserted_bvand = terms.mk_bvand(vec![t_store, guard_eq_as_bv]);
    let assertion = terms.mk_eq_coerce(one, asserted_bvand);

    let mut values = HashMap::default();
    values.insert(t_store, BigInt::from(1u8));
    values.insert(array_eq_as_bv, BigInt::from(1u8));
    values.insert(guard_eq_as_bv, BigInt::from(1u8));
    values.insert(asserted_bvand, BigInt::from(1u8));

    let bv_model = BvModel {
        values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    };

    let array_model = Executor::extract_array_model_from_bv_model(
        &terms,
        &bv_model,
        &[assertion],
        &Default::default(),
    );
    let interp = array_model
        .array_values
        .get(&mem1)
        .expect("nested true BV1 store-chain assertion should recover mem1 model");

    assert_eq!(interp.default.as_deref(), Some("#x00"));
    assert!(
        interp
            .stores
            .iter()
            .any(|(idx, val)| idx == "#x00000003" && val == "#xaa"),
        "expected recovered store at #x00000003 -> #xaa, got {:?}",
        interp.stores
    );
}

#[test]
fn test_recover_substituted_bv_values_defers_stale_substitution_target_11936() {
    let mut terms = TermStore::new();
    let head = terms.mk_var("head", Sort::bitvec(32));
    let curr = terms.mk_var("curr", Sort::bitvec(32));
    let zero = terms.mk_bitvec(BigInt::from(0u8), 32);

    let mut values = HashMap::default();
    values.insert(head, BigInt::from(13u8));
    let mut bv_model = BvModel {
        values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    };

    Executor::recover_substituted_bv_bool_values(
        &terms,
        &[(curr, head), (head, zero)],
        &mut bv_model,
    );

    assert_eq!(bv_model.values.get(&head), Some(&BigInt::from(0u8)));
    assert_eq!(bv_model.values.get(&curr), Some(&BigInt::from(0u8)));
}

/// #abv-select-congruence (wishlist#1): a substituted variable whose RHS is a
/// select over a Var-base array with an index built from OTHER substituted
/// (constant-pinned) variables must recover the value of the bit-blasted read
/// at the same concrete index — not the select's stale, unconstrained
/// bit-blast value.
#[test]
fn test_recover_substituted_select_by_index_congruence_wishlist1() {
    let mut terms = TermStore::new();
    let tbl = terms.mk_var("tbl", Sort::array(Sort::bitvec(24), Sort::bitvec(32)));
    let op = terms.mk_var("op", Sort::bitvec(8));
    let lhs = terms.mk_var("lhs", Sort::bitvec(8));
    let rhs = terms.mk_var("rhs", Sort::bitvec(8));
    let out = terms.mk_var("out", Sort::bitvec(32));

    // Original read: select(tbl, concat(op, concat(lhs, rhs))).
    let inner = terms.mk_app(Symbol::named("concat"), vec![lhs, rhs], Sort::bitvec(16));
    let orig_idx = terms.mk_app(Symbol::named("concat"), vec![op, inner], Sort::bitvec(24));
    let orig_sel = terms.mk_select(tbl, orig_idx);

    // Pinned read at the literal index 0x013f40 (a distinct term).
    let c01 = terms.mk_bitvec(BigInt::from(0x01u8), 8);
    let c3f = terms.mk_bitvec(BigInt::from(0x3fu8), 8);
    let c40 = terms.mk_bitvec(BigInt::from(0x40u8), 8);
    let lit_inner = terms.mk_app(Symbol::named("concat"), vec![c3f, c40], Sort::bitvec(16));
    let lit_idx = terms.mk_app(
        Symbol::named("concat"),
        vec![c01, lit_inner],
        Sort::bitvec(24),
    );
    let pinned_sel = terms.mk_select(tbl, lit_idx);

    let mut values = HashMap::default();
    values.insert(pinned_sel, BigInt::from(0x4040_0000u32));
    // Stale decoupled bits for the original read (free in the CNF): index
    // bits at some unrelated value, element bits at 0. These must be IGNORED.
    values.insert(orig_idx, BigInt::from(0xffffffu32));
    values.insert(orig_sel, BigInt::from(0u8));
    let mut bv_model = BvModel {
        values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    };

    Executor::recover_substituted_bv_bool_values(
        &terms,
        &[(out, orig_sel), (op, c01), (lhs, c3f), (rhs, c40)],
        &mut bv_model,
    );

    assert_eq!(bv_model.values.get(&op), Some(&BigInt::from(0x01u8)));
    assert_eq!(
        bv_model.values.get(&out),
        Some(&BigInt::from(0x4040_0000u32)),
        "out must recover the index-congruent pinned read value, \
         not the stale decoupled bit-blast value"
    );
}

/// #abv-select-congruence fail-closed: when two bit-blasted reads of the same
/// array at the same concrete index DISAGREE, the congruence entry is
/// poisoned and the substituted variable must stay unresolved — never
/// defaulted to either conflicting value or to the stale bit-blast value.
#[test]
fn test_recover_substituted_select_conflicted_index_fails_closed_wishlist1() {
    let mut terms = TermStore::new();
    let tbl = terms.mk_var("tbl", Sort::array(Sort::bitvec(16), Sort::bitvec(8)));
    let i = terms.mk_var("i", Sort::bitvec(16));
    let out = terms.mk_var("out", Sort::bitvec(8));

    let orig_sel = terms.mk_select(tbl, i);

    // Two distinct index TERMS with the same VALUE 0x0102, conflicting reads.
    let c0102 = terms.mk_bitvec(BigInt::from(0x0102u16), 16);
    let sel_a = terms.mk_select(tbl, c0102);
    let c01 = terms.mk_bitvec(BigInt::from(0x01u8), 8);
    let c02 = terms.mk_bitvec(BigInt::from(0x02u8), 8);
    let concat_idx = terms.mk_app(Symbol::named("concat"), vec![c01, c02], Sort::bitvec(16));
    let sel_b = terms.mk_select(tbl, concat_idx);

    let mut values = HashMap::default();
    values.insert(sel_a, BigInt::from(0xaau8));
    values.insert(sel_b, BigInt::from(0xbbu8));
    // Stale decoupled bits for the original read.
    values.insert(orig_sel, BigInt::from(0x77u8));
    let mut bv_model = BvModel {
        values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    };

    Executor::recover_substituted_bv_bool_values(
        &terms,
        &[(out, orig_sel), (i, c0102)],
        &mut bv_model,
    );

    assert_eq!(bv_model.values.get(&i), Some(&BigInt::from(0x0102u16)));
    assert!(
        !bv_model.values.contains_key(&out),
        "conflicting same-index reads must fail closed (leave out unresolved), got {:?}",
        bv_model.values.get(&out)
    );
}

#[test]
fn test_recover_substituted_bv_values_drops_unrecovered_stale_value_11936() {
    let mut terms = TermStore::new();
    let arr = terms.mk_var("arr", Sort::array(Sort::bitvec(8), Sort::bitvec(8)));
    let idx = terms.mk_var("idx", Sort::bitvec(8));
    let x = terms.mk_var("x", Sort::bitvec(8));
    let select = terms.mk_select(arr, idx);

    let mut values = HashMap::default();
    values.insert(x, BigInt::from(7u8));
    let mut bv_model = BvModel {
        values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    };

    Executor::recover_substituted_bv_bool_values(&terms, &[(x, select)], &mut bv_model);

    assert!(
        !bv_model.values.contains_key(&x),
        "stale value for unrecovered substituted variable must not survive"
    );
}

/// #8512-forced-or: a store-chain definition sitting in the ONLY arm of a
/// disjunction the model does not falsify is forced, so the chain is walked and
/// the resulting interpretation is complete — hence NOT read-conflicted.
#[test]
fn test_forced_or_arm_store_chain_definition_is_recovered_8512() {
    let mut terms = TermStore::new();
    let array_sort = Sort::array(Sort::bitvec(32), Sort::bitvec(8));
    let base = terms.mk_var("base", array_sort.clone());
    let mem = terms.mk_var("mem", array_sort);
    let p = terms.mk_var("p", Sort::bitvec(32));

    let idx1 = terms.mk_bitvec(BigInt::from(3u8), 32);
    let idx2 = terms.mk_bitvec(BigInt::from(7u8), 32);
    let value = terms.mk_bitvec(BigInt::from(0xaau8), 8);
    let inner = terms.mk_store(base, idx1, value);
    let store = terms.mk_store(inner, idx2, value);
    let def = terms.mk_eq_coerce_no_ite_expand(mem, store);

    let one = terms.mk_bitvec(BigInt::from(1u8), 32);
    let two = terms.mk_bitvec(BigInt::from(2u8), 32);
    let p_is_one = terms.mk_eq_coerce(p, one);
    let p_is_two = terms.mk_eq_coerce(p, two);
    let read = terms.mk_select(mem, idx2);
    let read_is_one = terms.mk_eq_coerce(read, value);
    let arm_live = terms.mk_and(vec![p_is_one, def]);
    let arm_dead = terms.mk_and(vec![p_is_two, read_is_one]);
    let assertion = terms.mk_or(vec![arm_live, arm_dead]);

    // The model sets p = 1, so `p = 2` is FALSE and the second arm cannot hold.
    let mut values = HashMap::default();
    values.insert(p, BigInt::from(1u8));
    let bv_model = BvModel {
        values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    };

    let array_model = Executor::extract_array_model_from_bv_model(
        &terms,
        &bv_model,
        &[assertion],
        &Default::default(),
    );

    assert!(
        !array_model.read_conflicted.contains(&mem),
        "a forced arm's chain resolves completely, so nothing should be withheld"
    );
    let interp = array_model
        .array_values
        .get(&mem)
        .expect("forced `or` arm should recover the mem model");
    for expected in ["#x00000003", "#x00000007"] {
        assert!(
            interp
                .stores
                .iter()
                .any(|(idx, val)| idx == expected && val == "#xaa"),
            "expected store at {expected} -> #xaa, got {:?}",
            interp.stores
        );
    }
}

/// #8512-forced-or, the soundness half: with TWO arms the model leaves live,
/// the disjunction forces neither, so the nested definition must NOT be adopted
/// — the model is free to satisfy the other arm. The variable keeps its partial
/// interpretation and stays read-conflicted.
#[test]
fn test_two_live_or_arms_leave_store_chain_definition_unadopted_8512() {
    let mut terms = TermStore::new();
    let array_sort = Sort::array(Sort::bitvec(32), Sort::bitvec(8));
    let base = terms.mk_var("base", array_sort.clone());
    let mem = terms.mk_var("mem", array_sort);
    let p = terms.mk_var("p", Sort::bitvec(32));

    let idx = terms.mk_bitvec(BigInt::from(3u8), 32);
    let value = terms.mk_bitvec(BigInt::from(0xaau8), 8);
    let store = terms.mk_store(base, idx, value);
    // A bare array equality: the BV model cannot evaluate it, so this arm is
    // never "known false" and the disjunction is not unit.
    let def = terms.mk_eq_coerce_no_ite_expand(mem, store);

    let two = terms.mk_bitvec(BigInt::from(2u8), 32);
    let p_is_two = terms.mk_eq_coerce(p, two);
    let assertion = terms.mk_or(vec![def, p_is_two]);

    let mut values = HashMap::default();
    values.insert(p, BigInt::from(2u8));
    let bv_model = BvModel {
        values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    };

    let array_model = Executor::extract_array_model_from_bv_model(
        &terms,
        &bv_model,
        &[assertion],
        &Default::default(),
    );

    assert!(
        array_model.read_conflicted.contains(&mem),
        "an unforced nested definition must leave mem withheld, not adopted"
    );
    assert!(
        array_model
            .array_values
            .get(&mem)
            .is_none_or(|interp| !interp.stores.iter().any(|(i, _)| i == "#x00000003")),
        "the unforced store chain must not have been written into the model"
    );
}

/// #8512-forced-or: a forced arm is not enough on its own. When a chain pair
/// cannot be made concrete by the BV model the interpretation still has a hole,
/// which would read back as the array's `default`, so the variable stays
/// read-conflicted.
#[test]
fn test_forced_or_arm_with_unresolvable_chain_pair_stays_read_conflicted_8512() {
    let mut terms = TermStore::new();
    let array_sort = Sort::array(Sort::bitvec(32), Sort::bitvec(8));
    let base = terms.mk_var("base", array_sort.clone());
    let mem = terms.mk_var("mem", array_sort);
    let p = terms.mk_var("p", Sort::bitvec(32));
    // No model value and no evaluable definition: this index never resolves.
    let opaque_idx = terms.mk_var("opaque_idx", Sort::bitvec(32));

    let idx1 = terms.mk_bitvec(BigInt::from(3u8), 32);
    let value = terms.mk_bitvec(BigInt::from(0xaau8), 8);
    let inner = terms.mk_store(base, idx1, value);
    let store = terms.mk_store(inner, opaque_idx, value);
    let def = terms.mk_eq_coerce_no_ite_expand(mem, store);

    let one = terms.mk_bitvec(BigInt::from(1u8), 32);
    let two = terms.mk_bitvec(BigInt::from(2u8), 32);
    let p_is_one = terms.mk_eq_coerce(p, one);
    let p_is_two = terms.mk_eq_coerce(p, two);
    let arm_live = terms.mk_and(vec![p_is_one, def]);
    let arm_dead = terms.mk_and(vec![p_is_two, p_is_two]);
    let assertion = terms.mk_or(vec![arm_live, arm_dead]);

    let mut values = HashMap::default();
    values.insert(p, BigInt::from(1u8));
    let bv_model = BvModel {
        values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    };

    let array_model = Executor::extract_array_model_from_bv_model(
        &terms,
        &bv_model,
        &[assertion],
        &Default::default(),
    );

    assert!(
        array_model.read_conflicted.contains(&mem),
        "an unresolved chain pair leaves a hole, so mem must stay withheld"
    );
}

/// #8512-forced-or: the arm-liveness test has to see past an UNEVALUABLE
/// conjunct. Real arms are hundred-conjunct BMC blocks that always contain an
/// array equality the BV model cannot evaluate; `model_bool_value` returns
/// `None` for the whole `and` in that case, which would leave every arm "live"
/// and the disjunction never unit. The structural short-circuit — one false
/// conjunct settles the conjunction — is what makes the rule fire at all.
#[test]
fn test_definitely_false_arm_short_circuits_past_an_unevaluable_conjunct_8512() {
    let mut terms = TermStore::new();
    let array_sort = Sort::array(Sort::bitvec(32), Sort::bitvec(8));
    let base = terms.mk_var("base", array_sort.clone());
    let mem = terms.mk_var("mem", array_sort.clone());
    let other = terms.mk_var("other", array_sort);
    let p = terms.mk_var("p", Sort::bitvec(32));

    let idx = terms.mk_bitvec(BigInt::from(3u8), 32);
    let value = terms.mk_bitvec(BigInt::from(0xaau8), 8);
    let store = terms.mk_store(base, idx, value);
    let def = terms.mk_eq_coerce_no_ite_expand(mem, store);

    // The dead arm pairs a FALSE scalar with an array equality that has no
    // model value at all. Only the short-circuit can call this arm false.
    let other_store = terms.mk_store(base, idx, value);
    let unevaluable = terms.mk_eq_coerce_no_ite_expand(other, other_store);

    let one = terms.mk_bitvec(BigInt::from(1u8), 32);
    let two = terms.mk_bitvec(BigInt::from(2u8), 32);
    let p_is_one = terms.mk_eq_coerce(p, one);
    let p_is_two = terms.mk_eq_coerce(p, two);
    let arm_live = terms.mk_and(vec![p_is_one, def]);
    let arm_dead = terms.mk_and(vec![p_is_two, unevaluable]);
    let assertion = terms.mk_or(vec![arm_live, arm_dead]);

    let mut values = HashMap::default();
    values.insert(p, BigInt::from(1u8));
    let bv_model = BvModel {
        values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    };

    let array_model = Executor::extract_array_model_from_bv_model(
        &terms,
        &bv_model,
        &[assertion],
        &Default::default(),
    );

    let interp = array_model
        .array_values
        .get(&mem)
        .expect("the dead arm's unevaluable conjunct must not block the walk");
    assert!(
        interp
            .stores
            .iter()
            .any(|(i, v)| i == "#x00000003" && v == "#xaa"),
        "expected store at #x00000003 -> #xaa, got {:?}",
        interp.stores
    );
}
