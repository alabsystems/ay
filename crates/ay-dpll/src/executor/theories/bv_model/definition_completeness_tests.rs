// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-true ground array definitions that used to stay withheld although
//! every cell they define is known:
//!
//! * a definition listed before the definition of the array it reads;
//! * an operand that is a read of an array variable, or an uninterpreted
//!   application;
//! * a definition the model has already made irrelevant, or whose atom the
//!   SAT assignment set false;
//! * a nested array (`(Array BV64 (Array BV64 BV8))`) definition.
//!
//! Each case has a twin whose definition genuinely cannot be built, or still
//! matters. A forced store chain that cannot be built stays withheld; a
//! definition the model does not force is not adopted, and since
//! #bv-array-delegation it no longer withholds its variable either
//! (`live_definitions.rs`).

use super::*;
use ay_core::term::Symbol;

pub(super) fn bv(terms: &mut TermStore, value: u64, width: u32) -> TermId {
    terms.mk_bitvec(BigInt::from(value), width)
}

pub(super) fn array_of(index_width: u32, element: Sort) -> Sort {
    Sort::array(Sort::bitvec(index_width), element)
}

pub(super) fn model(values: &[(TermId, u64)], bools: &[(TermId, bool)]) -> BvModel {
    BvModel {
        values: values.iter().map(|&(t, v)| (t, BigInt::from(v))).collect(),
        term_to_bits: HashMap::default(),
        bool_overrides: bools.iter().copied().collect(),
    }
}

pub(super) fn extract(terms: &TermStore, bv_model: &BvModel, assertions: &[TermId]) -> ArrayModel {
    Executor::extract_array_model_from_bv_model(terms, bv_model, assertions, &Default::default())
}

pub(super) fn cell<'a>(array_model: &'a ArrayModel, array: TermId, index: &str) -> &'a str {
    let interp = &array_model.array_values[&array];
    interp
        .stores
        .iter()
        .find(|(key, _)| key == index)
        .map(|(_, value)| value.as_str())
        .or(interp.default.as_deref())
        .expect("a complete interpretation")
}

/// `(or (= p 2) arm)` evaluated with `p = 1`: `arm` is the forced disjunct.
pub(super) fn forced(terms: &mut TermStore, arm: TermId) -> (TermId, TermId) {
    let p = terms.mk_var("p", Sort::bitvec(8));
    let two = bv(terms, 2, 8);
    let p_is_two = terms.mk_eq_coerce(p, two);
    (terms.mk_or(vec![p_is_two, arm]), p)
}

pub(super) fn define(terms: &mut TermStore, var: TermId, definition: TermId) -> TermId {
    terms.mk_eq_coerce_no_ite_expand(var, definition)
}

/// `d := (store c 9 false)` listed before `c := c_definition`, in one forced
/// arm; returns `(assertion, p, c, d)`.
fn base_defined_later(
    terms: &mut TermStore,
    c_definition: TermId,
) -> (TermId, TermId, TermId, TermId) {
    let c = terms.mk_var("c", array_of(32, Sort::Bool));
    let d = terms.mk_var("d", array_of(32, Sort::Bool));
    let nine = bv(terms, 9, 32);
    let fls = terms.mk_bool(false);
    let store = terms.mk_store(c, nine, fls);
    let d_def = define(terms, d, store);
    let c_def = define(terms, c, c_definition);
    let arm = terms.mk_and(vec![d_def, c_def]);
    let (assertion, p) = forced(terms, arm);
    (assertion, p, c, d)
}

#[test]
fn definition_listed_before_its_base_definition_resolves() {
    let mut terms = TermStore::new();
    let tru = terms.mk_bool(true);
    let all_true = terms.mk_const_array(Sort::bitvec(32), tru);
    let (assertion, p, c, d) = base_defined_later(&mut terms, all_true);

    let arrays = extract(&terms, &model(&[(p, 1)], &[]), &[assertion]);

    for var in [c, d] {
        assert!(
            !arrays.read_conflicted.contains(&var),
            "both definitions are forced and complete"
        );
    }
    assert_eq!(cell(&arrays, d, "#x00000009"), "false");
    assert_eq!(
        cell(&arrays, d, "#x00000005"),
        "true",
        "d inherits c's default"
    );
}

#[test]
fn definition_over_an_unbuilt_base_definition_stays_withheld() {
    let mut terms = TermStore::new();
    let tru = terms.mk_bool(true);
    let fls = terms.mk_bool(false);
    let all_true = terms.mk_const_array(Sort::bitvec(32), tru);
    // The index has no value, so c's store chain cannot be built.
    let open_index = terms.mk_var("i", Sort::bitvec(32));
    let unbuilt = terms.mk_store(all_true, open_index, fls);
    let (assertion, p, c, d) = base_defined_later(&mut terms, unbuilt);

    let arrays = extract(&terms, &model(&[(p, 1)], &[]), &[assertion]);

    assert!(
        arrays.read_conflicted.contains(&c),
        "c's own definition did not resolve"
    );
    assert!(
        arrays.read_conflicted.contains(&d),
        "a withheld base withholds d"
    );
}

/// The variables and reads of [`read_operand_definition`].
struct ReadOperands {
    assertion: TermId,
    p: TermId,
    x: TermId,
    m: TermId,
    z: TermId,
    read_one: TermId,
    read_three: TermId,
}

/// `z := (store (const (select m #x1)) x (select m #x3))` in a forced arm.
fn read_operand_definition(terms: &mut TermStore, element: Sort) -> ReadOperands {
    let m = terms.mk_var("m", array_of(4, element.clone()));
    let z = terms.mk_var("z", array_of(4, element));
    let x = terms.mk_var("x", Sort::bitvec(4));
    let one = bv(terms, 1, 4);
    let three = bv(terms, 3, 4);
    let read_one = terms.mk_select(m, one);
    let read_three = terms.mk_select(m, three);
    let all_read = terms.mk_const_array(Sort::bitvec(4), read_one);
    let store = terms.mk_store(all_read, x, read_three);
    let z_def = define(terms, z, store);
    let (assertion, p) = forced(terms, z_def);
    ReadOperands {
        assertion,
        p,
        x,
        m,
        z,
        read_one,
        read_three,
    }
}

#[test]
fn bool_read_operands_resolve_through_the_read_array() {
    let mut terms = TermStore::new();
    let r = read_operand_definition(&mut terms, Sort::Bool);

    // The reads are SAT atoms without BV bits; the select scan gives m their
    // values, and the definition reads them back from m.
    let bits = model(
        &[(r.p, 1), (r.x, 0)],
        &[(r.read_one, true), (r.read_three, false)],
    );
    let arrays = extract(&terms, &bits, &[r.assertion]);
    let z = r.z;

    assert!(!arrays.read_conflicted.contains(&z));
    assert_eq!(cell(&arrays, z, "#x0"), "false");
    assert_eq!(cell(&arrays, z, "#x5"), "true");
}

#[test]
fn bv_read_operands_resolve_through_the_read_array() {
    let mut terms = TermStore::new();
    let r = read_operand_definition(&mut terms, Sort::bitvec(8));

    let bits = model(
        &[(r.p, 1), (r.x, 0), (r.read_one, 0x2a), (r.read_three, 0x07)],
        &[],
    );
    let arrays = extract(&terms, &bits, &[r.assertion]);
    let z = r.z;

    assert!(!arrays.read_conflicted.contains(&z));
    assert_eq!(cell(&arrays, z, "#x0"), "#x07");
    assert_eq!(cell(&arrays, z, "#x5"), "#x2a");
}

#[test]
fn read_operand_of_a_withheld_array_stays_unresolved() {
    let mut terms = TermStore::new();
    let r = read_operand_definition(&mut terms, Sort::Bool);
    // m's only definition is a forced store chain whose index has no value:
    // m is withheld, so its reads are no evidence for z's cells.
    let m = r.m;
    let fls = terms.mk_bool(false);
    let tru = terms.mk_bool(true);
    let all_false = terms.mk_const_array(Sort::bitvec(4), fls);
    let open_index = terms.mk_var("i", Sort::bitvec(4));
    let unbuilt = terms.mk_store(all_false, open_index, tru);
    let m_def = define(&mut terms, m, unbuilt);
    let q = terms.mk_var("q", Sort::bitvec(8));
    let two = bv(&mut terms, 2, 8);
    let q_is_two = terms.mk_eq_coerce(q, two);
    let m_assertion = terms.mk_or(vec![m_def, q_is_two]);

    let bits = model(
        &[(r.p, 1), (r.x, 0), (q, 1)],
        &[(r.read_one, true), (r.read_three, false)],
    );
    let arrays = extract(&terms, &bits, &[r.assertion, m_assertion]);

    assert!(arrays.read_conflicted.contains(&m));
    assert!(
        arrays.read_conflicted.contains(&r.z),
        "z read a withheld array"
    );
}

#[test]
fn uninterpreted_application_operand_resolves_to_its_own_assignment() {
    for assigned in [true, false] {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::bitvec(8));
        let g_x = terms.mk_app(Symbol::named("g"), vec![x], Sort::bitvec(8));
        let z = terms.mk_var("z", array_of(4, Sort::bitvec(8)));
        let all_g = terms.mk_const_array(Sort::bitvec(4), g_x);
        let z_def = define(&mut terms, z, all_g);
        let (assertion, p) = forced(&mut terms, z_def);

        let mut values = vec![(p, 1), (x, 3)];
        if assigned {
            values.push((g_x, 5));
        }
        let arrays = extract(&terms, &model(&values, &[]), &[assertion]);

        if assigned {
            assert!(!arrays.read_conflicted.contains(&z));
            assert_eq!(cell(&arrays, z, "#x9"), "#x05");
        } else {
            assert!(
                !arrays.array_values.contains_key(&z),
                "no value for (g x): z's definition publishes nothing"
            );
        }
    }
}

/// #store-chain-dead-node: an interpreted operator is recomputed from its
/// arguments (`bvsmod`) or left unresolved (`bvredor`, which no registry
/// lists), never read back from its cached bits, which here are stale.
#[test]
fn interpreted_operator_operand_is_never_read_from_cached_bits() {
    for (op, binary, width, expected) in [
        ("bvsmod", true, 8, Some("#x01")),
        ("bvredor", false, 1, None),
    ] {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::bitvec(8));
        let y = terms.mk_var("y", Sort::bitvec(8));
        let args = if binary { vec![x, y] } else { vec![x] };
        let applied = terms.mk_app(Symbol::named(op), args, Sort::bitvec(width));
        let z = terms.mk_var("z", array_of(4, Sort::bitvec(width)));
        let all = terms.mk_const_array(Sort::bitvec(4), applied);
        let z_def = define(&mut terms, z, all);
        let (assertion, p) = forced(&mut terms, z_def);

        let bits = model(&[(p, 1), (x, 7), (y, 3), (applied, 0)], &[]);
        let arrays = extract(&terms, &bits, &[assertion]);

        match expected {
            Some(value) => assert_eq!(cell(&arrays, z, "#x9"), value, "{op}"),
            // Unresolved: nothing is published for z, whose stale cached
            // bits must not become its cells either.
            None => assert!(!arrays.array_values.contains_key(&z), "{op}"),
        }
    }
}

/// `(or (and guard (= c (store (const #x00) 1 #x05))) (= d ...))`; returns
/// `(assertion, c, d, c's definition)`.
fn guarded_definition(terms: &mut TermStore, guard: TermId) -> (TermId, TermId, TermId, TermId) {
    let c = terms.mk_var("c", array_of(32, Sort::bitvec(8)));
    let d = terms.mk_var("d", array_of(32, Sort::bitvec(8)));
    let zero = bv(terms, 0, 8);
    let five = bv(terms, 5, 8);
    let one = bv(terms, 1, 32);
    let two = bv(terms, 2, 32);
    let all_zero = terms.mk_const_array(Sort::bitvec(32), zero);
    let c_store = terms.mk_store(all_zero, one, five);
    let d_store = terms.mk_store(all_zero, two, five);
    let c_def = define(terms, c, c_store);
    let d_def = define(terms, d, d_store);
    let dead_arm = terms.mk_and(vec![guard, c_def]);
    (terms.mk_or(vec![dead_arm, d_def]), c, d, c_def)
}

#[test]
fn definition_under_a_false_conjunct_does_not_withhold() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(8));
    let seven = bv(&mut terms, 7, 8);
    let guard = terms.mk_bvuge(x, seven);
    let (assertion, c, d, _) = guarded_definition(&mut terms, guard);

    let arrays = extract(&terms, &model(&[(x, 1)], &[]), &[assertion]);

    assert!(
        !arrays.read_conflicted.contains(&c),
        "c's definition cannot matter"
    );
    assert!(!arrays.read_conflicted.contains(&d), "d's arm is forced");
    assert_eq!(cell(&arrays, d, "#x00000002"), "#x05");
}

#[test]
fn definition_whose_sibling_conjunct_is_open_is_not_adopted() {
    let mut terms = TermStore::new();
    let guard = terms.mk_var("g", Sort::Bool);
    let (assertion, c, _, c_def) = guarded_definition(&mut terms, guard);

    // An unassigned guard leaves the arm, and c's definition, able to hold,
    // whether the definition atom is unassigned or assigned true: the arm is
    // not forced, so the definition is not adopted.
    for bools in [vec![], vec![(c_def, true)]] {
        let arrays = extract(&terms, &model(&[], &bools), &[assertion]);
        assert!(!arrays.array_values.contains_key(&c), "{bools:?}");
        assert!(!arrays.read_conflicted.contains(&c), "{bools:?}");
    }
}

/// `(or (= z (const true)) (and q (= c (const false))))`: two live arms.
fn two_definition_arms(terms: &mut TermStore) -> (TermId, TermId, TermId, TermId) {
    let z = terms.mk_var("z", array_of(4, Sort::Bool));
    let c = terms.mk_var("c", array_of(4, Sort::Bool));
    let q = terms.mk_var("q", Sort::Bool);
    let tru = terms.mk_bool(true);
    let fls = terms.mk_bool(false);
    let all_true = terms.mk_const_array(Sort::bitvec(4), tru);
    let all_false = terms.mk_const_array(Sort::bitvec(4), fls);
    let z_def = define(terms, z, all_true);
    let c_def = define(terms, c, all_false);
    let arm = terms.mk_and(vec![q, c_def]);
    (terms.mk_or(vec![z_def, arm]), z, c, z_def)
}

#[test]
fn definition_the_assignment_set_false_does_not_withhold() {
    let mut terms = TermStore::new();
    let (assertion, z, c, z_def) = two_definition_arms(&mut terms);

    // The SAT assignment committed to z differing from (const true): nothing
    // relies on that definition's cells, and its arm is dead, so c's is
    // forced.
    let arrays = extract(&terms, &model(&[], &[(z_def, false)]), &[assertion]);

    assert!(!arrays.read_conflicted.contains(&z));
    assert!(!arrays.read_conflicted.contains(&c));
    assert_eq!(cell(&arrays, c, "#x5"), "false");
}

#[test]
fn definition_the_assignment_leaves_open_or_true_is_not_adopted() {
    for bools in [vec![], vec![true]] {
        let mut terms = TermStore::new();
        let (assertion, z, _, z_def) = two_definition_arms(&mut terms);
        let assigned: Vec<(TermId, bool)> = bools.iter().map(|&value| (z_def, value)).collect();
        let arrays = extract(&terms, &model(&[], &assigned), &[assertion]);
        assert!(!arrays.array_values.contains_key(&z), "{assigned:?}");
        assert!(!arrays.read_conflicted.contains(&z), "{assigned:?}");
    }
}

pub(super) fn memory() -> Sort {
    array_of(64, array_of(64, Sort::bitvec(8)))
}

pub(super) const ROW: &str = "(Array (_ BitVec 64) (_ BitVec 8))";

#[test]
fn nested_const_array_definition_renders_its_inner_array() {
    let mut terms = TermStore::new();
    let m = terms.mk_var("m", memory());
    let byte = bv(&mut terms, 0x2a, 8);
    let row = terms.mk_const_array(Sort::bitvec(64), byte);
    let all_rows = terms.mk_const_array(Sort::bitvec(64), row);
    let m_def = define(&mut terms, m, all_rows);
    let (assertion, p) = forced(&mut terms, m_def);

    let arrays = extract(&terms, &model(&[(p, 1)], &[]), &[assertion]);

    assert!(!arrays.read_conflicted.contains(&m));
    assert_eq!(
        cell(&arrays, m, "#x0000000000000003"),
        format!("((as const {ROW}) #x2a)")
    );
}

#[test]
fn nested_store_definition_renders_each_inner_store_chain() {
    let mut terms = TermStore::new();
    let m = terms.mk_var("m", memory());
    let zero = bv(&mut terms, 0, 8);
    let seven = bv(&mut terms, 7, 8);
    let one = bv(&mut terms, 1, 64);
    let two = bv(&mut terms, 2, 64);
    let zero_row = terms.mk_const_array(Sort::bitvec(64), zero);
    let all_zero = terms.mk_const_array(Sort::bitvec(64), zero_row);
    let row = terms.mk_store(zero_row, two, seven);
    let rows = terms.mk_store(all_zero, one, row);
    let m_def = define(&mut terms, m, rows);
    let (assertion, p) = forced(&mut terms, m_def);

    let arrays = extract(&terms, &model(&[(p, 1)], &[]), &[assertion]);

    assert!(!arrays.read_conflicted.contains(&m));
    assert_eq!(
        cell(&arrays, m, "#x0000000000000001"),
        format!("(store ((as const {ROW}) #x00) #x0000000000000002 #x07)")
    );
    assert_eq!(
        cell(&arrays, m, "#x0000000000000005"),
        format!("((as const {ROW}) #x00)")
    );
}

#[test]
fn free_array_of_arrays_base_gets_no_default() {
    let mut terms = TermStore::new();
    let m = terms.mk_var("m", memory());
    // No read reaches m0, so the nested select scan gives it no entry, and a
    // missing entry still invents no default for an array of arrays.
    let m0 = terms.mk_var("m0", memory());
    let zero = bv(&mut terms, 0, 8);
    let one = bv(&mut terms, 1, 64);
    let zero_row = terms.mk_const_array(Sort::bitvec(64), zero);
    let rows = terms.mk_store(m0, one, zero_row);
    let m_def = define(&mut terms, m, rows);
    let (assertion, p) = forced(&mut terms, m_def);

    let arrays = extract(&terms, &model(&[(p, 1)], &[]), &[assertion]);

    assert!(arrays.read_conflicted.contains(&m));
    assert!(!arrays.array_values.contains_key(&m0));
}

/// An array of arrays no read reaches has no select-derived interpretation,
/// and its definition under a false conjunct invents none: `n` is published
/// with no value at all. That used to need withholding, because an assertion
/// over `n` then evaluated to Unknown with no withheld array left to fail it
/// closed; since #bv-array-delegation an Unknown array assertion is never
/// counted verified (`model/tests/bv_array_delegation.rs`), so `n` is not
/// withheld (`live_definitions.rs`).
#[test]
fn array_of_arrays_definition_under_a_false_conjunct_publishes_nothing() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(8));
    let seven = bv(&mut terms, 7, 8);
    let guard = terms.mk_bvuge(x, seven);
    let n = terms.mk_var("n", memory());
    let n0 = terms.mk_var("n0", memory());
    let one = bv(&mut terms, 1, 64);
    let zero = bv(&mut terms, 0, 8);
    let zero_row = terms.mk_const_array(Sort::bitvec(64), zero);
    let rows = terms.mk_store(n0, one, zero_row);
    let n_def = define(&mut terms, n, rows);
    let dead_arm = terms.mk_and(vec![guard, n_def]);
    let q = terms.mk_var("q", Sort::Bool);
    let assertion = terms.mk_or(vec![dead_arm, q]);

    let arrays = extract(&terms, &model(&[(x, 1)], &[(q, true)]), &[assertion]);

    assert!(!arrays.array_values.contains_key(&n));
    assert!(!arrays.read_conflicted.contains(&n));
}
