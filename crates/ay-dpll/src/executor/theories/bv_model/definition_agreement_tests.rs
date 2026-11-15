// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A built definition is published only while it agrees with what the model
//! publishes for what it read (`definition_order.rs`):
//!
//! * two definitions of one variable that build different arrays withhold it;
//!   two that agree lift it, also with different defaults over a fully stored
//!   domain;
//! * a definition reading its own variable is published only as a fixpoint,
//!   and, asserted unconditionally, builds the model's `(default w)` over a
//!   base without a `(default u)` value of its own (`model_defaults_tests.rs`
//!   has the base whose own value disputes it);
//! * a definition over an array published after it (a cycle) is withheld.
//!
//! Also the acceptance paths of `definition_operands.rs`, `nested_cells.rs`
//! and `live_definitions.rs` that `definition_completeness_tests.rs` does not
//! reach: a definition in an untaken `ite` branch, a Bool-sorted uninterpreted
//! operand, and a nested read copied as a whole row.

use super::tests::{array_of, bv, cell, define, extract, forced, memory, model, ROW};
use super::*;
use ay_core::term::Symbol;

/// `(and (= w first) (= w second))` in a forced arm over `(Array BV4 BV8)`.
fn two_definitions(
    terms: &mut TermStore,
    first: TermId,
    second: TermId,
) -> (TermId, TermId, TermId) {
    let w = terms.mk_var("w", array_of(4, Sort::bitvec(8)));
    let first_def = define(terms, w, first);
    let second_def = define(terms, w, second);
    let arm = terms.mk_and(vec![first_def, second_def]);
    let (assertion, p) = forced(terms, arm);
    (assertion, p, w)
}

#[test]
fn two_disagreeing_definitions_withhold_their_variable() {
    let mut terms = TermStore::new();
    let five = bv(&mut terms, 5, 8);
    let zero = bv(&mut terms, 0, 8);
    let one = bv(&mut terms, 1, 4);
    let all_five = terms.mk_const_array(Sort::bitvec(4), five);
    let all_zero = terms.mk_const_array(Sort::bitvec(4), zero);
    let five_at_one = terms.mk_store(all_zero, one, five);
    let (assertion, p, w) = two_definitions(&mut terms, all_five, five_at_one);

    let arrays = extract(&terms, &model(&[(p, 1)], &[]), &[assertion]);

    assert!(
        arrays.read_conflicted.contains(&w),
        "no published interpretation satisfies both definitions"
    );
}

#[test]
fn two_agreeing_definitions_lift_their_variable() {
    let mut terms = TermStore::new();
    let five = bv(&mut terms, 5, 8);
    let one = bv(&mut terms, 1, 4);
    let all_five = terms.mk_const_array(Sort::bitvec(4), five);
    // Storing the default at #x1 denotes the same array.
    let same = terms.mk_store(all_five, one, five);
    let (assertion, p, w) = two_definitions(&mut terms, all_five, same);

    let arrays = extract(&terms, &model(&[(p, 1)], &[]), &[assertion]);

    assert!(!arrays.read_conflicted.contains(&w));
    assert_eq!(cell(&arrays, w, "#x1"), "#x05");
}

/// Over `(Array BV1 BV8)`, `(store (store (const #x00) #b0 #x05) #b1 #x05)`
/// and `(const #x05)` agree on both cells but not on their default: the same
/// array, whether the stored definition is asserted at the top level or not.
#[test]
fn fully_stored_definitions_with_different_defaults_agree() {
    for unconditional in [false, true] {
        let mut terms = TermStore::new();
        let w = terms.mk_var("w", array_of(1, Sort::bitvec(8)));
        let five = bv(&mut terms, 5, 8);
        let zero = bv(&mut terms, 0, 8);
        let low = bv(&mut terms, 0, 1);
        let high = bv(&mut terms, 1, 1);
        let all_zero = terms.mk_const_array(Sort::bitvec(1), zero);
        let all_five = terms.mk_const_array(Sort::bitvec(1), five);
        let low_five = terms.mk_store(all_zero, low, five);
        let stored = terms.mk_store(low_five, high, five);
        let stored_def = define(&mut terms, w, stored);
        let const_def = define(&mut terms, w, all_five);
        let (assertions, p) = if unconditional {
            let (forced_const, p) = forced(&mut terms, const_def);
            (vec![stored_def, forced_const], p)
        } else {
            let arm = terms.mk_and(vec![stored_def, const_def]);
            let (forced_both, p) = forced(&mut terms, arm);
            (vec![forced_both], p)
        };

        let arrays = extract(&terms, &model(&[(p, 1)], &[]), &assertions);

        assert!(!arrays.read_conflicted.contains(&w), "{unconditional}");
        assert_eq!(cell(&arrays, w, "#b0"), "#x05");
        assert_eq!(cell(&arrays, w, "#b1"), "#x05");
    }
}

/// The top-level `w := (store b #xa (select w y))`, `y = 3`, with the select
/// scan giving `w[3] = 5`. The new `w` reads `b`'s `#x3` back where the
/// definition read `w`'s own `#x3`, so it is published only when the two
/// agree: over `b = (const c)`, only for `c = 5`. Over a variable base `u`,
/// the read `w[3] = 5` reaches `u` by read-over-write (`read_pins.rs`) and
/// outranks the scan's unlinked `u[3]`, so `w` is published as a fixpoint of
/// the published `u` whatever `u[3]` the scan gave. (Under a forced arm `w`
/// starts withheld, so its own read refuses and the definition cannot build.)
#[test]
fn self_reading_definition_is_published_only_as_a_fixpoint() {
    for (base_at_three, lifted) in [(5u64, true), (1, false)] {
        let mut terms = TermStore::new();
        let w = terms.mk_var("w", array_of(4, Sort::bitvec(8)));
        let y = terms.mk_var("y", Sort::bitvec(4));
        let ten = bv(&mut terms, 10, 4);
        let base_value = bv(&mut terms, base_at_three, 8);
        let base = terms.mk_const_array(Sort::bitvec(4), base_value);
        let w_at_y = terms.mk_select(w, y);
        let store = terms.mk_store(base, ten, w_at_y);
        let w_def = define(&mut terms, w, store);

        let bits = model(&[(y, 3), (w_at_y, 5)], &[]);
        let arrays = extract(&terms, &bits, &[w_def]);

        assert_eq!(
            !arrays.read_conflicted.contains(&w),
            lifted,
            "b[3] = {base_at_three}"
        );
        if lifted {
            assert_eq!(cell(&arrays, w, "#x3"), "#x05");
            assert_eq!(cell(&arrays, w, "#xa"), "#x05");
        }
    }
    for u_at_three in [5u64, 1] {
        let mut terms = TermStore::new();
        let w = terms.mk_var("w", array_of(4, Sort::bitvec(8)));
        let u = terms.mk_var("u", array_of(4, Sort::bitvec(8)));
        let y = terms.mk_var("y", Sort::bitvec(4));
        let ten = bv(&mut terms, 10, 4);
        let w_at_y = terms.mk_select(w, y);
        let u_at_y = terms.mk_select(u, y);
        let store = terms.mk_store(u, ten, w_at_y);
        let w_def = define(&mut terms, w, store);

        let bits = model(&[(y, 3), (w_at_y, 5), (u_at_y, u_at_three)], &[]);
        let arrays = extract(&terms, &bits, &[w_def]);

        assert!(!arrays.read_conflicted.contains(&w), "u[3] = {u_at_three}");
        assert_eq!(cell(&arrays, u, "#x3"), "#x05", "u[3] = {u_at_three}");
        assert_eq!(cell(&arrays, w, "#x3"), "#x05");
        assert_eq!(cell(&arrays, w, "#xa"), "#x05");
    }
}

/// The same top-level self-read with `u[3] = w[3] = 5`, and a `(default w)`
/// term. `u` has no `(default u)` value, so it takes `(default w)`'s as its
/// else-value and the built default is the model's: the definition publishes
/// whatever that value is. (While `u` kept the select scan's `#x00`, a model
/// value `#x05` disputed it and withheld `w`, the self-read class.)
#[test]
fn self_reading_unconditional_definition_builds_the_models_default() {
    for (default_value, lifted) in [(None, true), (Some(0u64), true), (Some(5), true)] {
        let mut terms = TermStore::new();
        let w = terms.mk_var("w", array_of(4, Sort::bitvec(8)));
        let u = terms.mk_var("u", array_of(4, Sort::bitvec(8)));
        let y = terms.mk_var("y", Sort::bitvec(4));
        let ten = bv(&mut terms, 10, 4);
        let w_at_y = terms.mk_select(w, y);
        let u_at_y = terms.mk_select(u, y);
        let store = terms.mk_store(u, ten, w_at_y);
        let w_def = define(&mut terms, w, store);
        let default_w = terms.mk_array_default(w);

        let mut values = vec![(y, 3), (w_at_y, 5), (u_at_y, 5)];
        values.extend(default_value.map(|value| (default_w, value)));
        let arrays = extract(&terms, &model(&values, &[]), &[w_def]);

        assert_eq!(
            !arrays.read_conflicted.contains(&w),
            lifted,
            "(default w) = {default_value:?}"
        );
        let else_value = format!("#x{:02x}", default_value.unwrap_or(0));
        assert_eq!(cell(&arrays, w, "#x7"), else_value);
        assert_eq!(cell(&arrays, u, "#x7"), else_value);
    }
}

/// The top-level `(= v (store w #x1 #x05))` and `(= w (store v #x2 #x06))`: a
/// dependency cycle, built in source order, so `w` is published after `v` read
/// it. (Under a forced arm both start withheld and neither could build.) `w`
/// itself read the `v` that was published, now withheld, which keeps the
/// read-conflict oracle armed for every assertion over either.
#[test]
fn definition_over_an_array_published_after_it_is_withheld() {
    let mut terms = TermStore::new();
    let v = terms.mk_var("v", array_of(4, Sort::bitvec(8)));
    let w = terms.mk_var("w", array_of(4, Sort::bitvec(8)));
    let one = bv(&mut terms, 1, 4);
    let two = bv(&mut terms, 2, 4);
    let five = bv(&mut terms, 5, 8);
    let six = bv(&mut terms, 6, 8);
    let v_store = terms.mk_store(w, one, five);
    let w_store = terms.mk_store(v, two, six);
    let v_def = define(&mut terms, v, v_store);
    let w_def = define(&mut terms, w, w_store);

    let arrays = extract(&terms, &model(&[], &[]), &[v_def, w_def]);

    assert!(
        arrays.read_conflicted.contains(&v),
        "v was built from a w the model no longer publishes"
    );
}

/// A definition in an `ite` branch the model does not force, untaken
/// (`x = 1`) or undecided, is not adopted and does not withhold `c`
/// (`live_definitions.rs`).
#[test]
fn definition_in_an_unforced_ite_branch_is_not_adopted() {
    for assigned in [Some(1u64), None] {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::bitvec(8));
        let seven = bv(&mut terms, 7, 8);
        let cond = terms.mk_bvuge(x, seven);
        let c = terms.mk_var("c", array_of(32, Sort::bitvec(8)));
        let zero = bv(&mut terms, 0, 8);
        let five = bv(&mut terms, 5, 8);
        let one = bv(&mut terms, 1, 32);
        let all_zero = terms.mk_const_array(Sort::bitvec(32), zero);
        let c_store = terms.mk_store(all_zero, one, five);
        let c_def = define(&mut terms, c, c_store);
        let other = terms.mk_bvult(x, seven);
        let assertion = terms.mk_ite_raw(cond, c_def, other);
        let values: Vec<(TermId, u64)> = assigned.map(|v| vec![(x, v)]).unwrap_or_default();
        let arrays = extract(&terms, &model(&values, &[]), &[assertion]);
        assert!(!arrays.array_values.contains_key(&c), "{assigned:?}");
        assert!(!arrays.read_conflicted.contains(&c), "{assigned:?}");
    }
}

#[test]
fn bool_uninterpreted_application_operand_resolves_to_its_own_assignment() {
    for assigned in [true, false] {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::bitvec(8));
        let f_x = terms.mk_app(Symbol::named("f"), vec![x], Sort::Bool);
        let z = terms.mk_var("z", array_of(4, Sort::Bool));
        let all_f = terms.mk_const_array(Sort::bitvec(4), f_x);
        let z_def = define(&mut terms, z, all_f);
        let (assertion, p) = forced(&mut terms, z_def);
        let bools = if assigned { vec![(f_x, true)] } else { vec![] };
        let arrays = extract(&terms, &model(&[(p, 1), (x, 3)], &bools), &[assertion]);
        if assigned {
            assert!(!arrays.read_conflicted.contains(&z));
            assert_eq!(cell(&arrays, z, "#x9"), "true");
        } else {
            assert!(
                !arrays.array_values.contains_key(&z),
                "no value for (f x): z's definition publishes nothing"
            );
        }
    }
}

#[test]
fn nested_read_operand_copies_the_read_row() {
    for m0_defined in [true, false] {
        let mut terms = TermStore::new();
        let m = terms.mk_var("m", memory());
        let m0 = terms.mk_var("m0", memory());
        let byte = bv(&mut terms, 0x2a, 8);
        let zero = bv(&mut terms, 0, 8);
        let one = bv(&mut terms, 1, 64);
        let two = bv(&mut terms, 2, 64);
        let row = terms.mk_const_array(Sort::bitvec(64), byte);
        let zero_row = terms.mk_const_array(Sort::bitvec(64), zero);
        let all_rows = terms.mk_const_array(Sort::bitvec(64), row);
        let all_zero_rows = terms.mk_const_array(Sort::bitvec(64), zero_row);
        let read = terms.mk_select(m0, two);
        let rows = terms.mk_store(all_zero_rows, one, read);
        let m_def = define(&mut terms, m, rows);
        let arm = if m0_defined {
            let m0_def = define(&mut terms, m0, all_rows);
            terms.mk_and(vec![m_def, m0_def])
        } else {
            m_def
        };
        let (assertion, p) = forced(&mut terms, arm);
        let arrays = extract(&terms, &model(&[(p, 1)], &[]), &[assertion]);
        if m0_defined {
            assert!(!arrays.read_conflicted.contains(&m));
            assert_eq!(
                cell(&arrays, m, "#x0000000000000001"),
                format!("((as const {ROW}) #x2a)")
            );
        } else {
            assert!(
                arrays.read_conflicted.contains(&m),
                "m0 free: no row to copy"
            );
        }
    }
}
