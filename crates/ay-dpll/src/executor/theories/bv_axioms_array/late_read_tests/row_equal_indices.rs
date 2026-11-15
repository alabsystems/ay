// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[derive(Clone, Copy)]
enum Element {
    BitVector,
    NegatedBoolean,
}

fn check_equal_index_row(element: Element) {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let index_sort = Sort::bitvec(2);
    let value_sort = match element {
        Element::BitVector => Sort::bitvec(1),
        Element::NegatedBoolean => Sort::Bool,
    };
    let zero = terms.mk_bitvec(BigInt::from(0), 2);
    let alias = terms.mk_app(Symbol::named("bvadd"), [zero, zero], index_sort.clone());
    assert_ne!(zero, alias);
    let base = terms.mk_var("base", Sort::array(index_sort, value_sort.clone()));
    let source = terms.mk_var("source", value_sort);
    let value = match element {
        Element::BitVector => source,
        Element::NegatedBoolean => terms.mk_not_raw(source),
    };
    let stored = terms.mk_store(base, zero, value);
    // Normal select construction cannot equate an opaque add to zero here.
    let selected = terms.mk_select(stored, alias);
    assert_ne!(selected, value);
    let base_read = terms.mk_select(base, alias);
    let roots = [selected, base_read];
    let booleans = match element {
        Element::BitVector => vec![],
        Element::NegatedBoolean => vec![source, value, selected, base_read],
    };
    let bv = materialize(&executor, &roots, None, &booleans);
    for index in [zero, alias] {
        assert!(bv
            .get_term_bits(index)
            .unwrap()
            .iter()
            .all(|&bit| bv.bit_constant_value(bit) == Some(false)));
    }
    if matches!(element, Element::NegatedBoolean) {
        assert!(bv.bool_to_var()[&value] < 0);
    }
    let cnf = Circuit::with_offset(
        &executor,
        &bv,
        &roots,
        None,
        &[source, base_read, selected],
        &BTreeMap::new(),
        3,
    );
    assert_eq!(cnf.axioms.len(), 2);
    assert!(cnf.axioms.iter().all(|clause| clause.0.len() == 2));
    assert_eq!(cnf.num_vars, 3 + bv.num_vars());
    // The old base value is unconstrained: the store shadows it at this index.
    // Exact projection also requires every valid stored value to remain possible.
    cnf.check_relation(|v| {
        v[2] == match element {
            Element::BitVector => v[0],
            Element::NegatedBoolean => 1 - v[0],
        }
    });
}

#[test]
fn constant_bit_aliases_enforce_stored_bv_value_without_constraining_base_read() {
    check_equal_index_row(Element::BitVector);
}

#[test]
fn constant_bit_aliases_enforce_signed_boolean_value_at_nonzero_offset() {
    check_equal_index_row(Element::NegatedBoolean);
}
