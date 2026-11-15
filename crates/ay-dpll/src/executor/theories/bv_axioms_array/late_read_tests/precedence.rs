// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[derive(Clone, Copy)]
enum Representative {
    Unblasted,
    WrongWidth,
}

#[derive(Clone, Copy)]
enum Index {
    Exact,
    Normalized,
}

#[test]
fn existing_raw_or_normalized_representatives_keep_precedence_over_folded_results() {
    for representative in [Representative::Unblasted, Representative::WrongWidth] {
        for index in [Index::Exact, Index::Normalized] {
            check_precedence(representative, index);
        }
    }
}

fn check_precedence(representative: Representative, index: Index) {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let i = terms.mk_var("i", Sort::bitvec(2));
    let j = terms.mk_var("j", Sort::bitvec(2));
    let value = terms.mk_var("value", Sort::bitvec(1));
    let default = terms.mk_bitvec(BigInt::from(0), 1);
    let base = terms.mk_const_array(Sort::bitvec(2), default);
    let store = terms.mk_store(base, i, value);
    let result = raw_select(terms, store, j);
    let raw_index = match index {
        Index::Exact => j,
        Index::Normalized => {
            let zero = terms.mk_bitvec(BigInt::from(0), 2);
            let alias = terms.mk_app(Symbol::named("bvadd"), [j, zero], Sort::bitvec(2));
            assert_ne!(alias, j);
            alias
        }
    };
    let width = match representative {
        Representative::Unblasted => 1,
        Representative::WrongWidth => 2,
    };
    // Live raw-app API deliberately supplies a wrong recorded width in one
    // family, like the existing None-carrier defensive-width regression.
    let raw = terms.mk_app(
        Symbol::named("select"),
        [base, raw_index],
        Sort::bitvec(width),
    );
    let mut roots = vec![result];
    let reads = executor.materialize_array_row2_read_terms(&mut roots);
    assert_eq!(reads.get(base, j), Some(default));
    let mut bv = materialize(&executor, &roots, Some(&reads), &[]);
    if matches!(representative, Representative::WrongWidth) {
        assert_eq!(bv.ensure_term_bits(raw).unwrap().len(), 2);
    } else {
        assert!(bv.get_term_bits(raw).is_none());
    }
    let observed = [i, j, value, result];
    let before = Circuit::new(
        &executor,
        &bv,
        &roots,
        Some(&reads),
        &observed,
        &BTreeMap::new(),
    );
    before.check_relation(|v| v[3] == if v[0] == v[1] { v[2] } else { 0 });
    // Expose the already-existing representative only after the allocation
    // phase. The axiom generator must not retry the folded fallback when the
    // preferred representative lacks bits or has incompatible bit width.
    roots.push(raw);
    let old = Circuit::new(&executor, &bv, &roots, None, &observed, &BTreeMap::new());
    let current = Circuit::new(
        &executor,
        &bv,
        &roots,
        Some(&reads),
        &observed,
        &BTreeMap::new(),
    );
    assert_eq!(old.axioms, current.axioms);
    assert_eq!(old.num_vars, current.num_vars);
    assert!(current.axioms.len() < before.axioms.len());
    current.check_relation(|v| v[0] != v[1] || v[3] == v[2]);
}
