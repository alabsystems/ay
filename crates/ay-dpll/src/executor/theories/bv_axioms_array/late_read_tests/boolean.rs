// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn signed_and_constant_boolean_defaults_survive_nonzero_final_cnf_offsets() {
    #[derive(Clone, Copy)]
    enum Default {
        Negated,
        False,
        True,
    }
    for kind in [Default::Negated, Default::False, Default::True] {
        let mut executor = Executor::new();
        let terms = &mut executor.ctx.terms;
        let i = terms.mk_var("i", Sort::bitvec(2));
        let j = terms.mk_var("j", Sort::bitvec(2));
        let source = terms.mk_var("source", Sort::Bool);
        let value = terms.mk_var("value", Sort::Bool);
        let default = match kind {
            Default::Negated => terms.mk_not_raw(source),
            Default::False => terms.false_term(),
            Default::True => terms.true_term(),
        };
        let base = terms.mk_const_array(Sort::bitvec(2), default);
        let store = terms.mk_store(base, i, value);
        let result = raw_select(terms, store, j);
        let mut roots = vec![result];
        let reads = executor.materialize_array_row2_read_terms(&mut roots);
        assert_eq!(reads.get(base, j), Some(default));
        let bv = materialize(&executor, &roots, Some(&reads), &[source, value, result]);
        let literal = bv.bool_to_var()[&default];
        if matches!(kind, Default::Negated) {
            assert!(literal < 0);
        }
        let observed = [i, j, source, value, result];
        let cnf = Circuit::with_offset(
            &executor,
            &bv,
            &roots,
            Some(&reads),
            &observed,
            &BTreeMap::new(),
            3,
        );
        assert!(cnf
            .axioms
            .iter()
            .flat_map(|clause| &clause.0)
            .any(|&bit| bit == offset_bv_bit(literal, 3)));
        cnf.check_relation(|v| {
            let default = match kind {
                Default::Negated => 1 - v[2],
                Default::False => 0,
                Default::True => 1,
            };
            v[4] == if v[0] == v[1] { v[3] } else { default }
        });
    }
}

#[test]
fn computed_boolean_default_uses_its_real_predicate_encoding() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let i = terms.mk_var("i", Sort::bitvec(2));
    let j = terms.mk_var("j", Sort::bitvec(2));
    let x = terms.mk_var("x", Sort::bitvec(1));
    let y = terms.mk_var("y", Sort::bitvec(1));
    let product = terms.mk_app(Symbol::named("bvmul"), [x, y], Sort::bitvec(1));
    let zero = terms.mk_bitvec(BigInt::from(0), 1);
    let default = terms.mk_app(Symbol::named("="), [product, zero], Sort::Bool);
    let value = terms.mk_var("value", Sort::Bool);
    let base = terms.mk_const_array(Sort::bitvec(2), default);
    let store = terms.mk_store(base, i, value);
    let result = raw_select(terms, store, j);
    let mut roots = vec![result];
    let reads = executor.materialize_array_row2_read_terms(&mut roots);
    assert_eq!(reads.get(base, j), Some(default));
    let bv = materialize(&executor, &roots, Some(&reads), &[result, value]);
    assert!(bv.bool_to_var().contains_key(&default));
    assert!(bv.get_term_bits(default).is_none());
    let observed = [i, j, x, y, value, result];
    let cnf = Circuit::new(
        &executor,
        &bv,
        &roots,
        Some(&reads),
        &observed,
        &BTreeMap::new(),
    );
    cnf.check_relation(|v| {
        v[5] == if v[0] == v[1] {
            v[4]
        } else {
            u64::from(v[2] * v[3] == 0)
        }
    });
    let omitted = Circuit::new(&executor, &bv, &roots, None, &observed, &BTreeMap::new());
    omitted.check_relation(|v| v[0] != v[1] || v[5] == v[4]);
}

#[test]
fn computed_bitvector_default_is_constrained_by_its_arithmetic_circuit() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let i = terms.mk_var("i", Sort::bitvec(2));
    let j = terms.mk_var("j", Sort::bitvec(2));
    let x = terms.mk_var("x", Sort::bitvec(1));
    let y = terms.mk_var("y", Sort::bitvec(1));
    let default = terms.mk_app(Symbol::named("bvmul"), [x, y], Sort::bitvec(1));
    let value = terms.mk_var("value", Sort::bitvec(1));
    let base = terms.mk_const_array(Sort::bitvec(2), default);
    let store = terms.mk_store(base, i, value);
    let result = raw_select(terms, store, j);
    let mut roots = vec![result];
    let reads = executor.materialize_array_row2_read_terms(&mut roots);
    assert_eq!(reads.get(base, j), Some(default));
    let bv = materialize(&executor, &roots, Some(&reads), &[]);
    let observed = [i, j, x, y, value, result];
    let cnf = Circuit::new(
        &executor,
        &bv,
        &roots,
        Some(&reads),
        &observed,
        &BTreeMap::new(),
    );
    cnf.check_relation(|v| v[5] == if v[0] == v[1] { v[4] } else { v[2] * v[3] });
}
