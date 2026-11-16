// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Full-producer FC controls for distinct term IDs with equal index bits.

#![cfg(test)]

use super::*;
use ay_core::TermStore;

#[derive(Clone, Copy)]
enum Indices {
    Equal,
    Distinct,
    Symbolic,
}

impl Indices {
    fn make(self, terms: &mut TermStore) -> [TermId; 2] {
        match self {
            Self::Equal => {
                let zero = terms.mk_bitvec(BigInt::from(0), 2);
                let alias = terms.mk_app(Symbol::named("bvadd"), [zero, zero], Sort::bitvec(2));
                assert_ne!(zero, alias, "raw syntax must survive");
                [zero, alias]
            }
            Self::Distinct => [
                terms.mk_bitvec(BigInt::from(0), 2),
                terms.mk_bitvec(BigInt::from(1), 2),
            ],
            Self::Symbolic => [
                terms.mk_var("index-left", Sort::bitvec(2)),
                terms.mk_var("index-right", Sort::bitvec(2)),
            ],
        }
    }

    fn admits(self, left: u64, right: u64) -> bool {
        match self {
            Self::Equal => left == 0 && right == 0,
            Self::Distinct => left == 0 && right == 1,
            Self::Symbolic => true,
        }
    }
}

fn scalar(element: Sort, kind: Indices) {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let boolean = element == Sort::Bool;
    let array = terms.mk_var("array", Sort::array(Sort::bitvec(2), element));
    let [i, j] = kind.make(terms);
    let left = terms.mk_select(array, i);
    let right = terms.mk_select(array, j);
    let roots = [left, right];
    let atoms = if boolean { roots.as_slice() } else { &[] };
    let bv = materialize(&executor, &roots, None, atoms);
    let cnf = Circuit::new(
        &executor,
        &bv,
        &roots,
        None,
        &[i, j, left, right],
        &BTreeMap::new(),
    );
    cnf.check_relation(|v| kind.admits(v[0], v[1]) && (v[0] != v[1] || v[2] == v[3]));
    match kind {
        Indices::Equal => {
            for index in [i, j] {
                assert!(bv
                    .get_term_bits(index)
                    .unwrap()
                    .iter()
                    .all(|&bit| bv.bit_constant_value(bit) == Some(false)));
            }
            assert_eq!(cnf.num_vars, bv.num_vars() + 1);
            assert_eq!(cnf.axioms.len(), 3);
            assert_eq!(cnf.axioms[0].0, vec![(bv.num_vars() + 1) as i32]);
        }
        Indices::Distinct => {
            assert_eq!(cnf.axioms, [] as [ay_core::CnfClause; 0]);
            assert_eq!(cnf.num_vars, bv.num_vars());
        }
        Indices::Symbolic => {
            assert_eq!(cnf.num_vars, bv.num_vars() + 3);
            assert_eq!(cnf.axioms.len(), 13);
        }
    }
}

#[test]
fn scalar_bv_fc_enforces_equal_constant_aliases_and_preserves_other_index_cases() {
    for kind in [Indices::Equal, Indices::Distinct, Indices::Symbolic] {
        scalar(Sort::bitvec(1), kind);
    }
}

#[test]
fn scalar_bool_fc_enforces_equal_constant_aliases_and_preserves_other_index_cases() {
    for kind in [Indices::Equal, Indices::Distinct, Indices::Symbolic] {
        scalar(Sort::Bool, kind);
    }
}

#[test]
fn equal_index_bool_fc_preserves_signed_incremental_mapping_and_final_offset() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let array = terms.mk_var("array", Sort::array(Sort::bitvec(2), Sort::Bool));
    let [i, j] = Indices::Equal.make(terms);
    let left = terms.mk_select(array, i);
    let right = terms.mk_select(array, j);
    let variable = terms.mk_var("representation", Sort::Bool);
    let negated = terms.mk_not_raw(variable);
    let roots = [left, right];
    let mut bv = materialize(&executor, &roots, None, &[variable, right]);
    let literal = bv.ensure_bool_literal(negated).unwrap();
    assert!(literal < 0);
    // The existing incremental cache hook can represent an opaque read by
    // either polarity of a fresh variable. Reuse a real encoded Not literal;
    // this is a representation fixture, not a claimed source equality.
    let mut mapping = bv.bool_to_var().clone();
    mapping.insert(left, literal);
    bv.set_bool_to_var(mapping);
    let cnf = Circuit::with_offset(
        &executor,
        &bv,
        &roots,
        None,
        &[variable, left, right],
        &BTreeMap::new(),
        3,
    );
    cnf.check_relation(|v| v[1] == 1 - v[0] && v[1] == v[2]);
    assert_eq!(cnf.axioms.len(), 3);
    assert_eq!(cnf.axioms[0].0, vec![(3 + bv.num_vars() + 1) as i32]);
}

#[test]
fn known_equal_outer_indices_propagate_fc_to_existing_nested_array_reads() {
    for inner_kind in [Indices::Equal, Indices::Distinct, Indices::Symbolic] {
        let mut executor = Executor::new();
        let terms = &mut executor.ctx.terms;
        let inner_sort = Sort::array(Sort::bitvec(2), Sort::bitvec(1));
        let array = terms.mk_var("nested", Sort::array(Sort::bitvec(2), inner_sort));
        let [outer_i, outer_j] = Indices::Equal.make(terms);
        let left_array = terms.mk_select(array, outer_i);
        let right_array = terms.mk_select(array, outer_j);
        let [i, j] = inner_kind.make(terms);
        let left = terms.mk_select(left_array, i);
        let right = terms.mk_select(right_array, j);
        let roots = [left, right];
        let bv = materialize(&executor, &roots, None, &[]);
        assert!(bv.get_term_bits(left_array).is_none());
        assert!(bv.get_term_bits(right_array).is_none());
        let cnf = Circuit::new(
            &executor,
            &bv,
            &roots,
            None,
            &[i, j, left, right],
            &BTreeMap::new(),
        );
        cnf.check_relation(|v| inner_kind.admits(v[0], v[1]) && (v[0] != v[1] || v[2] == v[3]));
        assert_eq!(cnf.axioms[0].0, vec![(bv.num_vars() + 1) as i32]);
        if matches!(inner_kind, Indices::Distinct) {
            assert_eq!(
                cnf.axioms.len(),
                1,
                "equal outer arrays impose no relation on different cells"
            );
        }
    }
}

#[test]
fn missing_or_incompatible_index_bits_still_refuse_to_emit_fc_constraints() {
    #[derive(Clone, Copy)]
    enum Bits {
        Missing,
        WrongWidth,
    }
    for kind in [Bits::Missing, Bits::WrongWidth] {
        let mut executor = Executor::new();
        let terms = &mut executor.ctx.terms;
        let array = terms.mk_var("array", Sort::array(Sort::bitvec(2), Sort::bitvec(1)));
        let [i, alias] = Indices::Equal.make(terms);
        let j = match kind {
            Bits::Missing => alias,
            Bits::WrongWidth => terms.mk_var("wrong-index-width", Sort::bitvec(1)),
        };
        // Raw live applications retain the deliberately mistyped index for
        // the defensive width check, without forged/stale handles.
        let left = terms.mk_select(array, i);
        let right = match kind {
            Bits::Missing => terms.mk_select(array, j),
            Bits::WrongWidth => raw_select(terms, array, j),
        };
        let roots = [left, right];
        let mut bv = BvSolver::new(&executor.ctx.terms);
        for term in [i, left, right] {
            assert!(bv.ensure_term_bits(term).is_some());
        }
        match kind {
            Bits::Missing => assert!(bv.get_term_bits(j).is_none()),
            Bits::WrongWidth => assert_eq!(bv.ensure_term_bits(j).unwrap().len(), 1),
        }
        let cnf = Circuit::new(&executor, &bv, &roots, None, &roots, &BTreeMap::new());
        assert_eq!(cnf.axioms, [] as [ay_core::CnfClause; 0]);
        assert_eq!(cnf.num_vars, bv.num_vars());
        cnf.check_relation(|_| true);
    }
}
