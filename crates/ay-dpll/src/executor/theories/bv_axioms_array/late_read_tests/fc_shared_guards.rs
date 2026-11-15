// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Full FC producer tests; complete small CNF projection or bounded counts,
//! never a SAT invocation.

#![cfg(test)]

use super::*;
use ay_core::{CnfClause, TermStore};

mod controls;

fn array_reads(
    terms: &mut TermStore,
    name: &str,
    indices: [TermId; 2],
    element: Sort,
) -> [TermId; 2] {
    let index = terms.sort(indices[0]).clone();
    let array = terms.mk_var(name, Sort::array(index, element));
    indices.map(|index| terms.mk_select(array, index))
}

fn encode<'a>(executor: &'a Executor, roots: &[TermId]) -> BvSolver<'a> {
    let booleans: Vec<_> = roots
        .iter()
        .copied()
        .filter(|&term| executor.ctx.terms.sort(term) == &Sort::Bool)
        .collect();
    materialize(executor, roots, None, &booleans)
}

struct Mixed {
    executor: Executor,
    roots: Vec<TermId>,
    observed: Vec<TermId>,
}

fn mixed() -> Mixed {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let i = terms.mk_var("i", Sort::bitvec(2));
    let j = terms.mk_var("j", Sort::bitvec(2));
    let first = array_reads(terms, "bv", [i, j], Sort::bitvec(1));
    let second = array_reads(terms, "bool-reversed", [j, i], Sort::Bool);
    let nested = array_reads(
        terms,
        "nested",
        [i, j],
        Sort::array(Sort::bitvec(1), Sort::bitvec(1)),
    );
    let zero = terms.mk_bitvec(BigInt::from(0), 1);
    let third = nested.map(|array| terms.mk_select(array, zero));
    let roots: Vec<_> = first.into_iter().chain(second).chain(third).collect();
    let observed = [i, j].into_iter().chain(roots.iter().copied()).collect();
    Mixed {
        executor,
        roots,
        observed,
    }
}

fn shared_relation(values: &[u64]) -> bool {
    values[0] != values[1] || values[2..].chunks_exact(2).all(|pair| pair[0] == pair[1])
}

#[test]
fn identical_and_reversed_pairs_share_a_guard_but_not_values_across_arrays() {
    let fixture = mixed();
    let bv = encode(&fixture.executor, &fixture.roots);
    let cnf = Circuit::new(
        &fixture.executor,
        &bv,
        &fixture.roots,
        None,
        &fixture.observed,
        &BTreeMap::new(),
    );
    cnf.check_relation(shared_relation);
    assert_eq!(cnf.num_vars, bv.num_vars() + 3);
    assert_eq!(cnf.axioms.len(), 17); // One 11-clause guard + three equalities.
}

#[test]
fn a_new_generator_invocation_regenerates_its_guard_at_the_current_offset() {
    let fixture = mixed();
    let bv = encode(&fixture.executor, &fixture.roots);
    let first = Circuit::new(
        &fixture.executor,
        &bv,
        &fixture.roots,
        None,
        &fixture.observed,
        &BTreeMap::new(),
    );
    for offset in [0, 2] {
        let repeated = Circuit::with_offset(
            &fixture.executor,
            &bv,
            &fixture.roots,
            None,
            &fixture.observed,
            &BTreeMap::new(),
            offset,
        );
        repeated.check_relation(shared_relation);
        assert_eq!(repeated.num_vars, first.num_vars + offset);
        let displaced: Vec<_> = first
            .axioms
            .iter()
            .map(|clause| {
                CnfClause::new(
                    clause
                        .0
                        .iter()
                        .map(|&bit| offset_bv_bit(bit, offset))
                        .collect(),
                )
            })
            .collect();
        assert_eq!(repeated.axioms, displaced);
    }
}

#[test]
fn distinct_exact_pairs_do_not_alias_even_when_they_share_an_endpoint() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let i = terms.mk_var("i", Sort::bitvec(1));
    let j = terms.mk_var("j", Sort::bitvec(1));
    let k = terms.mk_var("k", Sort::bitvec(1));
    let a = array_reads(terms, "a", [i, j], Sort::bitvec(1));
    let b = array_reads(terms, "b", [j, k], Sort::bitvec(1));
    let c = array_reads(terms, "c", [k, i], Sort::bitvec(1));
    let roots: Vec<_> = a.into_iter().chain(b).chain(c).collect();
    let observed: Vec<_> = [i, j, k].into_iter().chain(roots.iter().copied()).collect();
    let bv = encode(&executor, &roots);
    let cnf = Circuit::new(&executor, &bv, &roots, None, &observed, &BTreeMap::new());
    cnf.check_relation(|v| {
        (v[0] != v[1] || v[3] == v[4])
            && (v[1] != v[2] || v[5] == v[6])
            && (v[2] != v[0] || v[7] == v[8])
    });
    assert_eq!(cnf.num_vars, bv.num_vars() + 6);
    assert_eq!(cnf.axioms.len(), 24);
}

#[test]
fn known_equal_constant_guards_reuse_exact_pairs_not_merely_normalized_indices() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let zero = terms.mk_bitvec(BigInt::from(0), 2);
    let add = terms.mk_app(Symbol::named("bvadd"), [zero, zero], Sort::bitvec(2));
    let sub = terms.mk_app(Symbol::named("bvsub"), [zero, zero], Sort::bitvec(2));
    assert_ne!(zero, add);
    assert_ne!(add, sub);
    let a = array_reads(terms, "a", [zero, add], Sort::bitvec(1));
    let b = array_reads(terms, "b", [add, zero], Sort::bitvec(1));
    let c = array_reads(terms, "c", [zero, sub], Sort::Bool);
    let d = array_reads(terms, "d", [sub, zero], Sort::Bool);
    let roots: Vec<_> = a.into_iter().chain(b).chain(c).chain(d).collect();
    let bv = encode(&executor, &roots);
    let cnf = Circuit::new(&executor, &bv, &roots, None, &roots, &BTreeMap::new());
    cnf.check_relation(|v| v.chunks_exact(2).all(|pair| pair[0] == pair[1]));
    assert_eq!(cnf.num_vars, bv.num_vars() + 2);
    assert_eq!(cnf.axioms.len(), 10); // Two unit guards + four equalities.
    assert_eq!(
        cnf.axioms
            .iter()
            .filter(|clause| clause.0.len() == 1)
            .count(),
        2
    );
}

#[test]
fn wide_shared_guard_storage_scales_with_arrays_only_in_consequents() {
    for arrays in [1usize, 2, 8, 32] {
        let mut executor = Executor::new();
        let terms = &mut executor.ctx.terms;
        let i = terms.mk_var("i", Sort::bitvec(64));
        let j = terms.mk_var("j", Sort::bitvec(64));
        let mut roots = Vec::new();
        for array in 0..arrays {
            let indices = if array % 2 == 0 { [i, j] } else { [j, i] };
            roots.extend(array_reads(
                terms,
                &format!("array-{array}"),
                indices,
                Sort::bitvec(1),
            ));
        }
        let bv = encode(&executor, &roots);
        let generated = executor.generate_array_bv_axioms(
            &bv,
            0,
            bv.num_vars(),
            &roots,
            &BTreeMap::new(),
            None,
        );
        assert_eq!(generated.num_vars, 65);
        assert_eq!(generated.clauses.len(), 321 + 2 * arrays);
        assert_eq!(
            generated
                .clauses
                .iter()
                .map(|clause| clause.0.len())
                .sum::<usize>(),
            961 + 6 * arrays
        );
        // Deterministic counts only: no 64-bit truth-table enumeration/search.
    }
}
