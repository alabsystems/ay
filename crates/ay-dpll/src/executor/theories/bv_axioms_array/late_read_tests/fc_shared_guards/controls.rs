// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn functional_consistency_does_not_reuse_a_separate_row_guard() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let i = terms.mk_var("i", Sort::bitvec(2));
    let j = terms.mk_var("j", Sort::bitvec(2));
    let value = terms.mk_var("value", Sort::bitvec(1));
    let array = terms.mk_var("row-array", Sort::array(Sort::bitvec(2), Sort::bitvec(1)));
    let store = terms.mk_store(array, i, value);
    let result = terms.mk_select(store, j);
    let base_read = terms.mk_select(array, j);
    let fc = array_reads(terms, "fc-array", [i, j], Sort::bitvec(1));
    let roots = [result, base_read, fc[0], fc[1]];
    let observed = [i, j, value, result, base_read, fc[0], fc[1]];
    let bv = encode(&executor, &roots);
    let cnf = Circuit::new(&executor, &bv, &roots, None, &observed, &BTreeMap::new());
    cnf.check_relation(|v| {
        let row = v[3] == if v[0] == v[1] { v[2] } else { v[4] };
        row && (v[0] != v[1] || v[5] == v[6])
    });
    assert_eq!(cnf.num_vars, bv.num_vars() + 6);
    assert_eq!(cnf.axioms.len(), 28); // ROW15 + FC13, distinct guard scopes.
}

#[test]
fn missing_values_do_not_lose_a_complete_guard_needed_by_another_array() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let i = terms.mk_var("i", Sort::bitvec(2));
    let j = terms.mk_var("j", Sort::bitvec(2));
    let absent = array_reads(terms, "unblasted-values", [i, j], Sort::bitvec(1));
    let present = array_reads(terms, "present-values", [j, i], Sort::bitvec(1));
    let roots: Vec<_> = absent.into_iter().chain(present).collect();
    let mut bv = BvSolver::new(&executor.ctx.terms);
    for term in [i, j, present[0], present[1]] {
        assert!(bv.ensure_term_bits(term).is_some());
    }
    for term in absent {
        assert!(bv.get_term_bits(term).is_none());
    }
    let cnf = Circuit::new(
        &executor,
        &bv,
        &roots,
        None,
        &[i, j, present[0], present[1]],
        &BTreeMap::new(),
    );
    cnf.check_relation(|v| v[0] != v[1] || v[2] == v[3]);
    assert_eq!(cnf.num_vars, bv.num_vars() + 3);
    assert_eq!(cnf.axioms.len(), 13);
}

#[test]
fn missing_index_bits_do_not_seed_a_guard_or_poison_an_independent_pair() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let i = terms.mk_var("i", Sort::bitvec(1));
    let missing = terms.mk_var("missing-index", Sort::bitvec(1));
    let k = terms.mk_var("k", Sort::bitvec(1));
    let l = terms.mk_var("l", Sort::bitvec(1));
    let absent = array_reads(terms, "missing-index-array", [i, missing], Sort::bitvec(1));
    let present = array_reads(terms, "present-index-array", [k, l], Sort::bitvec(1));
    let roots: Vec<_> = absent.into_iter().chain(present).collect();
    let mut bv = BvSolver::new(&executor.ctx.terms);
    for term in [i, k, l].into_iter().chain(roots.iter().copied()) {
        assert!(bv.ensure_term_bits(term).is_some());
    }
    assert!(bv.get_term_bits(missing).is_none());
    let observed: Vec<_> = [k, l].into_iter().chain(roots.iter().copied()).collect();
    let cnf = Circuit::new(&executor, &bv, &roots, None, &observed, &BTreeMap::new());
    cnf.check_relation(|v| v[0] != v[1] || v[4] == v[5]);
    assert_eq!(cnf.num_vars, bv.num_vars() + 2);
    assert_eq!(cnf.axioms.len(), 8);
}

#[test]
fn repeated_known_distinct_pairs_stay_pruned_before_shared_guard_allocation() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let zero = terms.mk_bitvec(BigInt::from(0), 1);
    let one = terms.mk_bitvec(BigInt::from(1), 1);
    let i = terms.mk_var("i", Sort::bitvec(1));
    let j = terms.mk_var("j", Sort::bitvec(1));
    let a = array_reads(terms, "pruned-a", [zero, one], Sort::bitvec(1));
    let b = array_reads(terms, "pruned-b", [one, zero], Sort::Bool);
    let c = array_reads(terms, "live-c", [i, j], Sort::bitvec(1));
    let roots: Vec<_> = a.into_iter().chain(b).chain(c).collect();
    let observed: Vec<_> = [i, j].into_iter().chain(roots.iter().copied()).collect();
    let bv = encode(&executor, &roots);
    let cnf = Circuit::new(&executor, &bv, &roots, None, &observed, &BTreeMap::new());
    cnf.check_relation(|v| v[0] != v[1] || v[6] == v[7]);
    assert_eq!(cnf.num_vars, bv.num_vars() + 2);
    assert_eq!(cnf.axioms.len(), 8);
}
