// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Strict-mode tests for the n-ary array schemas `ArrayStorePermutation` and
//! `ArrayRowChain`.
//!
//! These are the schemas that let QF_AX `storecomm` / `read5` UNSAT proofs stop
//! emitting `:rule trust`. Because a WRONG UNSAT is total failure, every
//! positive test is paired with a negative test that breaks exactly one side
//! condition and asserts the checker REJECTS.

use crate::checker::*;
use ay_core::{
    ArraySort, Proof, ProofId, ProofStep, Sort, Symbol, TermId, TermStore, TheoryLemmaKind,
};

/// Validate a `TheoryLemma` step in strict mode.
fn validate_strict(
    terms: &TermStore,
    clause: Vec<TermId>,
    kind: TheoryLemmaKind,
) -> Result<(), ProofCheckError> {
    let step = ProofStep::TheoryLemma {
        theory: "arrays".to_string(),
        clause,
        farkas: None,
        kind,
        lia: None,
    };
    let mut derived = Vec::new();
    validate_step(terms, &mut derived, ProofId(0), &step, true, None)
}

/// `(Array Int Int)`.
fn array_sort() -> Sort {
    Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int)))
}

fn store(terms: &mut TermStore, array: TermId, index: TermId, value: TermId) -> TermId {
    let sort = terms.sort(array).clone();
    terms.mk_app(Symbol::named("store"), vec![array, index, value], sort)
}

fn select(terms: &mut TermStore, array: TermId, index: TermId) -> TermId {
    terms.mk_app(Symbol::named("select"), vec![array, index], Sort::Int)
}

fn eq(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), vec![lhs, rhs], Sort::Bool)
}

/// Base array `a` plus indices `i0..` and values `v0..`.
struct Fixture {
    terms: TermStore,
    a: TermId,
    idx: Vec<TermId>,
    val: Vec<TermId>,
}

impl Fixture {
    fn new(n: usize) -> Self {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", array_sort());
        let idx = (0..n)
            .map(|k| terms.mk_var(format!("i{k}"), Sort::Int))
            .collect();
        let val = (0..n)
            .map(|k| terms.mk_var(format!("v{k}"), Sort::Int))
            .collect();
        Self { terms, a, idx, val }
    }

    /// `store(... store(base, idx[order[0]], val[order[0]]) ..., idx[last], val[last])`
    /// — `order` lists the writes innermost-first.
    fn chain(&mut self, base: TermId, order: &[usize]) -> TermId {
        let mut current = base;
        for &k in order {
            current = store(&mut self.terms, current, self.idx[k], self.val[k]);
        }
        current
    }

    /// Every `(= i_p i_q)` literal for `p < q` over the first `n` indices.
    fn all_index_eqs(&mut self, n: usize) -> Vec<TermId> {
        let mut out = Vec::new();
        for p in 0..n {
            for q in (p + 1)..n {
                let (ip, iq) = (self.idx[p], self.idx[q]);
                out.push(eq(&mut self.terms, ip, iq));
            }
        }
        out
    }
}

mod row_chain_guards_and_metering;
mod row_chain_reads;
mod row_chain_stores;
mod same_index_store_value;
mod store_permutation;
mod store_permutation_read_through;

// The constant-index skip is a sub-schema of `ArrayRowChain`, so its battery
// lives with the rest of the chain tests. It is registered here rather than in
// `checker/tests.rs` because that file is pinned at its exact length by the
// quality gate's file-size baseline.
#[path = "array_chain_const_index_tests.rs"]
mod array_chain_const_index_tests;
