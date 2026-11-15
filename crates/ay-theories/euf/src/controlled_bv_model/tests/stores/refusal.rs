// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn malformed_store_arity_base_index_cell_and_result_sorts_refuse() {
    let end = Instant::now() + Duration::from_secs(20);
    for case in 0..6 {
        let mut terms = TermStore::new();
        let sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
        let base = terms.mk_var("base", sort.clone());
        let index = terms.mk_bitvec(1u8.into(), 64);
        let value = terms.mk_bitvec(2u8.into(), 8);
        let mut args = vec![base, index, value];
        let mut result = sort;
        match case {
            0 => {
                args.pop();
            }
            1 => args.push(value),
            2 => args[0] = value,
            3 => args[1] = value,
            4 => args[2] = index,
            _ => result = Sort::array(Sort::bitvec(64), Sort::bitvec(16)),
        }
        terms.mk_app(Symbol::named("store"), args, result);
        refuse_arena(&terms);
        assert!(Instant::now() < end);
    }
}

#[test]
fn store_dead_immediate_and_nested_children_refuse_before_indexing() {
    let end = Instant::now() + Duration::from_secs(20);
    for nested in [false, true] {
        let mut terms = TermStore::new();
        let sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
        let base = terms.mk_var("base", sort.clone());
        let index = terms.mk_bitvec(0u8.into(), 64);
        let child = if nested {
            terms.mk_app(
                Symbol::named("foreign"),
                [TermId(u32::MAX)],
                Sort::bitvec(8),
            )
        } else {
            TermId(u32::MAX)
        };
        terms.mk_app(Symbol::named("store"), [base, index, child], sort);
        refuse_arena(&terms);
        assert!(Instant::now() < end);
    }
}

#[test]
fn hidden_casts_arithmetic_and_foreign_values_are_not_store_admission() {
    let end = Instant::now() + Duration::from_secs(20);
    for symbol in [
        Symbol::indexed("extract", vec![7, 0]),
        Symbol::indexed("zero_extend", vec![0]),
        Symbol::named("bvadd"),
        Symbol::named("foreign"),
    ] {
        let mut terms = TermStore::new();
        let sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
        let base = terms.mk_var("base", sort.clone());
        let index = terms.mk_bitvec(0u8.into(), 64);
        let raw = terms.mk_var("raw", Sort::bitvec(8));
        let child = terms.mk_app(symbol, [raw], Sort::bitvec(8));
        terms.mk_app(Symbol::named("store"), [base, index, child], sort);
        let root = terms.mk_bool(false);
        let source = prepare(&terms, &[]);
        assert!(matches!(
            measured(&source, &[root], u64::MAX, usize::MAX).0,
            Err(QueryError::Exhausted)
        ));
        assert!(source.model_term_scope.is_none());
        assert!(Instant::now() < end);
    }
}

#[test]
fn indexed_store_spelling_is_not_the_named_builtin_constructor() {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::Bool, Sort::Bool);
    let base = terms.mk_var("base", sort.clone());
    let value = terms.mk_bool(false);
    terms.mk_app(
        Symbol::indexed("store", vec![0]),
        [base, value, value],
        sort,
    );
    refuse_arena(&terms);
}
