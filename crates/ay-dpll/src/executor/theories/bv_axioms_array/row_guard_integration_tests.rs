// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Full array-axiom producer tests. These materialize BV literals, but do not
//! invoke SAT search. They are separate from the std-only guard-emitter tests.

#![cfg(test)]

use super::*;
use ay_core::ArraySort;

#[derive(Clone, Copy)]
enum BaseRead {
    Exact,
    Normalized,
    Missing,
    Unblasted,
    WrongWidth,
}

enum Indices {
    Symbolic,
    Identical,
    EqualConstants,
    DistinctConstants,
}

struct Fixture {
    executor: Executor,
    roots: Vec<TermId>,
    materialized: Vec<TermId>,
    selected: TermId,
    value: TermId,
}

impl Fixture {
    fn new(base: BaseRead) -> Self {
        Self::with_indices(base, Indices::Symbolic)
    }

    fn with_indices(base: BaseRead, indices: Indices) -> Self {
        let mut executor = Executor::new();
        let terms = &mut executor.ctx.terms;
        let index_sort = Sort::bitvec(64);
        let value_sort = Sort::bitvec(8);
        let array = terms.mk_var(
            "a",
            Sort::Array(Box::new(ArraySort::new(
                index_sort.clone(),
                value_sort.clone(),
            ))),
        );
        let (i, j) = match indices {
            Indices::Symbolic => (
                terms.mk_var("i", index_sort.clone()),
                terms.mk_var("j", index_sort.clone()),
            ),
            Indices::Identical => {
                let index = terms.mk_var("i", index_sort.clone());
                (index, index)
            }
            Indices::EqualConstants => {
                let zero = terms.mk_bitvec(BigInt::from(0), 64);
                let alias = terms.mk_app(Symbol::named("bvadd"), [zero, zero], index_sort.clone());
                assert_ne!(
                    zero, alias,
                    "exercise equal bits, not the syntactic fast path"
                );
                (zero, alias)
            }
            Indices::DistinctConstants => (
                terms.mk_bitvec(BigInt::from(0), 64),
                terms.mk_bitvec(BigInt::from(1), 64),
            ),
        };
        let value = terms.mk_var("v", value_sort.clone());
        let store = terms.mk_store(array, i, value);
        // Preserve residual select/store syntax without invoking term-level
        // ROW expansion before the bit-level producer under test.
        let selected = terms.mk_app(Symbol::named("select"), [store, j], value_sort.clone());
        let mut roots = vec![selected];
        let mut materialized = vec![i, j, value, selected];
        if !matches!(base, BaseRead::Missing) {
            let index = if matches!(base, BaseRead::Normalized) {
                let zero = terms.mk_bitvec(BigInt::from(0), 64);
                terms.mk_app(Symbol::named("bvadd"), [j, zero], index_sort)
            } else {
                j
            };
            // The wrong-width case deliberately uses only live handles and
            // the existing raw app API to exercise the defensive bit-width gate.
            let sort = if matches!(base, BaseRead::WrongWidth) {
                Sort::bitvec(4)
            } else {
                value_sort
            };
            let read = terms.mk_app(Symbol::named("select"), [array, index], sort);
            roots.push(read);
            if !matches!(base, BaseRead::Unblasted) {
                materialized.extend([read, index]);
            }
        }
        Self {
            executor,
            roots,
            materialized,
            selected,
            value,
        }
    }

    fn generate(&self) -> (ArrayAxiomResult, u32, Vec<i32>, Vec<i32>) {
        let mut bv = BvSolver::new(&self.executor.ctx.terms);
        for &term in &self.materialized {
            assert!(bv.ensure_term_bits(term).is_some());
        }
        // Nonzero offset exercises final signed-CNF numbering too.
        let bv_offset = 7;
        let var_offset = bv_offset + bv.num_vars();
        let selected = bv
            .get_term_bits(self.selected)
            .unwrap()
            .iter()
            .map(|&bit| offset_bv_bit(bit, bv_offset))
            .collect();
        let value = bv
            .get_term_bits(self.value)
            .unwrap()
            .iter()
            .map(|&bit| offset_bv_bit(bit, bv_offset))
            .collect();
        let result = self.executor.generate_array_bv_axioms(
            &bv,
            bv_offset,
            var_offset,
            &self.roots,
            &BTreeMap::new(),
            None,
        );
        (result, var_offset, selected, value)
    }
}

#[test]
fn full_producer_reuses_admitted_row2_summary_without_new_variables_or_clauses() {
    let fixture = Fixture::new(BaseRead::Exact);
    let (result, offset, selected, value) = fixture.generate();
    assert_eq!(result.num_vars, 65);
    assert_eq!(result.clauses.len(), 353);
    assert_eq!(
        result
            .clauses
            .iter()
            .map(|clause| clause.0.len())
            .sum::<usize>(),
        1057
    );
    let eq_idx = (offset + 65) as i32;
    for (index, (&selected, &value)) in selected.iter().zip(&value).enumerate() {
        assert_eq!(
            result.clauses[256 + 2 * index].0,
            vec![-eq_idx, -selected, value]
        );
        assert_eq!(
            result.clauses[257 + 2 * index].0,
            vec![-eq_idx, selected, -value]
        );
    }
    assert_eq!(result.clauses[272].0, vec![-eq_idx, -((offset + 1) as i32)]);
}

#[test]
fn full_producer_normalized_base_index_still_admits_shared_guard() {
    let fixture = Fixture::new(BaseRead::Normalized);
    let (result, _, _, _) = fixture.generate();
    assert_eq!(result.num_vars, 65);
    assert_eq!(result.clauses.len(), 353);
    assert_eq!(
        result
            .clauses
            .iter()
            .map(|clause| clause.0.len())
            .sum::<usize>(),
        1057
    );
}

#[test]
fn full_producer_unavailable_or_incompatible_base_preserves_wide_row1_only() {
    for base in [BaseRead::Missing, BaseRead::Unblasted, BaseRead::WrongWidth] {
        let fixture = Fixture::new(base);
        let (result, offset, selected, value) = fixture.generate();
        assert_eq!(result.num_vars, 64);
        assert_eq!(result.clauses.len(), 272);
        assert_eq!(
            result
                .clauses
                .iter()
                .map(|clause| clause.0.len())
                .sum::<usize>(),
            1824
        );
        let differences: Vec<_> = ((offset + 1)..=(offset + 64))
            .map(|var| var as i32)
            .collect();
        for (index, (&selected, &value)) in selected.iter().zip(&value).enumerate() {
            let mut positive = differences.clone();
            positive.extend([-selected, value]);
            let mut negative = differences.clone();
            negative.extend([selected, -value]);
            assert_eq!(result.clauses[256 + 2 * index].0, positive);
            assert_eq!(result.clauses[257 + 2 * index].0, negative);
        }
    }
}

#[test]
fn full_producer_syntactically_identical_indices_keep_rewriter_fast_path() {
    let fixture = Fixture::with_indices(BaseRead::Exact, Indices::Identical);
    let (result, _, _, _) = fixture.generate();
    assert!(result.clauses.is_empty());
    assert_eq!(result.num_vars, 0);
}

#[test]
fn full_producer_known_equal_aliases_require_row1_without_any_row2_base() {
    for base in [
        BaseRead::Exact,
        BaseRead::Normalized,
        BaseRead::Missing,
        BaseRead::Unblasted,
        BaseRead::WrongWidth,
    ] {
        let fixture = Fixture::with_indices(base, Indices::EqualConstants);
        let (result, _, selected, value) = fixture.generate();
        assert_eq!(result.num_vars, 0);
        assert_eq!(result.clauses.len(), 16);
        for (index, (&selected, &value)) in selected.iter().zip(&value).enumerate() {
            assert_eq!(result.clauses[2 * index].0, vec![-selected, value]);
            assert_eq!(result.clauses[2 * index + 1].0, vec![selected, -value]);
        }
    }
}

#[test]
fn full_producer_known_different_constant_indices_keep_one_xor_and_summary() {
    let fixture = Fixture::with_indices(BaseRead::Exact, Indices::DistinctConstants);
    let (result, offset, _, _) = fixture.generate();
    // 63 equal constant bit positions are skipped. The remaining position
    // keeps its exact XOR definition; this optimization adds no pruning rule.
    assert_eq!(result.num_vars, 2);
    assert_eq!(result.clauses.len(), 38);
    assert_eq!(
        result
            .clauses
            .iter()
            .map(|clause| clause.0.len())
            .sum::<usize>(),
        112
    );
    assert_eq!(result.clauses[4].0[0], -((offset + 2) as i32));
}
