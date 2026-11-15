// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::original_query::{
    FiniteAdmissionGrant, OriginalAdmission, OriginalAdmissionError, StopReason,
};
use ay_core::time::Instant;
use ay_core::{Sort, Symbol, TermStore, TheoryResult, TheorySolver};
use std::cell::Cell;
use std::sync::Arc;
use std::time::Duration;

mod resources;
mod semantics;

const UNITS: u64 = 1_000_000;
const BYTES: usize = 128 * 1024 * 1024;

enum Shape {
    Reads,
    Store,
}

struct Fixture {
    terms: TermStore,
    roots: Vec<TermId>,
    assignments: Vec<(TermId, bool)>,
    base: TermId,
    constant: TermId,
    read: TermId,
}

impl Fixture {
    fn new(cell: Sort, shape: Shape) -> Self {
        let mut terms = TermStore::new();
        let array_sort = Sort::array(Sort::bitvec(64), cell.clone());
        let base = terms.mk_var("a", array_sort.clone());
        let alias = terms.mk_var("alias", array_sort.clone());
        let index = terms.mk_bitvec(3u8.into(), 64);
        let outside = terms.mk_bitvec(4u8.into(), 64);
        let value = match &cell {
            Sort::Bool => terms.mk_bool(true),
            Sort::BitVec(bits) => terms.mk_bitvec(9u8.into(), bits.width),
            _ => unreachable!(),
        };
        let target = match shape {
            Shape::Reads => base,
            Shape::Store => terms.mk_app(
                Symbol::named("store"),
                [base, index, value],
                array_sort.clone(),
            ),
        };
        let read = terms.mk_app(Symbol::named("select"), [target, outside], cell.clone());
        let default = terms.mk_app(Symbol::named("default"), [base], cell.clone());
        let constant = terms.mk_app(Symbol::named("const-array"), [value], array_sort);
        // A raw select genuinely tracks the constant; mk_select would fold it.
        let constant_read = terms.mk_app(Symbol::named("select"), [constant, index], cell.clone());
        let equal = terms.mk_app(Symbol::named("="), [alias, target], Sort::Bool);
        // Real array-class assignment; scalar reads remain unassigned. Current
        // flat extraction refuses active scalar-equality adjacency, tested below.
        let roots = vec![read, default, equal, constant_read, constant];
        let assignments = vec![(equal, true)];
        Self {
            terms,
            roots,
            assignments,
            base,
            constant,
            read,
        }
    }

    fn prepared(&self) -> (TheoryCombiner<'_>, (EufModel, ArrayModel)) {
        let mut source = TheoryCombiner::array_euf(&self.terms);
        for &root in &self.roots {
            source.register_atom(root);
        }
        for &(term, value) in &self.assignments {
            source.assert_literal(term, value);
        }
        assert!(matches!(source.euf.check(), TheoryResult::Sat));
        source.scope_euf_model_to_roots(&self.roots);
        // Genuine legacy preparation/oracle work is outside this DATA ledger.
        let expected = source.extract_euf_array_models();
        (source, expected)
    }
}

fn same(actual: &(EufModel, ArrayModel), expected: &(EufModel, ArrayModel)) {
    let (a, b) = (&actual.0, &expected.0);
    assert_eq!(a.sort_elements, b.sort_elements);
    assert_eq!(a.term_values, b.term_values);
    assert_eq!(a.function_tables, b.function_tables);
    assert_eq!(a.function_table_terms, b.function_table_terms);
    assert_eq!(a.function_table_conflicts, b.function_table_conflicts);
    assert_eq!(a.func_app_const_terms, b.func_app_const_terms);
    assert_eq!(a.int_values, b.int_values);
    assert_eq!(a.speculative_int_terms, b.speculative_int_terms);
    assert_eq!(a.array_read_pins_repaired, b.array_read_pins_repaired);
    assert_eq!(actual.1.array_values, expected.1.array_values);
    assert_eq!(actual.1.read_conflicted, expected.1.read_conflicted);
    assert_eq!(
        actual.1.store_chain_class_candidate,
        expected.1.store_chain_class_candidate
    );
}

fn owner(units: u64, bytes: usize, end: Instant) -> OriginalAdmission {
    OriginalAdmission::new(
        FiniteAdmissionGrant::new(units, bytes),
        end,
        Arc::new(|| false),
    )
}

fn costs(source: &TheoryCombiner<'_>, roots: &[TermId], end: Instant) -> (u64, usize, usize) {
    let totals = Cell::new((0u64, 0usize, 0usize));
    let mut sink = |units, bytes| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        let (u, b, zeros) = totals.get();
        totals.set((
            u.checked_add(units as u64).unwrap(),
            b.checked_add(bytes).unwrap(),
            zeros + usize::from(units == 0),
        ));
        Ok(())
    };
    let mut work = WorkBudget::with_admission(UNITS, &mut sink);
    let output = source
        .try_extract_prepared_euf_array_models_with_budget(roots, &mut work)
        .unwrap();
    drop(output); // caller-owned later disposal, outside the component's claim
    drop(work);
    totals.get()
}
