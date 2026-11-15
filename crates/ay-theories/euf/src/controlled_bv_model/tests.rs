// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::original_query::{
    FiniteAdmissionGrant, OriginalAdmission, OriginalAdmissionError, StopReason,
};
use ay_core::term::TermStore;
use ay_core::time::Instant;
use ay_core::{TheoryResult, TheorySolver};
use std::cell::Cell;
use std::ops::ControlFlow;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

mod parity;
mod refusal;
mod resources;
mod stores;

// Native/TermStore fixture preparation and legacy oracle construction are
// outside this extraction-only component. Output disposal is caller-owned.
fn fixture(width: u32, boolean: bool) -> (TermStore, Vec<TermId>, Vec<(TermId, bool)>) {
    let mut terms = TermStore::new();
    let cell = if boolean {
        Sort::Bool
    } else {
        Sort::bitvec(width)
    };
    let array = terms.mk_var("a", Sort::array(Sort::bitvec(64), cell.clone()));
    let index = terms.mk_bitvec(3u8.into(), 64);
    let value = if boolean {
        terms.mk_bool(true)
    } else {
        terms.mk_bitvec((num_bigint::BigInt::from(1u8) << width) - 1u8, width)
    };
    let read = terms.mk_app(Symbol::named("select"), [array, index], cell.clone());
    let default = terms.mk_app(Symbol::named("default"), [array], cell.clone());
    let constant = terms.mk_app(
        Symbol::named("const-array"),
        [value],
        Sort::array(Sort::bitvec(64), cell),
    );
    let pinned = terms.mk_app(Symbol::named("="), [read, value], Sort::Bool);
    let pinned_default = terms.mk_app(Symbol::named("="), [default, value], Sort::Bool);
    let false_value = terms.mk_bool(false);
    let mut assignments = vec![(pinned, true), (pinned_default, true)];
    if boolean {
        assignments.push((read, true));
        assignments.push((default, true));
    }
    (
        terms,
        vec![pinned, pinned_default, read, default, constant, false_value],
        assignments,
    )
}

fn prepare<'a>(terms: &'a TermStore, assignments: &[(TermId, bool)]) -> EufSolver<'a> {
    let mut source = EufSolver::new(terms);
    for &(term, value) in assignments {
        source.assert_literal(term, value);
    }
    assert!(matches!(source.check(), TheoryResult::Sat));
    source
}

fn compare(a: &EufModel, b: &EufModel) {
    assert_eq!(a.sort_elements, b.sort_elements);
    assert_eq!(a.term_values, b.term_values);
    assert_eq!(a.function_tables, b.function_tables);
    assert_eq!(a.function_table_terms, b.function_table_terms);
    assert_eq!(a.function_table_conflicts, b.function_table_conflicts);
    assert_eq!(a.func_app_const_terms, b.func_app_const_terms);
    assert_eq!(a.int_values, b.int_values);
    assert_eq!(a.speculative_int_terms, b.speculative_int_terms);
    assert_eq!(a.array_read_pins_repaired, b.array_read_pins_repaired);
}

fn measured(
    source: &EufSolver<'_>,
    roots: &[TermId],
    units: u64,
    bytes: usize,
) -> (Result<EufModel, QueryError>, u64, usize, usize) {
    let used = Cell::new(0u64);
    let copied = Cell::new(0usize);
    let polls = Cell::new(0usize);
    let mut sink = |work: usize, copy: usize| {
        let next_work = used
            .get()
            .checked_add(u64::try_from(work).unwrap())
            .unwrap();
        let next_copy = copied.get().checked_add(copy).unwrap();
        if next_work > units || next_copy > bytes {
            return Err(QueryError::Exhausted);
        }
        used.set(next_work);
        copied.set(next_copy);
        if work == 0 {
            polls.set(polls.get() + 1);
        }
        Ok(())
    };
    let mut work = WorkBudget::with_admission(units, &mut sink);
    let result = source.try_extract_prepared_bv_model_from_roots_with_budget(roots, &mut work);
    drop(work);
    (result, used.get(), copied.get(), polls.get())
}

fn owner(units: u64, bytes: usize, end: Instant, flag: &Arc<AtomicBool>) -> OriginalAdmission {
    let watched = Arc::clone(flag);
    OriginalAdmission::new(
        FiniteAdmissionGrant::new(units, bytes),
        end,
        Arc::new(move || watched.load(Ordering::SeqCst)),
    )
}
