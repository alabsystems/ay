// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::original_query::{
    FiniteAdmissionGrant, OriginalAdmission, OriginalAdmissionError, StopReason,
};
use ay_core::time::Instant;
use std::cell::Cell;
use std::ops::ControlFlow;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};
use std::time::Duration;

mod borrowed_scan;
mod resources;
mod semantics;

fn row<'a>(index: &'a str, value: &'a str) -> ModelCellRow<'a> {
    ModelCellRow {
        key: ModelCellKey::Text(index),
        value,
    }
}

fn input<'a>(
    original: &'a [(ModelCellRow<'a>, CellAuthority)],
    observations: &'a [ModelCellRow<'a>],
) -> ArrayModelConstruction<'a> {
    ArrayModelConstruction {
        array: TermId(7),
        default: None,
        index_sort: None,
        element_sort: None,
        original,
        observations,
    }
}

fn healthy<T>(operation: impl FnOnce(&mut WorkBudget<'_>) -> T) -> T {
    let mut checkpoint = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(10_000_000, &mut checkpoint);
    operation(&mut work)
}

fn model() -> ArrayModel {
    let interpretation = ArrayInterpretation {
        default: Some("else".into()),
        stores: vec![("x".into(), "new".into()), ("x".into(), "old".into())],
        index_sort: Some(Sort::Int),
        element_sort: Some(Sort::Uninterpreted("Element".into())),
    };
    let mut source = ArrayModel::default();
    source
        .array_values
        .insert(TermId(7), interpretation.clone());
    source.read_conflicted.insert(TermId(7));
    source.store_chain_class_candidate = Some(HashMap::default());
    source
        .store_chain_class_candidate
        .as_mut()
        .unwrap()
        .insert(TermId(9), interpretation);
    source
}

fn costs(source: &ArrayModel) -> (usize, usize, usize) {
    let totals = Cell::new((0usize, 0usize, 0usize));
    let mut sink = |work, bytes| {
        let (w, b, p) = totals.get();
        totals.set((w + work, b + bytes, p + 1));
        Ok(())
    };
    let mut work = WorkBudget::with_admission(10_000_000, &mut sink);
    let result = source.try_clone_with_budget(&mut work).unwrap();
    assert_eq!(result.array_values, source.array_values);
    drop(result);
    drop(work);
    totals.get()
}
