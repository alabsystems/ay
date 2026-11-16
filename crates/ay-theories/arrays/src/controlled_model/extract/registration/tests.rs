// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::TheorySolver;
use ay_core::original_query::{
    FiniteAdmissionGrant, OriginalAdmission, OriginalAdmissionError, StopReason,
};
use ay_core::term::TermStore;
use ay_core::time::Instant;
use std::cell::Cell;
use std::sync::{
    atomic::{AtomicBool, AtomicUsize, Ordering},
    Arc,
};
use std::time::Duration;

mod refusals;
mod resources;
mod semantics;

struct Fixture {
    terms: TermStore,
    base: TermId,
    constant: TermId,
    indices: [TermId; 4],
    reads: [TermId; 4],
    constant_read: TermId,
    default: TermId,
    otherwise: TermId,
    equality: TermId,
}

impl Fixture {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let sort = Sort::array(Sort::Int, Sort::Int);
        let base = terms.mk_var("a", sort.clone());
        let other = terms.mk_var("b", sort);
        let indices = ["i", "j", "k", "l"].map(|name| terms.mk_var(name, Sort::Int));
        let otherwise = terms.mk_var("else", Sort::Int);
        let constant = terms.mk_const_array(Sort::Int, otherwise);
        let reads =
            indices.map(|index| terms.mk_app(Symbol::named("select"), [base, index], Sort::Int));
        // Do not use mk_select: that would fold the const-array and lose tracking.
        let constant_read =
            terms.mk_app(Symbol::named("select"), [constant, indices[0]], Sort::Int);
        let default = terms.mk_array_default(base);
        let equality = terms.mk_app(Symbol::named("="), [base, other], Sort::Bool);
        Self {
            terms,
            base,
            constant,
            indices,
            reads,
            constant_read,
            default,
            otherwise,
            equality,
        }
    }

    fn values(&self) -> HashMap<TermId, String> {
        let mut values = HashMap::default();
        for (i, (&index, &read)) in self.indices.iter().zip(&self.reads).enumerate() {
            values.insert(index, i.to_string());
            values.insert(read, format!("r{i}"));
        }
        values.insert(self.otherwise, "else".into());
        values.insert(self.default, "base-default".into());
        values
    }
}

fn owner(end: Instant, units: usize, bytes: usize) -> OriginalAdmission {
    OriginalAdmission::new(
        FiniteAdmissionGrant::new(units as u64, bytes),
        end,
        Arc::new(|| false),
    )
}

fn same(left: &ArrayModel, right: &ArrayModel) {
    assert_eq!(left.array_values, right.array_values);
    assert_eq!(left.read_conflicted, right.read_conflicted);
    assert_eq!(
        left.store_chain_class_candidate,
        right.store_chain_class_candidate
    );
}

fn costs(
    source: &ArraySolver<'_>,
    values: &HashMap<TermId, String>,
    end: Instant,
) -> (usize, usize, usize) {
    // Separate bounded instrumentation attempt, with the test's original end.
    // Production does not synthesize a grant from calibration or a retry.
    let totals = Cell::new((0usize, 0usize, 0usize));
    let mut sink = |units, bytes| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        let (u, b, p) = totals.get();
        totals.set((
            u.checked_add(units).unwrap(),
            b.checked_add(bytes).unwrap(),
            p + 1,
        ));
        Ok(())
    };
    let mut work = WorkBudget::with_admission(1_000_000, &mut sink);
    let output = source
        .try_extract_registered_model_with_budget(values, &mut work)
        .unwrap();
    drop(output);
    totals.get()
}

fn refused(source: &ArraySolver<'_>, end: Instant) {
    let original = owner(end, 1_000_000, 128 << 20);
    assert!(matches!(
        original.with_work(
            |work| source.try_extract_registered_model_with_budget(&HashMap::default(), work)
        ),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    ));
    assert!(original.clone().check().is_err());
}
