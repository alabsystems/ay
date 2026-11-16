// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::original_query::{
    FiniteAdmissionGrant, OriginalAdmission, OriginalAdmissionError, StopReason,
};
use ay_core::term::{Symbol, TermStore};
use ay_core::time::Instant;
use std::cell::Cell;
use std::sync::{
    atomic::{AtomicBool, AtomicUsize, Ordering},
    Arc,
};
use std::time::Duration;

mod classes;
mod resources;
mod semantics;

struct Fixture {
    terms: TermStore,
    base: TermId,
    constant: TermId,
    chain: TermId,
    indices: [TermId; 4],
    written: [TermId; 2],
    selects: [TermId; 3],
    default: TermId,
}

impl Fixture {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let array_sort = Sort::array(Sort::Int, Sort::Int);
        let base = terms.mk_var("a", array_sort.clone());
        let indices = ["i", "j", "k", "l"].map(|name| terms.mk_var(name, Sort::Int));
        let written = [terms.mk_int(1.into()), terms.mk_var("v", Sort::Int)];
        let default = terms.mk_var("else", Sort::Int);
        let constant = terms.mk_const_array(Sort::Int, default);
        // Raw registration keeps the const-array tracked without folding or a value pin.
        let _constant_read =
            terms.mk_app(Symbol::named("select"), [constant, indices[0]], Sort::Int);
        let inner = terms.mk_app(
            Symbol::named("store"),
            [base, indices[0], written[1]],
            array_sort.clone(),
        );
        let chain = terms.mk_app(
            Symbol::named("store"),
            [inner, indices[1], written[0]],
            array_sort,
        );
        let selects = [indices[0], indices[2], indices[3]]
            .map(|index| terms.mk_app(Symbol::named("select"), [base, index], Sort::Int));
        let _base_default = terms.mk_array_default(base);
        Self {
            terms,
            base,
            constant,
            chain,
            indices,
            written,
            selects,
            default,
        }
    }

    fn values(&self) -> HashMap<TermId, String> {
        let mut values = HashMap::default();
        for &index in &self.indices {
            values.insert(index, "cell".into());
        }
        values.insert(self.written[0], "concrete".into());
        values.insert(self.written[1], "soft".into());
        values.insert(self.default, "else".into());
        for &select in &self.selects {
            values.insert(select, "read".into());
        }
        values
    }

    fn solver(&self) -> ArraySolver<'_> {
        let mut solver = ArraySolver::new(&self.terms);
        // Fixture preparation is deliberately OUTSIDE the controlled API.
        solver.populate_caches();
        solver.rebuild_assign_indices();
        solver
    }
}

fn owner(end: Instant, work: usize, bytes: usize) -> OriginalAdmission {
    OriginalAdmission::new(
        FiniteAdmissionGrant::new(work as u64, bytes),
        end,
        Arc::new(|| false),
    )
}

fn costs(solver: &ArraySolver<'_>, values: &HashMap<TermId, String>) -> (usize, usize, usize) {
    let totals = Cell::new((0usize, 0usize, 0usize));
    let mut sink = |units, bytes| {
        let (u, b, p) = totals.get();
        totals.set((u + units, b + bytes, p + 1));
        Ok(())
    };
    let mut work = WorkBudget::with_admission(1_000_000, &mut sink);
    let output = solver
        .try_extract_prepared_model_with_budget(values, &mut work)
        .unwrap();
    drop(output);
    totals.get()
}

fn same(left: &ArrayModel, right: &ArrayModel) {
    assert_eq!(left.array_values, right.array_values);
    assert_eq!(left.read_conflicted, right.read_conflicted);
    assert_eq!(
        left.store_chain_class_candidate,
        right.store_chain_class_candidate
    );
}
