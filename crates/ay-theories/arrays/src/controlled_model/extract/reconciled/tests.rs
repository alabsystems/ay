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

mod boolean;
mod cycles;
mod defaults;
mod external;
mod refusals;
mod resources;
mod scalar;
mod semantics;

struct Fixture {
    terms: TermStore,
    bases: [TermId; 2],
    alias: TermId,
    missing: TermId,
    indices: [TermId; 4],
    writes: [TermId; 2],
    stores: [TermId; 3],
    selects: [TermId; 4],
    defaults: [TermId; 5],
    constant: TermId,
    else_value: TermId,
    equalities: [TermId; 3],
}

impl Fixture {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let index = Sort::BitVec(ay_core::BitVecSort { width: 64 });
        let element = Sort::BitVec(ay_core::BitVecSort { width: 128 });
        let sort = Sort::array(index.clone(), element.clone());
        let bases = ["a", "b"].map(|n| terms.mk_var(n, sort.clone()));
        let alias = terms.mk_var("alias", sort.clone());
        let missing = terms.mk_var("missing", sort.clone());
        let indices = ["i", "j", "k", "l"].map(|n| terms.mk_var(n, index.clone()));
        let writes = [
            terms.mk_var("written", element.clone()),
            terms.mk_bitvec((num_bigint::BigInt::from(1u8) << 128usize) - 1u8, 128),
        ];
        let inner = store(&mut terms, bases[0], indices[0], writes[0], &sort);
        let left = store(&mut terms, inner, indices[1], writes[1], &sort);
        let right = store(&mut terms, bases[1], indices[0], writes[1], &sort);
        let stores = [inner, left, right];
        let selects = [
            (bases[0], indices[2]),
            (bases[1], indices[2]),
            (alias, indices[2]),
            (bases[0], indices[3]),
        ]
        .map(|(a, i)| read(&mut terms, a, i, &element));
        let defaults = [bases[0], bases[1], alias, left, right].map(|a| terms.mk_array_default(a));
        read(&mut terms, missing, indices[2], &element);
        let else_value = terms.mk_var("else", element.clone());
        let constant = terms.mk_const_array(index, else_value);
        read(&mut terms, constant, indices[2], &element);
        let equalities = [
            terms.mk_eq(alias, left),
            terms.mk_eq(left, right),
            terms.mk_eq(alias, missing),
        ];
        Self {
            terms,
            bases,
            alias,
            missing,
            indices,
            writes,
            stores,
            selects,
            defaults,
            constant,
            else_value,
            equalities,
        }
    }

    fn solver(&self) -> ArraySolver<'_> {
        let mut solver = ArraySolver::new(&self.terms);
        // Real legacy preparation is fixture work OUTSIDE this DATA budget.
        solver.populate_caches();
        for &equality in &self.equalities {
            solver.register_atom(equality);
            solver.assert_literal(equality, true);
        }
        let _ = solver.check();
        solver.rebuild_assign_indices();
        assert!(!solver.eq_adj.is_empty());
        assert!(!solver.dirty && !solver.assign_dirty && !solver.var_layer_dirty);
        solver
    }

    fn values(&self) -> HashMap<TermId, String> {
        let mut values = HashMap::default();
        for (&term, value) in self.indices.iter().zip(["0", "1", "2", "3"]) {
            values.insert(term, value.into());
        }
        values.insert(self.writes[0], "soft".into());
        values.insert(
            self.writes[1],
            "340282366920938463463374607431768211455".into(),
        );
        for (&term, value) in
            self.selects
                .iter()
                .zip(["outside-a", "outside-b", "outside-alias", "outside-extra"])
        {
            values.insert(term, value.into());
        }
        values.insert(self.else_value, "const-else".into());
        values
    }
}

fn store(
    terms: &mut TermStore,
    array: TermId,
    index: TermId,
    value: TermId,
    sort: &Sort,
) -> TermId {
    terms.mk_app(Symbol::named("store"), [array, index, value], sort.clone())
}

fn read(terms: &mut TermStore, array: TermId, index: TermId, sort: &Sort) -> TermId {
    terms.mk_app(Symbol::named("select"), [array, index], sort.clone())
}

fn owner(end: Instant, units: usize, bytes: usize) -> OriginalAdmission {
    OriginalAdmission::new(
        FiniteAdmissionGrant::new(units as u64, bytes),
        end,
        Arc::new(|| false),
    )
}

fn run(
    solver: &ArraySolver<'_>,
    values: &HashMap<TermId, String>,
    original: &OriginalAdmission,
) -> ArrayModel {
    original
        .with_work(|work| solver.try_extract_prepared_flat_model_with_budget(values, work))
        .unwrap()
}

fn same(output: &ArrayModel, legacy: &ArrayModel) {
    assert_eq!(output.array_values, legacy.array_values);
    assert_eq!(output.read_conflicted, legacy.read_conflicted);
    assert_eq!(
        output.store_chain_class_candidate,
        legacy.store_chain_class_candidate
    );
}

fn costs(
    solver: &ArraySolver<'_>,
    values: &HashMap<TermId, String>,
    end: Instant,
) -> (usize, usize, usize) {
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
    let output = solver
        .try_extract_prepared_flat_model_with_budget(values, &mut work)
        .unwrap();
    drop(output);
    work.charge(0).unwrap();
    drop(work);
    totals.get()
}
