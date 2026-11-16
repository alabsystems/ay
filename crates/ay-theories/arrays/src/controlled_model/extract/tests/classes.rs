// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::TheorySolver;

mod resources;
mod semantics;

struct ClassFixture {
    terms: TermStore,
    arrays: [TermId; 3],
    equalities: [TermId; 2],
    indices: [TermId; 2],
    selects: [TermId; 5],
    defaults: [TermId; 3],
}

impl ClassFixture {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let sort = Sort::array(Sort::Int, Sort::Int);
        let arrays = ["left", "right", "missing"].map(|name| terms.mk_var(name, sort.clone()));
        let indices = ["i", "j"].map(|name| terms.mk_var(name, Sort::Int));
        let selects = [(0, 0), (0, 1), (1, 0), (1, 1), (2, 0)].map(|(a, i)| {
            terms.mk_app(Symbol::named("select"), [arrays[a], indices[i]], Sort::Int)
        });
        let defaults = arrays.map(|array| terms.mk_array_default(array));
        let equalities = [
            terms.mk_eq(arrays[0], arrays[1]),
            terms.mk_eq(arrays[1], arrays[2]),
        ];
        Self {
            terms,
            arrays,
            equalities,
            indices,
            selects,
            defaults,
        }
    }

    fn solver(&self) -> ArraySolver<'_> {
        let mut solver = ArraySolver::new(&self.terms);
        // Real registration/assert/check; no hand-built eq_adj and no claim
        // that fixture preparation itself belongs to the extraction budget.
        solver.populate_caches();
        for &equality in &self.equalities {
            solver.register_atom(equality);
            solver.assert_literal(equality, true);
        }
        let _ = solver.check();
        solver.rebuild_assign_indices();
        assert_ne!(solver.eq_adj.len(), 0);
        assert_ne!(solver.array_var_merge_log.len(), 0);
        assert_eq!(
            solver.array_var_merge_log.len(),
            solver.array_var_merge_undo.len()
        );
        assert!(!solver.dirty && !solver.assign_dirty && !solver.var_layer_dirty);
        solver
    }

    fn values(&self) -> HashMap<TermId, String> {
        let mut values = HashMap::default();
        for (&index, spelling) in self.indices.iter().zip(["0", "1"]) {
            values.insert(index, spelling.into());
        }
        for (&select, spelling) in self.selects[..4].iter().zip(["L0", "L1", "R0", "R1"]) {
            values.insert(select, spelling.into());
        }
        values
    }
}

fn class_costs(
    solver: &ArraySolver<'_>,
    values: &HashMap<TermId, String>,
    end: Instant,
) -> (usize, usize, usize) {
    // Separate instrumentation attempt, sharing the test's ONE absolute end.
    // Production never derives/renews a grant from this test calibration.
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
        .try_extract_prepared_model_with_budget(values, &mut work)
        .unwrap();
    drop(output);
    work.charge(0).unwrap();
    totals.get()
}

fn controlled(
    solver: &ArraySolver<'_>,
    values: &HashMap<TermId, String>,
    original: &OriginalAdmission,
) -> ArrayModel {
    original
        .with_work(|work| solver.try_extract_prepared_model_with_budget(values, work))
        .unwrap()
}
