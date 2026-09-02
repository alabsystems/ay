// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Reusable support types for check_sat: theory solver construction and BV clause helpers.

// #8529: Use deterministic hash sets in all builds.
use ay_arrays::{AffineCache, ArraySolver};
use ay_core::kani_compat::DetHashSet as HbHashSet;
use ay_core::TermStore;
use ay_euf::EufSolver;
use ay_lia::{DiophState, HnfCutKey, LiaSolver, StoredCut};

#[derive(Default)]
pub(super) struct LiaReusableState {
    dioph: DiophState,
    learned_cuts: Vec<StoredCut>,
    seen_hnf_cuts: HbHashSet<HnfCutKey>,
    /// Shared affine normal-form / interning memo, persisted across the
    /// fresh-`ArraySolver`-per-refinement-round recreation in the DPLL(T) outer
    /// loop. It is a pure function of the immutable `TermStore` (stable for the
    /// duration of one `run_check_sat_theory_loop`), so reuse is byte-identical
    /// to recompute — it only elides redundant re-parsing/re-interning of the
    /// same terms every round. Carries no assignment or lemma-reason content.
    affine_cache: std::rc::Rc<AffineCache>,
}

impl LiaReusableState {
    pub(super) fn capture(&mut self, solver: &mut LiaSolver<'_>) {
        let (learned_cuts, seen_hnf_cuts) = solver.take_learned_state();
        self.dioph = solver.take_dioph_state();
        self.learned_cuts = learned_cuts;
        self.seen_hnf_cuts = seen_hnf_cuts;
    }

    pub(super) fn restore_into(&mut self, solver: &mut LiaSolver<'_>) -> bool {
        solver.import_dioph_state(std::mem::take(&mut self.dioph));

        let needs_cut_replay = !self.learned_cuts.is_empty();
        if needs_cut_replay || !self.seen_hnf_cuts.is_empty() {
            solver.import_learned_state(
                std::mem::take(&mut self.learned_cuts),
                std::mem::take(&mut self.seen_hnf_cuts),
            );
        }

        needs_cut_replay
    }
}

pub(super) fn build_theory_solvers<'a>(
    terms: &'a TermStore,
    has_array_ops: bool,
    needs_euf: bool,
    start: ay_core::time::Instant,
    timeout: Option<std::time::Duration>,
    global_deadline: Option<ay_core::time::Instant>,
    lia_state: &mut LiaReusableState,
) -> (
    LiaSolver<'a>,
    Option<ArraySolver<'a>>,
    Option<EufSolver<'a>>,
    bool,
) {
    #[cfg(test)]
    super::record_theory_solver_build_for_tests();

    let mut lia = LiaSolver::new(terms);
    if needs_euf {
        lia.set_combined_theory_mode(true);
    }
    if let Some(timeout) = timeout {
        lia.set_timeout_callback(move || start.elapsed() >= timeout);
    }
    // Install the earliest absolute boundary as well as the legacy relative
    // callback. Exact-arithmetic subroutines poll this deadline internally;
    // without propagating the solve-wide boundary, one such call could keep a
    // cancelled portfolio worker inside synchronous reaping indefinitely.
    let per_check_deadline = timeout.map(|timeout| start + timeout);
    if let Some(deadline) = match (per_check_deadline, global_deadline) {
        (Some(per_check), Some(global)) => Some(per_check.min(global)),
        (Some(deadline), None) | (None, Some(deadline)) => Some(deadline),
        (None, None) => None,
    } {
        lia.set_deadline(deadline);
    }
    let needs_cut_replay = lia_state.restore_into(&mut lia);

    let arrays = has_array_ops.then(|| {
        let mut arrays = ArraySolver::new(terms);
        // Persist the affine memo across rounds: hand this fresh solver the
        // shared cache accumulated by earlier refinement rounds over the same
        // immutable `TermStore`.
        arrays.adopt_affine_cache(lia_state.affine_cache.clone());
        arrays
    });

    (
        lia,
        arrays,
        needs_euf.then(|| EufSolver::new(terms)),
        needs_cut_replay,
    )
}

pub(super) fn add_offset_bv_clause(
    sat: &mut ay_sat::Solver,
    clause: &ay_core::CnfClause,
    offset: i32,
) {
    let lits: Vec<ay_sat::Literal> = clause
        .literals()
        .iter()
        .map(|&lit| {
            let offset_lit = if lit > 0 { lit + offset } else { lit - offset };
            ay_sat::Literal::from_dimacs(offset_lit)
        })
        .collect();
    sat.add_clause(lits);
}
