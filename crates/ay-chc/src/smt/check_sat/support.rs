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

/// The DPLL(T) loop's SAT solver together with the log of every clause the
/// loop itself added after the initial CNF: theory blocking clauses (Farkas
/// and violated-atom), integer/disequality/expression split encodings and
/// model-equality encodings.
///
/// The log exists for the #5384 UNSAT defense in `run_check_sat_theory_loop`,
/// which re-checks a SAT-level UNSAT by replaying the INPUT clauses — and none
/// of the solver's learned clauses — in a fresh solver. A replay of the
/// initial CNF alone silently dropped the loop's theory lemmas: a query that
/// is UNSAT only modulo those lemmas came back SAT from the fresh solver, the
/// defense installed that solver as the main one, and the loop re-derived the
/// same lemmas from the same models forever (2026-09-23, 3 h 40 min observed;
/// the development design notes at `9598c4206`).
///
/// Two logs, because not every clause the loop adds is a lemma:
///
/// - `added` — theory conflicts (Farkas and plain), split encodings and
///   model-equality encodings: consequences of the formula and the theory.
///   The replay re-adds them.
/// - `model_blocks` — the `violated_constraint` block of the
///   `TheoryResult::Sat` arm: the negation of the whole current Boolean
///   assignment, added because the loop's model re-evaluation
///   (`get_term_value`) recomputes `*`/`div`/`mod` from argument values while
///   ay-lia carries those terms as OPAQUE columns, so the two disagree on a
///   perfectly feasible assignment (`x*y >= 7 ∧ x >= 0 ∧ y >= 0`: LIA says
///   x = y = 0 with the product column at 7; recomputed, `0 >= 7` is false).
///   That block is a model-repair heuristic, not a lemma, and it can exclude
///   the only satisfying assignment. It goes into the solver (the loop needs
///   to move on) but NOT into the replay: a SAT-level UNSAT that needs a model
///   block is unjustified, and the replay's job is to detect exactly that
///   (2026-09-23 adversarial review of f8a77d505). The durable fix is for
///   `get_term_value` to read the opaque columns from `lia_model.values`
///   instead of recomputing them; until then the loop fails closed.
///
/// The clause trace cannot tell the two apart, nor either from the input: it
/// marks EVERY clause given to `Solver::add_clause` original, so its
/// originals end with the lemmas AND the model blocks. The replay therefore
/// takes only the first `initial_originals` of them (the formula as the loop
/// received it) and the lemmas from `added` (`replay_clauses`). Replaying all
/// trace originals re-added the blocks and confirmed an UNSAT that rested on
/// one (faulty__barthe!_000: a satisfiable transition check came back UNSAT
/// and a non-inductive invariant was published as SAFE).
///
/// Everything except the two `add_*` entry points goes straight to the solver
/// through `Deref`/`DerefMut`; `add_clause` is shadowed so no call site can
/// bypass the log.
pub(super) struct LoopSat {
    solver: ay_sat::Solver,
    /// Trace originals present when this handle took the solver: no model
    /// block is among them, and every clause added later is logged here.
    initial_originals: usize,
    added: Vec<Vec<ay_sat::Literal>>,
    model_blocks: Vec<Vec<ay_sat::Literal>>,
}

impl LoopSat {
    pub(super) fn new(solver: ay_sat::Solver) -> Self {
        Self {
            initial_originals: trace_original_count(&solver),
            solver,
            added: Vec::new(),
            model_blocks: Vec::new(),
        }
    }

    /// Add a lemma to the solver and log it for the UNSAT replay.
    pub(super) fn add_clause(&mut self, clause: Vec<ay_sat::Literal>) -> bool {
        self.added.push(clause.clone());
        self.solver.add_clause(clause)
    }

    /// Add a model-based assignment block to the solver. It is logged apart
    /// from the lemmas and never replayed (see the type-level comment).
    pub(super) fn add_model_block(&mut self, clause: Vec<ay_sat::Literal>) -> bool {
        self.model_blocks.push(clause.clone());
        self.solver.add_clause(clause)
    }

    /// Every lemma added through this handle since the formula, in order.
    pub(super) fn added_clauses(&self) -> &[Vec<ay_sat::Literal>] {
        &self.added
    }

    /// The model-based blocks currently in the solver.
    pub(super) fn model_blocks(&self) -> &[Vec<ay_sat::Literal>] {
        &self.model_blocks
    }

    /// The #5384 UNSAT replay's clauses: the formula the loop received plus
    /// every lemma, never a model block. `None` without a clause trace.
    pub(super) fn replay_clauses(&self) -> Option<Vec<Vec<ay_sat::Literal>>> {
        let trace = self.solver.clause_trace()?;
        let initial = trace.original_clauses().take(self.initial_originals);
        let initial = initial.map(|entry| entry.clause.to_vec());
        Some(initial.chain(self.added.iter().cloned()).collect())
    }

    /// Install a replacement solver (the #5384 recovery). The replacement was
    /// built from `replay_clauses()`, so all of its trace originals are the
    /// formula and lemmas, and no model block is in it: both logs restart.
    pub(super) fn replace_solver(&mut self, solver: ay_sat::Solver) {
        self.initial_originals = trace_original_count(&solver);
        self.solver = solver;
        self.added.clear();
        self.model_blocks.clear();
    }
}

fn trace_original_count(solver: &ay_sat::Solver) -> usize {
    solver
        .clause_trace()
        .map_or(0, |trace| trace.original_clauses().count())
}

impl std::ops::Deref for LoopSat {
    type Target = ay_sat::Solver;

    fn deref(&self) -> &ay_sat::Solver {
        &self.solver
    }
}

impl std::ops::DerefMut for LoopSat {
    fn deref_mut(&mut self) -> &mut ay_sat::Solver {
        &mut self.solver
    }
}

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

#[cfg(test)]
mod tests;
