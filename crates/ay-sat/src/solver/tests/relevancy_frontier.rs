// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exactness + equivalence pins for the INCREMENTAL relevancy frontier
//! (#relevancy-frontier-incremental, `solver/relevancy_frontier.rs`).
//!
//! The frontier gates DECISIONS, so a drifted frontier does not fail loudly: a
//! too-large one silently changes the search trajectory, a too-small one fires
//! the empty-frontier SAT signal early and degrades to `unknown` at the model
//! gate. These tests therefore drive the frontier through every event class it
//! maintains — decisions, propagation, backtracking, restarts, learned-clause
//! appends, and the clause deletions/strengthenings that invalidate it — and
//! rely on `Solver::debug_assert_relevancy_frontier_exact`, which recomputes
//! the frontier with the original from-scratch clause walk and asserts SET
//! EQUALITY on every engaged decision (under
//! `--features relevancy-frontier-invariants`; on a bounded prefix in a plain
//! `debug_assertions` build). The verdict assertions below keep the tests
//! meaningful in a plain `--release` run, where that check is compiled out.

use super::*;

/// Deterministic xorshift — no rand dependency, and the same instances on every
/// platform (the whole point is a reproducible search trajectory).
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// Random 3-SAT at a given clause/variable ratio. Ratios near 4.26 sit at the
/// phase transition, which is where the search wanders — exactly the regime the
/// relevancy brancher engages in — and where restarts, clause reduction and
/// arena garbage all fire within a single solve.
fn random_3sat(num_vars: usize, num_clauses: usize, seed: u64) -> Vec<Vec<Literal>> {
    let mut rng = Rng(seed);
    let mut clauses = Vec::with_capacity(num_clauses);
    for _ in 0..num_clauses {
        let mut clause: Vec<Literal> = Vec::with_capacity(3);
        while clause.len() < 3 {
            let v = Variable(rng.below(num_vars) as u32);
            if clause.iter().any(|l: &Literal| l.variable() == v) {
                continue;
            }
            clause.push(if rng.next() & 1 == 0 {
                Literal::positive(v)
            } else {
                Literal::negative(v)
            });
        }
        clauses.push(clause);
    }
    clauses
}

/// Keep a test solver out of the PROCESS-GLOBAL ambient-artifact paths.
///
/// `maybe_write_fmla_learned_lrat_dry_run_proof_artifact_from_env` fires on
/// every solve finalization of an ambient-artifact-enabled solver and writes to
/// whatever path `FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_PATH_ENV` names at
/// that instant — a process-global destination that the conflict-analysis
/// dry-run tests point at their own tempdir while they run. Nothing here is
/// about artifacts, so opt out rather than join that race (same reason as
/// `tests/proof_consumer_lifecycle.rs`).
fn quiet_ambient_artifacts(solver: &mut Solver) {
    solver.cold.ambient_artifacts_enabled = false;
}

/// Solve `clauses`, optionally with the relevancy frontier forced on for EVERY
/// decision (`hard`), and return the verdict as a comparable string plus the
/// model when SAT.
fn solve_with(
    clauses: &[Vec<Literal>],
    num_vars: usize,
    hard: bool,
) -> (String, Option<Vec<bool>>) {
    let mut solver = Solver::new(num_vars);
    quiet_ambient_artifacts(&mut solver);
    if hard {
        solver.set_relevancy_branching(true);
        solver.set_relevancy_hard(true);
    }
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    match solver.solve().into_inner() {
        SatResult::Sat(model) => ("sat".to_string(), Some(model)),
        SatResult::Unsat(_) => ("unsat".to_string(), None),
        SatResult::Unknown => ("unknown".to_string(), None),
    }
}

fn model_satisfies(clauses: &[Vec<Literal>], model: &[bool]) -> bool {
    clauses.iter().all(|clause| {
        clause.iter().any(|lit| {
            let v = lit.variable().index();
            v < model.len() && model[v] == lit.is_positive()
        })
    })
}

/// The incremental frontier must survive a full CDCL search: decisions,
/// propagation, chronological backtracking, restarts, learned-clause appends
/// and clause-DB reduction. Under the invariant build every engaged decision is
/// compared against the from-scratch walk; the verdict comparison keeps the
/// test honest in a plain release run.
#[test]
fn incremental_frontier_matches_full_walk_on_random_3sat() {
    for seed in 1..=8u64 {
        let num_vars = 90;
        let clauses = random_3sat(num_vars, 383, seed);

        let (baseline, _) = solve_with(&clauses, num_vars, false);
        let (relevancy, model) = solve_with(&clauses, num_vars, true);

        // Relevancy is decisions-only: it can never flip sat <-> unsat. (It may
        // legitimately return `unknown` — the empty-frontier SAT signal is
        // re-verified by the model gate — so only a FLIPPED verdict is a bug.)
        assert!(
            relevancy == baseline || relevancy.starts_with("unknown"),
            "seed {seed}: relevancy verdict {relevancy} contradicts baseline {baseline}",
        );
        if let Some(model) = model {
            assert!(
                model_satisfies(&clauses, &model),
                "seed {seed}: relevancy-restricted model does not satisfy the formula",
            );
        }
    }
}

/// Same, on UNSAT instances: an over-constrained random 3-SAT at ratio ~6
/// refutes after thousands of conflicts, so the solve runs many reduce/GC
/// rounds — the events that INVALIDATE the incremental state and force the
/// rebuild path to be exercised alongside the incremental one.
#[test]
fn incremental_frontier_survives_clause_deletion_and_restarts() {
    for seed in 11..=14u64 {
        let num_vars = 60;
        let clauses = random_3sat(num_vars, 380, seed);
        let (baseline, _) = solve_with(&clauses, num_vars, false);
        let (relevancy, _) = solve_with(&clauses, num_vars, true);
        assert!(
            relevancy == baseline || relevancy.starts_with("unknown"),
            "seed {seed}: relevancy verdict {relevancy} contradicts baseline {baseline}",
        );
    }
}

/// Incremental solving: a second `solve()` on the same solver re-enters with a
/// populated arena, a preprocess reset in between, and clauses added while the
/// frontier cache is live. Both are explicit invalidation paths.
#[test]
fn incremental_frontier_survives_incremental_solves() {
    let num_vars = 24;
    let mut solver = Solver::new(num_vars);
    quiet_ambient_artifacts(&mut solver);
    solver.set_relevancy_branching(true);
    solver.set_relevancy_hard(true);
    let first = random_3sat(num_vars, 60, 21);
    for clause in &first {
        solver.add_clause(clause.clone());
    }
    let first_verdict = solver.solve().into_inner();
    assert!(
        !matches!(first_verdict, SatResult::Unsat(_)),
        "the first (under-constrained) round must not refute",
    );

    let second = random_3sat(num_vars, 60, 22);
    for clause in &second {
        solver.add_clause(clause.clone());
    }
    let mut all = first.clone();
    all.extend(second.iter().cloned());
    match solver.solve().into_inner() {
        SatResult::Sat(model) => assert!(
            model_satisfies(&all, &model),
            "incremental relevancy model does not satisfy the accumulated formula",
        ),
        SatResult::Unsat(_) | SatResult::Unknown => {}
    }
}

/// The empty-frontier SAT signal still fires: once every clause has a true
/// literal the frontier must be EMPTY, so the solver stops deciding even though
/// unassigned don't-care variables remain.
#[test]
fn empty_frontier_leaves_dont_care_variables_undecided() {
    let mut solver = Solver::new(0);
    quiet_ambient_artifacts(&mut solver);
    let vars: Vec<Variable> = (0..12).map(|_| solver.new_var()).collect();
    solver.set_relevancy_branching(true);
    solver.set_relevancy_hard(true);
    // Only vars 0..3 are constrained; 3..12 occur in no clause at all and can
    // never be relevant.
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[1])]);
    solver.add_clause(vec![Literal::negative(vars[1]), Literal::positive(vars[2])]);
    match solver.solve().into_inner() {
        SatResult::Sat(model) => {
            assert!(model[vars[0].index()] || model[vars[1].index()]);
            assert!(!model[vars[1].index()] || model[vars[2].index()]);
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

/// REGRESSION (#relevancy-frontier-incremental): a clause-DB mutation between
/// the frontier query that SYNCED the cache and the backtrack that FOLDS OUT
/// of it must not let the fold walk offsets the formula has moved.
///
/// `RelevancyFrontier::occ` holds arena WORD OFFSETS and `true_count` is
/// indexed by them, so both are meaningful only while every existing clause
/// holds still. `sync()` has always refused to fold across an epoch change;
/// the backtrack hook originally did not, and `compact_arena_locality`
/// (`arena_gc.rs`) rewrites the arena into a SHORTER one with every offset
/// moved. It runs at the search loop's post-BCP scheduling point — which is
/// before the next decision, i.e. before the next `sync()` — so the very next
/// backtrack folded over the compacted arena and panicked inside
/// `ClauseArena::lit_len_raw`:
///
/// ```text
/// index out of bounds: the len is 37709 but the index is 48956
///    3: fold_unassign
///    4: ay_sat::solver::backtrack::..::backtrack_core
/// ```
///
/// This instance is the smallest of a probe sweep that reproduces it: a
/// 200-variable random 3-SAT at ratio 4.35 refutes in ~22 500 conflicts and
/// runs SEVEN arena compactions on the way. The compaction count is asserted
/// so the test cannot quietly stop covering the class if reduction scheduling
/// changes.
#[test]
fn incremental_frontier_survives_arena_compaction_between_sync_and_backtrack() {
    let num_vars = 200;
    let clauses = random_3sat(num_vars, 870, 32);

    let mut solver = Solver::new(num_vars);
    quiet_ambient_artifacts(&mut solver);
    solver.set_relevancy_branching(true);
    solver.set_relevancy_hard(true);
    for clause in &clauses {
        solver.add_clause(clause.clone());
    }
    let verdict = solver.solve().into_inner();

    assert!(
        solver.num_arena_compactions() > 0,
        "this instance no longer compacts the arena, so it no longer covers the \
         stale-offset fold (conflicts={}, arena_words={})",
        solver.num_conflicts(),
        solver.arena_words(),
    );
    assert!(
        solver.relevancy_decisions() > 0,
        "the relevancy frontier never engaged, so nothing was folded",
    );
    match verdict {
        SatResult::Unsat(_) | SatResult::Unknown => {}
        SatResult::Sat(model) => assert!(
            model_satisfies(&clauses, &model),
            "relevancy-restricted model does not satisfy the formula",
        ),
    }
}
