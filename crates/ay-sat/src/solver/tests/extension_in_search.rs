// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! G1-G4 of the development design notes §3.10: what an extension may do in
//! the middle of one search; and GT-G6's search-tick reading
//! (the development design notes DR-36), what it may read there.

use super::*;
use crate::extension::{ExtCheckResult, ExtContinue, ExtPropagateResult, Extension, SolverContext};

fn pos(v: u32) -> Literal {
    Literal::positive(Variable(v))
}

fn neg(v: u32) -> Literal {
    Literal::negative(Variable(v))
}

/// The literal of `var` that is true under the context's assignment.
fn true_lit(ctx: &dyn SolverContext, var: u32) -> Literal {
    if ctx.value(Variable(var)) == Some(true) {
        pos(var)
    } else {
        neg(var)
    }
}

/// Returns one final-check lemma over two fresh variables, then accepts.
/// Records every backtrack the solver makes after that lemma.
struct FreshLemmaAtFinalCheck {
    fresh: u32,
    restart_semantics: bool,
    check_levels: Vec<u32>,
    backtracks_after_lemma: Vec<u32>,
}

impl Extension for FreshLemmaAtFinalCheck {
    fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
        ExtPropagateResult::none()
    }

    fn check(&mut self, ctx: &dyn SolverContext) -> ExtCheckResult {
        self.check_levels.push(ctx.decision_level());
        if self.check_levels.len() > 1 {
            return ExtCheckResult::Sat;
        }
        let lemma = vec![pos(self.fresh), pos(self.fresh + 1)];
        if self.restart_semantics {
            ExtCheckResult::AddClauses(vec![lemma])
        } else {
            ExtCheckResult::Continue(ExtContinue::new(vec![lemma], Vec::new()))
        }
    }

    fn backtrack(&mut self, new_level: u32) {
        if !self.check_levels.is_empty() {
            self.backtracks_after_lemma.push(new_level);
        }
    }
}

fn run_fresh_lemma(restart_semantics: bool) -> (SatResult, FreshLemmaAtFinalCheck, Solver) {
    let mut solver = Solver::new(3);
    solver.add_clause(vec![pos(0), pos(1), pos(2)]);
    let mut ext = FreshLemmaAtFinalCheck {
        fresh: 3,
        restart_semantics,
        check_levels: Vec::new(),
        backtracks_after_lemma: Vec::new(),
    };
    let result = solver.solve_with_extension(&mut ext).into_inner();
    (result, ext, solver)
}

/// G2: a final-check lemma continues the search at the current level. The
/// same lemma through `AddClauses` restarts from level 0 (the contrast shows
/// the test can tell the two apart).
#[test]
fn final_check_lemma_continues_at_the_current_level() {
    let (result, ext, solver) = run_fresh_lemma(false);
    let SatResult::Sat(model) = result else {
        panic!("expected sat, got {result:?}");
    };
    assert!(model[3] || model[4], "the lemma holds in the model");
    assert_eq!(ext.check_levels.len(), 2, "{:?}", ext.check_levels);
    assert!(
        ext.backtracks_after_lemma.iter().all(|&level| level > 0),
        "no restart after a Continue lemma: {:?}",
        ext.backtracks_after_lemma
    );
    assert!(ext.check_levels[1] > ext.check_levels[0]);
    assert!(solver.is_frozen(Variable(3)) && solver.is_frozen(Variable(4)));

    let (result, ext, _) = run_fresh_lemma(true);
    assert!(matches!(result, SatResult::Sat(_)));
    assert!(
        ext.backtracks_after_lemma.contains(&0),
        "AddClauses keeps its restart semantics: {:?}",
        ext.backtracks_after_lemma
    );
}

/// Blocks the complete assignment of `vars` at every final check, with a
/// lemma that is false when it is returned (so it is a conflict).
struct BlockEveryModel {
    vars: u32,
    checks: u32,
    limit: u32,
}

impl Extension for BlockEveryModel {
    fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
        ExtPropagateResult::none()
    }

    fn check(&mut self, ctx: &dyn SolverContext) -> ExtCheckResult {
        self.checks += 1;
        if self.checks > self.limit {
            return ExtCheckResult::Sat;
        }
        let blocking = (0..self.vars).map(|v| true_lit(ctx, v).negated()).collect();
        ExtCheckResult::Continue(ExtContinue::new(vec![blocking], Vec::new()))
    }
}

/// G2: a falsified final-check lemma is handled as a conflict at the current
/// level; the next model differs, and the lemma is kept.
#[test]
fn falsified_final_check_lemma_is_a_conflict() {
    let mut solver = Solver::new(2);
    solver.add_clause(vec![pos(0), pos(1)]);
    let mut ext = BlockEveryModel {
        vars: 2,
        checks: 0,
        limit: 1,
    };
    let result = solver.solve_with_extension(&mut ext).into_inner();
    assert!(matches!(result, SatResult::Sat(_)), "{result:?}");
    assert_eq!(ext.checks, 2);
}

/// G2: blocking every model through `Continue` exhausts the space: unsat.
#[test]
fn continue_lemmas_can_refute() {
    let mut solver = Solver::new(3);
    let mut ext = BlockEveryModel {
        vars: 3,
        checks: 0,
        limit: u32::MAX,
    };
    let result = solver.solve_with_extension(&mut ext).into_inner();
    assert!(matches!(result, SatResult::Unsat(_)), "{result:?}");
    assert!(
        ext.checks <= 8,
        "one check per model at most: {}",
        ext.checks
    );
}

/// G1: a definition is irredundant, global in the ledger, and its fresh
/// variable is frozen (G3).
#[test]
fn definition_is_irredundant_and_in_the_ledger() {
    let mut solver = Solver::new(2);
    let before = solver.cold.original_ledger.num_clauses();
    let clause_ref = solver
        .add_theory_definition(vec![pos(0), pos(2)])
        .expect("a two-literal definition is stored");
    assert!(!solver.arena.is_learned(clause_ref.0 as usize));
    assert_eq!(solver.cold.original_ledger.num_clauses(), before + 1);
    assert!(solver.is_frozen(Variable(2)));
    assert!(solver.add_theory_definition(vec![pos(1), neg(1)]).is_none());
}

/// Returns, once, a definition over a fresh variable beside a conflict.
struct DefinitionBesideConflict {
    fired: bool,
}

impl Extension for DefinitionBesideConflict {
    fn propagate(&mut self, ctx: &dyn SolverContext) -> ExtPropagateResult {
        if self.fired || ctx.decision_level() == 0 || ctx.value(Variable(0)).is_none() {
            return ExtPropagateResult::none();
        }
        self.fired = true;
        // `v2 ∨ v3` defines nothing the SAT solver can check, but it must
        // survive: the conflict alone would drop plain lemmas.
        ExtPropagateResult::conflict(vec![true_lit(ctx, 0).negated()])
            .with_definitions(vec![vec![pos(2), pos(3)]])
    }
}

/// G1: definitions are added even when the same result carries a conflict.
#[test]
fn definitions_survive_a_conflict_in_the_same_result() {
    let mut solver = Solver::new(2);
    solver.add_clause(vec![pos(0), pos(1)]);
    let before = solver.cold.original_ledger.num_clauses();
    let mut ext = DefinitionBesideConflict { fired: false };
    let result = solver.solve_with_extension(&mut ext).into_inner();
    let SatResult::Sat(model) = result else {
        panic!("expected sat, got {result:?}");
    };
    assert!(ext.fired);
    assert_eq!(solver.cold.original_ledger.num_clauses(), before + 1);
    assert!(model[2] || model[3], "the definition holds in the model");
}

/// Returns, once, a clause whose first literal is false and whose second is
/// a variable the solver does not have yet, plus a request for more.
struct MintInPropagate {
    fired: bool,
}

impl Extension for MintInPropagate {
    fn propagate(&mut self, ctx: &dyn SolverContext) -> ExtPropagateResult {
        if self.fired || ctx.value(Variable(0)) != Some(true) {
            return ExtPropagateResult::none();
        }
        self.fired = true;
        ExtPropagateResult::clause(vec![neg(0), pos(5)]).with_num_vars(10)
    }
}

/// G3: minting in `propagate` is safe. Before G3 the falsified-clause test
/// indexed the assignment with variable 5 and panicked.
#[test]
fn propagate_may_name_variables_the_solver_lacks() {
    let mut solver = Solver::new(2);
    solver.add_clause(vec![pos(0)]);
    solver.add_clause(vec![pos(0), pos(1)]);
    let mut ext = MintInPropagate { fired: false };
    let result = solver.solve_with_extension(&mut ext).into_inner();
    let SatResult::Sat(model) = result else {
        panic!("expected sat, got {result:?}");
    };
    assert!(ext.fired);
    assert!(
        model.len() >= 10,
        "variables requested without a clause exist"
    );
    assert!(model[5], "the minted literal is implied");
    for var in 2..10 {
        assert!(solver.is_frozen(Variable(var)), "var {var} is frozen");
    }
}

/// Redirects the first heuristic decision to `¬v2`; records its level.
struct RedirectFirstDecision {
    redirected: bool,
    level_of_v2: Option<u32>,
}

impl Extension for RedirectFirstDecision {
    fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
        ExtPropagateResult::none()
    }

    fn check(&mut self, ctx: &dyn SolverContext) -> ExtCheckResult {
        if ctx.value(Variable(2)) == Some(false) {
            self.level_of_v2 = ctx.var_level(Variable(2));
        }
        ExtCheckResult::Sat
    }

    fn on_decide(&mut self, _ctx: &dyn SolverContext, _lit: Literal) -> Option<Literal> {
        if self.redirected {
            return None;
        }
        self.redirected = true;
        Some(neg(2))
    }
}

/// G4: `on_decide` replaces the heuristic's pick.
#[test]
fn on_decide_replaces_the_heuristic_pick() {
    let mut solver = Solver::new(3);
    solver.add_clause(vec![pos(0), pos(1), pos(2)]);
    let mut ext = RedirectFirstDecision {
        redirected: false,
        level_of_v2: None,
    };
    let result = solver.solve_with_extension(&mut ext).into_inner();
    let SatResult::Sat(model) = result else {
        panic!("expected sat, got {result:?}");
    };
    assert!(!model[2]);
    assert_eq!(ext.level_of_v2, Some(1), "¬v2 was the first decision");
}

/// Counts learned clauses when asked to.
struct CountLearned {
    wants: bool,
    learned: Vec<usize>,
}

impl Extension for CountLearned {
    fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
        ExtPropagateResult::none()
    }

    fn wants_learned_clauses(&self) -> bool {
        self.wants
    }

    fn on_learned(&mut self, clause: &[Literal]) {
        self.learned.push(clause.len());
    }
}

/// Pigeonhole: `pigeons` pigeons, one fewer holes. Unsat, needs conflicts.
fn pigeonhole(pigeons: u32) -> Solver {
    let holes = pigeons - 1;
    let var = |p: u32, h: u32| p * holes + h;
    let mut solver = Solver::new((pigeons * holes) as usize);
    for p in 0..pigeons {
        solver.add_clause((0..holes).map(|h| pos(var(p, h))).collect());
    }
    for h in 0..holes {
        for p in 0..pigeons {
            for q in p + 1..pigeons {
                solver.add_clause(vec![neg(var(p, h)), neg(var(q, h))]);
            }
        }
    }
    solver
}

/// G4: `on_learned` sees conflict-analysis clauses, only when asked.
#[test]
fn on_learned_sees_learned_clauses_when_asked() {
    let mut ext = CountLearned {
        wants: true,
        learned: Vec::new(),
    };
    let result = pigeonhole(5).solve_with_extension(&mut ext).into_inner();
    assert!(matches!(result, SatResult::Unsat(_)), "{result:?}");
    assert_ne!(ext.learned.len(), 0, "pigeonhole needs learned clauses");
    assert!(ext.learned.iter().all(|&len| len > 0));

    let mut quiet = CountLearned {
        wants: false,
        learned: Vec::new(),
    };
    let result = pigeonhole(5).solve_with_extension(&mut quiet).into_inner();
    assert!(matches!(result, SatResult::Unsat(_)));
    assert_eq!(quiet.learned.len(), 0);
}

/// Reads `search_ticks` at every callback.
struct ReadSearchTicks {
    readings: Vec<u64>,
}

impl Extension for ReadSearchTicks {
    fn propagate(&mut self, ctx: &dyn SolverContext) -> ExtPropagateResult {
        self.readings.push(ctx.search_ticks());
        ExtPropagateResult::none()
    }

    fn check(&mut self, ctx: &dyn SolverContext) -> ExtCheckResult {
        self.readings.push(ctx.search_ticks());
        ExtCheckResult::Sat
    }
}

/// GT-G6 (the development design notes DR-36): the real solver's `search_ticks` is its
/// search-tick count, and it never decreases from one callback to the next,
/// so a caller can charge the change since its previous reading.
#[test]
fn search_ticks_never_decrease_across_callbacks() {
    let mut solver = pigeonhole(7);
    let mut ext = ReadSearchTicks {
        readings: Vec::new(),
    };
    let result = solver.solve_with_extension(&mut ext).into_inner();
    assert!(matches!(result, SatResult::Unsat(_)), "{result:?}");
    let readings = &ext.readings;
    let fall = readings.windows(2).position(|pair| pair[1] < pair[0]);
    assert_eq!(fall, None, "a reading fell at callback {fall:?}");
    let (first, last) = (readings[0], readings[readings.len() - 1]);
    assert!(
        first < last,
        "the search spent ticks between {} callbacks: {first} .. {last}",
        readings.len()
    );
    assert!(last <= solver.total_search_ticks());
}
