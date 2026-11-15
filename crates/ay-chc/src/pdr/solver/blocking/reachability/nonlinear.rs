// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The Spacer lane on NONLINEAR problems (`SpacerLane::nonlinear`,
//! `PdrSolver::lane_nonlinear`): Spacer's `expand_pob` over clauses with any
//! number of body atoms (`spacer_context.cpp`, `pred_transformer::is_reachable`,
//! `context::create_children`, `derivation::create_next_child`).
//!
//! For a POB `(P, φ, k)` and a clause `P(h) ← Q_1(y_1) ∧ … ∧ Q_n(y_n) ∧ T`:
//!
//! 1. **Q1** `T ∧ φ(h) ∧ ∧_i F(Q_i)(y_i)` where `F` is the delta frame at
//!    `k-1` (the may summary) or, at `k-1 = 0`, the disjunction of `Q_i`'s
//!    renamed facts. UNSAT ⇒ the clause's core over `φ`'s literals (C3), and
//!    the lane's `lemma_from_cores` generalises it like any linear clause.
//! 2. **SAT** ⇒ must coverage, atom by atom: an atom whose state in the model
//!    lies in a reach fact (a must summary: a concrete state with a complete
//!    derivation tree) is covered; otherwise one must-extension query
//!    `T ∧ φ(h) ∧ pins(<i) ∧ RF(Q_i)(y_i) ∧ F(>i)` tries to move it onto one.
//!    At `k-1 = 0` every atom is covered by the fact its disjunct names.
//! 3. **All covered** ⇒ the POB is reachable: a new reach fact of `P` (the
//!    head point of the model, premises = the covering facts) is recorded and
//!    the POB returns `BlockResult::MustReachable`; the parent re-queries and
//!    meets it through its own must coverage, the root builds the
//!    counterexample tree from the facts (`build_cex_from_reach_facts`).
//! 4. **First uncovered atom `i`** ⇒ the child POB `(Q_i, MBP(T ∧ φ(h) ∧
//!    pins(<i) ∧ F(>i)), k-1)` from the exact under-approximating free
//!    constructor (Spacer's premise summaries: must before, may after).
//!
//! Soundness: a lemma still needs an observed UNSAT of every defining clause
//! (the cores above, `lemma_from_cores` unchanged); a reach fact is recorded
//! only when a completed model EVALUATES `T ∧ pins ∧ φ(h)` to true, so every
//! reach fact is a genuine derivation, and every counterexample built from
//! them is replayed by the verifier before it is reported.

mod cover;
mod may_summaries;
mod queries;
mod reach_facts;
mod roots;

use super::*;
use crate::pdr::reach_fact::ReachFactId;
use crate::pdr::solver::spacer_core::stats::UnknownClass;
use crate::HornClause;
use may_summaries::AtomHyp;
pub(in crate::pdr::solver) use queries::NlRound;
use reach_facts::complete_model;

/// Per-call cap of the lane's proxied core solves (`lane_clause_core`).
pub(super) const NL_CORE_PER_CALL: std::time::Duration = std::time::Duration::from_millis(400);

/// One clause of the POB's predicate as the lane step sees it.
pub(super) struct NlClause<'a> {
    pub(super) index: usize,
    pub(super) clause: &'a HornClause,
    pub(super) head_args: &'a [ChcExpr],
    /// `T`: the clause constraint (`Bool(true)` when absent).
    pub(super) constraint: &'a ChcExpr,
    /// `φ(h)`: the POB's state on the head arguments.
    pub(super) state_on_head: &'a ChcExpr,
    /// The clause-guarded lemmas on the head (`clause_guarded_constraint`).
    pub(super) guarded: &'a ChcExpr,
}

/// A built Q1 (`nl_build_query`).
struct NlQuery {
    hyps: Vec<AtomHyp>,
    exclusions: Vec<ChcExpr>,
    /// The exclusion-free core background `T ∧ guarded ∧ hyps` (C3).
    background: Vec<ChcExpr>,
    query: ChcExpr,
}

/// `nl_build_query`'s outcome.
enum NlBuilt {
    Query(NlQuery),
    /// An atom has no fact at frame index 0: the clause is vacuously UNSAT.
    Vacuous,
    /// An `apply_to_args` or rename failure (the POB answers `Unknown`).
    Failed,
}

/// The body side of a SAT Q1 query: each atom's may summary and exclusion.
struct NlSat<'a> {
    hyps: &'a [AtomHyp],
    exclusions: &'a [ChcExpr],
}

/// The coverage of a SAT Q1 model (step 2 of the module docs).
struct Coverage {
    /// The model the pins hold in (a must extension replaces the Q1 model).
    model: FxHashMap<String, SmtValue>,
    /// The covering reach fact of each atom.
    chosen: Vec<Option<ReachFactId>>,
    /// Its state on the atom's arguments.
    pins: Vec<Option<ChcExpr>>,
    /// The first atom no reach fact covers.
    first_uncovered: Option<usize>,
}

/// The may summaries and exclusions of the atoms after `i` (the context of
/// atom `i`'s must extension and child).
fn later_summaries<'a>(sat: &'a NlSat<'_>, i: usize) -> impl Iterator<Item = ChcExpr> + 'a {
    sat.hyps
        .iter()
        .zip(sat.exclusions)
        .skip(i + 1)
        .flat_map(|(h, e)| [h.expr.clone(), e.clone()])
}

impl PdrSolver {
    /// The nonlinear lane's predecessor step for ONE clause of `pob`'s
    /// predicate at `pob.level ≥ 1` (module docs). `None` = the clause is
    /// UNSAT (its core is pushed to `cores`) or its SAT model yielded no child
    /// cube (`had_sat_no_cube` set); `Some` = `Reachable` (a child),
    /// `MustReachable` (the POB is reachable) or `Unknown`.
    pub(super) fn nl_check_clause(
        &mut self,
        pob: &ProofObligation,
        unknown_predecessors: &[(usize, PredicateId, ChcExpr)],
        cl: &NlClause<'_>,
        cores: &mut Vec<ClauseCore>,
        had_sat_no_cube: &mut bool,
    ) -> Option<BlockResult> {
        let prev = pob.level - 1;
        self.spacer_stats.nl_q1 += 1;
        let q = match self.nl_build_query(pob, unknown_predecessors, cl, prev) {
            NlBuilt::Query(q) => q,
            NlBuilt::Vacuous => {
                // An atom without a fact at frame index 0: vacuously UNSAT.
                cores.push(ClauseCore {
                    clause_index: cl.index,
                    fact_index: None,
                    core: vec![false; pob.cube().len()],
                    exact: true,
                    had_exclusion: false,
                    uses_level: None,
                });
                return None;
            }
            NlBuilt::Failed => {
                self.pending_unknown_class = Some(UnknownClass::Other);
                return Some(BlockResult::Unknown);
            }
        };
        let result = if matches!(q.query.propagate_equalities(), ChcExpr::Bool(false)) {
            SmtResult::Unsat
        } else {
            let verbose = self.config.verbose;
            self.spacer_stats.smt_solves_total += 1;
            self.smt
                .with_phase_seed_model(pob.smt_model.as_ref(), |smt| {
                    Self::check_sat_with_ite_case_split(smt, verbose, &q.query)
                })
                .0
        };
        match result {
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                let had_exclusion = q
                    .exclusions
                    .iter()
                    .any(|e| !matches!(e, ChcExpr::Bool(true)));
                let core = self.lane_clause_core(
                    pob,
                    cl.index,
                    None,
                    &q.background,
                    cl.head_args,
                    had_exclusion,
                );
                cores.push(core);
                None
            }
            SmtResult::Unknown => {
                self.pending_unknown_class = Some(UnknownClass::SmtUnknown);
                Some(BlockResult::Unknown)
            }
            SmtResult::Sat(model) => {
                self.spacer_stats.nl_q1_sat += 1;
                self.record_reachable_pob_countermodel(pob, cl.head_args, &model);
                // Complete the model on the query's variables so coverage and
                // the child constructor evaluate every atom (kept only when the
                // completed model still satisfies the query).
                let model = match complete_model(&q.query, cl.clause.vars(), &model) {
                    Some(m) if self.mbp.eval_bool(&q.query, &m) == Some(true) => m,
                    _ => model,
                };
                let sat = NlSat {
                    hyps: &q.hyps,
                    exclusions: &q.exclusions,
                };
                let step = self.nl_expand_sat(pob, unknown_predecessors, cl, &sat, prev, model);
                if step.is_none() {
                    *had_sat_no_cube = true;
                    self.telemetry.sat_no_cube_events += 1;
                }
                step
            }
        }
    }

    /// The Q1 of one clause: the atoms' body hypotheses at frame index `prev`,
    /// their exclusions (unknown predecessors at this parent level), the
    /// exclusion-free core background `T ∧ guarded ∧ hyps`, and the query.
    fn nl_build_query(
        &self,
        pob: &ProofObligation,
        unknown_predecessors: &[(usize, PredicateId, ChcExpr)],
        cl: &NlClause<'_>,
        prev: usize,
    ) -> NlBuilt {
        let atoms = &cl.clause.body.predicates;
        let roots = [
            cl.constraint.clone(),
            cl.state_on_head.clone(),
            cl.guarded.clone(),
        ];
        let hyps = match self.lane_body_hyps(atoms, prev, &roots) {
            Some(Some(h)) => h,
            Some(None) => return NlBuilt::Vacuous,
            None => return NlBuilt::Failed,
        };
        let exclusions: Vec<ChcExpr> = atoms
            .iter()
            .map(|(body_pred, body_args)| {
                self.predecessor_exclusion_constraint(
                    "[nonlinear]",
                    pob.level,
                    *body_pred,
                    body_args,
                    unknown_predecessors,
                )
            })
            .collect();
        let mut background: Vec<ChcExpr> = vec![cl.constraint.clone(), cl.guarded.clone()];
        background.extend(hyps.iter().map(|h| h.expr.clone()));
        let query = self
            .bound_int_vars(ChcExpr::and_all(
                background
                    .iter()
                    .cloned()
                    .chain(std::iter::once(cl.state_on_head.clone()))
                    .chain(exclusions.iter().cloned()),
            ))
            .expand_select_store_symbolic();
        NlBuilt::Query(NlQuery {
            hyps,
            exclusions,
            background,
            query,
        })
    }

    /// Steps 2–4 on a SAT Q1 model: coverage, then the reach fact of the POB
    /// (every atom covered) or the child of the first uncovered atom (`None`
    /// when no child cube could be built).
    fn nl_expand_sat(
        &mut self,
        pob: &ProofObligation,
        unknown_predecessors: &[(usize, PredicateId, ChcExpr)],
        cl: &NlClause<'_>,
        sat: &NlSat<'_>,
        prev: usize,
        model: FxHashMap<String, SmtValue>,
    ) -> Option<BlockResult> {
        let key = (
            pob.predicate,
            pob.level,
            pob.state.structural_hash(),
            cl.index,
        );
        let cov = self.nl_cover(prev, cl, sat, model, key);
        let Some(i) = cov.first_uncovered else {
            self.reachability.lane_derivations.remove(&key);
            return Some(self.nl_close_step(pob, cl, &cov));
        };
        let child = self.nl_child(pob, unknown_predecessors, cl, sat, &cov, i);
        if child.is_some() {
            let prefix: Vec<ReachFactId> = cov.chosen.iter().take(i).flatten().copied().collect();
            self.reachability.lane_derivations.insert(key, prefix);
        }
        child
    }

    /// Step 3: every atom covered — record the reach fact of the POB's
    /// predicate through this clause (`MustReachable`), or `Unknown` when the
    /// completed model does not evaluate the step.
    fn nl_close_step(
        &mut self,
        pob: &ProofObligation,
        cl: &NlClause<'_>,
        cov: &Coverage,
    ) -> BlockResult {
        let premises: Vec<ReachFactId> = cov.chosen.iter().flatten().copied().collect();
        let mut step: Vec<ChcExpr> = vec![cl.constraint.clone(), cl.state_on_head.clone()];
        step.extend(cov.pins.iter().flatten().cloned());
        let step = ChcExpr::and_all(step);
        match self.nl_record_reach_fact(
            pob.predicate,
            cl.index,
            cl.clause,
            cl.head_args,
            &step,
            &cov.model,
            premises,
        ) {
            Some(id) => BlockResult::MustReachable(id),
            None => {
                self.spacer_stats.nl_rf_fail += 1;
                self.pending_unknown_class = Some(UnknownClass::Other);
                BlockResult::Unknown
            }
        }
    }

    /// Step 4: the child POB for the first uncovered atom `i`; the other
    /// atoms contribute their must pin when the model covers them, their may
    /// summary otherwise. `None` when even the point fallback yields no cube.
    fn nl_child(
        &mut self,
        pob: &ProofObligation,
        unknown_predecessors: &[(usize, PredicateId, ChcExpr)],
        cl: &NlClause<'_>,
        sat: &NlSat<'_>,
        cov: &Coverage,
        i: usize,
    ) -> Option<BlockResult> {
        let atoms = &cl.clause.body.predicates;
        let (child_pred, child_args) = &atoms[i];
        // The context the must extension of atom `i` uses: the earlier atoms'
        // pins and the later atoms' may summaries, so a reach fact inside the
        // child extends to that query (the MBP under-approximates it).
        let mut context: Vec<ChcExpr> = vec![cl.constraint.clone()];
        context.extend(cov.pins.iter().take(i).flatten().cloned());
        context.extend(later_summaries(sat, i));
        let context = ChcExpr::and_all(context);
        let excluded = Self::excluded_states(pob.level, *child_pred, unknown_predecessors);
        let child = self.child_cube_from_model(
            *child_pred,
            child_args,
            &context,
            cl.state_on_head,
            &cov.model,
            Some(&sat.exclusions[i]),
            &excluded,
        );
        self.spacer_stats
            .record_free_child(child.source, child.substituted, &child.exact);
        let cube = child.cube?;
        self.spacer_stats.nl_children += 1;
        Some(BlockResult::Reachable(Box::new(PredecessorState {
            predicate: *child_pred,
            state: cube.expr().clone(),
            clause_index: cl.index,
            smt_model: cov.model.clone(),
            derivation_id: None,
            lits: Some(cube),
        })))
    }
}
