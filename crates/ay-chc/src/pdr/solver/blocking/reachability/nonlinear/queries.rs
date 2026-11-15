// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Queries and counterexamples of the nonlinear Spacer lane.
//!
//! * A query clause with several body atoms (`P(x) ∧ Q(y) ∧ φ → false`)
//!   has no root POB (a root is one predicate's state). Spacer treats it as
//!   the only rule of a virtual error predicate; here one query step per
//!   strengthen round does the same: `φ ∧ ∧_i F_k(Q_i)(y_i)` UNSAT blocks the
//!   query at level `k`, SAT covers the atoms by reach facts and either
//!   proves the query reachable or yields the child POB of the first
//!   uncovered atom (a root: no parent, re-examined by the next step).
//! * Every counterexample the lane finds carries a GROUND derivation of
//!   `false` built from its reach facts: each reach fact is a clause instance
//!   under a total assignment whose premises are the facts that cover its
//!   body atoms, so the tree replays through
//!   `ground_derivation::validate_ground_derivation` — whatever the shape of
//!   the query (the derivation-witness check covers single-body queries
//!   only).

use super::super::*;
use super::reach_facts::complete_model;
use super::{later_summaries, Coverage, NlClause, NlSat};
use crate::ground_derivation::{GroundDerivation, GroundDerivationStep};
use crate::pdr::counterexample::Counterexample;
use crate::pdr::reach_fact::ReachFactId;
use crate::pdr::types::StrengthenResult;
use crate::HornClause;

/// A multi-atom query child produced more often than this ends its step
/// Unknown (a step that makes no progress).
const NL_QUERY_CHILD_REPEATS: usize = 64;

/// One step of a multi-atom query (`nl_hyper_query_step`).
enum NlQueryStep {
    /// `φ ∧ ∧ F_k` is UNSAT: the query is blocked at this level.
    Blocked,
    /// Every atom is covered: the query is reachable.
    Cex(Counterexample),
    /// The child POB of the first uncovered atom.
    Child(ProofObligation),
    /// The step could not decide.
    Unknown,
}

/// One round of multi-atom query steps (`nl_query_round`).
pub(in crate::pdr::solver) enum NlRound {
    /// The child POBs to queue (none: every multi-atom query is blocked).
    Children(Vec<ProofObligation>),
    /// `strengthen` returns this (a counterexample, or an undecided step).
    Done(StrengthenResult),
}

impl PdrSolver {
    /// One query step per multi-atom query clause (called when the POB queue
    /// drains): the children of the unblocked ones, or the strengthen result
    /// a counterexample / an undecided step ends the round with.
    pub(in crate::pdr::solver) fn nl_query_round(
        &mut self,
        queries: &[(usize, HornClause)],
        level: usize,
    ) -> NlRound {
        let mut children = Vec::new();
        for (qi, q) in queries {
            if self.is_cancelled() {
                return NlRound::Done(StrengthenResult::Unknown);
            }
            match self.nl_hyper_query_step(*qi, q, level) {
                NlQueryStep::Blocked => {}
                NlQueryStep::Child(child) => children.push(child),
                NlQueryStep::Cex(cex) => return NlRound::Done(StrengthenResult::Unsafe(cex)),
                NlQueryStep::Unknown => {
                    // As an unblockable root POB: a deeper bound may still decide.
                    return NlRound::Done(
                        if self.config.use_must_summaries && !self.obligations.overflowed {
                            StrengthenResult::Continue
                        } else {
                            StrengthenResult::Unknown
                        },
                    );
                }
            }
        }
        NlRound::Children(children)
    }

    /// One step of the multi-atom query clause `qi` at `level` (module docs).
    fn nl_hyper_query_step(&mut self, qi: usize, query: &HornClause, level: usize) -> NlQueryStep {
        let constraint = query.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
        let truth = ChcExpr::Bool(true);
        let cl = NlClause {
            index: qi,
            clause: query,
            head_args: &[],
            constraint: &constraint,
            state_on_head: &truth,
            guarded: &truth,
        };
        let atoms = &query.body.predicates;
        let hyps = match self.lane_body_hyps(atoms, level, std::slice::from_ref(&constraint)) {
            Some(Some(h)) => h,
            Some(None) => return NlQueryStep::Blocked,
            None => return NlQueryStep::Unknown,
        };
        let exclusions = vec![ChcExpr::Bool(true); atoms.len()];
        let q = self
            .bound_int_vars(ChcExpr::and_all(
                std::iter::once(constraint.clone()).chain(hyps.iter().map(|h| h.expr.clone())),
            ))
            .expand_select_store_symbolic();
        self.spacer_stats.nl_q1 += 1;
        let result = if matches!(q.propagate_equalities(), ChcExpr::Bool(false)) {
            SmtResult::Unsat
        } else {
            self.spacer_stats.smt_solves_total += 1;
            let verbose = self.config.verbose;
            Self::check_sat_with_ite_case_split(&mut self.smt, verbose, &q).0
        };
        let model = match result {
            SmtResult::Sat(m) => m,
            SmtResult::Unknown => return NlQueryStep::Unknown,
            _ => return NlQueryStep::Blocked,
        };
        self.spacer_stats.nl_q1_sat += 1;
        let model = match complete_model(&q, query.vars(), &model) {
            Some(m) if self.mbp.eval_bool(&q, &m) == Some(true) => m,
            _ => model,
        };
        let sat = NlSat {
            hyps: &hyps,
            exclusions: &exclusions,
        };
        // The derivation memo of a query step is keyed by the query clause.
        let key = (PredicateId::new(u32::MAX), level, 0, qi);
        let cov = self.nl_cover(level, &cl, &sat, model, key);
        match cov.first_uncovered {
            None => {
                let rfs: Vec<ReachFactId> = cov.chosen.iter().flatten().copied().collect();
                match self.nl_query_cex(qi, &rfs) {
                    Some(cex) => NlQueryStep::Cex(cex),
                    None => NlQueryStep::Unknown,
                }
            }
            Some(i) => {
                let step = self.nl_query_child(&cl, &sat, &cov, i, level);
                if matches!(step, NlQueryStep::Child(_)) {
                    let prefix: Vec<ReachFactId> =
                        cov.chosen.iter().take(i).flatten().copied().collect();
                    self.reachability.lane_derivations.insert(key, prefix);
                }
                step
            }
        }
    }

    /// The root child of atom `i` of a multi-atom query (context: the earlier
    /// atoms' pins, the later atoms' may summaries).
    fn nl_query_child(
        &mut self,
        cl: &NlClause<'_>,
        sat: &NlSat<'_>,
        cov: &Coverage,
        i: usize,
        level: usize,
    ) -> NlQueryStep {
        let (pred, args) = &cl.clause.body.predicates[i];
        let mut context: Vec<ChcExpr> = vec![cl.constraint.clone()];
        context.extend(cov.pins.iter().take(i).flatten().cloned());
        context.extend(later_summaries(sat, i));
        let context = ChcExpr::and_all(context);
        let child = self.child_cube_from_model(
            *pred,
            args,
            &context,
            &ChcExpr::Bool(true),
            &cov.model,
            None,
            &[],
        );
        self.spacer_stats
            .record_free_child(child.source, child.substituted, &child.exact);
        let Some(cube) = child.cube else {
            return NlQueryStep::Unknown;
        };
        // A child the query keeps producing is a step without progress.
        let repeats = self
            .reachability
            .lane_query_children
            .entry((cl.index, level, *pred, cube.expr().structural_hash()))
            .or_insert(0);
        *repeats += 1;
        if *repeats > NL_QUERY_CHILD_REPEATS {
            return NlQueryStep::Unknown;
        }
        self.spacer_stats.nl_children += 1;
        let mut pob = ProofObligation::new(*pred, cube.expr().clone(), level)
            .with_smt_model(cov.model.clone());
        pob.lits = Some(std::sync::Arc::new(cube));
        NlQueryStep::Child(pob)
    }

    /// The counterexample of query clause `qi` whose body atoms are covered by
    /// the reach facts `rfs` (in body order): the reach-fact tree of the first
    /// atom as the derivation witness plus the ground derivation of `false`
    /// through all of them (`None` when no total query instance is found).
    pub(in crate::pdr::solver) fn nl_query_cex(
        &mut self,
        qi: usize,
        rfs: &[ReachFactId],
    ) -> Option<Counterexample> {
        let ground = self.nl_ground_derivation(qi, rfs)?;
        let mut cex = self.build_cex_from_reach_facts(*rfs.first()?, Some(qi))?;
        cex.ground_derivation = Some(ground);
        self.spacer_stats.nl_cex += 1;
        Some(cex)
    }

    /// The ground derivation of `false` through query clause `qi` over the
    /// reach facts `rfs` (one per body atom, in body order): the facts' trees
    /// in topological order, then the query instance, whose total assignment
    /// comes from one solve of `φ ∧ args_i = point_i` (re-evaluated).
    fn nl_ground_derivation(&mut self, qi: usize, rfs: &[ReachFactId]) -> Option<GroundDerivation> {
        let query = self.problem.clauses().get(qi)?.clone();
        if query.body.predicates.len() != rfs.len() {
            return None;
        }
        let mut pins = Vec::with_capacity(rfs.len());
        for ((pred, args), id) in query.body.predicates.iter().zip(rfs) {
            let rf = self.reachability.reach_facts.get(*id)?;
            pins.push(self.apply_to_args(*pred, &rf.state, args)?);
        }
        let constraint = query.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
        let instance = ChcExpr::and_all(std::iter::once(constraint).chain(pins));
        self.smt.reset();
        self.spacer_stats.smt_solves_total += 1;
        let verbose = self.config.verbose;
        let q = self.bound_int_vars(instance.clone());
        let SmtResult::Sat(model) =
            Self::check_sat_with_ite_case_split(&mut self.smt, verbose, &q).0
        else {
            return None;
        };
        let env = complete_model(&instance, query.vars(), &model)?;
        if self.mbp.eval_bool(&instance, &env) != Some(true) {
            return None;
        }
        let mut steps: Vec<GroundDerivationStep> = Vec::new();
        let mut index: FxHashMap<ReachFactId, usize> = FxHashMap::default();
        let mut premises = Vec::with_capacity(rfs.len());
        for id in rfs {
            premises.push(self.nl_emit_ground_steps(*id, &mut steps, &mut index)?);
        }
        steps.push(GroundDerivationStep {
            clause_index: qi,
            env: clause_env(&query, &env)?,
            premises,
        });
        Some(GroundDerivation {
            query_step: steps.len() - 1,
            steps,
        })
    }

    /// Emit reach fact `id`'s tree (premises first) into `steps`; its step index.
    fn nl_emit_ground_steps(
        &self,
        id: ReachFactId,
        steps: &mut Vec<GroundDerivationStep>,
        index: &mut FxHashMap<ReachFactId, usize>,
    ) -> Option<usize> {
        // Iterative post-order (derivations can be deep).
        let mut stack: Vec<(ReachFactId, bool)> = vec![(id, false)];
        while let Some((rf_id, expanded)) = stack.pop() {
            if index.contains_key(&rf_id) {
                continue;
            }
            let rf = self.reachability.reach_facts.get(rf_id)?;
            if !expanded {
                stack.push((rf_id, true));
                for p in rf.premises.iter().rev() {
                    if !index.contains_key(p) {
                        stack.push((*p, false));
                    }
                }
                continue;
            }
            let clause_index = rf.incoming_clause?;
            let clause = self.problem.clauses().get(clause_index)?;
            let mut premise_steps = Vec::with_capacity(rf.premises.len());
            for p in &rf.premises {
                premise_steps.push(*index.get(p)?);
            }
            steps.push(GroundDerivationStep {
                clause_index,
                env: clause_env(clause, &rf.instances)?,
                premises: premise_steps,
            });
            index.insert(rf_id, steps.len() - 1);
        }
        index.get(&id).copied()
    }
}

/// `model` restricted to the variables of `clause` (all of them bound).
fn clause_env(
    clause: &HornClause,
    model: &FxHashMap<String, SmtValue>,
) -> Option<FxHashMap<String, SmtValue>> {
    let mut env = FxHashMap::default();
    for v in clause.vars() {
        env.insert(v.name.clone(), model.get(&v.name)?.clone());
    }
    Some(env)
}
