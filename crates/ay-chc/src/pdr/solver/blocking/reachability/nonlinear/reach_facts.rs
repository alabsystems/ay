// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Reach facts of the nonlinear Spacer lane: point states of a predicate with
//! a complete derivation tree (a fact clause, or a clause step over earlier
//! lane facts), recorded only after a completed model evaluates the step, and
//! the lane's must summaries (`blocking/reachability/nonlinear.rs`).

use super::super::*;
use crate::pdr::cube;
use crate::pdr::reach_fact::{ReachFact, ReachFactId};
use crate::pdr::types::StrengthenResult;
use crate::{ChcSort, HornClause};

/// Reach facts per predicate offered to one must-extension query (newest first).
const MUST_EXT_MAX_FACTS: usize = 64;

/// The default value of a sort for a variable the SMT model left unassigned
/// (the query does not constrain it; the completed model is re-evaluated).
fn default_value(sort: &ChcSort) -> Option<SmtValue> {
    match sort {
        ChcSort::Int => Some(SmtValue::Int(0)),
        ChcSort::Bool => Some(SmtValue::Bool(false)),
        ChcSort::Real => Some(SmtValue::Real(num_rational::BigRational::from_integer(
            num_bigint::BigInt::from(0),
        ))),
        _ => None,
    }
}

/// `canon = value` as a point literal (`c` / `¬c` for Booleans).
fn point_literal(canon: &crate::ChcVar, value: ChcExpr) -> ChcExpr {
    match value {
        ChcExpr::Bool(true) => ChcExpr::var(canon.clone()),
        ChcExpr::Bool(false) => ChcExpr::not(ChcExpr::var(canon.clone())),
        v => ChcExpr::eq(ChcExpr::var(canon.clone()), v),
    }
}

/// `model` completed on the variables of `formula` (and `extra`): values
/// implied by its equalities first, then sort defaults for the variables the
/// solver left unassigned (the formula does not constrain them after its own
/// simplification). `None` when a variable of an unsupported sort is missing.
/// Callers re-evaluate the formula on the result before relying on it.
pub(super) fn complete_model(
    formula: &ChcExpr,
    extra: impl IntoIterator<Item = crate::ChcVar>,
    model: &FxHashMap<String, SmtValue>,
) -> Option<FxHashMap<String, SmtValue>> {
    let mut m = model.clone();
    cube::augment_model_from_equalities(formula, &mut m);
    for v in formula.vars().into_iter().chain(extra) {
        if !m.contains_key(&v.name) {
            m.insert(v.name.clone(), default_value(&v.sort)?);
        }
    }
    Some(m)
}

impl PdrSolver {
    /// The lane's reach facts of `pred` (newest first, at most
    /// `MUST_EXT_MAX_FACTS`) with their states applied to `args`.
    pub(super) fn nl_reach_candidates(
        &self,
        pred: PredicateId,
        args: &[ChcExpr],
    ) -> Vec<(ReachFactId, ChcExpr)> {
        let Some(ids) = self.reachability.lane_facts.get(&pred) else {
            return Vec::new();
        };
        ids.iter()
            .rev()
            .take(MUST_EXT_MAX_FACTS)
            .filter_map(|id| {
                let rf = self.reachability.reach_facts.get(*id)?;
                let pin = self.apply_to_args(pred, &rf.state, args)?;
                Some((*id, pin))
            })
            .collect()
    }

    /// The reach fact of `pred` at the point `args(model)` derived by the fact
    /// clause `fact_index` (instances in the fact clause's own names), and its
    /// state on `args`. Reuses an existing lane fact at the same point.
    pub(in crate::pdr::solver) fn nl_fact_reach_fact(
        &mut self,
        pred: PredicateId,
        args: &[ChcExpr],
        model: &FxHashMap<String, SmtValue>,
        fact_index: usize,
    ) -> Option<(ReachFactId, ChcExpr)> {
        let fact = self.problem.clauses().get(fact_index)?.clone();
        let crate::ClauseHead::Predicate(_, fact_head_args) = &fact.head else {
            return None;
        };
        // The point: the atom's argument values under the model.
        let mut values: Vec<SmtValue> = Vec::with_capacity(args.len());
        for a in args {
            values.push(crate::expr::evaluate_expr(a, model)?);
        }
        let canon = self.canonical_vars(pred)?.to_vec();
        if canon.len() != args.len() || fact_head_args.len() != args.len() {
            return None;
        }
        let mut point_model: FxHashMap<String, SmtValue> = FxHashMap::default();
        for (c, v) in canon.iter().zip(values.iter()) {
            point_model.insert(c.name.clone(), v.clone());
        }
        let mut lits = Vec::with_capacity(canon.len());
        for c in &canon {
            lits.push(point_literal(
                c,
                crate::mbp::Mbp::value_expr_for(c, &point_model)?,
            ));
        }
        let state = ChcExpr::and_all(lits);
        let pin = self.apply_to_args(pred, &state, args)?;
        if let Some(id) = self
            .reachability
            .lane_fact_index
            .get(&(pred, state.clone()))
        {
            return Some((*id, pin));
        }
        // The fact clause's own witness: its constraint with the head pinned.
        let fact_constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
        let mut parts = vec![fact_constraint.clone()];
        for (h, c) in fact_head_args.iter().zip(canon.iter()) {
            parts.push(ChcExpr::eq(
                h.clone(),
                crate::mbp::Mbp::value_expr_for(c, &point_model)?,
            ));
        }
        let fact_query = ChcExpr::and_all(parts);
        let q = self.bound_int_vars(fact_query.clone());
        self.smt.reset();
        self.spacer_stats.smt_solves_total += 1;
        let verbose = self.config.verbose;
        let (res, _) = Self::check_sat_with_ite_case_split(&mut self.smt, verbose, &q);
        let SmtResult::Sat(fact_model) = res else {
            return None;
        };
        let id = self.nl_record_reach_fact(
            pred,
            fact_index,
            &fact,
            fact_head_args,
            &fact_query,
            &fact_model,
            Vec::new(),
        )?;
        Some((id, pin))
    }

    /// Record the reach fact of `pred` derived by `clause` under `model`: the
    /// model is completed (equalities of `step`, then sort defaults for the
    /// variables it leaves free) and must EVALUATE `step` (the derivation step:
    /// `T ∧ pins ∧ φ(h)`) to true; the fact is the head point, its instances
    /// the completed model on the clause's variables plus the canonical head
    /// values. `None` when the step does not evaluate (no fact is recorded).
    pub(super) fn nl_record_reach_fact(
        &mut self,
        pred: PredicateId,
        clause_index: usize,
        clause: &HornClause,
        head_args: &[ChcExpr],
        step: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
        premises: Vec<ReachFactId>,
    ) -> Option<ReachFactId> {
        let canon = self.canonical_vars(pred)?.to_vec();
        if canon.len() != head_args.len() {
            return None;
        }
        let m = complete_model(
            step,
            head_args
                .iter()
                .flat_map(ChcExpr::vars)
                .chain(clause.vars()),
            model,
        )?;
        if self.mbp.eval_bool(step, &m) != Some(true) {
            tracing::debug!(
                pred = pred.index(),
                clause = clause_index,
                "PDR-SPACER: nl reach fact step does not evaluate; none recorded"
            );
            return None;
        }
        let mut instances: FxHashMap<String, SmtValue> = FxHashMap::default();
        for v in clause.vars() {
            if let Some(val) = m.get(&v.name) {
                instances.insert(v.name.clone(), val.clone());
            }
        }
        let mut lits = Vec::with_capacity(canon.len());
        for (c, a) in canon.iter().zip(head_args) {
            let val = crate::expr::evaluate_expr(a, &m)?;
            instances.insert(c.name.clone(), val);
            lits.push(point_literal(
                c,
                crate::mbp::Mbp::value_expr_for(c, &instances)?,
            ));
        }
        let state = ChcExpr::and_all(lits);
        if let Some(id) = self
            .reachability
            .lane_fact_index
            .get(&(pred, state.clone()))
        {
            return Some(*id);
        }
        let level = premises
            .iter()
            .filter_map(|p| self.reachability.reach_facts.get(*p).map(|r| r.level))
            .max()
            .map_or(0, |l| l + 1);
        tracing::debug!(
            pred = pred.index(),
            level,
            clause = clause_index,
            premises = premises.len(),
            state = %state,
            "PDR-SPACER: nl reach fact"
        );
        let id = Self::insert_reach_fact_bounded(
            &mut self.reachability,
            self.config.verbose,
            ReachFact {
                id: ReachFactId(0),
                predicate: pred,
                level,
                state: state.clone(),
                incoming_clause: Some(clause_index),
                premises,
                instances,
            },
        )?;
        self.register_lane_reach_fact(pred, state, id);
        Some(id)
    }

    /// Index a reach fact as the lane's must summary of `pred` (lane facts and
    /// the reach solver, whose matches become reach-fact trees). NOT the
    /// legacy `must_summaries`: their hyperedge shortcuts
    /// (`check_hyperedge_unsafe`) turn every summary into an AXIOM witness
    /// entry, which a derived (non-fact) state cannot justify.
    pub(in crate::pdr::solver) fn register_lane_reach_fact(
        &mut self,
        pred: PredicateId,
        state: ChcExpr,
        id: ReachFactId,
    ) {
        self.spacer_stats.nl_reach_facts += 1;
        self.reachability
            .lane_fact_index
            .insert((pred, state.clone()), id);
        self.reachability
            .lane_facts
            .entry(pred)
            .or_default()
            .push(id);
        self.reachability.reach_solvers.add_backed(pred, id, state);
    }

    /// A POB the nonlinear lane proved reachable (reach fact `rf_id` lies in
    /// it). A child closes (its parent, queued behind it, re-queries and meets
    /// the fact through its must coverage); a query-derived root is a
    /// counterexample, built as the reach-fact tree (the verifier replays it
    /// before it is reported). `Some(result)` ⇒ `strengthen` returns it.
    pub(in crate::pdr::solver) fn nl_reachable_pob(
        &mut self,
        pob: &ProofObligation,
        rf_id: ReachFactId,
        query_derived: bool,
    ) -> Option<StrengthenResult> {
        self.spacer_stats.nl_must_reachable += 1;
        tracing::debug!(
            pred = pob.predicate.index(),
            level = pob.level,
            root = pob.parent.is_none(),
            "PDR-SPACER: nl POB reachable"
        );
        if pob.is_may() || pob.parent.is_some() || !query_derived {
            return None;
        }
        // The ground derivation through the query clause when it can be
        // built; the reach-fact witness alone otherwise.
        let cex = match pob.query_clause {
            Some(qi) => self
                .nl_query_cex(qi, &[rf_id])
                .or_else(|| self.build_cex_from_reach_facts(rf_id, Some(qi))),
            None => self.build_cex_from_reach_facts(rf_id, None),
        };
        Some(cex.map_or(StrengthenResult::Unknown, StrengthenResult::Unsafe))
    }
}
