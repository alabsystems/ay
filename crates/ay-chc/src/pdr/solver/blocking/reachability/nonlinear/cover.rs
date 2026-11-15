// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Must coverage of the nonlinear Spacer lane: each body atom of a SAT query
//! moved onto a reach fact (the model already in one, a must-extension query,
//! or a recorded derivation resumed), in body order
//! (`blocking/reachability/nonlinear.rs`, step 2).

use super::super::*;
use super::reach_facts::complete_model;
use super::{later_summaries, Coverage, NlClause, NlSat};
use crate::pdr::reach_fact::ReachFactId;

impl PdrSolver {
    /// Step 2: cover the atoms of a SAT Q1 model by reach facts, in order.
    pub(super) fn nl_cover(
        &mut self,
        prev: usize,
        cl: &NlClause<'_>,
        sat: &NlSat<'_>,
        model: FxHashMap<String, SmtValue>,
        key: (PredicateId, usize, u64, usize),
    ) -> Coverage {
        let hyps = sat.hyps;
        let atoms = &cl.clause.body.predicates;
        let n = atoms.len();
        let mut cov = Coverage {
            model,
            chosen: vec![None; n],
            pins: vec![None; n],
            first_uncovered: None,
        };
        let mut start = 0;
        if prev >= 1 {
            if let Some(prefix) = self.reachability.lane_derivations.get(&key).cloned() {
                match self.nl_resume(cl, sat, &prefix, &mut cov) {
                    Some(next) => start = next,
                    None => {
                        self.reachability.lane_derivations.remove(&key);
                    }
                }
            }
        }
        for i in start..n {
            let (pred, args) = &atoms[i];
            let covered = if prev == 0 {
                // Every atom sits in one of its facts: cover it by that fact.
                hyps[i]
                    .facts
                    .iter()
                    .find(|(_, d)| self.mbp.eval_bool(d, &cov.model) == Some(true))
                    .map(|(fi, _)| *fi)
                    .and_then(|fi| self.nl_fact_reach_fact(*pred, args, &cov.model, fi))
            } else {
                self.nl_must_cover(i, cl, sat, &mut cov)
            };
            match covered {
                Some((id, pin)) => {
                    cov.chosen[i] = Some(id);
                    cov.pins[i] = Some(pin);
                }
                None => {
                    cov.first_uncovered = Some(i);
                    break;
                }
            }
        }
        cov
    }

    /// Cover atom `i` (frame index ≥ 1) by a lane reach fact: one the model
    /// already lies in, or else one a must-extension query `T ∧ φ(h) ∧
    /// pins(<i) ∧ RF(Q_i)(y_i) ∧ F(>i) ∧ excl(>i)` reaches (its model then
    /// replaces `cov.model`; the earlier pins hold in it by construction).
    fn nl_must_cover(
        &mut self,
        i: usize,
        cl: &NlClause<'_>,
        sat: &NlSat<'_>,
        cov: &mut Coverage,
    ) -> Option<(ReachFactId, ChcExpr)> {
        let atoms = &cl.clause.body.predicates;
        let (pred, args) = &atoms[i];
        let cands = self.nl_reach_candidates(*pred, args);
        if cands.is_empty() {
            return None;
        }
        if let Some(hit) = cands
            .iter()
            .find(|(_, pin)| self.mbp.eval_bool(pin, &cov.model) == Some(true))
        {
            return Some(hit.clone());
        }
        // The later atoms keep their may summaries (and exclusions): the model
        // a later child is projected from must lie in its frame, or the child
        // is a state its frame already excludes and the parent never moves on.
        let mut parts: Vec<ChcExpr> = vec![cl.constraint.clone(), cl.state_on_head.clone()];
        parts.extend(cov.pins.iter().take(i).flatten().cloned());
        parts.push(ChcExpr::or_all(cands.iter().map(|(_, p)| p.clone())));
        parts.extend(later_summaries(sat, i));
        let q = self
            .bound_int_vars(ChcExpr::and_all(parts))
            .expand_select_store_symbolic();
        self.spacer_stats.nl_must_ext += 1;
        self.spacer_stats.smt_solves_total += 1;
        let verbose = self.config.verbose;
        let SmtResult::Sat(m2) = Self::check_sat_with_ite_case_split(&mut self.smt, verbose, &q).0
        else {
            return None;
        };
        let m2 = match complete_model(&q, cl.clause.vars(), &m2) {
            Some(m) if self.mbp.eval_bool(&q, &m) == Some(true) => m,
            _ => m2,
        };
        let hit = cands
            .iter()
            .find(|(_, pin)| self.mbp.eval_bool(pin, &m2) == Some(true))?
            .clone();
        self.spacer_stats.nl_must_ext_sat += 1;
        cov.model = m2;
        Some(hit)
    }

    /// Resume a recorded derivation (`lane_derivations`): the prefix atoms
    /// pinned to their recorded reach facts, the next atom moved onto one of
    /// its reach facts by one must-extension query. `Some(j + 1)` = the first
    /// atom still to cover; `None` = the prefix no longer extends (the caller
    /// covers afresh).
    fn nl_resume(
        &mut self,
        cl: &NlClause<'_>,
        sat: &NlSat<'_>,
        prefix: &[ReachFactId],
        cov: &mut Coverage,
    ) -> Option<usize> {
        let atoms = &cl.clause.body.predicates;
        let j = prefix.len();
        if j >= atoms.len() {
            return None;
        }
        let mut pins = Vec::with_capacity(j);
        for ((pred, args), id) in atoms.iter().zip(prefix) {
            let rf = self.reachability.reach_facts.get(*id)?;
            pins.push(self.apply_to_args(*pred, &rf.state, args)?);
        }
        let (pred_j, args_j) = &atoms[j];
        let cands = self.nl_reach_candidates(*pred_j, args_j);
        if cands.is_empty() {
            return None;
        }
        let mut parts: Vec<ChcExpr> = vec![cl.constraint.clone(), cl.state_on_head.clone()];
        parts.extend(pins.iter().cloned());
        parts.push(ChcExpr::or_all(cands.iter().map(|(_, p)| p.clone())));
        parts.extend(later_summaries(sat, j));
        let q = self
            .bound_int_vars(ChcExpr::and_all(parts))
            .expand_select_store_symbolic();
        self.spacer_stats.nl_must_ext += 1;
        self.spacer_stats.smt_solves_total += 1;
        let verbose = self.config.verbose;
        let SmtResult::Sat(m2) = Self::check_sat_with_ite_case_split(&mut self.smt, verbose, &q).0
        else {
            return None;
        };
        let m2 = match complete_model(&q, cl.clause.vars(), &m2) {
            Some(m) if self.mbp.eval_bool(&q, &m) == Some(true) => m,
            _ => m2,
        };
        let (id_j, pin_j) = cands
            .iter()
            .find(|(_, pin)| self.mbp.eval_bool(pin, &m2) == Some(true))?
            .clone();
        if pins
            .iter()
            .any(|p| self.mbp.eval_bool(p, &m2) != Some(true))
        {
            return None;
        }
        self.spacer_stats.nl_must_ext_sat += 1;
        for (i, (id, pin)) in prefix.iter().zip(pins).enumerate() {
            cov.chosen[i] = Some(*id);
            cov.pins[i] = Some(pin);
        }
        cov.chosen[j] = Some(id_j);
        cov.pins[j] = Some(pin_j);
        cov.model = m2;
        Some(j + 1)
    }
}
