// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Forward re-concretisation of a counterexample chain before `build_cex`
//! (`DESIGN` §3.6, §4.1.5, decision D3; contract C6). Owner: **WP-B1-P**.
//!
//! `verify_counterexample_premise_head_alignment` pins each premise head to
//! its recorded instances and compares position-wise with the parent's body
//! values; free-variable POBs (R2) would make every such chain `Spurious`.
//! This walk re-solves each incoming clause with its body pinned to the
//! previous step's head values and replaces the chain's `smt_model`s — the
//! verifier's DECISION is untouched (S1). `strengthen.rs` calls it on every
//! level-0 hit, lane on or off: legacy child cubes are not always points
//! either (a non-point cube made the default configuration lose a real
//! counterexample to the spurious-cex limit, `model/cex_wiring_tests.rs`); a
//! failure is counted and the caller keeps today's chain.
//!
//! Chain layout (from `strengthen.rs` child creation): node `i` carries
//! `incoming_clause = c_i` (the clause that derived it from node `i-1`) and
//! `smt_model = m_i` (the Q1 model of THAT clause, in `c_i`'s variable
//! names); the leaf (`i = 0`, level 0) carries the fact clause and the fact
//! model. `build_cex` copies every `smt_model` verbatim into the witness
//! entry's `instances`, so the models produced here are in clause names too.
//!
//! Step `i` solves `T_{c_i} ∧ (body_args_i = s_{i-1}) ∧ state_i(head_args_i)`
//! — no frame, no exclusions — and sets `s_i := head_args_i` under the model.
//! When the recorded model already satisfies that query (every pinned cube in
//! R1) it is kept as is: the walk is then a no-op in effect and costs no
//! solve. INV-P (`child ⊆ ∃post.(T ∧ post)`, `model ⊨ child`) guarantees SAT;
//! an UNSAT step is the second INV-P detector (`cex_concretize_fail_unsat`).

use crate::pdr::solver::{
    ChcExpr, ChcSort, FxHashMap, PdrSolver, ProofObligation, SmtResult, SmtValue,
};
use crate::smt::ScopedSmtDeadline;

/// Why the walk stopped (`cex_concretize_fail` counters).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::pdr::solver) enum ConcretizeFail {
    /// Step `step`'s query was UNSAT (INV-P violated upstream).
    Unsat { step: usize },
    /// Step `step`'s query was Unknown (deadline / theory), or the node could
    /// not be re-solved at all (no incoming clause, uninstantiable state,
    /// unrepresentable pin value).
    Unknown { step: usize },
    /// A hyperedge incoming clause stops the walk; nonlinear chains keep today's models.
    Hyperedge { step: usize },
}

/// Head values of one step: `s_i[j]` = `head_args_i[j]` under the step's
/// model (`None` when the head term does not evaluate).
type HeadValues = Vec<Option<SmtValue>>;

impl PdrSolver {
    /// C6. Input: the level-0 leaf with `incoming_clause` (a fact) and
    /// `smt_model` (the fact model) and its parent chain. Walks root-ward:
    /// `s_0` = head values of the leaf's fact clause under its model; for node
    /// `i ≥ 1` with single-body incoming clause `c_i`: solve
    /// `T_{c_i} ∧ (body_args_i = s_{i-1}) ∧ state_i(head_args_i)` [no frame,
    /// no exclusions] under the scoped deadline; SAT ⇒ replace node `i`'s
    /// `smt_model` by the model, `s_i` := head values. Returns the rebuilt
    /// chain (same `state`s, levels, clauses, kinds) or the first failure with
    /// the ORIGINAL chain (no model is replaced unless every step succeeded).
    pub(in crate::pdr::solver) fn concretize_cex_chain(
        &mut self,
        leaf: ProofObligation,
    ) -> Result<ProofObligation, (ProofObligation, ConcretizeFail)> {
        // Unlink the chain leaf-first (nodes[0] = leaf, nodes[last] = root).
        let mut nodes: Vec<ProofObligation> = Vec::new();
        let mut cur = Some(leaf);
        while let Some(mut node) = cur {
            cur = node.parent.take().map(|parent| *parent);
            nodes.push(node);
        }

        let mut new_models: Vec<FxHashMap<String, SmtValue>> = Vec::with_capacity(nodes.len());
        let mut prev_head: Option<HeadValues> = None;
        let mut failure: Option<ConcretizeFail> = None;
        for (step, node) in nodes.iter().enumerate() {
            if self.is_cancelled() {
                failure = Some(ConcretizeFail::Unknown { step });
                break;
            }
            match self.concretize_step(step, node, prev_head.as_deref()) {
                Ok((model, head)) => {
                    new_models.push(model);
                    prev_head = Some(head);
                }
                Err(fail) => {
                    failure = Some(fail);
                    break;
                }
            }
        }

        if failure.is_none() {
            for (node, model) in nodes.iter_mut().zip(new_models) {
                node.smt_model = Some(model);
            }
        }
        let leaf = relink_chain(nodes);
        match failure {
            None => Ok(leaf),
            Some(fail) => {
                if self.config.verbose {
                    safe_eprintln!("PDR-SPACER: cex concretisation stopped: {fail:?}");
                }
                Err((leaf, fail))
            }
        }
    }

    /// One step of the walk: the (possibly kept) model of node `step` and its
    /// head values.
    fn concretize_step(
        &mut self,
        step: usize,
        node: &ProofObligation,
        prev_head: Option<&[Option<SmtValue>]>,
    ) -> Result<(FxHashMap<String, SmtValue>, HeadValues), ConcretizeFail> {
        let Some(clause_index) = node.incoming_clause else {
            return Err(ConcretizeFail::Unknown { step });
        };
        let Some(clause) = self.problem.clauses().get(clause_index).cloned() else {
            return Err(ConcretizeFail::Unknown { step });
        };
        let crate::ClauseHead::Predicate(_, head_args) = &clause.head else {
            return Err(ConcretizeFail::Unknown { step });
        };
        if clause.body.predicates.len() > 1 {
            return Err(ConcretizeFail::Hyperedge { step });
        }
        let Some(state_on_head) = self.apply_to_args(node.predicate, &node.state, head_args) else {
            return Err(ConcretizeFail::Unknown { step });
        };
        let transition = clause
            .body
            .constraint
            .clone()
            .unwrap_or(ChcExpr::Bool(true));

        // Body pin: `body_args[j] = s_{i-1}[j]` for every evaluated position.
        let mut pins: Vec<ChcExpr> = Vec::new();
        if let (Some((body_pred, body_args)), Some(prev)) =
            (clause.body.predicates.first(), prev_head)
        {
            let sorts: Vec<ChcSort> = self
                .canonical_vars(*body_pred)
                .map(|vars| vars.iter().map(|v| v.sort.clone()).collect())
                .unwrap_or_default();
            for (j, (arg, value)) in body_args.iter().zip(prev.iter()).enumerate() {
                let Some(value) = value else { continue };
                let sort = sorts
                    .get(j)
                    .cloned()
                    .unwrap_or_else(|| sort_of_value(value));
                let Some(constant) = pin_constant(value, &sort) else {
                    return Err(ConcretizeFail::Unknown { step });
                };
                pins.push(ChcExpr::eq(arg.clone(), constant));
            }
        }

        let mut conjuncts = Vec::with_capacity(pins.len() + 2);
        conjuncts.push(transition);
        conjuncts.extend(pins);
        conjuncts.push(state_on_head);
        let query = self
            .bound_int_vars(ChcExpr::and_all(conjuncts))
            .expand_select_store_symbolic();

        // Keep the recorded model when it already satisfies the pinned query
        // (every pinned cube in R1): no solve, identical witness.
        let kept = node
            .smt_model
            .as_ref()
            .filter(|m| {
                matches!(
                    crate::expr::evaluate_expr(&query, m),
                    Some(SmtValue::Bool(true))
                )
            })
            .cloned();
        let mut model = match kept {
            Some(m) => m,
            None => {
                let per_call = self
                    .smt
                    .current_timeout()
                    .unwrap_or(std::time::Duration::from_secs(5));
                let _deadline = ScopedSmtDeadline::install(per_call);
                self.smt.reset();
                let result = self
                    .smt
                    .with_phase_seed_model(node.smt_model.as_ref(), |smt| {
                        smt.check_sat_with_timeout(&query, per_call)
                    });
                self.spacer_stats.smt_solves_total += 1;
                match result {
                    SmtResult::Sat(m) => m,
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {
                        return Err(ConcretizeFail::Unsat { step });
                    }
                    SmtResult::Unknown => return Err(ConcretizeFail::Unknown { step }),
                }
            }
        };

        // Head values. A head VARIABLE absent from the model does not occur
        // in `T ∧ pins ∧ state` at all, so any value is consistent: assign
        // the sort default and record it, so the witness instances pin it
        // and the next step's body pin matches it.
        let head_sorts: Vec<ChcSort> = self
            .canonical_vars(node.predicate)
            .map(|vars| vars.iter().map(|v| v.sort.clone()).collect())
            .unwrap_or_default();
        let mut head: HeadValues = Vec::with_capacity(head_args.len());
        for (j, arg) in head_args.iter().enumerate() {
            if let ChcExpr::Var(v) = arg {
                if !model.contains_key(&v.name) {
                    let sort = head_sorts.get(j).unwrap_or(&v.sort);
                    if let Some(default) = default_value(sort) {
                        model.insert(v.name.clone(), default);
                    }
                }
            }
            head.push(crate::expr::evaluate_expr(arg, &model));
        }
        Ok((model, head))
    }
}

/// Re-link `nodes` (leaf first) into one chain and return the leaf.
fn relink_chain(mut nodes: Vec<ProofObligation>) -> ProofObligation {
    let mut acc = nodes
        .pop()
        .expect("BUG: concretize_cex_chain on an empty chain");
    while let Some(mut node) = nodes.pop() {
        node.parent = Some(Box::new(acc));
        acc = node;
    }
    acc
}

/// The constant to pin a body argument of sort `sort` to `value` (the lane's
/// sorts only: Int / Real / Bool; anything else stops the walk).
fn pin_constant(value: &SmtValue, sort: &ChcSort) -> Option<ChcExpr> {
    use num_traits::ToPrimitive;
    Some(match (sort, value) {
        (ChcSort::Int, SmtValue::Int(n)) => ChcExpr::Int(*n),
        (ChcSort::Int, SmtValue::BigInt(n)) => ChcExpr::from_bigint(n.as_ref().clone()),
        (ChcSort::Int, SmtValue::Real(r)) if num_traits::One::is_one(r.denom()) => {
            ChcExpr::Int(r.numer().to_i128()?)
        }
        (ChcSort::Real, SmtValue::Real(r)) => {
            ChcExpr::Real(r.numer().to_i64()?, r.denom().to_i64()?)
        }
        (ChcSort::Real, SmtValue::Int(n)) => ChcExpr::Real(i64::try_from(*n).ok()?, 1),
        (ChcSort::Bool, SmtValue::Bool(b)) => ChcExpr::Bool(*b),
        _ => return None,
    })
}

fn sort_of_value(value: &SmtValue) -> ChcSort {
    match value {
        SmtValue::Bool(_) => ChcSort::Bool,
        SmtValue::Real(_) => ChcSort::Real,
        _ => ChcSort::Int,
    }
}

fn default_value(sort: &ChcSort) -> Option<SmtValue> {
    Some(match sort {
        ChcSort::Int => SmtValue::Int(0),
        ChcSort::Bool => SmtValue::Bool(false),
        ChcSort::Real => SmtValue::Real(num_rational::BigRational::from_integer(
            num_bigint::BigInt::from(0),
        )),
        _ => return None,
    })
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::panic)]
#[path = "cex_concretize_tests.rs"]
mod tests;
