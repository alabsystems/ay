// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Pull a bad tuple backwards through a chain of linear rules to propose a
//! model for mixed datatype/array problems. Every published interpretation is
//! checked by the ordinary invariant validator on the complete original CHC.

use crate::adaptive::{deterministic_array_forwarded_surface_caps, AdaptivePortfolio};
use crate::adaptive_route_admission::scan_problem_surface;
use crate::classifier::ProblemFeatures;
use crate::engine_result::ValidationEvidence;
use crate::portfolio::PortfolioResult;
use crate::{
    ChcExpr, ChcOp, ChcProblem, ChcVar, ClauseHead, HornClause, InvariantModel, PdrConfig,
    PredicateInterpretation, SpacerLane,
};
use ay_core::kani_compat::DetHashSet;
use ay_core::time::Instant;
use std::time::Duration;

const MAX_CHAIN: usize = 64;
const MAX_EXPR_NODES: usize = 2048;

impl AdaptivePortfolio {
    pub(crate) fn try_linear_chain_invariant(
        &self,
        features: &ProblemFeatures,
        deadline: Option<Instant>,
    ) -> Option<(PortfolioResult, ValidationEvidence)> {
        if !features.uses_arrays
            || self.problem.datatype_defs().is_empty()
            || features.has_cycles
            || !features.is_linear
            || features.num_queries != 1
            || features.num_clauses > 128
            || features.num_predicates > 128
            || crate::bmc::BmcSolver::closed_under_effort()
        {
            return None;
        }
        let budget = self
            .remaining_budget(deadline)
            .unwrap_or(Duration::from_secs(2));
        let end = Instant::now().checked_add(budget.min(Duration::from_secs(2)))?;
        let token = self.lane_token();
        let memory = crate::bmc::memory::Budget::capture(None, self.config.memory_budget);
        let open = || Instant::now() < end && !token.is_cancelled() && memory.open();
        if !open() {
            return None;
        }
        let chain = unique_chain(&self.problem)?;
        scan_problem_surface(
            &self.problem,
            deterministic_array_forwarded_surface_caps(),
            &token,
            end,
        )
        .ok()?;
        // Datatype selectors can occur only in rule constraints, with entirely
        // scalar or array predicate columns. An unused declaration is common.
        if !self.problem.uses_datatype_features() || !open() {
            return None;
        }
        let model = propose(&self.problem, &chain, &open)?;
        let config = PdrConfig {
            strict_proofs: true,
            disable_array_scalarization: true,
            preserve_original_clauses: true,
            memory_budget: self.config.memory_budget,
            cancellation_token: Some(token.clone()),
            solve_timeout: Some(end.saturating_duration_since(Instant::now())),
            spacer: SpacerLane::OFF,
            ..PdrConfig::default()
        };
        if open()
            && crate::engines::validate_external_invariant_model(&self.problem, &model, &config)
                .ok()?
            && open()
        {
            Some((
                PortfolioResult::Safe(model),
                ValidationEvidence::FullVerification,
            ))
        } else {
            None
        }
    }
}

/// Follow every producer in the query cone. A join, second producer, cycle,
/// missing definition or overlong chain declines before synthesis starts.
fn unique_chain(problem: &ChcProblem) -> Option<Vec<&HornClause>> {
    let mut queries = problem.clauses().iter().filter(|c| c.is_query());
    let mut clause = queries.next()?;
    if queries.next().is_some() {
        return None;
    }
    let mut seen = DetHashSet::default();
    let mut chain = Vec::new();
    loop {
        if chain.len() == MAX_CHAIN {
            return None;
        }
        chain.push(clause);
        match clause.body.predicates.as_slice() {
            [] => return Some(chain),
            [(p, _)] if seen.insert(*p) => {
                let mut definitions = problem.clauses().iter().filter(
                    |source| matches!(&source.head, ClauseHead::Predicate(head, _) if head == p),
                );
                clause = definitions.next()?;
                if definitions.next().is_some() {
                    return None;
                }
            }
            _ => return None,
        }
    }
}

fn propose(
    problem: &ChcProblem,
    chain: &[&HornClause],
    open: &impl Fn() -> bool,
) -> Option<InvariantModel> {
    let mut model = InvariantModel::new();
    for pred in problem.predicates() {
        if !open() {
            return None;
        }
        let vars = pred
            .arg_sorts
            .iter()
            .enumerate()
            .map(|(i, sort)| ChcVar::new(format!("arg{i}"), sort.clone()))
            .collect();
        model.set(
            pred.id,
            PredicateInterpretation::new(vars, ChcExpr::Bool(true)),
        );
    }
    let mut forbidden = ChcExpr::Bool(true);
    let mut formals: Vec<ChcVar> = Vec::new();
    for clause in chain {
        if !open() {
            return None;
        }
        let [(body, args)] = clause.body.predicates.as_slice() else {
            break;
        };
        let locals: Vec<_> = args
            .iter()
            .map(|arg| match arg {
                ChcExpr::Var(v) => Some(v.clone()),
                _ => None,
            })
            .collect::<Option<_>>()?;
        let bound: DetHashSet<_> = locals.iter().cloned().collect();
        if bound.len() != locals.len() {
            return None;
        }
        if let ClauseHead::Predicate(_, head_args) = &clause.head {
            if head_args.len() != formals.len() {
                return None;
            }
            let subst: Vec<_> = formals.drain(..).zip(head_args.iter().cloned()).collect();
            forbidden = forbidden.substitute_checked(&subst, || !open())?;
        }
        let guards = match &clause.body.constraint {
            Some(expr) => expr.conjuncts_checked(|| !open())?,
            None => Vec::new(),
        };
        let mut defs = Vec::new();
        let mut remaining = Vec::new();
        for guard in guards {
            if let Some(def) = local_definition(guard, &bound) {
                defs.push(def);
            } else {
                remaining.push(guard);
            }
        }
        let depends_on_args = |t: &ChcExpr| t.vars().iter().all(|v| bound.contains(v));
        forbidden = expand(forbidden, &defs, open)?;
        if !depends_on_args(&forbidden) {
            // A universally quantified clause-local input enters here. Leave
            // the predecessor at true; the verifier must establish this
            // transition for all its inputs before accepting the model.
            break;
        }
        let mut conditions = vec![forbidden];
        for guard in remaining {
            let guard = expand(guard.clone(), &defs, open)?;
            if depends_on_args(&guard) {
                conditions.push(guard);
            }
        }
        forbidden = ChcExpr::and_all_checked(conditions, || !open())?;
        if forbidden.node_count(MAX_EXPR_NODES) >= MAX_EXPR_NODES {
            return None;
        }
        formals = locals;
        model.set(
            *body,
            PredicateInterpretation::new(formals.clone(), ChcExpr::not(forbidden.clone())),
        );
    }
    Some(model)
}

fn local_definition(guard: &ChcExpr, bound: &DetHashSet<ChcVar>) -> Option<(ChcVar, ChcExpr)> {
    let ChcExpr::Op(ChcOp::Eq | ChcOp::Iff, pair) = guard else {
        return None;
    };
    let [left, right] = pair.as_slice() else {
        return None;
    };
    [(left, right), (right, left)]
        .into_iter()
        .find_map(|(lhs, rhs)| match lhs.as_ref() {
            ChcExpr::Var(v) if !bound.contains(v) => Some((v.clone(), rhs.as_ref().clone())),
            _ => None,
        })
}

fn expand(
    mut term: ChcExpr,
    defs: &[(ChcVar, ChcExpr)],
    open: &impl Fn() -> bool,
) -> Option<ChcExpr> {
    for _ in 0..8 {
        if !open() || term.node_count(MAX_EXPR_NODES) >= MAX_EXPR_NODES {
            return None;
        }
        if defs.is_empty() {
            return Some(term);
        }
        let next = term.substitute_checked(defs, || !open())?;
        if next == term {
            return Some(term);
        }
        term = next;
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ChcParser;

    const CHAIN: &str = "
        (set-logic HORN)
        (declare-datatype Cell ((mk (word (_ BitVec 8)) (data (Array (_ BitVec 8) Bool)))))
        (declare-rel p (Bool (_ BitVec 8) (Array (_ BitVec 8) Bool)))
        (declare-rel q ((_ BitVec 8) (Array (_ BitVec 8) Bool)))
        (declare-rel hit ())
        (declare-var c Cell)
        (declare-var a (Array (_ BitVec 8) Bool))
        (declare-var x (_ BitVec 8)) (declare-var y (_ BitVec 8)) (declare-var b Bool)
        (rule (=> (and (= c (mk (ite (bvule x #x04) x #x04) a)) (= y (word c))) (p true y a)))
        (rule (=> (and (p b x a) b (= y x)) (q y a)))
        (rule (=> (and (q y a) (= y #x05)) hit))
        (query hit)";

    #[test]
    fn original_clauses_decide_the_chain_candidate() {
        for (bound, valid) in [("#x05", true), ("#x04", false)] {
            let problem = ChcParser::parse(&CHAIN.replace("#x05", bound)).unwrap();
            assert!(problem.uses_datatype_features());
            let chain = unique_chain(&problem).unwrap();
            let candidate = propose(&problem, &chain, &|| true).unwrap();
            let config = PdrConfig {
                strict_proofs: true,
                preserve_original_clauses: true,
                disable_array_scalarization: true,
                solve_timeout: Some(Duration::from_secs(5)),
                ..PdrConfig::default()
            };
            assert_eq!(
                crate::engines::validate_external_invariant_model(&problem, &candidate, &config)
                    .unwrap(),
                valid
            );
            assert!(propose(&problem, &chain, &|| false).is_none());
            let features = crate::classifier::ProblemClassifier::classify(&problem);
            let config = crate::AdaptiveConfig::with_budget(Duration::from_secs(3), false);
            let route = AdaptivePortfolio::new(problem, config);
            assert_eq!(
                route
                    .try_linear_chain_invariant(
                        &features,
                        Instant::now().checked_add(Duration::from_secs(3))
                    )
                    .is_some(),
                valid
            );
        }
    }

    #[test]
    fn a_second_producer_or_cycle_declines_the_chain() {
        let second_producer = CHAIN.replace("(query hit)", "(rule (q #x05 a)) (query hit)");
        // Replace the fact so p and q still have one producer each.
        let cycle = CHAIN.replace(
            "(rule (=> (and (= c (mk (ite (bvule x #x04) x #x04) a)) (= y (word c))) (p true y a)))",
            "(rule (=> (q x a) (p true x a)))",
        );
        assert_ne!(cycle, CHAIN);
        for script in [second_producer, cycle] {
            let problem = ChcParser::parse(&script).unwrap();
            assert!(unique_chain(&problem).is_none());
        }
    }
}
