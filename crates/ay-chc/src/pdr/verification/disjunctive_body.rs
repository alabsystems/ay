// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Case split of an undecided transition-clause query on a disjunctive body
//! interpretation.
//!
//! IMC's invariant is its reached set `init ∨ I1 ∨ … ∨ In`, each disjunct an
//! interpolated image that pins its own constants. `inv(x) ∧ T(x, x') ∧
//! ¬inv(x')` hides those constants under the disjunction; one case per
//! disjunct exposes them as top-level units (om1_with_relays_agreement: the
//! whole query stays undecided past the per-clause budget while IMC's own
//! per-disjunct check refutes every case in 0.5 s). The cases' disjunction is
//! exactly the query, so the clause holds iff every case is refuted.

use super::*;

/// Wall-clock bound on one clause's whole split (all cases together).
const DISJUNCTIVE_BODY_SPLIT_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(2);

impl PdrSolver {
    /// `true` when the clause has one body predicate whose interpretation is
    /// a disjunction (possibly conjoined with other constraints).
    pub(super) fn body_interpretation_is_disjunctive(
        clause: &crate::HornClause,
        model: &InvariantModel,
    ) -> bool {
        let [(pred, _)] = clause.body.predicates.as_slice() else {
            return false;
        };
        model.get(pred).is_some_and(|interp| match &interp.formula {
            ChcExpr::Op(ChcOp::Or, ds) => ds.len() >= 2,
            ChcExpr::Op(ChcOp::And, cs) => cs.iter().any(|c| is_disjunction(c)),
            _ => false,
        })
    }

    /// Refute `query` one case at a time (see the module docs). `false` when
    /// the split does not apply, a case is satisfiable, or a case stays
    /// undecided within [`DISJUNCTIVE_BODY_SPLIT_TIMEOUT`].
    pub(super) fn prove_by_disjunctive_body_split(
        &mut self,
        clause_idx: usize,
        query: &ChcExpr,
    ) -> bool {
        let Some(cases) = disjunctive_cases(query) else {
            return false;
        };
        let deadline =
            ay_core::time::Instant::now() + self.cap_timeout(DISJUNCTIVE_BODY_SPLIT_TIMEOUT);
        for case in &cases {
            let remaining = deadline.saturating_duration_since(ay_core::time::Instant::now());
            if remaining.is_zero() || self.is_cancelled() {
                return false;
            }
            self.smt.reset();
            match self.smt.check_sat_with_timeout(case, remaining) {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
                _ => return false,
            }
        }
        tracing::debug!(
            clause_idx,
            cases = cases.len(),
            "verify_model: transition clause proven via disjunctive-body split"
        );
        true
    }
}

fn is_disjunction(e: &ChcExpr) -> bool {
    matches!(e, ChcExpr::Op(ChcOp::Or, ds) if ds.len() >= 2)
}

/// One formula per disjunct of `query`'s first top-level disjunctive
/// conjunct (nested `or`s flattened), each conjoined with the other
/// conjuncts; `None` without such a conjunct.
fn disjunctive_cases(query: &ChcExpr) -> Option<Vec<ChcExpr>> {
    let conjuncts = query.collect_conjuncts();
    let pos = conjuncts.iter().position(is_disjunction)?;
    let mut disjuncts = Vec::new();
    let mut stack = vec![&conjuncts[pos]];
    while let Some(e) = stack.pop() {
        match e {
            ChcExpr::Op(ChcOp::Or, ds) => stack.extend(ds.iter().rev().map(|d| d.as_ref())),
            other => disjuncts.push(other.clone()),
        }
    }
    let rest: Vec<ChcExpr> = conjuncts
        .iter()
        .enumerate()
        .filter(|(i, _)| *i != pos)
        .map(|(_, c)| c.clone())
        .collect();
    Some(
        disjuncts
            .into_iter()
            .map(|d| ChcExpr::and_all(std::iter::once(d).chain(rest.iter().cloned())))
            .collect(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ChcProblem, ClauseBody, ClauseHead, HornClause};

    fn x() -> ChcExpr {
        ChcExpr::var(ChcVar::new("x", ChcSort::Real))
    }

    fn real(n: i64) -> ChcExpr {
        ChcExpr::Real(n, 1)
    }

    #[test]
    fn cases_flatten_nested_disjunctions_and_keep_the_other_conjuncts() {
        let query = ChcExpr::and(
            ChcExpr::or(
                ChcExpr::eq(x(), real(0)),
                ChcExpr::or(ChcExpr::eq(x(), real(1)), ChcExpr::eq(x(), real(2))),
            ),
            ChcExpr::ge(x(), real(5)),
        );
        let cases = disjunctive_cases(&query).unwrap_or_default();
        assert_eq!(cases.len(), 3);
        for case in &cases {
            assert!(case.to_string().contains(">="), "{case}");
        }
        assert!(disjunctive_cases(&ChcExpr::ge(x(), real(5))).is_none());
    }

    #[test]
    fn a_disjunctive_body_is_proven_only_when_every_case_is_refuted() {
        let mut problem = ChcProblem::new();
        let inv = problem.declare_predicate("inv", vec![ChcSort::Real]);
        let clause = HornClause::new(
            ClauseBody::new(vec![(inv, vec![x()])], None),
            ClauseHead::Predicate(inv, vec![x()]),
        );
        let mut model = InvariantModel::new();
        model.set(
            inv,
            PredicateInterpretation::new(
                vec![ChcVar::new("x", ChcSort::Real)],
                ChcExpr::or(ChcExpr::eq(x(), real(0)), ChcExpr::eq(x(), real(1))),
            ),
        );
        assert!(PdrSolver::body_interpretation_is_disjunctive(
            &clause, &model
        ));
        let mut solver = PdrSolver::new(problem, crate::pdr::PdrConfig::default());
        // (x = 0 ∨ x = 1) ∧ x >= 2: both cases refuted.
        let refuted = ChcExpr::and(
            ChcExpr::or(ChcExpr::eq(x(), real(0)), ChcExpr::eq(x(), real(1))),
            ChcExpr::ge(x(), real(2)),
        );
        assert!(solver.prove_by_disjunctive_body_split(0, &refuted));
        // (x = 0 ∨ x = 1) ∧ x >= 1: the second case is satisfiable.
        let satisfiable = ChcExpr::and(
            ChcExpr::or(ChcExpr::eq(x(), real(0)), ChcExpr::eq(x(), real(1))),
            ChcExpr::ge(x(), real(1)),
        );
        assert!(!solver.prove_by_disjunctive_body_split(0, &satisfiable));
    }
}
