// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::UniversalPremise;
use super::*;
use crate::{ChcOp, ClauseBody, ClauseHead, HornClause};

#[derive(Default)]
struct Body {
    predicates: Vec<(PredicateId, Vec<ChcExpr>)>,
    constraints: Vec<Arc<ChcExpr>>,
    premises: Vec<UniversalPremise>,
}

impl Parser<'_> {
    pub(super) fn clause(&mut self, term: &Arc<Term>) -> ChcResult<()> {
        let mut term = term;
        let mut depth = 0;
        while let Term::Forall(_, inner) = term.as_ref() {
            self.budget.enter(depth)?;
            depth += 1;
            term = inner;
        }
        let mut body = Body::default();
        let head = match term.as_ref() {
            Term::Implies(antecedent, consequent) => {
                self.body(antecedent, &mut body, 0)?;
                self.head(consequent, &mut body)?
            }
            _ => self.head(term, &mut body)?,
        };
        self.finish(body, head)
    }

    pub(super) fn query(&mut self, term: &Arc<Term>) -> ChcResult<()> {
        let Term::Predicate(id, args) = term.as_ref() else {
            return Err(invalid("query must name one relation application"));
        };
        let args = self.copy_arguments(args)?;
        self.finish(
            Body {
                predicates: vec![(*id, args)],
                ..Body::default()
            },
            ClauseHead::False,
        )
    }

    fn body(&mut self, term: &Arc<Term>, out: &mut Body, depth: usize) -> ChcResult<()> {
        self.budget.enter(depth)?;
        match term.as_ref() {
            Term::And(children) => {
                for child in children {
                    self.body(child, out, depth + 1)?;
                }
            }
            Term::Predicate(id, args) => {
                out.predicates.push((*id, self.copy_arguments(args)?));
            }
            Term::Forall(vars, matrix) => {
                if vars.is_empty() || vars.len() > super::super::MAX_PREMISE_BINDERS {
                    return Err(invalid(
                        "universal premise requires one to eight BV binders",
                    ));
                }
                for binder in vars {
                    if !matches!(binder.sort, ChcSort::BitVec(1..=64)) {
                        return Err(invalid("universal premise binder must be BV1..64"));
                    }
                    self.budget.name(&binder.name)?;
                    self.budget.sort_copy(&binder.sort)?;
                }
                let (matrix, sort) = self.value(matrix, 0)?;
                if sort != ChcSort::Bool {
                    return Err(invalid("non-Boolean universal matrix"));
                }
                let matrix = self.copy_expression(&matrix)?;
                out.premises
                    .push(UniversalPremise::with_binders(vars.clone(), matrix)?);
            }
            _ => {
                let (value, sort) = self.value(term, 0)?;
                if sort != ChcSort::Bool {
                    return Err(invalid("non-Boolean antecedent"));
                }
                out.constraints.push(value);
            }
        }
        Ok(())
    }

    fn head(&mut self, term: &Arc<Term>, body: &mut Body) -> ChcResult<ClauseHead> {
        self.budget.enter(0)?;
        if let Term::Predicate(id, args) = term.as_ref() {
            return Ok(ClauseHead::Predicate(*id, self.copy_arguments(args)?));
        }
        if self.dialect == Dialect::Fixedpoint {
            return Err(invalid("fixedpoint rule head must be a relation"));
        }
        let (value, sort) = self.value(term, 0)?;
        if sort != ChcSort::Bool {
            return Err(invalid("non-Boolean Horn head"));
        }
        if !matches!(value.as_ref(), ChcExpr::Bool(false)) {
            // A theory consequent is exactly C => theory iff C & !theory =>
            // false. Keep the raw Not, even for true/false constants.
            body.constraints
                .push(Arc::new(ChcExpr::Op(ChcOp::Not, vec![value])));
        }
        Ok(ClauseHead::False)
    }

    fn finish(&mut self, mut body: Body, head: ClauseHead) -> ChcResult<()> {
        self.budget.charge(1, 256)?;
        let constraint = match body.constraints.len() {
            0 => None,
            1 => {
                let expr = body
                    .constraints
                    .pop()
                    .ok_or_else(|| invalid("constraint state"))?;
                Some(self.copy_expression(&expr)?)
            }
            _ => Some(ChcExpr::Op(ChcOp::And, body.constraints)),
        };
        let clause = HornClause::new(ClauseBody::new(body.predicates, constraint), head);
        // Do not pass through ChcProblem::add_clause: false clauses, query
        // positions, duplicate rules and relational equalities remain raw.
        self.clauses
            .push(QuantifiedHornClause::new(clause, body.premises));
        Ok(())
    }

    fn copy_arguments(&mut self, args: &[Arc<ChcExpr>]) -> ChcResult<Vec<ChcExpr>> {
        self.budget
            .charge(args.len(), args.len().saturating_mul(128))?;
        args.iter().map(|arg| self.copy_expression(arg)).collect()
    }

    fn copy_expression(&mut self, expr: &ChcExpr) -> ChcResult<ChcExpr> {
        // Clone only one root, whose descendants remain shared. Charge its
        // vector/name allocation first, including a wide resolved let value.
        let (work, bytes) = match expr {
            ChcExpr::Op(_, args) => (args.len(), args.len().saturating_mul(64)),
            ChcExpr::Var(var) => {
                self.budget.sort_copy(&var.sort)?;
                (1, var.name.len().saturating_mul(2).saturating_add(128))
            }
            ChcExpr::FuncApp(name, sort, args) => {
                self.budget.sort_copy(sort)?;
                (
                    args.len(),
                    name.len()
                        .saturating_mul(2)
                        .saturating_add(args.len().saturating_mul(64)),
                )
            }
            _ => (1, 256),
        };
        self.budget.charge(work, bytes)?;
        Ok(expr.clone())
    }
}
