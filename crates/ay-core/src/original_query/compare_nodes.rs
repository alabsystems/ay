// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::compare::{Engine, Environment};
use super::compare_syntax::literal;
use super::*;

impl Engine<'_> {
    pub(super) fn node_pair(
        &mut self,
        a: NodeId,
        b: NodeId,
        env: &Environment,
        work: &mut WorkBudget<'_>,
    ) -> Result<bool, QueryError> {
        let left = self.left;
        let right = self.right;
        let a = &left.nodes[a.0 as usize];
        let b = &right.nodes[b.0 as usize];
        self.sort(a.sort, b.sort, env, work)?;
        match (&a.kind, &b.kind) {
            (NodeKind::Literal(a), NodeKind::Literal(b)) => literal(a, b, work),
            (NodeKind::Free(a), NodeKind::Free(b)) => Ok(a == b),
            (NodeKind::Bound(a), NodeKind::Bound(b)) => {
                self.environments.terms_match(*env, *a, *b, work)
            }
            (
                NodeKind::Apply {
                    operator: a,
                    arguments: aa,
                },
                NodeKind::Apply {
                    operator: b,
                    arguments: ba,
                },
            ) => Ok(self.operator(a, b, env, work)? && self.nodes(aa, ba, env, work)?),
            (
                NodeKind::Let {
                    bindings: a,
                    body: ab,
                },
                NodeKind::Let {
                    bindings: b,
                    body: bb,
                },
            ) => {
                let Some(bound) = self.let_bindings(a, b, env, work)? else {
                    return Ok(false);
                };
                self.node(*ab, *bb, &bound, work)?;
                Ok(true)
            }
            (
                NodeKind::Quantified {
                    quantifier: aq,
                    binders: a,
                    body: ab,
                },
                NodeKind::Quantified {
                    quantifier: bq,
                    binders: b,
                    body: bb,
                },
            ) => {
                if aq != bq {
                    return Ok(false);
                }
                let Some(bound) = self.binders(a, b, env, work)? else {
                    return Ok(false);
                };
                self.node(*ab, *bb, &bound, work)?;
                Ok(true)
            }
            (
                NodeKind::Match {
                    scrutinee: a,
                    cases: ac,
                },
                NodeKind::Match {
                    scrutinee: b,
                    cases: bc,
                },
            ) => {
                self.node(*a, *b, env, work)?;
                self.cases(ac, bc, env, work)
            }
            (
                NodeKind::Annotated {
                    body: a,
                    attributes: aa,
                },
                NodeKind::Annotated {
                    body: b,
                    attributes: ba,
                },
            ) => {
                self.node(*a, *b, env, work)?;
                self.attributes(aa, ba, env, work)
            }
            _ => Ok(false),
        }
    }

    fn cases(
        &mut self,
        a: &[MatchCase],
        b: &[MatchCase],
        env: &Environment,
        work: &mut WorkBudget<'_>,
    ) -> Result<bool, QueryError> {
        if a.len() != b.len() {
            return Ok(false);
        }
        for (a, b) in a.iter().zip(b) {
            work.charge(1)?;
            let Some(bound) = self.pattern(&a.pattern, &b.pattern, env, work)? else {
                return Ok(false);
            };
            self.node(a.body, b.body, &bound, work)?;
        }
        Ok(true)
    }

    fn let_bindings(
        &mut self,
        a: &[LetBinding],
        b: &[LetBinding],
        env: &Environment,
        work: &mut WorkBudget<'_>,
    ) -> Result<Option<Environment>, QueryError> {
        if a.len() != b.len() {
            return Ok(None);
        }
        let mut bound = *env;
        for (a, b) in a.iter().zip(b) {
            // Both RHS roots use incoming scope, never the partial let scope.
            self.node(a.value, b.value, env, work)?;
            let Some(next) = self.binders(
                std::slice::from_ref(&a.binder),
                std::slice::from_ref(&b.binder),
                &bound,
                work,
            )?
            else {
                return Ok(None);
            };
            bound = next;
        }
        Ok(Some(bound))
    }

    fn pattern(
        &mut self,
        a: &MatchPattern,
        b: &MatchPattern,
        env: &Environment,
        work: &mut WorkBudget<'_>,
    ) -> Result<Option<Environment>, QueryError> {
        work.charge(1)?;
        match (a, b) {
            (MatchPattern::Variable(a), MatchPattern::Variable(b)) => {
                self.binders(std::slice::from_ref(a), std::slice::from_ref(b), env, work)
            }
            (MatchPattern::Wildcard, MatchPattern::Wildcard) => Ok(Some(*env)),
            (
                MatchPattern::Constructor {
                    declaration: a,
                    fields: af,
                },
                MatchPattern::Constructor {
                    declaration: b,
                    fields: bf,
                },
            ) => {
                if a != b || af.len() != bf.len() {
                    return Ok(None);
                }
                let mut bound = *env;
                for (a, b) in af.iter().zip(bf) {
                    work.charge(1)?;
                    match (a, b) {
                        (PatternField::Wildcard(a), PatternField::Wildcard(b)) => {
                            self.sort(*a, *b, env, work)?
                        }
                        (PatternField::Binder(a), PatternField::Binder(b)) => {
                            let Some(next) = self.binders(
                                std::slice::from_ref(a),
                                std::slice::from_ref(b),
                                &bound,
                                work,
                            )?
                            else {
                                return Ok(None);
                            };
                            bound = next;
                        }
                        _ => return Ok(None),
                    }
                }
                Ok(Some(bound))
            }
            _ => Ok(None),
        }
    }
}
