// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Price beta-expanded native replay without constructing an expanded AST.
//!
//! A term pairs original code with a lexical closure environment. Reads visit
//! every possible Store/Ite arm; private variables resolve by parallel
//! substitution. Thus sharing, repeated formals and nested reads cannot hide
//! work from the preflight. No solver or model value chooses a cheaper arm.

use super::*;
use crate::expr::ChcArrayLambda;
use crate::ChcOp;

#[derive(Clone, Copy)]
struct Term<'a> {
    node: &'a ChcExpr,
    scope: Option<usize>,
}

struct Scope<'a> {
    lambda: &'a ChcArrayLambda,
    parent: Option<usize>,
    index: Term<'a>,
}

enum Work<'a> {
    Value(Term<'a>, usize),
    Read(Term<'a>, Vec<Term<'a>>, usize),
}

pub(super) struct ReplayProfile {
    pub(super) work: usize,
    pub(super) value_occurrences: usize,
}

struct Walker<'a, 'problem, 'source, 'control> {
    cache: &'a mut GroundSourceSurfaceCache<'problem>,
    control: &'a mut GroundValidationControl<'control>,
    scopes: Vec<Scope<'source>>,
    pending: Vec<Work<'source>>,
    value_occurrences: usize,
}

impl GroundSourceSurfaceCache<'_> {
    pub(super) fn reserve_lambda_replay(
        &mut self,
        clause: &HornClause,
        control: &mut GroundValidationControl<'_>,
    ) -> Result<ReplayProfile, GroundSourceSurfaceError> {
        let start = self.work_used;
        let mut walker = Walker {
            cache: self,
            control,
            scopes: Vec::new(),
            pending: Vec::new(),
            value_occurrences: 0,
        };
        let roots = clause
            .body
            .constraint
            .iter()
            .chain(clause.body.predicates.iter().flat_map(|(_, args)| args))
            .chain(head_args(clause).into_iter().flatten());
        for node in roots {
            walker.push(Work::Value(Term { node, scope: None }, 1))?;
        }
        while let Some(work) = walker.pending.pop() {
            walker.control.poll()?;
            match work {
                Work::Value(term, depth) => walker.value(term, depth)?,
                Work::Read(term, indices, depth) => walker.read(term, indices, depth)?,
            }
        }
        let value_occurrences = walker.value_occurrences;
        Ok(ReplayProfile {
            work: self
                .work_used
                .checked_sub(start)
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?,
            value_occurrences,
        })
    }
}

impl<'source> Walker<'_, '_, 'source, '_> {
    fn push(&mut self, work: Work<'source>) -> Result<(), GroundSourceSurfaceError> {
        let (depth, entries) = match &work {
            Work::Value(_, depth) => (*depth, 1),
            Work::Read(_, indices, depth) => (
                *depth,
                indices
                    .len()
                    .checked_add(1)
                    .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?,
            ),
        };
        if depth > CHC_GROUND_DERIVATION_MAX_SOURCE_DEPTH {
            return Err(GroundSourceSurfaceError::SourceWorkLimitExceeded);
        }
        self.cache.charge(entries)?;
        self.pending.push(work);
        Ok(())
    }

    fn resolve(
        &mut self,
        mut term: Term<'source>,
        depth: &mut usize,
    ) -> Result<Term<'source>, GroundSourceSurfaceError> {
        while let (ChcExpr::Var(variable), Some(scope)) = (term.node, term.scope) {
            self.control.poll()?;
            *depth = depth
                .checked_add(1)
                .filter(|depth| *depth <= CHC_GROUND_DERIVATION_MAX_SOURCE_DEPTH)
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
            let scope = &self.scopes[scope];
            self.cache.charge(
                scope
                    .lambda
                    .formals()
                    .len()
                    .checked_add(1)
                    .and_then(|slots| {
                        variable
                            .name
                            .len()
                            .checked_add(1)
                            .and_then(|bytes| slots.checked_mul(bytes))
                    })
                    .and_then(|cost| cost.checked_add(64))
                    .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?,
            )?;
            // The complete scoped source walk checked the exact sorts first.
            // Match names here without repeatedly comparing datatype layouts.
            if variable.name == scope.lambda.binder().name {
                term = scope.index;
            } else {
                let position = scope
                    .lambda
                    .formals()
                    .iter()
                    .position(|formal| formal.name == variable.name)
                    .ok_or(GroundSourceSurfaceError::InvalidVariableSurface)?;
                let node = scope
                    .lambda
                    .captures()
                    .get(position)
                    .ok_or(GroundSourceSurfaceError::InvalidVariableSurface)?;
                term = Term {
                    node,
                    scope: scope.parent,
                };
            }
        }
        Ok(term)
    }

    fn price(&mut self, term: Term<'source>, depth: usize) -> Result<(), GroundSourceSurfaceError> {
        self.control.poll()?;
        self.value_occurrences = self
            .value_occurrences
            .checked_add(1)
            .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
        let metadata = match term.node {
            ChcExpr::Var(variable) => variable.name.len(),
            ChcExpr::FuncApp(name, _, args) | ChcExpr::PredicateApp(name, _, args) => name
                .len()
                .checked_add(args.len())
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?,
            ChcExpr::IsTesterMarker(name) => name.len(),
            _ => 0,
        };
        self.cache.charge(
            depth
                .checked_mul(64)
                .and_then(|cost| cost.checked_add(metadata))
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?,
        )?;
        // These are original source nodes, whose recursive sort derivations
        // were already depth-bounded by the complete source walk.
        let sort = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| term.node.sort()))
            .map_err(|_| GroundSourceSurfaceError::InvalidUfSurface)?;
        self.control.poll()?;
        self.cache.reserve_source_sort(&sort, self.control)?;
        if let ChcExpr::ArrayLambda(lambda) = term.node {
            self.cache.reserve_lambda_metadata(lambda, self.control)?;
        }
        Ok(())
    }

    fn value(
        &mut self,
        term: Term<'source>,
        mut depth: usize,
    ) -> Result<(), GroundSourceSurfaceError> {
        let term = self.resolve(term, &mut depth)?;
        self.price(term, depth)?;
        match term.node {
            ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 => {
                let index = Term {
                    node: &args[1],
                    scope: term.scope,
                };
                self.push(Work::Value(index, depth + 1))?;
                self.push(Work::Read(
                    Term {
                        node: &args[0],
                        scope: term.scope,
                    },
                    vec![index],
                    depth + 1,
                ))
            }
            ChcExpr::ArrayLambda(lambda) => self.values(lambda.captures(), term.scope, depth + 1),
            ChcExpr::Op(_, args)
            | ChcExpr::FuncApp(_, _, args)
            | ChcExpr::PredicateApp(_, _, args) => self.values(args, term.scope, depth + 1),
            ChcExpr::ConstArray(_, value) => self.push(Work::Value(
                Term {
                    node: value,
                    scope: term.scope,
                },
                depth + 1,
            )),
            _ => Ok(()),
        }
    }

    fn values(
        &mut self,
        nodes: &'source [std::sync::Arc<ChcExpr>],
        scope: Option<usize>,
        depth: usize,
    ) -> Result<(), GroundSourceSurfaceError> {
        for node in nodes {
            self.control.poll()?;
            self.push(Work::Value(Term { node, scope }, depth))?;
        }
        Ok(())
    }

    fn read(
        &mut self,
        term: Term<'source>,
        mut indices: Vec<Term<'source>>,
        mut depth: usize,
    ) -> Result<(), GroundSourceSurfaceError> {
        let term = self.resolve(term, &mut depth)?;
        self.price(term, depth)?;
        match term.node {
            ChcExpr::ArrayLambda(lambda) => self.read_lambda(term, lambda, indices, depth),
            ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
                self.read_choice(term, args, indices, depth)
            }
            ChcExpr::Op(ChcOp::Store, args) if args.len() == 3 => {
                self.read_store(term, args, indices, depth)
            }
            ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 => {
                self.cache.charge(
                    indices
                        .len()
                        .checked_add(1)
                        .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?,
                )?;
                let index = Term {
                    node: &args[1],
                    scope: term.scope,
                };
                self.push(Work::Value(index, depth + 1))?;
                indices.insert(0, index);
                self.push(Work::Read(
                    Term {
                        node: &args[0],
                        scope: term.scope,
                    },
                    indices,
                    depth + 1,
                ))
            }
            ChcExpr::ConstArray(_, value) => {
                if indices.is_empty() {
                    return Err(GroundSourceSurfaceError::InvalidUfSurface);
                }
                indices.remove(0);
                self.result(
                    Term {
                        node: value,
                        scope: term.scope,
                    },
                    indices,
                    depth + 1,
                )
            }
            // Ground bindings and ordinary-UF observations are finite SmtValue
            // arrays. They cannot contain executable lambda code.
            ChcExpr::Var(_) | ChcExpr::FuncApp(..) => self.value(term, depth + 1),
            _ => Err(GroundSourceSurfaceError::InvalidUfSurface),
        }
    }

    fn read_lambda(
        &mut self,
        term: Term<'source>,
        lambda: &'source ChcArrayLambda,
        mut indices: Vec<Term<'source>>,
        depth: usize,
    ) -> Result<(), GroundSourceSurfaceError> {
        if indices.is_empty() {
            return Err(GroundSourceSurfaceError::InvalidVariableSurface);
        }
        self.cache.charge(
            lambda
                .formals()
                .len()
                .checked_add(indices.len())
                .and_then(|cost| cost.checked_add(1))
                .and_then(|cost| cost.checked_mul(64))
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?,
        )?;
        let index = indices.remove(0);
        // Instantiation clones and checks the index even if its binder is
        // unused. Charge each candidate call as well as the enclosing read.
        self.push(Work::Value(index, depth + 1))?;
        let scope = self.scopes.len();
        self.scopes.push(Scope {
            lambda,
            parent: term.scope,
            index,
        });
        self.result(
            Term {
                node: lambda.body(),
                scope: Some(scope),
            },
            indices,
            depth + 1,
        )
    }

    fn read_choice(
        &mut self,
        term: Term<'source>,
        args: &'source [std::sync::Arc<ChcExpr>],
        indices: Vec<Term<'source>>,
        depth: usize,
    ) -> Result<(), GroundSourceSurfaceError> {
        self.push(Work::Value(
            Term {
                node: &args[0],
                scope: term.scope,
            },
            depth + 1,
        ))?;
        self.cache.charge(indices.len())?;
        self.push(Work::Read(
            Term {
                node: &args[1],
                scope: term.scope,
            },
            indices.clone(),
            depth + 1,
        ))?;
        self.push(Work::Read(
            Term {
                node: &args[2],
                scope: term.scope,
            },
            indices,
            depth + 1,
        ))
    }

    fn read_store(
        &mut self,
        term: Term<'source>,
        args: &'source [std::sync::Arc<ChcExpr>],
        indices: Vec<Term<'source>>,
        depth: usize,
    ) -> Result<(), GroundSourceSurfaceError> {
        self.push(Work::Value(
            Term {
                node: &args[1],
                scope: term.scope,
            },
            depth + 1,
        ))?;
        self.cache.charge(indices.len())?;
        let rest = indices
            .get(1..)
            .ok_or(GroundSourceSurfaceError::InvalidUfSurface)?
            .to_vec();
        self.result(
            Term {
                node: &args[2],
                scope: term.scope,
            },
            rest,
            depth + 1,
        )?;
        self.push(Work::Read(
            Term {
                node: &args[0],
                scope: term.scope,
            },
            indices,
            depth + 1,
        ))
    }

    fn result(
        &mut self,
        term: Term<'source>,
        indices: Vec<Term<'source>>,
        depth: usize,
    ) -> Result<(), GroundSourceSurfaceError> {
        self.push(if indices.is_empty() {
            Work::Value(term, depth)
        } else {
            Work::Read(term, indices, depth)
        })
    }
}
