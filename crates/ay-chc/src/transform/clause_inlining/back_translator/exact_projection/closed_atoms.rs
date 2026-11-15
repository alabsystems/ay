// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact separation: exists x. (A(keep) and B) = A(keep) and exists x. B.
//! Only top-level conjunctions are separated; an OR is always one whole atom.
//! A closed array atom is retained verbatim. Every other atom, including a
//! flat-array atom over a local, goes to the arena, which eliminates an array
//! local only through an occurs-checked definition and otherwise declines.

use super::control::{Failure, Scope};
use super::formals::{charge_sort, Formals};
use super::{Arc, ChcExpr, ChcOp, ChcSort};

pub(super) struct Parts<'a> {
    /// The atoms the arena projects: scalar atoms, and array atoms that are
    /// not closed over the retained formals.
    pub(super) scalar: Vec<&'a ChcExpr>,
    preserved: Vec<&'a ChcExpr>,
}

struct Typed {
    sort: ChcSort,
    closed: bool,
    arrays: bool,
}

impl<'a> Parts<'a> {
    pub(super) fn read(
        formula: &'a ChcExpr,
        formals: &Formals<'_>,
        scope: &mut Scope<'_>,
    ) -> Result<Self, Failure> {
        let mut parts = Self {
            scalar: Vec::new(),
            preserved: Vec::new(),
        };
        parts.conjunct(formula, formals, 0, scope)?;
        Ok(parts)
    }

    fn conjunct(
        &mut self,
        formula: &'a ChcExpr,
        formals: &Formals<'_>,
        depth: usize,
        scope: &mut Scope<'_>,
    ) -> Result<(), Failure> {
        scope.depth(depth)?;
        if let ChcExpr::Op(ChcOp::And, args) = formula {
            scope.node()?;
            if args.len() < 2 {
                return Err(Failure::Declined);
            }
            for arg in args {
                self.conjunct(arg, formals, depth + 1, scope)?;
            }
            return Ok(());
        }
        let typed = validate(formula, formals, depth, scope)?;
        if typed.sort != ChcSort::Bool {
            return Err(Failure::Declined);
        }
        scope.grow::<&ChcExpr>(1)?;
        if typed.arrays && typed.closed {
            self.preserved.push(formula);
        } else {
            // An array atom over a local is the arena's (5eb47055a): it is
            // eliminated exactly through a definition, or the arena declines.
            self.scalar.push(formula);
        }
        Ok(())
    }

    pub(super) fn assemble(
        self,
        scalar: ChcExpr,
        scope: &mut Scope<'_>,
    ) -> Result<ChcExpr, Failure> {
        if self.preserved.is_empty() {
            scope.poll()?;
            return Ok(scalar);
        }
        scope.grow::<Arc<ChcExpr>>(self.preserved.len().saturating_add(1))?;
        let mut args = Vec::with_capacity(self.preserved.len() + 1);
        for atom in self.preserved {
            // ChcExpr::clone shares Arc children. Only its root's owned fields
            // are copied; the complete retained subtree was already validated.
            scope.grow::<ChcExpr>(1)?;
            match atom {
                ChcExpr::Op(_, children) => scope.grow::<Arc<ChcExpr>>(children.len())?,
                _ => return Err(Failure::Declined),
            }
            args.push(Arc::new(atom.clone()));
        }
        scope.grow::<ChcExpr>(1)?;
        args.push(Arc::new(scalar));
        scope.node()?;
        scope.poll()?;
        Ok(ChcExpr::Op(ChcOp::And, args))
    }
}

fn validate(
    expr: &ChcExpr,
    formals: &Formals<'_>,
    depth: usize,
    scope: &mut Scope<'_>,
) -> Result<Typed, Failure> {
    scope.depth(depth)?;
    scope.node()?;
    match expr {
        ChcExpr::Bool(_) => Ok(Typed {
            sort: ChcSort::Bool,
            closed: true,
            arrays: false,
        }),
        ChcExpr::BitVec(value, width)
            if (1..=128).contains(width) && (*width == 128 || *value >> width == 0) =>
        {
            Ok(Typed {
                sort: ChcSort::BitVec(*width),
                closed: true,
                arrays: false,
            })
        }
        ChcExpr::Var(var) => {
            let closed = formals.contains(var, scope)?;
            charge_sort(&var.sort, depth, scope)?;
            Ok(Typed {
                sort: var.sort.clone(),
                closed,
                arrays: matches!(var.sort, ChcSort::Array(..)),
            })
        }
        ChcExpr::ConstArray(key, value) => {
            charge_sort(key, depth + 1, scope)?;
            let value = validate(value, formals, depth + 1, scope)?;
            scope.grow::<ChcSort>(2)?;
            Ok(Typed {
                sort: ChcSort::Array(Box::new(key.clone()), Box::new(value.sort)),
                closed: value.closed,
                arrays: true,
            })
        }
        ChcExpr::Op(op, args) => operation(*op, args, formals, depth, scope),
        // No UFs, datatype calls, parser markers, or implicit binders are
        // accepted on the strength of a free-variable scan alone.
        _ => Err(Failure::Declined),
    }
}

fn operation(
    op: ChcOp,
    args: &[Arc<ChcExpr>],
    formals: &Formals<'_>,
    depth: usize,
    scope: &mut Scope<'_>,
) -> Result<Typed, Failure> {
    scope.grow::<ChcSort>(args.len())?;
    let mut sorts = Vec::with_capacity(args.len());
    let mut closed = true;
    let mut arrays = false;
    for arg in args {
        let typed = validate(arg, formals, depth + 1, scope)?;
        closed &= typed.closed;
        arrays |= typed.arrays;
        // The shared strict validator compares argument sorts and may clone
        // one result sort. Prepay the complete spines before calling it.
        charge_sort(&typed.sort, depth, scope)?;
        sorts.push(typed.sort);
    }
    scope.work(args.len().saturating_add(1))?;
    let sort = crate::pdr::validate_qf_operation(op, &sorts).map_err(|_| Failure::Declined)?;
    charge_sort(&sort, depth, scope)?;
    Ok(Typed {
        sort,
        closed,
        arrays,
    })
}
