// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Typed, metered DAG storage: no opaque expression cloning or substitution.

use super::control::{Failure, Scope};
use super::formals::Formals;
use super::{Arc, ChcExpr, ChcOp, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashMap;

pub(super) type Id = usize;

pub(super) enum Kind {
    Bool(bool),
    BitVec(u128, u32),
    Var(usize),
    Op(ChcOp, Vec<Id>),
    ConstArray(Id),
}

pub(super) struct Node {
    pub(super) kind: Kind,
    pub(super) sort: ChcSort,
}

pub(super) struct Arena<'a> {
    pub(super) nodes: Vec<Node>,
    pub(super) vars: Vec<&'a ChcVar>,
    pub(super) kept: usize,
    pub(super) formals: Formals<'a>,
    names: DetHashMap<&'a str, usize>,
}

fn scalar(sort: &ChcSort) -> bool {
    matches!(sort, ChcSort::Bool | ChcSort::BitVec(1..=128))
}

fn supported(sort: &ChcSort) -> bool {
    scalar(sort) || matches!(sort, ChcSort::Array(key, value) if scalar(key) && scalar(value))
}

/// Scalar clones allocate nothing. Flat array clones own two boxed sorts;
/// reserve their cumulative storage before invoking the ordinary clone.
fn clone_sort(sort: &ChcSort, scope: &mut Scope<'_>) -> Result<ChcSort, Failure> {
    if !supported(sort) {
        return Err(Failure::Declined);
    }
    if matches!(sort, ChcSort::Array(_, _)) {
        scope.work(2)?;
        scope.grow::<ChcSort>(2)?;
    }
    Ok(sort.clone())
}

impl<'a> Arena<'a> {
    pub(super) fn new(keep: &'a [ChcVar], scope: &mut Scope<'_>) -> Result<Self, Failure> {
        let mut arena = Self {
            nodes: Vec::new(),
            vars: Vec::new(),
            kept: 0,
            formals: Formals::new(keep, scope)?,
            names: DetHashMap::default(),
        };
        for var in keep {
            scope.work(1)?;
            if supported(&var.sort) {
                arena.variable(var, scope)?;
            } else if matches!(var.sort, ChcSort::Array(..)) {
                // An unused scalar formal outside the arena is harmless; an
                // opaque or nested array formal still declines (5eb47055a).
                return Err(Failure::Declined);
            }
        }
        arena.kept = arena.vars.len();
        Ok(arena)
    }

    fn variable(&mut self, var: &'a ChcVar, scope: &mut Scope<'_>) -> Result<usize, Failure> {
        scope.work(var.name.len().saturating_add(1))?;
        if !supported(&var.sort) {
            return Err(Failure::Declined);
        }
        self.formals.contains(var, scope)?;
        if let Some(&id) = self.names.get(var.name.as_str()) {
            return if self.vars[id].sort == var.sort {
                Ok(id)
            } else {
                Err(Failure::Declined)
            };
        }
        scope.grow::<&ChcVar>(1)?;
        scope.grow::<(&str, usize)>(2)?;
        let id = self.vars.len();
        self.vars.push(var);
        self.names.insert(var.name.as_str(), id);
        Ok(id)
    }

    pub(super) fn push(
        &mut self,
        kind: Kind,
        sort: ChcSort,
        scope: &mut Scope<'_>,
    ) -> Result<Id, Failure> {
        scope.node()?;
        scope.grow::<Node>(1)?;
        let id = self.nodes.len();
        self.nodes.push(Node { kind, sort });
        Ok(id)
    }

    pub(super) fn read(
        &mut self,
        expr: &'a ChcExpr,
        depth: usize,
        scope: &mut Scope<'_>,
    ) -> Result<Id, Failure> {
        scope.depth(depth)?;
        match expr {
            ChcExpr::Bool(value) => self.push(Kind::Bool(*value), ChcSort::Bool, scope),
            ChcExpr::BitVec(value, width) if (1..=128).contains(width) => {
                if *width < 128 && *value >> width != 0 {
                    return Err(Failure::Declined);
                }
                self.push(Kind::BitVec(*value, *width), ChcSort::BitVec(*width), scope)
            }
            ChcExpr::Var(var) => {
                let id = self.variable(var, scope)?;
                self.push(Kind::Var(id), clone_sort(&var.sort, scope)?, scope)
            }
            ChcExpr::Op(op, args) => {
                scope.grow::<Id>(args.len())?;
                let mut children = Vec::with_capacity(args.len());
                for arg in args {
                    children.push(self.read(arg, depth + 1, scope)?);
                }
                // Validate the complete source before any simplification can
                // hide malformed or unsupported subexpressions in dead arms.
                self.operation(*op, children, scope)
            }
            ChcExpr::ConstArray(key, value) => {
                if !scalar(key) {
                    return Err(Failure::Declined);
                }
                let value = self.read(value, depth + 1, scope)?;
                self.constant_array(key, value, scope)
            }
            _ => Err(Failure::Declined),
        }
    }

    pub(super) fn constant_array(
        &mut self,
        key: &ChcSort,
        value: Id,
        scope: &mut Scope<'_>,
    ) -> Result<Id, Failure> {
        scope.work(2)?;
        if !scalar(key) || !scalar(&self.nodes[value].sort) {
            return Err(Failure::Declined);
        }
        scope.grow::<ChcSort>(2)?;
        let sort = ChcSort::Array(
            Box::new(key.clone()),
            Box::new(self.nodes[value].sort.clone()),
        );
        self.push(Kind::ConstArray(value), sort, scope)
    }

    /// All expression children, including the default of a constant array.
    /// Closure, occurrence and exclusive-use walks must use this same list.
    pub(super) fn children(&self, id: Id) -> &[Id] {
        match &self.nodes[id].kind {
            Kind::Op(_, args) => args,
            Kind::ConstArray(value) => std::slice::from_ref(value),
            Kind::Bool(_) | Kind::BitVec(_, _) | Kind::Var(_) => &[],
        }
    }

    pub(super) fn operation(
        &mut self,
        op: ChcOp,
        args: Vec<Id>,
        scope: &mut Scope<'_>,
    ) -> Result<Id, Failure> {
        scope.work(args.len().saturating_add(1))?;
        scope.grow::<ChcSort>(args.len())?;
        let mut sorts = Vec::with_capacity(args.len());
        for id in &args {
            sorts.push(clone_sort(&self.nodes[*id].sort, scope)?);
        }
        // The operation validator may clone an array result (store or ITE).
        // Reserve an upper bound before calling it, including invalid inputs.
        if sorts
            .iter()
            .any(|sort| matches!(sort, ChcSort::Array(_, _)))
        {
            scope.work(2)?;
            scope.grow::<ChcSort>(2)?;
        }
        let sort = crate::pdr::validate_qf_operation(op, &sorts).map_err(|_| Failure::Declined)?;
        if !supported(&sort) {
            return Err(Failure::Declined);
        }
        self.push(Kind::Op(op, args), sort, scope)
    }

    /// Internal Boolean composition accepts its mathematical identities and
    /// singleton form. Source syntax always goes through `operation` instead,
    /// so these reductions cannot hide malformed source arities or sorts.
    pub(super) fn join(
        &mut self,
        op: ChcOp,
        args: Vec<Id>,
        scope: &mut Scope<'_>,
    ) -> Result<Id, Failure> {
        scope.work(args.len().saturating_add(1))?;
        if !matches!(op, ChcOp::And | ChcOp::Or)
            || args.iter().any(|id| self.nodes[*id].sort != ChcSort::Bool)
        {
            return Err(Failure::Declined);
        }
        match args.as_slice() {
            [] => self.push(Kind::Bool(op == ChcOp::And), ChcSort::Bool, scope),
            [only] => Ok(*only),
            _ => self.operation(op, args, scope),
        }
    }

    pub(super) fn same(&self, lhs: Id, rhs: Id, scope: &mut Scope<'_>) -> Result<bool, Failure> {
        scope.grow::<(Id, Id)>(1)?;
        let mut pending = vec![(lhs, rhs)];
        while let Some((lhs, rhs)) = pending.pop() {
            scope.work(1)?;
            if lhs == rhs {
                continue;
            }
            match (&self.nodes[lhs].kind, &self.nodes[rhs].kind) {
                (Kind::Var(a), Kind::Var(b)) if a == b => {}
                (Kind::Bool(a), Kind::Bool(b)) if a == b => {}
                (Kind::BitVec(a, aw), Kind::BitVec(b, bw)) if a == b && aw == bw => {}
                (Kind::Op(a, aa), Kind::Op(b, ba)) if a == b && aa.len() == ba.len() => {
                    scope.grow::<(Id, Id)>(aa.len())?;
                    pending.extend(aa.iter().copied().zip(ba.iter().copied()));
                }
                (Kind::ConstArray(a), Kind::ConstArray(b))
                    if self.nodes[lhs].sort == self.nodes[rhs].sort =>
                {
                    scope.grow::<(Id, Id)>(1)?;
                    pending.push((*a, *b));
                }
                _ => return Ok(false),
            }
        }
        Ok(true)
    }

    pub(super) fn contains(
        &self,
        root: Id,
        variable: usize,
        scope: &mut Scope<'_>,
    ) -> Result<bool, Failure> {
        scope.grow::<Id>(1)?;
        let mut pending = vec![root];
        while let Some(id) = pending.pop() {
            scope.work(1)?;
            match &self.nodes[id].kind {
                Kind::Var(var) if *var == variable => return Ok(true),
                _ => {
                    let children = self.children(id);
                    if !children.is_empty() {
                        scope.grow::<Id>(children.len())?;
                        pending.extend(children.iter().copied());
                    }
                }
            }
        }
        Ok(false)
    }

    pub(super) fn closed(&self, root: Id, scope: &mut Scope<'_>) -> Result<bool, Failure> {
        scope.grow::<Id>(1)?;
        let mut pending = vec![root];
        while let Some(id) = pending.pop() {
            scope.work(1)?;
            match &self.nodes[id].kind {
                Kind::Var(var) if *var >= self.kept => return Ok(false),
                _ => {
                    let children = self.children(id);
                    if !children.is_empty() {
                        scope.grow::<Id>(children.len())?;
                        pending.extend(children.iter().copied());
                    }
                }
            }
        }
        Ok(true)
    }

    pub(super) fn export(&self, root: Id, scope: &mut Scope<'_>) -> Result<ChcExpr, Failure> {
        scope.grow::<Option<Arc<ChcExpr>>>(self.nodes.len())?;
        let mut cache = vec![None; self.nodes.len()];
        let result = self.emit(root, &mut cache, 0, scope)?;
        // The cache may own the root too. Bound its shallow clone explicitly.
        match result.as_ref() {
            ChcExpr::Op(_, args) => scope.grow::<Arc<ChcExpr>>(args.len())?,
            ChcExpr::Var(var) => scope.grow::<u8>(var.name.len())?,
            _ => scope.work(1)?,
        }
        let result = Arc::unwrap_or_clone(result);
        scope.poll()?;
        Ok(result)
    }

    fn emit(
        &self,
        id: Id,
        cache: &mut [Option<Arc<ChcExpr>>],
        depth: usize,
        scope: &mut Scope<'_>,
    ) -> Result<Arc<ChcExpr>, Failure> {
        scope.depth(depth)?;
        if let Some(expr) = &cache[id] {
            return Ok(Arc::clone(expr));
        }
        scope.grow::<ChcExpr>(1)?;
        let expr = match &self.nodes[id].kind {
            Kind::Bool(value) => ChcExpr::Bool(*value),
            Kind::BitVec(value, width) => ChcExpr::BitVec(*value, *width),
            Kind::Var(var) => {
                scope.grow::<u8>(self.vars[*var].name.len())?;
                ChcExpr::Var(ChcVar {
                    name: self.vars[*var].name.clone(),
                    sort: clone_sort(&self.vars[*var].sort, scope)?,
                })
            }
            Kind::Op(op, args) => {
                scope.grow::<Arc<ChcExpr>>(args.len())?;
                let mut children = Vec::with_capacity(args.len());
                for child in args {
                    children.push(self.emit(*child, cache, depth + 1, scope)?);
                }
                ChcExpr::Op(*op, children)
            }
            Kind::ConstArray(value) => {
                let ChcSort::Array(key, _) = &self.nodes[id].sort else {
                    return Err(Failure::Declined);
                };
                ChcExpr::ConstArray(
                    clone_sort(key, scope)?,
                    self.emit(*value, cache, depth + 1, scope)?,
                )
            }
        };
        let expr = Arc::new(expr);
        cache[id] = Some(Arc::clone(&expr));
        Ok(expr)
    }
}
