// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fresh, query-local Boolean proxies. Hashes only index borrowed name
//! buckets: every collision is compared byte-for-byte, never trusted as
//! identity. The borrowed roots keep all DAG pointers and names alive.

use crate::{ChcExpr, ChcSort};
use std::collections::{BTreeMap, BTreeSet};

#[cfg(test)]
mod tests;

/// Test adapter over the SAME production mapper. Production attribution below
/// instead uses the retained query-preparation credit and original callback.
#[cfg(test)]
pub(in crate::pdr::solver) fn map_proxies(
    conjuncts: &[ChcExpr],
    proxies: &[ChcExpr],
) -> Option<Vec<bool>> {
    map(conjuncts, proxies, &mut Admission::new(), &mut || {
        !crate::smt::smt_deadline_expired() && !ay_sys::current_memory_group_soft_tripped()
    })
}

pub(super) struct Admission {
    remaining: Option<usize>,
}

impl Admission {
    pub(super) fn new() -> Self {
        Self {
            remaining: Some(crate::expr::MAX_PREPROCESSING_NODES),
        }
    }

    fn spend(&mut self, amount: usize, open: &mut impl FnMut() -> bool) -> Option<()> {
        let remaining = self.remaining?;
        if !open() {
            return self.refuse();
        }
        self.remaining = remaining.checked_sub(amount);
        self.remaining.map(|_| ())
    }

    fn refuse<T>(&mut self) -> Option<T> {
        self.remaining = None;
        None
    }

    fn tree(&mut self, len: usize, open: &mut impl FnMut() -> bool) -> Option<()> {
        // Integer keys have constant-size comparisons. Twelve comparisons per
        // binary-height bound also covers a B-tree node's linear key search.
        let height = len.bit_width() as usize + 1;
        self.spend(height.checked_mul(12)?, open)
    }

    pub(super) fn reserve<T>(
        &mut self,
        into: &mut Vec<T>,
        count: usize,
        open: &mut impl FnMut() -> bool,
    ) -> Option<()> {
        self.spend(count, open)?;
        if into.try_reserve_exact(count).is_err() {
            return self.refuse();
        }
        self.spend(0, open)
    }

    fn push<T>(
        &mut self,
        into: &mut Vec<T>,
        value: T,
        open: &mut impl FnMut() -> bool,
    ) -> Option<()> {
        self.spend(1, open)?;
        if into.len() == into.capacity() {
            // Prepay the live elements moved by a backing-allocation change.
            let additional = into.capacity().max(1);
            self.spend(into.len().checked_add(additional)?, open)?;
            if into.try_reserve_exact(additional).is_err() {
                return self.refuse();
            }
        }
        into.push(value);
        self.spend(0, open)
    }

    fn name_hash(&mut self, name: &str, open: &mut impl FnMut() -> bool) -> Option<u64> {
        let mut hash = 0xcbf2_9ce4_8422_2325u64;
        for byte in name.bytes() {
            self.spend(1, open)?;
            hash = (hash ^ u64::from(byte)).wrapping_mul(0x100_0000_01b3);
        }
        Some(hash)
    }

    fn same_name(&mut self, a: &str, b: &str, open: &mut impl FnMut() -> bool) -> Option<bool> {
        self.spend(1, open)?;
        if a.len() != b.len() {
            return Some(false);
        }
        for (x, y) in a.bytes().zip(b.bytes()) {
            self.spend(1, open)?;
            if x != y {
                return Some(false);
            }
        }
        Some(true)
    }

    /// Prepay the owned part of a derived root clone. Expression children and
    /// datatype metadata are Arc clones, but names, argument vectors and boxed
    /// array sorts are owned. No recursive source walk or new credit is used.
    pub(super) fn root_copy(
        &mut self,
        expr: &ChcExpr,
        open: &mut impl FnMut() -> bool,
    ) -> Option<()> {
        let mut sorts = Vec::new();
        match expr {
            ChcExpr::ArrayLambda(_) => return self.refuse(),
            ChcExpr::Var(v) => {
                self.name_hash(&v.name, open)?;
                self.push(&mut sorts, (&v.sort, 0usize), open)?;
            }
            ChcExpr::Op(_, args) => self.spend(args.len(), open)?,
            ChcExpr::PredicateApp(name, _, args) => {
                self.name_hash(name, open)?;
                self.spend(args.len(), open)?;
            }
            ChcExpr::FuncApp(name, sort, args) => {
                self.name_hash(name, open)?;
                self.spend(args.len(), open)?;
                self.push(&mut sorts, (sort, 0), open)?;
            }
            ChcExpr::ConstArrayMarker(sort) | ChcExpr::ConstArray(sort, _) => {
                self.push(&mut sorts, (sort, 0), open)?;
            }
            ChcExpr::IsTesterMarker(name) => {
                self.name_hash(name, open)?;
            }
            ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _) => {}
        }
        while let Some((sort, depth)) = sorts.pop() {
            self.spend(1, open)?;
            // ChcSort's existing derived clone/drop is recursive for Array.
            // Refuse before invoking it on an unbounded-depth source sort.
            if depth >= crate::expr::MAX_EXPR_RECURSION_DEPTH {
                return self.refuse();
            }
            match sort {
                ChcSort::Array(key, value) => {
                    self.push(&mut sorts, (&**key, depth + 1), open)?;
                    self.push(&mut sorts, (&**value, depth + 1), open)?;
                }
                ChcSort::Uninterpreted(name) | ChcSort::Datatype { name, .. } => {
                    self.name_hash(name, open)?;
                }
                ChcSort::Bool | ChcSort::Int | ChcSort::Real | ChcSort::BitVec(_) => {}
            }
        }
        self.spend(0, open)
    }
}

#[derive(Default)]
struct Names<'a>(BTreeMap<u64, Vec<&'a str>>);

impl<'a> Names<'a> {
    fn insert(
        &mut self,
        name: &'a str,
        credit: &mut Admission,
        open: &mut impl FnMut() -> bool,
    ) -> Option<()> {
        let hash = credit.name_hash(name, open)?;
        credit.tree(self.0.len(), open)?;
        let bucket = self.0.entry(hash).or_default();
        for prior in bucket.iter() {
            if credit.same_name(prior, name, open)? {
                return Some(());
            }
        }
        credit.push(bucket, name, open)
    }

    fn contains(
        &self,
        name: &str,
        credit: &mut Admission,
        open: &mut impl FnMut() -> bool,
    ) -> Option<bool> {
        let hash = credit.name_hash(name, open)?;
        credit.tree(self.0.len(), open)?;
        if let Some(bucket) = self.0.get(&hash) {
            for prior in bucket {
                if credit.same_name(prior, name, open)? {
                    return Some(true);
                }
            }
        }
        credit.spend(0, open)?;
        Some(false)
    }
}

enum Node<'a> {
    Expr(&'a ChcExpr),
    Sort(&'a ChcSort),
}

fn expression<'a>(
    expr: &'a ChcExpr,
    names: &mut Names<'a>,
    pending: &mut Vec<Node<'a>>,
    credit: &mut Admission,
    open: &mut impl FnMut() -> bool,
) -> Option<()> {
    match expr {
        ChcExpr::ArrayLambda(_) => return credit.refuse(),
        ChcExpr::Var(v) => {
            names.insert(&v.name, credit, open)?;
            credit.push(pending, Node::Sort(&v.sort), open)?;
        }
        ChcExpr::Op(_, args) => {
            for arg in args {
                credit.push(pending, Node::Expr(arg), open)?;
            }
        }
        ChcExpr::PredicateApp(name, _, args) => {
            names.insert(name, credit, open)?;
            for arg in args {
                credit.push(pending, Node::Expr(arg), open)?;
            }
        }
        ChcExpr::FuncApp(name, sort, args) => {
            names.insert(name, credit, open)?;
            credit.push(pending, Node::Sort(sort), open)?;
            for arg in args {
                credit.push(pending, Node::Expr(arg), open)?;
            }
        }
        ChcExpr::ConstArrayMarker(sort) => credit.push(pending, Node::Sort(sort), open)?,
        ChcExpr::IsTesterMarker(name) => names.insert(name, credit, open)?,
        ChcExpr::ConstArray(sort, value) => {
            credit.push(pending, Node::Sort(sort), open)?;
            credit.push(pending, Node::Expr(value), open)?;
        }
        ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _) => {}
    }
    Some(())
}

fn sort<'a>(
    sort: &'a ChcSort,
    names: &mut Names<'a>,
    pending: &mut Vec<Node<'a>>,
    credit: &mut Admission,
    open: &mut impl FnMut() -> bool,
) -> Option<()> {
    match sort {
        ChcSort::Uninterpreted(name) => names.insert(name, credit, open)?,
        ChcSort::Array(key, value) => {
            credit.push(pending, Node::Sort(key), open)?;
            credit.push(pending, Node::Sort(value), open)?;
        }
        ChcSort::Datatype { name, constructors } => {
            names.insert(name, credit, open)?;
            for constructor in constructors.iter() {
                names.insert(&constructor.name, credit, open)?;
                for selector in &constructor.selectors {
                    names.insert(&selector.name, credit, open)?;
                    credit.push(pending, Node::Sort(&selector.sort), open)?;
                }
            }
        }
        ChcSort::Bool | ChcSort::Int | ChcSort::Real | ChcSort::BitVec(_) => {}
    }
    Some(())
}

fn census<'a>(
    bg: &'a [ChcExpr],
    lits: &'a [ChcExpr],
    credit: &mut Admission,
    open: &mut impl FnMut() -> bool,
) -> Option<Names<'a>> {
    let mut names = Names::default();
    let mut pending = Vec::new();
    let mut seen = BTreeSet::new();
    for root in bg.iter().chain(lits) {
        credit.push(&mut pending, Node::Expr(root), open)?;
    }
    while let Some(node) = pending.pop() {
        credit.spend(1, open)?;
        let key = match &node {
            Node::Expr(e) => (0u8, std::ptr::from_ref::<ChcExpr>(*e) as usize),
            Node::Sort(s) => (1u8, std::ptr::from_ref::<ChcSort>(*s) as usize),
        };
        credit.tree(seen.len(), open)?;
        if !seen.insert(key) {
            continue;
        }
        match node {
            Node::Expr(e) => expression(e, &mut names, &mut pending, credit, open)?,
            Node::Sort(s) => sort(s, &mut names, &mut pending, credit, open)?,
        }
    }
    credit.spend(0, open)?;
    Some(names)
}

pub(super) fn fresh(
    bg: &[ChcExpr],
    lits: &[ChcExpr],
    credit: &mut Admission,
    open: &mut impl FnMut() -> bool,
) -> Option<Vec<ChcExpr>> {
    let names = census(bg, lits, credit, open)?;
    let mut proxies = Vec::new();
    let mut next = 0usize;
    while proxies.len() < lits.len() {
        credit.spend(1, open)?;
        // Prefix and decimal usize rendering have a fixed, prepaid bound.
        credit.spend(super::PROXY_PREFIX.len() + usize::BITS as usize, open)?;
        let candidate = format!("{}{next}", super::PROXY_PREFIX);
        let Some(successor) = next.checked_add(1) else {
            return credit.refuse();
        };
        next = successor;
        if names.contains(&candidate, credit, open)? {
            continue;
        }
        // Monotone `next` makes all generated names pairwise distinct, including
        // when source spellings occupied earlier slots. No positional decode.
        let term = ChcExpr::var(crate::ChcVar::new(candidate, ChcSort::Bool));
        credit.push(&mut proxies, term, open)?;
    }
    credit.spend(0, open)?;
    Some(proxies)
}

pub(super) fn prepare(
    bg: &[ChcExpr],
    lits: &[ChcExpr],
    credit: &mut Admission,
    open: &mut impl FnMut() -> bool,
) -> Option<(Vec<ChcExpr>, Vec<ChcExpr>)> {
    let proxies = fresh(bg, lits, credit, open)?;
    let Some(capacity) = bg.len().checked_add(lits.len()) else {
        return credit.refuse();
    };
    let mut background = Vec::new();
    credit.reserve(&mut background, capacity, open)?;
    for root in bg {
        credit.root_copy(root, open)?;
        background.push(root.clone());
    }
    for (proxy, literal) in proxies.iter().zip(lits) {
        credit.root_copy(proxy, open)?;
        credit.root_copy(literal, open)?;
        credit.spend(3, open)?;
        background.push(ChcExpr::or(ChcExpr::not(proxy.clone()), literal.clone()));
    }
    credit.spend(0, open)?;
    Some((background, proxies))
}

pub(super) fn map(
    conjuncts: &[ChcExpr],
    proxies: &[ChcExpr],
    credit: &mut Admission,
    open: &mut impl FnMut() -> bool,
) -> Option<Vec<bool>> {
    // Core attribution is structural Bool-variable identity, not a positional
    // suffix, hash or display string. Foreign identities refuse the whole core.
    let mut core = Vec::new();
    for _ in proxies {
        credit.push(&mut core, false, open)?;
    }
    for conjunct in conjuncts {
        credit.spend(1, open)?;
        let ChcExpr::Var(found) = conjunct else {
            return credit.refuse();
        };
        if found.sort != ChcSort::Bool {
            return credit.refuse();
        }
        let mut matched = None;
        for (i, proxy) in proxies.iter().enumerate() {
            let ChcExpr::Var(expected) = proxy else {
                return credit.refuse();
            };
            if expected.sort != ChcSort::Bool {
                return credit.refuse();
            }
            if credit.same_name(&found.name, &expected.name, open)? {
                matched = Some(i);
                break;
            }
        }
        let Some(index) = matched else {
            return credit.refuse();
        };
        core[index] = true;
    }
    credit.spend(0, open)?;
    Some(core)
}
