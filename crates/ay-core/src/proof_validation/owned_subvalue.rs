// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded containment witnesses for native inductive values with sequences.
//! Datatype fields decrease owned structure. A sequence element preserves
//! containment but is never by itself a strict datatype descent. In particular
//! no sequence concatenation is treated as a strict edge.
//!
//! Constructor identities and current equality/literal classes are supplied by
//! the theory context; a witness grants no authority to those inputs. A proof
//! checker must rebuild them from its own exact clause and declaration context.

use crate::{Constant, Sort, Symbol, TermData, TermId, TermStore, TheoryLit};
use num_traits::Zero;
use std::mem::size_of;

/// Borrowed registered constructor and exact nominal result carrier.
#[derive(Clone, Copy)]
pub struct OwnedSubvalueConstructor<'a> {
    /// Actual internal declaration identity, never a guessed public spelling.
    pub identity: &'a str,
    /// Actual nominal datatype carrier.
    pub carrier: &'a str,
}

/// The native semantics justifying one containment edge.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OwnedSubvalueEdgeKind {
    /// One actual constructor field; this is strict owned datatype descent.
    DatatypeField {
        /// Zero-based field in declaration order.
        index: usize,
    },
    /// The element in a well-sorted native `seq.unit`.
    SequenceUnit,
    /// An actual native `seq.nth`, with both exact in-bounds premises.
    SequenceNth {
        /// Lower-bound premise; absent only for literal index zero.
        lower: Option<TheoryLit>,
        /// Strict upper-bound premise.
        upper: TheoryLit,
    },
}

/// Original term endpoints, retained separately from their equality classes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OwnedSubvalueEdge {
    /// Value containing the field/element.
    pub container: TermId,
    /// Contained field/element value.
    pub content: TermId,
    /// Independently reconstructible semantic source.
    pub kind: OwnedSubvalueEdgeKind,
}

/// Ordered cycle. Consecutive content/container endpoints must be explained
/// equal in the caller's current context, including the last-to-first link.
#[derive(Debug)]
pub struct OwnedSubvalueCycle {
    /// The first edge is always an actual strict datatype field edge.
    pub edges: Vec<OwnedSubvalueEdge>,
}

/// A refusal conveys no theorem and allocates no source-controlled diagnostic.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OwnedSubvalueRefusal {
    /// Cumulative work/storage/depth allowance was exhausted.
    Limit,
    /// Caller/resource cancellation was observed.
    Cancelled,
    /// Input contains an invalid handle or incomplete source universe.
    InvalidSource,
    /// A bounded workspace reservation failed.
    Allocation,
}

/// Cumulative owner shared by all checks in one theory/checker invocation.
/// Scope rollback does not replenish it.
#[derive(Debug)]
pub struct OwnedSubvalueBudget {
    work: usize,
    storage: usize,
    refusal: Option<OwnedSubvalueRefusal>,
}
impl OwnedSubvalueBudget {
    /// Explicit finite allowance; zero remains zero.
    pub const fn new(work: usize, storage: usize) -> Self {
        Self {
            work,
            storage,
            refusal: None,
        }
    }
    /// Spend source/workspace admission through this same cumulative owner.
    pub fn charge_with_progress(
        &mut self,
        work: usize,
        storage: usize,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<(), OwnedSubvalueRefusal> {
        Meter {
            owner: self,
            progress,
        }
        .pay(work, storage)
    }
    /// First resource refusal, retained across later calls.
    pub const fn refusal(&self) -> Option<OwnedSubvalueRefusal> {
        self.refusal
    }
}
struct Meter<'a> {
    owner: &'a mut OwnedSubvalueBudget,
    progress: &'a mut dyn FnMut(usize, usize) -> bool,
}
impl Meter<'_> {
    fn fail<T>(&mut self, reason: OwnedSubvalueRefusal) -> Result<T, OwnedSubvalueRefusal> {
        Err(*self.owner.refusal.get_or_insert(reason))
    }
    fn pay(&mut self, work: usize, storage: usize) -> Result<(), OwnedSubvalueRefusal> {
        if let Some(reason) = self.owner.refusal {
            return Err(reason);
        }
        let (Some(left_work), Some(left_storage)) = (
            self.owner.work.checked_sub(work),
            self.owner.storage.checked_sub(storage),
        ) else {
            return self.fail(OwnedSubvalueRefusal::Limit);
        };
        if work == usize::MAX || storage == usize::MAX {
            return self.fail(OwnedSubvalueRefusal::Limit);
        }
        self.owner.refusal = Some(OwnedSubvalueRefusal::Cancelled);
        if !(self.progress)(work, storage) || crate::resource::check_stop_requested() {
            return Err(OwnedSubvalueRefusal::Cancelled);
        }
        self.owner.refusal = None;
        self.owner.work = left_work;
        self.owner.storage = left_storage;
        Ok(())
    }
    fn push<T>(&mut self, vec: &mut Vec<T>, value: T) -> Result<(), OwnedSubvalueRefusal> {
        if vec.len() == vec.capacity() {
            let next = vec.capacity().saturating_mul(2).max(4);
            self.pay(vec.len(), next.saturating_mul(size_of::<T>()))?;
            vec.try_reserve_exact(next.saturating_sub(vec.len()))
                .map_err(|_| {
                    *self
                        .owner
                        .refusal
                        .get_or_insert(OwnedSubvalueRefusal::Allocation)
                })?;
        }
        vec.push(value);
        Ok(())
    }
}

fn sort_eq(a: &Sort, b: &Sort, meter: &mut Meter<'_>) -> Result<bool, OwnedSubvalueRefusal> {
    let mut pending = Vec::new();
    meter.push(&mut pending, (a, b, 0usize))?;
    while let Some((a, b, depth)) = pending.pop() {
        meter.pay(1, 0)?;
        if depth >= 128 {
            return meter.fail(OwnedSubvalueRefusal::Limit);
        }
        match (a, b) {
            (Sort::Bool, Sort::Bool)
            | (Sort::Int, Sort::Int)
            | (Sort::Real, Sort::Real)
            | (Sort::String, Sort::String)
            | (Sort::RegLan, Sort::RegLan)
            | (Sort::Char, Sort::Char) => {}
            (Sort::Uninterpreted(a), Sort::Uninterpreted(b))
            | (Sort::TypeVar(a), Sort::TypeVar(b)) => {
                meter.pay(a.len().saturating_add(b.len()), 0)?;
                if a != b {
                    return Ok(false);
                }
            }
            (Sort::FiniteDomain(a, n), Sort::FiniteDomain(b, m)) => {
                meter.pay(a.len().saturating_add(b.len()), 0)?;
                if a != b || n != m {
                    return Ok(false);
                }
            }
            (Sort::BitVec(a), Sort::BitVec(b)) if a == b => {}
            (Sort::FloatingPoint(a, b), Sort::FloatingPoint(c, d)) if a == c && b == d => {}
            (Sort::Seq(a), Sort::Seq(b)) => meter.push(&mut pending, (&**a, &**b, depth + 1))?,
            (Sort::Array(a), Sort::Array(b)) => {
                meter.push(&mut pending, (&a.index_sort, &b.index_sort, depth + 1))?;
                meter.push(&mut pending, (&a.element_sort, &b.element_sort, depth + 1))?;
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}

struct Node {
    id: TermId,
    class: u64,
    truth: Option<bool>,
}
fn index(nodes: &[Node], id: TermId, meter: &mut Meter<'_>) -> Result<usize, OwnedSubvalueRefusal> {
    meter.pay(nodes.len().saturating_add(1), 0)?;
    nodes
        .binary_search_by_key(&id, |node| node.id)
        .map_err(|_| OwnedSubvalueRefusal::InvalidSource)
}
fn class(nodes: &[Node], id: TermId, meter: &mut Meter<'_>) -> Result<u64, OwnedSubvalueRefusal> {
    Ok(nodes[index(nodes, id, meter)?].class)
}
fn zero(terms: &TermStore, id: TermId) -> bool {
    matches!(terms.get(id), TermData::Const(Constant::Int(value)) if value.is_zero())
}
fn len_of(
    terms: &TermStore,
    nodes: &[Node],
    len: TermId,
    sequence: TermId,
    meter: &mut Meter<'_>,
) -> Result<bool, OwnedSubvalueRefusal> {
    if terms.entry_stamp(len).is_none() {
        return Err(OwnedSubvalueRefusal::InvalidSource);
    }
    let TermData::App(Symbol::Named(name), args) = terms.get(len) else {
        return Ok(false);
    };
    meter.pay(name.len().saturating_add(1), 0)?;
    if name != "seq.len" || args.len() != 1 || terms.sort(len) != &Sort::Int {
        return Ok(false);
    }
    if terms.entry_stamp(args[0]).is_none() || !matches!(terms.sort(args[0]), Sort::Seq(_)) {
        return Ok(false);
    }
    Ok(class(nodes, args[0], meter)? == class(nodes, sequence, meter)?)
}

fn guards(
    terms: &TermStore,
    nodes: &[Node],
    sequence: TermId,
    at: TermId,
    meter: &mut Meter<'_>,
) -> Result<Option<(Option<TheoryLit>, TheoryLit)>, OwnedSubvalueRefusal> {
    let mut lower = if zero(terms, at) { Some(None) } else { None };
    let mut upper = None;
    for node in nodes {
        meter.pay(1, 0)?;
        let Some(value) = node.truth else {
            continue;
        };
        if terms.sort(node.id) != &Sort::Bool {
            continue;
        }
        let TermData::App(Symbol::Named(name), args) = terms.get(node.id) else {
            continue;
        };
        meter.pay(name.len().saturating_add(1), 0)?;
        if args.len() != 2 || !matches!(name.as_str(), "<" | "<=" | ">" | ">=") {
            continue;
        }
        if args
            .iter()
            .any(|&arg| terms.entry_stamp(arg).is_none() || terms.sort(arg) != &Sort::Int)
        {
            return Err(OwnedSubvalueRefusal::InvalidSource);
        }
        let mut left = args[0];
        let mut right = args[1];
        let strict = matches!(name.as_str(), "<" | ">");
        if matches!(name.as_str(), ">" | ">=") {
            std::mem::swap(&mut left, &mut right);
        }
        // Canonical true comparison: left < right (strict) or left <= right.
        // False comparison reverses operands and flips strictness.
        let strict = if value {
            strict
        } else {
            std::mem::swap(&mut left, &mut right);
            !strict
        };
        let literal = TheoryLit::new(node.id, value);
        if !strict && zero(terms, left) && class(nodes, right, meter)? == class(nodes, at, meter)? {
            lower = Some(Some(literal));
        }
        if strict
            && class(nodes, left, meter)? == class(nodes, at, meter)?
            && len_of(terms, nodes, right, sequence, meter)?
        {
            upper = Some(literal);
        }
        if let (Some(lower), Some(upper)) = (lower, upper) {
            return Ok(Some((lower, upper)));
        }
    }
    Ok(None)
}

/// Build a genuine cycle from the current typed term universe and equality
/// classes. `classify` supplies class identity and an exact currently asserted
/// Boolean value (None when unknown); no proposed model values are used.
///
/// All needed terms must occur once in `universe`. Work/storage refusal is
/// sticky in the caller's owner; every later check spends the same allowance.
/// Constructor declaration/schema authentication remains the caller's duty.
pub fn owned_subvalue_cycle_with_progress(
    terms: &TermStore,
    constructors: &[OwnedSubvalueConstructor<'_>],
    universe: &[TermId],
    classify: &mut dyn FnMut(TermId) -> (u64, Option<bool>),
    budget: &mut OwnedSubvalueBudget,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<Option<OwnedSubvalueCycle>, OwnedSubvalueRefusal> {
    let mut meter = Meter {
        owner: budget,
        progress,
    };
    meter.pay(universe.len().saturating_add(constructors.len()), 0)?;
    if universe.len() > 4096 {
        return meter.fail(OwnedSubvalueRefusal::Limit);
    }
    let mut nodes = Vec::new();
    for &id in universe {
        if terms.entry_stamp(id).is_none() {
            return Err(OwnedSubvalueRefusal::InvalidSource);
        }
        meter.pay(universe.len().saturating_add(1), 0)?;
        let (class, truth) = classify(id);
        meter.push(&mut nodes, Node { id, class, truth })?;
    }
    meter.pay(nodes.len().saturating_mul(nodes.len()), 0)?;
    nodes.sort_unstable_by_key(|node| node.id);
    if nodes.windows(2).any(|pair| pair[0].id == pair[1].id) {
        return Err(OwnedSubvalueRefusal::InvalidSource);
    }
    // Equality classes must remain typed even when a direct theory/checker
    // caller supplied malformed input. Cross-sort class aliases confer no
    // ownership theorem.
    let mut class_sorts = Vec::new();
    for (position, node) in nodes.iter().enumerate() {
        meter.push(&mut class_sorts, (node.class, position))?;
    }
    meter.pay(nodes.len().saturating_mul(nodes.len()), 0)?;
    class_sorts.sort_unstable_by_key(|&(class, _)| class);
    for pair in class_sorts.windows(2) {
        if pair[0].0 == pair[1].0
            && !sort_eq(
                terms.sort(nodes[pair[0].1].id),
                terms.sort(nodes[pair[1].1].id),
                &mut meter,
            )?
        {
            return Err(OwnedSubvalueRefusal::InvalidSource);
        }
    }
    let mut edges = Vec::new();
    for node in &nodes {
        meter.pay(1, 0)?;
        let TermData::App(Symbol::Named(name), args) = terms.get(node.id) else {
            continue;
        };
        meter.pay(name.len().saturating_add(args.len()), 0)?;
        let mut registered = false;
        for constructor in constructors {
            meter.pay(
                name.len()
                    .saturating_add(constructor.identity.len())
                    .saturating_add(constructor.carrier.len()),
                0,
            )?;
            if name == constructor.identity
                && matches!(terms.sort(node.id),Sort::Uninterpreted(carrier) if carrier==constructor.carrier)
            {
                registered = true;
                break;
            }
        }
        if registered {
            for (field, &content) in args.iter().enumerate() {
                index(&nodes, content, &mut meter)?;
                meter.push(
                    &mut edges,
                    OwnedSubvalueEdge {
                        container: node.id,
                        content,
                        kind: OwnedSubvalueEdgeKind::DatatypeField { index: field },
                    },
                )?;
            }
        } else if name == "seq.unit" && args.len() == 1 {
            let content = args[0];
            index(&nodes, content, &mut meter)?;
            if let Sort::Seq(element) = terms.sort(node.id) {
                if sort_eq(element, terms.sort(content), &mut meter)? {
                    meter.push(
                        &mut edges,
                        OwnedSubvalueEdge {
                            container: node.id,
                            content,
                            kind: OwnedSubvalueEdgeKind::SequenceUnit,
                        },
                    )?;
                }
            }
        } else if name == "seq.nth" && args.len() == 2 {
            let sequence = args[0];
            let at = args[1];
            index(&nodes, sequence, &mut meter)?;
            index(&nodes, at, &mut meter)?;
            if let Sort::Seq(element) = terms.sort(sequence) {
                if terms.sort(at) == &Sort::Int
                    && sort_eq(element, terms.sort(node.id), &mut meter)?
                {
                    if let Some((lower, upper)) = guards(terms, &nodes, sequence, at, &mut meter)? {
                        meter.push(
                            &mut edges,
                            OwnedSubvalueEdge {
                                container: sequence,
                                content: node.id,
                                kind: OwnedSubvalueEdgeKind::SequenceNth { lower, upper },
                            },
                        )?;
                    }
                }
            }
        }
    }
    // Search back from the content of an explicitly strict edge. Weak-only
    // cycles are harmless, and are never promoted to an inductive cycle.
    for (first, edge) in edges.iter().enumerate() {
        if !matches!(edge.kind, OwnedSubvalueEdgeKind::DatatypeField { .. }) {
            continue;
        }
        let target = class(&nodes, edge.container, &mut meter)?;
        let start = class(&nodes, edge.content, &mut meter)?;
        let mut pending = Vec::new();
        let mut seen = Vec::new();
        let mut parents = Vec::<(u64, u64, usize)>::new();
        meter.push(&mut pending, start)?;
        while let Some(current) = pending.pop() {
            meter.pay(seen.len().saturating_add(1), 0)?;
            if seen.contains(&current) {
                continue;
            }
            meter.push(&mut seen, current)?;
            if current == target {
                let mut path = Vec::new();
                let mut at = target;
                while at != start {
                    meter.pay(1, 0)?;
                    meter.pay(parents.len().saturating_add(1), 0)?;
                    let &(_, previous, via) = parents
                        .iter()
                        .find(|&&(node, _, _)| node == at)
                        .ok_or(OwnedSubvalueRefusal::InvalidSource)?;
                    meter.push(&mut path, edges[via])?;
                    at = previous;
                }
                path.reverse();
                let mut cycle = Vec::new();
                meter.push(&mut cycle, edges[first])?;
                for edge in path {
                    meter.push(&mut cycle, edge)?;
                }
                meter.pay(0, 0)?;
                return Ok(Some(OwnedSubvalueCycle { edges: cycle }));
            }
            for (via, candidate) in edges.iter().enumerate() {
                meter.pay(1, 0)?;
                if class(&nodes, candidate.container, &mut meter)? != current {
                    continue;
                }
                let next = class(&nodes, candidate.content, &mut meter)?;
                meter.pay(
                    seen.len().saturating_add(parents.len()).saturating_add(1),
                    0,
                )?;
                if !seen.contains(&next)
                    && !parents.iter().any(|&(node, _, _)| node == next)
                    && next != start
                {
                    meter.push(&mut parents, (next, current, via))?;
                    meter.push(&mut pending, next)?;
                }
            }
        }
    }
    meter.pay(0, 0)?;
    Ok(None)
}

#[cfg(test)]
mod tests;
