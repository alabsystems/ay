// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded address spans selected from the original, positive guard. Recognition
//! grants no facts: the caller must prove the universally free offset query.

use super::*;

mod pricing;
pub(super) use pricing::candidate_bound;

#[derive(Clone, Copy)]
pub(crate) struct Address {
    pub(crate) base: Option<TermId>,
    pub(crate) offset: u128,
}

#[derive(Clone, Copy)]
pub(crate) struct Span {
    pub(crate) start: TermId,
    pub(crate) address: Address,
    pub(crate) length: u128,
}

#[derive(Clone)]
pub(crate) struct Shape {
    pub(crate) root: TermId,
    pub(crate) guards: [TermId; 3],
    pub(crate) width: u32,
    pub(crate) spans: [Span; 2],
}

fn binary(terms: &TermStore, term: TermId, op: &str) -> Option<[TermId; 2]> {
    terms.entry_stamp(term)?;
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    let [a, b] = args.as_slice() else { return None };
    (name == op).then_some([*a, *b])
}

fn ge(terms: &TermStore, term: TermId) -> Option<[TermId; 2]> {
    binary(terms, term, "bvuge").or_else(|| binary(terms, term, "bvule").map(|[a, b]| [b, a]))
}

fn conjuncts(terms: &TermStore, term: TermId) -> Option<&[TermId]> {
    terms.entry_stamp(term)?;
    let TermData::App(Symbol::Named(op), args) = terms.get(term) else {
        return None;
    };
    (op == "and" && !args.is_empty() && args.len() <= 128).then_some(args.as_slice())
}

// Select comparisons inside each positive branch, retaining the entire original
// disjunction as the premise. A selected comparison alone grants no fact.
fn branch_comparisons(terms: &TermStore, root: TermId) -> Option<Vec<[TermId; 2]>> {
    let mut pending = vec![root];
    let mut comparisons = Vec::new();
    let mut visited = 0;
    while let Some(term) = pending.pop() {
        visited += 1;
        if visited + pending.len() > 32 {
            return None;
        }
        terms.entry_stamp(term)?;
        if let Some(pair) = ge(terms, term) {
            comparisons.push(pair);
        } else if let Some(args) = conjuncts(terms, term) {
            pending.extend_from_slice(args);
        }
    }
    Some(comparisons)
}

// These select source premises only. The free-offset refutation still proves
// that their exact conjunction entails separation, including non-wrap.
fn nonwrap(
    terms: &TermStore,
    facts: &[TermId],
    start: TermId,
    end: TermId,
    length: u128,
    width: u32,
) -> Option<TermId> {
    let mask = u128::MAX >> (128 - width);
    facts.iter().copied().find(|&fact| {
        if binary(terms, fact, "bvugt") == Some([end, start])
            || binary(terms, fact, "bvult") == Some([start, end])
        {
            return true;
        }
        let Some([high, low]) = ge(terms, fact) else {
            return false;
        };
        let literal = |term| {
            terms.entry_stamp(term)?;
            let TermData::Const(Constant::BitVec {
                value,
                width: actual,
            }) = terms.get(term)
            else {
                return None;
            };
            (*actual == width && terms.sort(term) == &Sort::bitvec(width))
                .then(|| value.to_u128())
                .flatten()
        };
        // Accessed bytes must not wrap; the exclusive endpoint may be zero.
        (low == start && literal(high).is_some_and(|bound| bound <= mask - (length - 1)))
            || (high == end && literal(low).is_some_and(|bound| bound >= length && bound <= mask))
    })
}

pub(crate) fn address(terms: &TermStore, term: TermId, width: u32) -> Option<Address> {
    fn walk(
        terms: &TermStore,
        term: TermId,
        width: u32,
        nodes: &mut usize,
        depth: usize,
    ) -> Option<Address> {
        *nodes = nodes.checked_add(1)?;
        if *nodes > 64 || depth > 16 || width == 0 || width > 128 {
            return None;
        }
        terms.entry_stamp(term)?;
        if terms.sort(term) != &Sort::bitvec(width) {
            return None;
        }
        let mask = u128::MAX >> (128 - width);
        if let TermData::Const(Constant::BitVec {
            value,
            width: actual,
        }) = terms.get(term)
        {
            let value = value.to_u128()?;
            return (*actual == width && value <= mask).then_some(Address {
                base: None,
                offset: value,
            });
        }
        if let Some([a, b]) = binary(terms, term, "bvadd") {
            let a = walk(terms, a, width, nodes, depth + 1)?;
            let b = walk(terms, b, width, nodes, depth + 1)?;
            if a.base.is_none() || b.base.is_none() {
                return Some(Address {
                    base: a.base.or(b.base),
                    offset: a.offset.wrapping_add(b.offset) & mask,
                });
            }
        }
        if let Some([a, b]) = binary(terms, term, "bvsub") {
            let a = walk(terms, a, width, nodes, depth + 1)?;
            let b = walk(terms, b, width, nodes, depth + 1)?;
            if b.base.is_none() {
                return Some(Address {
                    base: a.base,
                    offset: a.offset.wrapping_sub(b.offset) & mask,
                });
            }
        }
        Some(Address {
            base: Some(term),
            offset: 0,
        })
    }
    walk(terms, term, width, &mut 0, 0)
}

impl Shape {
    pub(crate) fn recognize(terms: &TermStore, clause: &[TermId]) -> Option<Self> {
        let [negative] = clause else { return None };
        terms.entry_stamp(*negative)?;
        let TermData::Not(root) = terms.get(*negative) else {
            return None;
        };
        if terms.sort(*negative) != &Sort::Bool || !contains_read(terms, *root)? {
            return None;
        }
        conjuncts(terms, *root)?;
        let mut pending = vec![*root];
        let mut facts = Vec::new();
        while let Some(term) = pending.pop() {
            terms.entry_stamp(term)?;
            if facts.len() + pending.len() >= 64 || terms.sort(term) != &Sort::Bool {
                return None;
            }
            facts.push(term);
            if let Some(args) = conjuncts(terms, term) {
                pending.extend_from_slice(args);
            }
        }
        let mut candidates = 0;
        for &fact in &facts {
            let Some([a, b]) = binary(terms, fact, "or") else {
                continue;
            };
            let (Some(left), Some(right)) =
                (branch_comparisons(terms, a), branch_comparisons(terms, b))
            else {
                continue;
            };
            for &first in &left {
                for &second in &right {
                    candidates += 1;
                    if candidates > 256 {
                        return None;
                    }
                    if let Some(shape) = Self::from_guard(terms, *root, fact, &facts, first, second)
                    {
                        return Some(shape);
                    }
                }
            }
        }
        None
    }

    fn from_guard(
        terms: &TermStore,
        root: TermId,
        fact: TermId,
        facts: &[TermId],
        [s0, e1]: [TermId; 2],
        [s1, e0]: [TermId; 2],
    ) -> Option<Self> {
        let Sort::BitVec(sort) = terms.sort(s0) else {
            return None;
        };
        let width = sort.width;
        if width == 0 || width > 128 {
            return None;
        }
        let mask = u128::MAX >> (128 - width);
        let span = |start, end| {
            let a = address(terms, start, width)?;
            let b = address(terms, end, width)?;
            let length = b.offset.wrapping_sub(a.offset) & mask;
            // The sparse memory model validates at most 64 byte writes.
            (a.base == b.base && length > 0 && length <= 64).then_some(Span {
                start,
                address: a,
                length,
            })
        };
        let (Some(first), Some(second)) = (span(s0, e0), span(s1, e1)) else {
            return None;
        };
        let nowrap0 = nonwrap(terms, facts, s0, e0, first.length, width)?;
        let nowrap1 = nonwrap(terms, facts, s1, e1, second.length, width)?;
        Some(Self {
            root,
            guards: [fact, nowrap0, nowrap1],
            width,
            spans: [first, second],
        })
    }

    pub(crate) fn offset(&self, terms: &TermStore, term: TermId, span: usize) -> Option<u128> {
        let at = address(terms, term, self.width)?;
        let range = self.spans.get(span)?;
        let delta =
            at.offset.wrapping_sub(range.address.offset) & (u128::MAX >> (128 - self.width));
        (at.base == range.address.base && delta < range.length).then_some(delta)
    }

    pub(crate) fn separates(&self, terms: &TermStore, a: TermId, b: TermId) -> bool {
        (self.offset(terms, a, 0).is_some() && self.offset(terms, b, 1).is_some())
            || (self.offset(terms, b, 0).is_some() && self.offset(terms, a, 1).is_some())
    }
}

fn contains_read(terms: &TermStore, root: TermId) -> Option<bool> {
    let mut pending = vec![(root, 0usize)];
    let mut nodes = 0usize;
    while let Some((term, depth)) = pending.pop() {
        nodes += 1;
        if nodes > 2048 || depth > 64 {
            return None;
        }
        terms.entry_stamp(term)?;
        match terms.get(term) {
            TermData::Not(child) => pending.push((*child, depth + 1)),
            TermData::App(Symbol::Named(op), args) if op == "select" && args.len() == 2 => {
                return Some(true)
            }
            TermData::App(_, args) if args.len() <= 128 => {
                pending.extend(args.iter().map(|&arg| (arg, depth + 1)))
            }
            TermData::Var(..) | TermData::Const(..) => (),
            _ => return None,
        }
    }
    Some(false)
}
