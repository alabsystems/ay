// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded source matching grants no fact; the caller proves the offset lemma.

use super::*;
use crate::checker::bv_bitblast::disjoint::Address;

pub(super) mod pricing;
mod syntax;
use syntax::binary;

#[derive(Clone)]
pub(crate) struct Shape {
    pub(crate) root: TermId,
    pub(crate) guard: TermId,
    pub(crate) property: TermId,
    pub(crate) property_value: bool,
    pub(crate) equality: TermId,
    pub(crate) outside: TermId,
    pub(crate) start: TermId,
    pub(crate) observe: TermId,
    pub(crate) width: u32,
    pub(crate) length: u128,
}

fn constant(terms: &TermStore, term: TermId, width: u32) -> Option<u128> {
    terms.entry_stamp(term)?;
    let TermData::Const(Constant::BitVec {
        value,
        width: actual,
    }) = terms.get(term)
    else {
        return None;
    };
    let value = value.to_u128()?;
    (*actual == width
        && terms.sort(term) == &Sort::bitvec(width)
        && value <= (u128::MAX >> (128 - width)))
        .then_some(value)
}

fn address(terms: &TermStore, term: TermId, width: u32, budget: &mut usize) -> Option<Address> {
    *budget = budget.checked_sub(1)?;
    terms.entry_stamp(term)?;
    if terms.sort(term) != &Sort::bitvec(width) {
        return None;
    }
    if let Some(value) = constant(terms, term, width) {
        return Some(Address {
            base: None,
            offset: value,
        });
    }
    let mask = u128::MAX >> (128 - width);
    for op in ["bvadd", "bvsub"] {
        if let Some([a, b]) = binary(terms, term, op) {
            let a = address(terms, a, width, budget)?;
            let b = address(terms, b, width, budget)?;
            if op == "bvadd" && (a.base.is_none() || b.base.is_none()) {
                return Some(Address {
                    base: a.base.or(b.base),
                    offset: a.offset.wrapping_add(b.offset) & mask,
                });
            }
            if op == "bvsub" && (b.base.is_none() || a.base == b.base) {
                return Some(Address {
                    base: if b.base.is_none() { a.base } else { None },
                    offset: a.offset.wrapping_sub(b.offset) & mask,
                });
            }
        }
    }
    Some(Address {
        base: Some(term),
        offset: 0,
    })
}

fn boolean_nodes(terms: &TermStore, root: TermId, conjuncts_only: bool) -> Option<Vec<TermId>> {
    let mut pending = vec![root];
    let mut found = Vec::new();
    let mut seen = HashSet::new();
    while let Some(term) = pending.pop() {
        terms.entry_stamp(term)?;
        if terms.sort(term) != &Sort::Bool || !seen.insert(term) {
            continue;
        }
        if seen.len() > 1024 {
            return None;
        }
        found.push(term);
        if conjuncts_only {
            if let TermData::App(Symbol::Named(op), args) = terms.get(term) {
                if op == "and" && args.len() <= 128 {
                    pending.extend(args.iter().copied());
                }
            }
        } else {
            match terms.get(term) {
                TermData::Not(child) => pending.push(*child),
                TermData::App(_, args) if args.len() <= 128 => pending.extend(args.iter().copied()),
                TermData::Var(..) | TermData::Const(..) => (),
                _ => return None,
            }
        }
    }
    Some(found)
}

impl Shape {
    pub(crate) fn offset(&self, terms: &TermStore, key: TermId) -> Option<u128> {
        let start = address(terms, self.start, self.width, &mut 64)?;
        let at = address(terms, key, self.width, &mut 64)?;
        let offset = at.offset.wrapping_sub(start.offset) & (u128::MAX >> (128 - self.width));
        (start.base == at.base && offset < self.length).then_some(offset)
    }

    pub(crate) fn recognize(terms: &TermStore, clause: &[TermId]) -> Option<Self> {
        let [negative] = clause else { return None };
        terms.entry_stamp(*negative)?;
        let TermData::Not(root) = terms.get(*negative) else {
            return None;
        };
        Self::recognize_root(terms, *root)
    }

    pub(crate) fn recognize_root(terms: &TermStore, root: TermId) -> Option<Self> {
        terms.entry_stamp(root)?;
        if terms.sort(root) != &Sort::Bool {
            return None;
        }
        let facts = boolean_nodes(terms, root, true)?;
        let nodes = boolean_nodes(terms, root, false)?;
        for guard in facts {
            let Some([end, length]) = syntax::ge(terms, guard) else {
                continue;
            };
            terms.entry_stamp(end)?;
            let Sort::BitVec(sort) = terms.sort(end) else {
                continue;
            };
            let width = sort.width;
            if width == 0 || width > 128 {
                continue;
            }
            let Some(length) = constant(terms, length, width) else {
                continue;
            };
            if length == 0 || length > 64 {
                continue;
            }
            for &property in &nodes {
                if let Some(mut shape) = Self::property(terms, property, end, width, length) {
                    shape.root = root;
                    shape.guard = guard;
                    return Some(shape);
                }
            }
        }
        None
    }

    fn property(
        terms: &TermStore,
        property: TermId,
        end: TermId,
        width: u32,
        length: u128,
    ) -> Option<Self> {
        let (outside, equality, property_value) = syntax::property(terms, property, end)?;
        let [observe, start] = syntax::outside(terms, outside, end)?;
        let at_start = address(terms, start, width, &mut 64)?;
        let at_end = address(terms, end, width, &mut 64)?;
        if at_start.base != at_end.base
            || at_end.offset.wrapping_sub(at_start.offset) & (u128::MAX >> (128 - width)) != length
        {
            return None;
        }
        let [a, b] = binary(terms, equality, "=")?;
        let [mut a, i] = binary(terms, a, "select")?;
        let [mut b, j] = binary(terms, b, "select")?;
        if i != observe || j != observe {
            return None;
        }
        // Identical later writes preserve equality of a read, whether or not
        // their key aliases the observation. Values and sorts are validated
        // independently before this candidate may simplify any property.
        for _ in 0..64 {
            let (Some([pa, ka, va]), Some([pb, kb, vb])) = (store(terms, a), store(terms, b))
            else {
                break;
            };
            if ka != kb || va != vb {
                break;
            }
            a = pa;
            b = pb;
        }
        if !writes(terms, a, b, at_start, width, length)
            && !writes(terms, b, a, at_start, width, length)
        {
            return None;
        }
        Some(Self {
            root: property,
            guard: property,
            property,
            property_value,
            equality,
            outside,
            start,
            observe,
            width,
            length,
        })
    }
}

fn store(terms: &TermStore, term: TermId) -> Option<[TermId; 3]> {
    terms.entry_stamp(term)?;
    let TermData::App(Symbol::Named(op), args) = terms.get(term) else {
        return None;
    };
    let [base, key, value] = args.as_slice() else {
        return None;
    };
    (op == "store").then_some([*base, *key, *value])
}

fn writes(
    terms: &TermStore,
    mut array: TermId,
    base: TermId,
    start: Address,
    width: u32,
    length: u128,
) -> bool {
    for count in 0..=64 {
        if array == base {
            return count > 0;
        }
        if count == 64 || terms.entry_stamp(array).is_none() {
            return false;
        }
        let TermData::App(Symbol::Named(op), args) = terms.get(array) else {
            return false;
        };
        let [previous, index, _value] = args.as_slice() else {
            return false;
        };
        if op != "store" {
            return false;
        }
        let Some(at) = address(terms, *index, width, &mut 64) else {
            return false;
        };
        if at.base != start.base
            || at.offset.wrapping_sub(start.offset) & (u128::MAX >> (128 - width)) >= length
        {
            return false;
        }
        array = *previous;
    }
    false
}
