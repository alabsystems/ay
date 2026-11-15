// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact model-independent constructor eta characterization.
//!
//! A registry supplies declaration metadata, never model values. A positive
//! result proves `is-C(y) = (y = C(sel_0(y), .., sel_n(y)))`. It does not
//! prove the bare inner equality for a multi-constructor datatype.

use std::collections::BTreeSet;

use ay_core::term::{Symbol, TermData};
use ay_core::{DatatypeField, Sort, TermId, TermStore};

/// Borrow one constructor's fields without cloning a datatype inventory.
#[derive(Clone, Copy)]
pub enum Fields<'a> {
    /// Native declaration table representation.
    Tuples(&'a [(String, Sort)]),
    /// Embedded datatype-sort representation.
    Datatype(&'a [DatatypeField]),
}

impl<'a> Fields<'a> {
    fn len(self) -> usize {
        match self {
            Self::Tuples(v) => v.len(),
            Self::Datatype(v) => v.len(),
        }
    }
    fn get(self, index: usize) -> Option<(&'a str, &'a Sort)> {
        match self {
            Self::Tuples(v) => v.get(index).map(|(name, sort)| (name.as_str(), sort)),
            Self::Datatype(v) => v.get(index).map(|field| (field.name.as_str(), &field.sort)),
        }
    }
}

/// Exact argument sorts, including allocation-free unary/constructor views.
#[derive(Clone, Copy)]
pub enum Arguments<'a> {
    /// The actual registered signature.
    Slice(&'a [Sort]),
    /// A datatype tester or selector's sole owner argument.
    Unary(&'a Sort),
    /// An embedded constructor's argument sorts.
    Fields(Fields<'a>),
}

impl<'a> Arguments<'a> {
    fn len(self) -> usize {
        match self {
            Self::Slice(v) => v.len(),
            Self::Unary(_) => 1,
            Self::Fields(v) => v.len(),
        }
    }
    fn get(self, index: usize) -> Option<&'a Sort> {
        match self {
            Self::Slice(v) => v.get(index),
            Self::Unary(v) => (index == 0).then_some(v),
            Self::Fields(v) => v.get(index).map(|(_, sort)| sort),
        }
    }
}

/// Positive declaration classification; a matching ordinary UF never qualifies.
#[derive(Clone, Copy)]
pub enum Kind<'a> {
    /// An actual constructor declaration.
    Constructor,
    /// An actual tester, retaining its exact constructor core identity.
    Tester(&'a str),
    /// An actual selector declaration.
    Selector,
    /// An ordinary declaration, even if its spelling resembles a member.
    Ordinary,
}

/// Borrowed exact member signature. The caller authenticates its declaration.
pub struct Member<'a> {
    /// Positive declaration kind.
    pub kind: Kind<'a>,
    /// Complete ordered arguments.
    pub arguments: Arguments<'a>,
    /// Exact result sort.
    pub result: &'a Sort,
}

/// A declaration resolver, not a source/proof authority constructor.
/// Implementations charge scans and return only borrowed exact core identities.
pub trait Registry {
    /// The complete ordered fields of this exact constructor and owner.
    fn fields<'a>(
        &'a self,
        owner: &'a Sort,
        constructor: &str,
        budget: &mut Budget<'_>,
    ) -> Option<Fields<'a>>;
    /// The actual member kind and signature, without surface-name fallback.
    fn member<'a>(
        &'a self,
        owner: &'a Sort,
        name: &'a str,
        budget: &mut Budget<'_>,
    ) -> Option<Member<'a>>;
}

/// One bounded, nonrefundable work window with the caller's physical stop check.
pub struct Budget<'a> {
    remaining: usize,
    stopped: &'a dyn Fn() -> bool,
    refused: bool,
}

impl<'a> Budget<'a> {
    /// No solver or query resource policy is changed by this local cap.
    pub fn new(remaining: usize, stopped: &'a dyn Fn() -> bool) -> Self {
        Self {
            remaining,
            stopped,
            refused: false,
        }
    }
    /// Pay before any metadata scan, recursive sort comparison or name walk.
    pub fn charge(&mut self, amount: usize) -> Option<()> {
        if self.refused {
            return None;
        }
        if (self.stopped)() {
            self.refused = true;
            return None;
        }
        let Some(remaining) = self.remaining.checked_sub(amount) else {
            self.remaining = 0;
            self.refused = true;
            return None;
        };
        self.remaining = remaining;
        Some(())
    }
    fn name(&mut self, name: &str) -> Option<()> {
        if name.len() > 256 {
            self.refused = true;
            return None;
        }
        self.charge(name.len().checked_add(1)?)
    }
}

fn sort_equal(a: &Sort, b: &Sort, budget: &mut Budget<'_>, depth: usize) -> Option<bool> {
    budget.charge(1)?;
    if depth >= 64 {
        budget.refused = true;
        return None;
    }
    Some(match (a, b) {
        (Sort::Bool, Sort::Bool)
        | (Sort::Int, Sort::Int)
        | (Sort::Real, Sort::Real)
        | (Sort::String, Sort::String)
        | (Sort::RegLan, Sort::RegLan)
        | (Sort::Char, Sort::Char)
        | (Sort::Complex, Sort::Complex) => true,
        (Sort::BitVec(a), Sort::BitVec(b)) => a.width == b.width,
        (Sort::FloatingPoint(a, b), Sort::FloatingPoint(c, d)) => a == c && b == d,
        (Sort::Uninterpreted(a), Sort::Uninterpreted(b)) | (Sort::TypeVar(a), Sort::TypeVar(b)) => {
            budget.name(a)?;
            budget.name(b)?;
            a == b
        }
        (Sort::FiniteDomain(a, n), Sort::FiniteDomain(b, m)) => {
            budget.name(a)?;
            budget.name(b)?;
            a == b && n == m
        }
        (Sort::Array(a), Sort::Array(b)) => {
            sort_equal(&a.index_sort, &b.index_sort, budget, depth + 1)?
                && sort_equal(&a.element_sort, &b.element_sort, budget, depth + 1)?
        }
        (Sort::Seq(a), Sort::Seq(b)) => sort_equal(a, b, budget, depth + 1)?,
        (Sort::Datatype(a), Sort::Datatype(b)) => {
            budget.name(&a.name)?;
            budget.name(&b.name)?;
            if a.name != b.name || a.constructors.len() != b.constructors.len() {
                return Some(false);
            }
            budget.charge(a.constructors.len())?;
            for (a, b) in a.constructors.iter().zip(&b.constructors) {
                budget.name(&a.name)?;
                budget.name(&b.name)?;
                if a.name != b.name || a.fields.len() != b.fields.len() {
                    return Some(false);
                }
                budget.charge(a.fields.len())?;
                for (a, b) in a.fields.iter().zip(&b.fields) {
                    budget.name(&a.name)?;
                    budget.name(&b.name)?;
                    if a.name != b.name || !sort_equal(&a.sort, &b.sort, budget, depth + 1)? {
                        return Some(false);
                    }
                }
            }
            true
        }
        _ => false,
    })
}

fn app<'a>(
    terms: &'a TermStore,
    term: TermId,
    budget: &mut Budget<'_>,
) -> Option<(&'a str, &'a [TermId])> {
    budget.charge(1)?;
    terms.entry_stamp(term)?;
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    budget.name(name)?;
    if terms.is_declared_function(name) {
        return None;
    }
    Some((name, args))
}

fn unary(member: &Member<'_>, owner: &Sort, result: &Sort, budget: &mut Budget<'_>) -> Option<()> {
    if member.arguments.len() != 1
        || !sort_equal(member.arguments.get(0)?, owner, budget, 0)?
        || !sort_equal(member.result, result, budget, 0)?
    {
        return None;
    }
    Some(())
}

fn oriented(
    terms: &TermStore,
    tester: TermId,
    equality: TermId,
    registry: &dyn Registry,
    budget: &mut Budget<'_>,
) -> Option<()> {
    let (tester_name, tester_args) = app(terms, tester, budget)?;
    if tester_args.len() != 1 || !matches!(terms.sort(tester), Sort::Bool) {
        return None;
    }
    let y = tester_args[0];
    terms.entry_stamp(y)?;
    let owner = terms.sort(y);
    if !matches!(owner, Sort::Datatype(_) | Sort::Uninterpreted(_)) {
        return None;
    }
    // Also preflight an embedded declaration before a registry can scan it.
    if !sort_equal(owner, owner, budget, 0)? {
        return None;
    }
    let test = registry.member(owner, tester_name, budget)?;
    let Kind::Tester(constructor) = test.kind else {
        return None;
    };
    budget.name(constructor)?;
    unary(&test, owner, &Sort::Bool, budget)?;
    let (equal_name, equal_args) = app(terms, equality, budget)?;
    if equal_name != "=" || equal_args.len() != 2 || !matches!(terms.sort(equality), Sort::Bool) {
        return None;
    }
    let rebuilt = if equal_args[0] == y {
        equal_args[1]
    } else if equal_args[1] == y {
        equal_args[0]
    } else {
        return None;
    };
    let (head, arguments) = app(terms, rebuilt, budget)?;
    if head != constructor || !sort_equal(terms.sort(rebuilt), owner, budget, 0)? {
        return None;
    }
    let fields = registry.fields(owner, constructor, budget)?;
    budget.charge(fields.len())?;
    let ctor = registry.member(owner, constructor, budget)?;
    if !matches!(ctor.kind, Kind::Constructor)
        || fields.len() != arguments.len()
        || ctor.arguments.len() != fields.len()
        || !sort_equal(ctor.result, owner, budget, 0)?
    {
        return None;
    }
    let mut seen = BTreeSet::new();
    for (index, &field_term) in arguments.iter().enumerate() {
        let (field, field_sort) = fields.get(index)?;
        budget.name(field)?;
        if !seen.insert(field) || !sort_equal(ctor.arguments.get(index)?, field_sort, budget, 0)? {
            return None;
        }
        let (head, args) = app(terms, field_term, budget)?;
        if head != field
            || args != [y]
            || !sort_equal(terms.sort(field_term), field_sort, budget, 0)?
        {
            return None;
        }
        let member = registry.member(owner, field, budget)?;
        if !matches!(member.kind, Kind::Selector) {
            return None;
        }
        unary(&member, owner, field_sort, budget)?;
    }
    budget.charge(0)
}

/// Positive proof only. Every unavailable, malformed or stopped case declines.
pub fn is_constructor_eta(
    terms: &TermStore,
    term: TermId,
    registry: &dyn Registry,
    budget: &mut Budget<'_>,
) -> bool {
    let mut check = || -> Option<()> {
        let (name, args) = app(terms, term, budget)?;
        if name != "=" || args.len() != 2 || !matches!(terms.sort(term), Sort::Bool) {
            return None;
        }
        oriented(terms, args[0], args[1], registry, budget)
            .or_else(|| oriented(terms, args[1], args[0], registry, budget))
    };
    check().is_some()
}

/// Borrow embedded datatype declarations. Named registry carriers need their
/// caller's real resolver and are deliberately not guessed by this adapter.
pub struct Embedded;

impl Registry for Embedded {
    fn fields<'a>(
        &'a self,
        owner: &'a Sort,
        constructor: &str,
        budget: &mut Budget<'_>,
    ) -> Option<Fields<'a>> {
        let Sort::Datatype(datatype) = owner else {
            return None;
        };
        for ctor in &datatype.constructors {
            budget.name(&ctor.name)?;
            if ctor.name == constructor {
                return Some(Fields::Datatype(&ctor.fields));
            }
        }
        None
    }
    fn member<'a>(
        &'a self,
        owner: &'a Sort,
        name: &'a str,
        budget: &mut Budget<'_>,
    ) -> Option<Member<'a>> {
        let Sort::Datatype(datatype) = owner else {
            return None;
        };
        for ctor in &datatype.constructors {
            budget.name(&ctor.name)?;
            if name == ctor.name {
                return Some(Member {
                    kind: Kind::Constructor,
                    arguments: Arguments::Fields(Fields::Datatype(&ctor.fields)),
                    result: owner,
                });
            }
            if name.strip_prefix("is-") == Some(ctor.name.as_str()) {
                return Some(Member {
                    kind: Kind::Tester(&ctor.name),
                    arguments: Arguments::Unary(owner),
                    result: &Sort::Bool,
                });
            }
            for field in &ctor.fields {
                budget.name(&field.name)?;
                if name == field.name {
                    return Some(Member {
                        kind: Kind::Selector,
                        arguments: Arguments::Unary(owner),
                        result: &field.sort,
                    });
                }
            }
        }
        None
    }
}

#[cfg(test)]
mod tests;
