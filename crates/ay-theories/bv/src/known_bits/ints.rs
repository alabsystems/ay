// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded integers as 64-bit two's-complement values.
//!
//! Trust states machine-integer obligations over mathematical integers:
//! every variable is bounded by its Rust type at the top level
//! (`(<= 0 x) (<= x 255)`), and bit operations cross into bit-vectors with
//! `int2bv` and back with `bv2nat`. An integer term whose value lies in
//! `[-2^62, 2^62]` in every model of the assertions is exactly its 64-bit
//! two's-complement pattern, and `+`, `-`, multiplication by a constant,
//! `div`/`mod` by a power of two, comparisons, `int2bv` and `bv2nat` are
//! exactly bit-vector operations on it. Such a term is *certified* here by
//! interval arithmetic from the top-level bounds; the region holds certified
//! terms only. An uncertified integer never gets a node, so an atom over one
//! becomes an unconstrained Boolean, which forgets but never misleads.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Constant, Symbol, TermData, TermId, TermStore};
use ay_core::Sort;
use num_bigint::BigInt;
use num_traits::ToPrimitive;

/// Width of an integer in the region.
pub const INT_WIDTH: u32 = 64;

/// Largest magnitude a certified integer term may take.
pub const INT_LIMIT: i128 = 1 << 62;

/// Value ranges of integer terms under the assertions' top-level bounds.
pub struct IntRanges<'a> {
    terms: &'a TermStore,
    vars: HashMap<TermId, (Option<i128>, Option<i128>)>,
    memo: HashMap<TermId, Option<(i128, i128)>>,
}

/// An integer constant that fits `i128`.
pub fn int_constant(terms: &TermStore, term: TermId) -> Option<i128> {
    match terms.get(term) {
        TermData::Const(Constant::Int(value)) => value.to_i128(),
        _ => None,
    }
}

fn is_int_var(terms: &TermStore, term: TermId) -> bool {
    matches!(terms.sort(term), Sort::Int) && matches!(terms.get(term), TermData::Var(..))
}

/// The conjuncts of `assertions`, with top-level `and`s flattened.
pub fn top_level_conjuncts(terms: &TermStore, assertions: &[TermId]) -> Vec<TermId> {
    let mut out = Vec::new();
    let mut stack: Vec<TermId> = assertions.iter().rev().copied().collect();
    while let Some(term) = stack.pop() {
        match terms.get(term) {
            TermData::App(Symbol::Named(name), args) if name == "and" => {
                stack.extend(args.iter().rev().copied());
            }
            _ => out.push(term),
        }
    }
    out
}

impl<'a> IntRanges<'a> {
    /// Collect the variable bounds the top-level conjuncts state.
    pub fn new(terms: &'a TermStore, assertions: &[TermId]) -> Self {
        let mut ranges = Self {
            terms,
            vars: HashMap::default(),
            memo: HashMap::default(),
        };
        for conjunct in top_level_conjuncts(terms, assertions) {
            ranges.note_bound(conjunct);
        }
        ranges
    }

    /// Record `atom` if it bounds an integer variable by a constant.
    fn note_bound(&mut self, atom: TermId) {
        let (negated, inner) = match self.terms.get(atom) {
            TermData::Not(inner) => (true, *inner),
            _ => (false, atom),
        };
        let TermData::App(Symbol::Named(name), args) = self.terms.get(inner) else {
            return;
        };
        let [a, b] = args.as_slice() else {
            return;
        };
        // Normalize to `var OP constant`.
        let (var, constant, op) = match (
            is_int_var(self.terms, *a),
            int_constant(self.terms, *b),
            int_constant(self.terms, *a),
            is_int_var(self.terms, *b),
        ) {
            (true, Some(c), _, _) => (*a, c, name.as_str()),
            (_, _, Some(c), true) => {
                let flipped = match name.as_str() {
                    "<=" => ">=",
                    "<" => ">",
                    ">=" => "<=",
                    ">" => "<",
                    "=" => "=",
                    _ => return,
                };
                (*b, c, flipped)
            }
            _ => return,
        };
        let op = if negated {
            match op {
                "<=" => ">",
                "<" => ">=",
                ">=" => "<",
                ">" => "<=",
                _ => return,
            }
        } else {
            op
        };
        let (lo, hi) = match op {
            "<=" => (None, Some(constant)),
            "<" => (None, constant.checked_sub(1)),
            ">=" => (Some(constant), None),
            ">" => (constant.checked_add(1), None),
            "=" => (Some(constant), Some(constant)),
            _ => return,
        };
        let entry = self.vars.entry(var).or_insert((None, None));
        if let Some(lo) = lo {
            entry.0 = Some(entry.0.map_or(lo, |old| old.max(lo)));
        }
        if let Some(hi) = hi {
            entry.1 = Some(entry.1.map_or(hi, |old| old.min(hi)));
        }
    }

    /// Whether `term` is a certified integer.
    pub fn certified(&mut self, term: TermId) -> bool {
        self.range(term).is_some()
    }

    /// The range of an integer term when it is certified.
    pub fn range(&mut self, term: TermId) -> Option<(i128, i128)> {
        if let Some(range) = self.memo.get(&term) {
            return *range;
        }
        let range = stacker::maybe_grow(64 * 1024, 1024 * 1024, || self.compute(term))
            .filter(|&(lo, hi)| lo <= hi && -INT_LIMIT <= lo && hi <= INT_LIMIT);
        self.memo.insert(term, range);
        range
    }

    fn compute(&mut self, term: TermId) -> Option<(i128, i128)> {
        if !matches!(self.terms.sort(term), Sort::Int) {
            return None;
        }
        let terms = self.terms;
        match terms.get(term) {
            TermData::Const(Constant::Int(value)) => value.to_i128().map(|v| (v, v)),
            TermData::Var(..) => match self.vars.get(&term) {
                Some(&(Some(lo), Some(hi))) => Some((lo, hi)),
                _ => None,
            },
            TermData::Ite(_, t, e) => self.hull(*t, *e),
            TermData::App(symbol, args) => match (symbol.name(), args.as_slice()) {
                ("+", [_, ..]) => {
                    let mut acc = (0i128, 0i128);
                    for &arg in args {
                        let (lo, hi) = self.range(arg)?;
                        acc = (acc.0.checked_add(lo)?, acc.1.checked_add(hi)?);
                    }
                    Some(acc)
                }
                ("-", [a]) => {
                    let (lo, hi) = self.range(*a)?;
                    Some((-hi, -lo))
                }
                ("-", [first, rest @ ..]) => {
                    let mut acc = self.range(*first)?;
                    for &arg in rest {
                        let (lo, hi) = self.range(arg)?;
                        acc = (acc.0.checked_sub(hi)?, acc.1.checked_sub(lo)?);
                    }
                    Some(acc)
                }
                ("*", [_, ..]) => {
                    let mut acc = (1i128, 1i128);
                    for &arg in args {
                        let (lo, hi) = self.range(arg)?;
                        let corners = [
                            acc.0.checked_mul(lo)?,
                            acc.0.checked_mul(hi)?,
                            acc.1.checked_mul(lo)?,
                            acc.1.checked_mul(hi)?,
                        ];
                        acc = (
                            *corners.iter().min().expect("four corners"),
                            *corners.iter().max().expect("four corners"),
                        );
                    }
                    Some(acc)
                }
                ("div", [a, c]) => {
                    let c = int_constant(terms, *c).filter(|&c| c > 0)?;
                    let (lo, hi) = self.range(*a)?;
                    Some((lo.div_euclid(c), hi.div_euclid(c)))
                }
                ("mod", [_, c]) => {
                    let c = int_constant(terms, *c).filter(|&c| c > 0)?;
                    Some((0, c - 1))
                }
                ("bv2nat", [b]) => {
                    let width = terms.sort(*b).bitvec_width()?;
                    (width <= 62).then(|| (0, (1i128 << width) - 1))
                }
                ("ite", [_, t, e]) => self.hull(*t, *e),
                _ => None,
            },
            _ => None,
        }
    }

    fn hull(&mut self, t: TermId, e: TermId) -> Option<(i128, i128)> {
        let (a, b) = (self.range(t)?, self.range(e)?);
        Some((a.0.min(b.0), a.1.max(b.1)))
    }
}

/// Two's-complement pattern of a certified integer constant.
#[must_use]
pub fn twos_complement(value: i128) -> u64 {
    value as i64 as u64
}

/// An integer constant as a `BigInt`, for the encoder's constant bits.
#[must_use]
pub fn pattern_bigint(value: i128) -> BigInt {
    BigInt::from(twos_complement(value))
}
