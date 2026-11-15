// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact extensional equality of GROUND array terms
//! (#aufbv-const-array-equality).
//!
//! A ground array term is a `const-array`, under any number of `store`s, `ite`s
//! whose condition the model decides, and empty `let`s, whose indices, elements
//! and default evaluate to scalar model values. Its value is fixed by the term
//! and those scalar values: no array interpretation, completion default or
//! select reconstruction takes part. Two such values are equal exactly when
//! they read the same element at every index:
//!
//! * an index either side writes reads, on each side, the newest write there,
//!   or that side's default when the side does not write it;
//! * every other index reads the two defaults, and such an index exists unless
//!   the written indices cover the whole index sort, which only a finite sort
//!   (Bool, a bit-vector) allows: over `(_ BitVec 1)`, `(store (store ((as
//!   const A) false) #b0 true) #b1 true)` is `((as const A) true)`.
//!
//! The general comparison reads array VARIABLES from their reconstructed
//! interpretations, so on the BV lane a mismatch there is not an extensional
//! witness and stays Unknown. None of that applies to a ground pair, whose
//! verdict is exact in both directions. Without it the solver's own
//! `distinct_const_array` axiom `(not (= ((as const A) true) ((as const A)
//! false)))` evaluated Unknown on every QF_AUFBV model with two such constants,
//! and model validation failed closed (`BV-backed array assertion evaluates to
//! Unknown`, measured on the w37 fuzz file f035).

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{Sort, TermId};
use num_bigint::BigInt;
use num_rational::BigRational;

use super::super::{EvalValue, Executor, Model};

/// A scalar model value in canonical form: two keys of one sort are equal
/// exactly when the values they stand for are.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum ScalarKey {
    Bool(bool),
    /// The unsigned residue; the width is the sort's.
    BitVec(BigInt),
    Rational(BigRational),
}

/// The syntactic shape of a ground array term: its writes, newest first, and
/// the term of the `const-array` default it bottoms out in.
struct GroundSpine {
    writes: Vec<(TermId, TermId)>,
    default: TermId,
}

/// The value of a ground array term: its default and, per written index, the
/// newest element written there.
struct GroundArray {
    default: ScalarKey,
    cells: HashMap<ScalarKey, ScalarKey>,
}

impl GroundArray {
    fn read(&self, index: &ScalarKey) -> &ScalarKey {
        self.cells.get(index).unwrap_or(&self.default)
    }
}

/// The scalar sorts whose evaluated values [`ScalarKey`] canonicalizes.
fn canonical_scalar_sort(sort: &Sort) -> bool {
    matches!(sort, Sort::Bool | Sort::BitVec(_) | Sort::Int | Sort::Real)
}

/// Whether `written` distinct indices exhaust `index_sort`. Only called on a
/// [`canonical_scalar_sort`]; `Int` and `Real` are infinite.
fn index_sort_covered(index_sort: &Sort, written: usize) -> bool {
    match index_sort {
        Sort::Bool => written >= 2,
        Sort::BitVec(bv) => bv.width < usize::BITS && written >= 1usize << bv.width,
        _ => false,
    }
}

impl Executor {
    /// Exact equality of two ground array terms under `model`.
    ///
    /// `None` when either operand is not ground, an index, element, default
    /// or `ite` condition does not evaluate, or the index or element sort is
    /// not one [`ScalarKey`] canonicalizes; the caller then keeps its general
    /// comparison.
    pub(super) fn ground_array_equality(
        &self,
        model: &Model,
        lhs: TermId,
        rhs: TermId,
    ) -> Option<bool> {
        let Sort::Array(sort) = self.ctx.terms.sort(lhs) else {
            return None;
        };
        if self.ctx.terms.sort(rhs) != self.ctx.terms.sort(lhs)
            || !canonical_scalar_sort(&sort.index_sort)
            || !canonical_scalar_sort(&sort.element_sort)
        {
            return None;
        }
        // Both shapes first: a non-ground side costs no scalar evaluation.
        let left = self.ground_spine(model, lhs)?;
        let right = self.ground_spine(model, rhs)?;
        let left = self.ground_array_value(model, left, &sort.index_sort, &sort.element_sort)?;
        let right = self.ground_array_value(model, right, &sort.index_sort, &sort.element_sort)?;
        let mut written = left.cells.len();
        for (index, value) in &left.cells {
            if value != right.read(index) {
                return Some(false);
            }
        }
        for (index, value) in &right.cells {
            if !left.cells.contains_key(index) {
                written += 1;
                if *value != left.default {
                    return Some(false);
                }
            }
        }
        if left.default == right.default {
            return Some(true);
        }
        // The defaults differ, so the arrays are equal only when no index is
        // left to read them.
        Some(index_sort_covered(&sort.index_sort, written))
    }

    /// The writes and default term of `term` when it is ground (module docs).
    /// Iterative, so a long store chain needs no stack.
    fn ground_spine(&self, model: &Model, term: TermId) -> Option<GroundSpine> {
        let mut writes = Vec::new();
        let mut current = term;
        loop {
            match self.ctx.terms.get(current) {
                TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                    writes.push((args[1], args[2]));
                    current = args[0];
                }
                TermData::App(sym, args) if sym.name() == "const-array" && args.len() == 1 => {
                    return Some(GroundSpine {
                        writes,
                        default: args[0],
                    });
                }
                TermData::Ite(cond, then_branch, else_branch) => {
                    current = match self.evaluate_term(model, *cond) {
                        EvalValue::Bool(true) => *then_branch,
                        EvalValue::Bool(false) => *else_branch,
                        _ => return None,
                    };
                }
                TermData::Let(bindings, body) if bindings.is_empty() => current = *body,
                _ => return None,
            }
        }
    }

    /// The value of a ground spine under `model`.
    fn ground_array_value(
        &self,
        model: &Model,
        spine: GroundSpine,
        index_sort: &Sort,
        element_sort: &Sort,
    ) -> Option<GroundArray> {
        let default = self.ground_scalar_key(model, spine.default, element_sort)?;
        let mut cells = HashMap::default();
        for (index, value) in spine.writes {
            let index = self.ground_scalar_key(model, index, index_sort)?;
            // A newer write to the same index shadows this one entirely.
            if !cells.contains_key(&index) {
                let value = self.ground_scalar_key(model, value, element_sort)?;
                cells.insert(index, value);
            }
        }
        Some(GroundArray { default, cells })
    }

    /// The canonical key of `term`'s value, when it evaluates to a value of
    /// `sort` that [`ScalarKey`] represents exactly.
    fn ground_scalar_key(&self, model: &Model, term: TermId, sort: &Sort) -> Option<ScalarKey> {
        match (sort, self.evaluate_term(model, term)) {
            (Sort::Bool, EvalValue::Bool(value)) => Some(ScalarKey::Bool(value)),
            (Sort::BitVec(bv), EvalValue::BitVec { value, width }) if width == bv.width => {
                Some(ScalarKey::BitVec(Self::normalize_bv_value(value, width)))
            }
            (Sort::Int, EvalValue::Rational(value)) if value.is_integer() => {
                Some(ScalarKey::Rational(value))
            }
            (Sort::Real, EvalValue::Rational(value)) => Some(ScalarKey::Rational(value)),
            _ => None,
        }
    }
}
