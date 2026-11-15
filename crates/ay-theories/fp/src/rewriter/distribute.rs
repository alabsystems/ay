// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Case splits over constants: the rewriter's value-`ite` distribution.
//!
//! When every argument of a foldable FP application is a constant or an `ite`
//! tree whose leaves are constants, the application distributes over the
//! `ite`s and each leaf folds (z3 distributes over value `ite`s the same way):
//!
//! ```text
//! (fp.div rm 1.0 (ite c a b))  ->  (ite c (fp.div rm 1.0 a) (fp.div rm 1.0 b))
//! ```
//!
//! A symbolic rounding mode splits the same way, over its five values:
//! `f(rm, consts)` becomes the `ite` over `(= rm MODE)` of the five constant
//! results, equal results sharing one leaf. Both steps are equivalences: an
//! `ite` distributes over any function, and the `RoundingMode` domain is
//! exactly the five modes.
//!
//! The payoff is that a formula whose FP arithmetic depends only on constants
//! and a mode never reaches the bit-blaster as arithmetic: `(fp.div rm 1.0
//! ((_ to_fp 11 53) rm (/ 8 5)))` is a binary64 divider circuit of 779k
//! clauses, and after the split it is a Boolean combination of `(= rm MODE)`.
//!
//! The split is bounded: an application is distributed only when its result
//! has at most [`MAX_LEAVES`] leaves, so a term never grows by more than that
//! factor. Arguments that are not constant trees are never duplicated.

use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};

use super::numeral::{bv_constant, ground_rational, wide_numeral};
use super::{fold_app, is_rounding_mode_sort, rounding_mode_literal, theory_operator, MODES};

/// The most constant leaves one distributed application may produce.
pub(super) const MAX_LEAVES: usize = 32;

/// One rewrite step on an application whose arguments are rewritten: fold it
/// to a constant, or distribute it over constant case splits.
pub(super) fn rewrite_app(
    terms: &mut TermStore,
    sym: &Symbol,
    args: &[TermId],
    sort: &Sort,
) -> Option<TermId> {
    if let Some(folded) = fold_app(terms, sym, args, sort) {
        return Some(folded);
    }
    distribute(terms, sym, args, sort)
}

/// The operators whose constant instances [`fold_app`] folds, as far as
/// distribution may assume: FP operators, and `=`/`distinct` over
/// FloatingPoint or rounding-mode arguments.
fn distributable(terms: &TermStore, name: &str, args: &[TermId]) -> bool {
    match name {
        "=" | "distinct" => args.first().is_some_and(|&a| {
            let sort = terms.sort(a);
            matches!(sort, Sort::FloatingPoint(..)) || is_rounding_mode_sort(sort)
        }),
        "to_fp" | "to_fp_unsigned" => args.len() == 2,
        "fp.abs" | "fp.neg" | "fp.add" | "fp.sub" | "fp.mul" | "fp.div" | "fp.fma" | "fp.sqrt"
        | "fp.rem" | "fp.roundToIntegral" | "fp.min" | "fp.max" | "fp.leq" | "fp.lt" | "fp.geq"
        | "fp.gt" | "fp.eq" | "fp.isNormal" | "fp.isSubnormal" | "fp.isZero" | "fp.isInfinite"
        | "fp.isNaN" | "fp.isNegative" | "fp.isPositive" | "fp.to_real" | "fp.to_ubv"
        | "fp.to_sbv" | "fp.to_ieee_bv" => true,
        _ => false,
    }
}

/// Whether `term` is a constant the folder reads.
fn is_constant(terms: &TermStore, term: TermId) -> bool {
    wide_numeral(terms, term).is_some()
        || rounding_mode_literal(terms, term).is_some()
        || bv_constant(terms, term).is_some()
        || ground_rational(terms, term).is_some()
        || matches!(terms.get(term), TermData::Const(_))
}

fn as_ite(terms: &TermStore, term: TermId) -> Option<(TermId, TermId, TermId)> {
    match terms.get(term) {
        TermData::Ite(c, t, e) => Some((*c, *t, *e)),
        TermData::App(Symbol::Named(name), args)
            if name == "ite" && args.len() == 3 && !terms.is_declared_function(name) =>
        {
            Some((args[0], args[1], args[2]))
        }
        _ => None,
    }
}

/// The number of constant leaves of a constant `ite` tree, `None` when `term`
/// is not one or has more than `cap` leaves.
fn leaves(terms: &TermStore, term: TermId, cap: usize) -> Option<usize> {
    if is_constant(terms, term) {
        return Some(1);
    }
    let (_, t, e) = as_ite(terms, term)?;
    let a = leaves(terms, t, cap)?;
    let b = leaves(terms, e, cap.checked_sub(a)?)?;
    let total = a + b;
    (total <= cap).then_some(total)
}

/// A symbolic rounding mode: rounding-mode sorted and not a literal.
fn is_symbolic_mode(terms: &TermStore, term: TermId) -> bool {
    is_rounding_mode_sort(terms.sort(term)) && rounding_mode_literal(terms, term).is_none()
}

fn distribute(terms: &mut TermStore, sym: &Symbol, args: &[TermId], sort: &Sort) -> Option<TermId> {
    let name = theory_operator(terms, sym)?;
    if !distributable(terms, name, args) {
        return None;
    }
    // Every argument is a constant tree, except that a symbolic mode that is
    // not an `ite` of literals splits over its five values.
    let mut total = 1usize;
    let mut split = None;
    for (i, &arg) in args.iter().enumerate() {
        let n = match leaves(terms, arg, MAX_LEAVES) {
            Some(n) => n,
            None if is_symbolic_mode(terms, arg) => MODES.len(),
            None => return None,
        };
        if n > 1 && split.is_none() {
            split = Some(i);
        }
        total = total.checked_mul(n)?;
    }
    if total > MAX_LEAVES {
        return None;
    }
    let position = split?;
    let at = |terms: &mut TermStore, value: TermId| {
        let mut replaced = args.to_vec();
        replaced[position] = value;
        rewrite_app(terms, sym, &replaced, sort)
            .unwrap_or_else(|| terms.mk_app(sym.clone(), replaced, sort.clone()))
    };
    let arg = args[position];
    if let Some((c, t, e)) = as_ite(terms, arg) {
        let (then_case, else_case) = (at(terms, t), at(terms, e));
        return Some(terms.mk_ite(c, then_case, else_case));
    }
    // A symbolic mode: `ite (= rm RNE) f(RNE) (ite (= rm RNA) f(RNA) ...)`.
    if terms.is_declared_function("=")
        || MODES
            .iter()
            .any(|mode| terms.is_declared_function(mode.name()))
    {
        return None;
    }
    let mode_sort = terms.sort(arg).clone();
    let mut result = None;
    for mode in MODES.into_iter().rev() {
        let literal = terms.mk_app(Symbol::named(mode.name()), vec![], mode_sort.clone());
        let case = at(terms, literal);
        result = Some(match result {
            None => case,
            Some(rest) => {
                let is_mode = terms.mk_eq(arg, literal);
                terms.mk_ite(is_mode, case, rest)
            }
        });
    }
    result
}

#[cfg(test)]
mod tests;
