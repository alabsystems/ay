// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Small canonical-term predicates shared by proof-surgery planners.

use super::*;

/// The two operands of a top-level binary `(= a b)` application, or `None`.
pub(super) fn decode_binary_equality(
    terms: &ay_core::TermStore,
    term: TermId,
) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

pub(super) fn atom_of(terms: &ay_core::TermStore, lit: TermId) -> TermId {
    match terms.get(lit) {
        TermData::Not(inner) => *inner,
        _ => lit,
    }
}

/// Whether `t` is a PURE linear-arithmetic term: numerals, arithmetic
/// variables / declared constants, and `+`/`-`/`*` applications thereof.
/// The internal Farkas verifier treats any non-arithmetic atom (e.g. an
/// array `select`) as an opaque linear unknown, but external `la_generic`
/// checking evaluates the linear combination syntactically — so promotions
/// that flip a lemma onto `la_generic` must reject impure atoms.
pub(super) fn term_is_pure_linear_arith(terms: &ay_core::TermStore, t: TermId) -> bool {
    if !matches!(terms.sort(t), Sort::Int | Sort::Real) {
        return false;
    }
    match terms.get(t) {
        TermData::Const(_) | TermData::Var(..) => true,
        TermData::App(Symbol::Named(op), args) => match op.as_str() {
            "+" | "-" | "*" => args.iter().all(|&a| term_is_pure_linear_arith(terms, a)),
            _ => args.is_empty(),
        },
        _ => false,
    }
}

/// Whether both operands of the equality application `eq` are pure
/// linear-arithmetic terms (see [`term_is_pure_linear_arith`]).
pub(super) fn equality_is_pure_linear_arith(terms: &ay_core::TermStore, eq: TermId) -> bool {
    match terms.get(eq) {
        TermData::App(Symbol::Named(op), args) if op == "=" && args.len() == 2 => {
            let (a, b) = (args[0], args[1]);
            term_is_pure_linear_arith(terms, a) && term_is_pure_linear_arith(terms, b)
        }
        _ => false,
    }
}

/// Complement of a literal without double negation.
pub(super) fn complement_of(terms: &mut ay_core::TermStore, lit: TermId) -> TermId {
    match terms.get(lit) {
        TermData::Not(inner) => *inner,
        _ => terms.mk_not_raw(lit),
    }
}
