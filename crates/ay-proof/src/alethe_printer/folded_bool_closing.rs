// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Closing a derived `(= P b)` into the term store's folded spelling.
//!
//! `TermStore::mk_eq` folds an equality with a Boolean constant into the
//! literal it denotes: `(= P true)` interns as `P`, `(= P false)` as `(not P)`.
//! A checked `ArrayRowChain` lemma whose conclusion was folded that way
//! (`checker::array_axiom::folded_conclusions`) is lowered through the ordinary
//! `UnderArrayEq` derivation, which ends on the UNFOLDED `(= P b)`; these steps
//! bridge it to the clause's own literal. Everything is compared as printed
//! strings, so any surface mismatch fails closed to the honest fallback.

use std::fmt::Display;

/// Whether `conclusion` is `(= left right)` folded the way the term store
/// folds an equality with a Boolean constant: the other side for `true`, its
/// negation for `false`. The pinned checker's `equiv_simplify` proves exactly
/// `(= (= P true) P)`, `(= (= true P) P)`, `(= (= P false) (not P))` and
/// `(= (= false P) (not P))`.
pub(super) fn folded_bool_conclusion(left: &str, right: &str, conclusion: &str) -> bool {
    [(left, right), (right, left)]
        .into_iter()
        .any(|(atom, constant)| match constant {
            "true" => conclusion == atom,
            "false" => conclusion == format!("(not {atom})"),
            _ => false,
        })
}

/// Append the steps that turn `derived` — the `(= P b)` concluded by step
/// `last` — into the folded literal `conclusion`, ending on step `{id}.fin`:
/// `equiv_simplify` proves `(= (= P b) conclusion)`, `equiv1` weakens it to
/// `(cl (not (= P b)) conclusion)`, and `resolution` against `last` leaves
/// `conclusion`. Callers check [`folded_bool_conclusion`] first.
pub(super) fn push_folded_bool_closing(
    body: &mut Vec<String>,
    id: impl Display,
    derived: &str,
    conclusion: &str,
    last: &str,
) {
    body.push(format!(
        "(step {id}.fs (cl (= {derived} {conclusion})) :rule equiv_simplify)"
    ));
    body.push(format!(
        "(step {id}.fe (cl (not {derived}) {conclusion}) :rule equiv1 :premises ({id}.fs))"
    ));
    body.push(format!(
        "(step {id}.fin (cl {conclusion}) :rule resolution :premises ({id}.fe {last}))"
    ));
}
