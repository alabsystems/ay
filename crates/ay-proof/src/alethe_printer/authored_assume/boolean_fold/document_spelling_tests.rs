// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The Boolean fold confines a bridge root only when no other override
//! re-spells a term inside or around it.

use super::*;
use ay_core::{Symbol, TermStore};
use num_bigint::BigInt;

/// Booleans `p`, `q`, `r`, the atom `(< x 3)`, and the conjunction
/// `(and p (< x 3))`.
struct Fixture {
    terms: TermStore,
    p: TermId,
    q: TermId,
    r: TermId,
    atom: TermId,
    conjunction: TermId,
}

fn fixture() -> Fixture {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let r = terms.mk_var("r", Sort::Bool);
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let atom = terms.mk_app(Symbol::named("<"), [x, three], Sort::Bool);
    let conjunction = terms.mk_app(Symbol::named("and"), [p, atom], Sort::Bool);
    Fixture {
        terms,
        p,
        q,
        r,
        atom,
        conjunction,
    }
}

/// Whether the authored-assume equivalence engine bridges `surface` onto
/// `term` under the document override table `overrides`.
fn bridges(
    terms: &TermStore,
    overrides: &HashMap<TermId, String>,
    term: TermId,
    surface: &str,
) -> bool {
    AlethePrinter::new_with_overrides(terms, Some(overrides)).authored_equivalence(
        "probe",
        surface,
        term,
        &mut 0,
        &mut Vec::new(),
    )
}

/// `(and p (not (not (< x 3))))`: the root collector records
/// `(not (not (< x 3)))` on the descendant `(< x 3)`, which keeps that text
/// in every step; confining the conjunction to `(and p (< x 3))` beside it
/// cost the base's carcara-`valid` document its publication.
#[test]
fn a_fold_above_a_respelled_descendant_is_declined() {
    let f = fixture();
    let surface = "(and p (not (not (< x 3))))";
    let mut overrides = HashMap::default();
    overrides.insert(f.conjunction, surface.to_string());
    assert!(
        bridges(&f.terms, &overrides, f.conjunction, surface),
        "with no other spelling in the document the fold confines the root"
    );
    overrides.insert(f.atom, "(not (not (< x 3)))".to_string());
    assert!(
        !bridges(&f.terms, &overrides, f.conjunction, surface),
        "a re-spelled descendant keeps the root where the base left it"
    );
}

/// `(= (< x 3) true)` below an ancestor the document re-spells: the ancestor
/// keeps embedding the root's authored text, so the fold declines. An
/// ancestor entry that IS the canonical rendering (the identity seal) re-spells
/// nothing.
#[test]
fn a_fold_below_a_respelled_ancestor_is_declined() {
    let mut f = fixture();
    let surface = "(= (< x 3) true)";
    let ancestor = f
        .terms
        .mk_app(Symbol::named("and"), [f.q, f.atom], Sort::Bool);
    let mut overrides = HashMap::default();
    overrides.insert(f.atom, surface.to_string());
    overrides.insert(ancestor, "(and q (< x 3))".to_string());
    assert!(
        bridges(&f.terms, &overrides, f.atom, surface),
        "an identity entry on the ancestor re-spells nothing"
    );
    overrides.insert(ancestor, "(and q (= (< x 3) true))".to_string());
    assert!(
        !bridges(&f.terms, &overrides, f.atom, surface),
        "an ancestor carrying the authored text keeps the root where the base left it"
    );
}

/// Equality operand order is one term to carcara's `alpha_equiv`. ABOVE the
/// root it only meets the confined root at literals, which the resolution
/// orientation repair bridges, so the fold proceeds; BELOW the root an
/// `and_pos` conjunct must occur in the printed conjunction verbatim, so the
/// fold declines.
#[test]
fn equality_orientation_blocks_the_fold_only_below_the_root() {
    let mut f = fixture();
    let (p, q, r) = (f.p, f.q, f.r);
    let equality = f.terms.mk_app(Symbol::named("="), [p, q], Sort::Bool);
    let ancestor = f.terms.mk_app(Symbol::named("="), [p, r], Sort::Bool);
    let mut overrides = HashMap::default();
    overrides.insert(p, "(or p false)".to_string());
    overrides.insert(ancestor, "(= r p)".to_string());
    assert!(
        bridges(&f.terms, &overrides, p, "(or p false)"),
        "an ancestor re-oriented by its own row does not block the fold"
    );

    let root = f
        .terms
        .mk_app(Symbol::named("and"), [r, equality], Sort::Bool);
    let surface = "(and r (= (= p q) true))";
    let mut overrides = HashMap::default();
    overrides.insert(root, surface.to_string());
    assert!(bridges(&f.terms, &overrides, root, surface));
    overrides.insert(equality, "(= q p)".to_string());
    assert!(
        !bridges(&f.terms, &overrides, root, surface),
        "a re-oriented descendant keeps the root where the base left it"
    );
}

/// The folded linear implication (`(or (< y 2.5) false)` over
/// `(< y (/ 5.0 2.0))`) confines its root exactly like the fold leaf, so it
/// declines under the same condition.
#[test]
fn the_folded_linear_implication_declines_beside_a_respelled_descendant() {
    let mut terms = TermStore::new();
    let y = terms.mk_var("y", Sort::Real);
    let half = terms.mk_rational(num_rational::BigRational::new(
        BigInt::from(5),
        BigInt::from(2),
    ));
    let root = terms.mk_app(Symbol::named("<"), [y, half], Sort::Bool);
    let surface = "(or (< y 2.5) false)";
    let canonical = crate::render_term_canonical(&terms, root);
    let mut overrides = HashMap::default();
    overrides.insert(root, surface.to_string());
    let admitted = |overrides: &HashMap<TermId, String>| {
        AlethePrinter::new_with_overrides(&terms, Some(overrides))
            .folded_linear_implication_admitted(root, surface, &canonical)
    };
    assert!(admitted(&overrides), "{canonical}");
    overrides.insert(half, "2.5".to_string());
    assert!(!admitted(&overrides), "{canonical}");
}
