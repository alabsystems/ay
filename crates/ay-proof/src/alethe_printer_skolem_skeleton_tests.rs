// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The skeleton guard a Skolemized `exists` body has to pass before its
//! AUTHORED spelling is carried into the anchor, the `choice` and every
//! projected instance (`printed_body_corresponds_to_internal`).
//!
//! Two refutations shaped it. The first (2026-09-16, `061e437f66`): a head
//! token is not a structure — an authored two-conjunct `and` the store had De
//! Morgan'd and FLATTENED into three passed a head-only guard, and the
//! `and_pos` that could not project conjunct 2 refused the export. The
//! second (2026-09-16, pass three): below the root, a store THEORY ATOM was
//! matched by ANY printed application — the arm ended `!root || head ==
//! Some(symbol.name())` — so an authored `(not (or A B))` whose `A` the store
//! folded to `false` and whose `(or false B)` it collapsed to `B` passed the
//! `not` arm and then matched the atom `B` with the printed `(or A B)`. The
//! carried body mixed two identities and `judge_printed_resolution` refused
//! the export at `t16`, where the base publishes a two-hole document.
//!
//! Every case here states what the base prints on refusal: the store's own
//! spelling and an honest hole, never a refused export.

use super::AlethePrinter;
use ay_core::{Sort, Symbol, TermData, TermStore};
use num_bigint::BigInt;

struct Bodies {
    terms: TermStore,
    /// `(exists ((z Int)) (not (or (< 0 (- 0 1)) (>= (g z) z))))` — the
    /// store folds the first disjunct to `false`, collapses the `or`, and
    /// keeps `(not (<= z (g z)))`.
    folded_disjunct: ay_core::TermId,
    /// `(exists ((z Int)) (and (>= z 0) (< (g z) z)))` — greenflag13, whose
    /// authored `(>= z 0)` is `(<= 0 z)` to the store.
    flipped_comparison: ay_core::TermId,
    /// `(exists ((z Int)) (and (>= z 0) (not (or (< z 0) (>= (g z) z)))))` —
    /// the first refutation: De Morgan'd and flattened to three conjuncts.
    flattened: ay_core::TermId,
}

fn bodies() -> Bodies {
    let mut terms = TermStore::new();
    let z = terms.mk_var("z_3", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let g_z = terms.mk_app(Symbol::named("g"), [z], Sort::Int);
    let minus_one = terms.mk_sub(vec![zero, one]);
    let zero_lt_minus_one = terms.mk_lt(zero, minus_one);
    let gz_ge_z = terms.mk_ge(g_z, z);
    let disjunction = terms.mk_or(vec![zero_lt_minus_one, gz_ge_z]);
    let folded_disjunct = terms.mk_not(disjunction);
    let z_ge_zero = terms.mk_ge(z, zero);
    let gz_lt_z = terms.mk_lt(g_z, z);
    let flipped_comparison = terms.mk_and(vec![z_ge_zero, gz_lt_z]);
    let z_lt_zero = terms.mk_lt(z, zero);
    let inner = terms.mk_or(vec![z_lt_zero, gz_ge_z]);
    let not_inner = terms.mk_not(inner);
    let flattened = terms.mk_and(vec![z_ge_zero, not_inner]);
    Bodies {
        terms,
        folded_disjunct,
        flipped_comparison,
        flattened,
    }
}

#[test]
fn a_store_atom_below_the_root_is_not_matched_by_a_printed_connective() {
    let bodies = bodies();
    // The premise of the test: the store really did fold the disjunct, so
    // its body is `(not ATOM)` and the authored `(or ..)` meets an atom.
    let TermData::Not(inner) = bodies.terms.get(bodies.folded_disjunct) else {
        panic!("the store keeps a negation at the root");
    };
    assert!(
        matches!(bodies.terms.get(*inner), TermData::App(symbol, args) if symbol.name() == "<=" && args.len() == 2),
        "the store collapsed `(or false B)` to the atom `B`: {:?}",
        bodies.terms.get(*inner)
    );
    let printer = AlethePrinter::new(&bodies.terms);
    assert!(
        !printer.printed_body_corresponds_to_internal(
            "(not (or (< 0 (- 0 1)) (>= (g z) z)))",
            bodies.folded_disjunct
        ),
        "a connective is never an atom's spelling"
    );
    // F06's shape, the same fold from a constant comparison.
    assert!(!printer.printed_body_corresponds_to_internal(
        "(not (or (< 1 0) (>= (g z) z)))",
        bodies.folded_disjunct
    ));
    // The atom's own spelling, or the store's known normalisation of it,
    // still corresponds.
    assert!(
        printer.printed_body_corresponds_to_internal("(not (>= (g z) z))", bodies.folded_disjunct)
    );
    assert!(
        printer.printed_body_corresponds_to_internal("(not (<= z (g z)))", bodies.folded_disjunct)
    );
}

#[test]
fn a_comparison_the_store_flipped_still_corresponds_below_the_root() {
    // greenflag13 / `ev_greenflag13`: MEASURED valid with the authored body
    // carried, because the `and_pos` bridge derives `(<= 0 z)` from
    // `(>= z 0)`. The enumerated normalisations must keep it.
    let bodies = bodies();
    let printer = AlethePrinter::new(&bodies.terms);
    assert!(printer.printed_body_corresponds_to_internal(
        "(and (>= z 0) (< (g z) z))",
        bodies.flipped_comparison
    ));
    // A head that is neither the atom's nor an enumerated normalisation of
    // it does not — even when the arity agrees.
    assert!(!printer.printed_body_corresponds_to_internal(
        "(and (= z 0) (< (g z) z))",
        bodies.flipped_comparison
    ));
    assert!(!printer.printed_body_corresponds_to_internal(
        "(and (distinct z 0) (< (g z) z))",
        bodies.flipped_comparison
    ));
    // At the ROOT the head has to agree exactly, as it always did.
    let TermData::App(_, conjuncts) = bodies.terms.get(bodies.flipped_comparison) else {
        panic!("an and-term");
    };
    let z_le = conjuncts[0];
    assert!(printer.printed_body_corresponds_to_internal("(<= 0 z)", z_le));
    assert!(!printer.printed_body_corresponds_to_internal("(>= z 0)", z_le));
}

#[test]
fn a_flattened_conjunction_still_does_not_correspond() {
    // The first refutation stays refused: head AND arity through every
    // connective.
    let bodies = bodies();
    let printer = AlethePrinter::new(&bodies.terms);
    assert!(!printer.printed_body_corresponds_to_internal(
        "(and (>= z 0) (not (or (< z 0) (>= (g z) z))))",
        bodies.flattened
    ));
}
