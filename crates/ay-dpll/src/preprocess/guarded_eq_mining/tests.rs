// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the GuardedEqMining preprocessing pass (#23).

use super::super::PreprocessingPass;
use super::GuardedEqMining;
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;

fn int_var(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::Int)
}

fn bool_var(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::Bool)
}

fn int(terms: &mut TermStore, v: i64) -> TermId {
    terms.mk_int(BigInt::from(v))
}

/// Whether `needle` occurs in the DAG of `hay`.
fn contains_term(terms: &TermStore, hay: TermId, needle: TermId) -> bool {
    use ay_core::term::TermData;
    if hay == needle {
        return true;
    }
    match terms.get(hay) {
        TermData::App(_, args) => args
            .clone()
            .iter()
            .any(|&a| contains_term(terms, a, needle)),
        TermData::Not(inner) => contains_term(terms, *inner, needle),
        TermData::Ite(c, t, e) => {
            let (c, t, e) = (*c, *t, *e);
            contains_term(terms, c, needle)
                || contains_term(terms, t, needle)
                || contains_term(terms, e, needle)
        }
        _ => false,
    }
}

/// One guard, both branches conserve x + y = 1; the conservation atom is
/// nested under a Bool definition. The atom must fold to true and be
/// re-asserted as a unit (exact output shape of the design).
#[test]
fn mines_single_guard_conservation_and_folds_atom() {
    let mut terms = TermStore::new();
    let g = bool_var(&mut terms, "g");
    let s = bool_var(&mut terms, "s");
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let zero = int(&mut terms, 0);
    let one = int(&mut terms, 1);

    // g true:  x = 1, y = 0;  g false:  x = 0, y = 1.
    let not_g = terms.mk_not(g);
    let eq_x1 = terms.mk_eq(x, one);
    let eq_y0 = terms.mk_eq(y, zero);
    let eq_x0 = terms.mk_eq(x, zero);
    let eq_y1 = terms.mk_eq(y, one);
    let c1 = terms.mk_or(vec![not_g, eq_x1]);
    let c2 = terms.mk_or(vec![not_g, eq_y0]);
    let c3 = terms.mk_or(vec![g, eq_x0]);
    let c4 = terms.mk_or(vec![g, eq_y1]);

    // s <-> (x + y = 1), the mined conservation atom.
    let sum = terms.mk_add(vec![x, y]);
    let atom = terms.mk_eq(sum, one);
    let def = terms.mk_eq(s, atom);
    let not_s = terms.mk_not(s);

    let mut assertions = vec![c1, c2, c3, c4, def, not_s];
    let mut pass = GuardedEqMining::new();
    let modified = pass.apply(&mut terms, &mut assertions);

    assert!(modified, "conservation atom should be folded");
    assert_eq!(pass.folded_atoms, 1);
    assert!(pass.mined_rows >= 1, "x + y = 1 should be mined");
    assert_eq!(pass.guards_two_sided, 1);

    // Paired unit re-assertion: the atom itself is now a unit assertion.
    assert!(
        assertions.contains(&atom),
        "entailed atom must be re-asserted as a unit"
    );
    // The Bool definition must no longer contain the atom (folded to true).
    let def_after = assertions[4];
    assert_ne!(def_after, def, "definition should be rewritten");
    assert!(
        !contains_term(&terms, def_after, atom),
        "atom occurrence inside the definition must be folded to a constant"
    );
    // Nothing deleted: all original positions still present.
    assert_eq!(assertions.len(), 7);
    // Guarded clauses are untouched (their atoms are not unconditional).
    assert_eq!(assertions[..4].to_vec(), vec![c1, c2, c3, c4]);
}

/// An atom contradicting the mined rows folds to false with a negated unit.
#[test]
fn entailed_false_atom_folds_to_negated_unit() {
    let mut terms = TermStore::new();
    let g = bool_var(&mut terms, "g");
    let s = bool_var(&mut terms, "s");
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let zero = int(&mut terms, 0);
    let one = int(&mut terms, 1);
    let two = int(&mut terms, 2);

    let not_g = terms.mk_not(g);
    let eq_x1 = terms.mk_eq(x, one);
    let eq_y0 = terms.mk_eq(y, zero);
    let eq_x0 = terms.mk_eq(x, zero);
    let eq_y1 = terms.mk_eq(y, one);
    let c1 = terms.mk_or(vec![not_g, eq_x1]);
    let c2 = terms.mk_or(vec![not_g, eq_y0]);
    let c3 = terms.mk_or(vec![g, eq_x0]);
    let c4 = terms.mk_or(vec![g, eq_y1]);

    // s <-> (x + y = 2): contradicts the mined x + y = 1.
    let sum = terms.mk_add(vec![x, y]);
    let atom = terms.mk_eq(sum, two);
    let def = terms.mk_eq(s, atom);

    let mut assertions = vec![c1, c2, c3, c4, def];
    let mut pass = GuardedEqMining::new();
    let modified = pass.apply(&mut terms, &mut assertions);

    assert!(modified);
    assert_eq!(pass.folded_atoms, 1);
    let not_atom = terms.mk_not(atom);
    assert!(
        assertions.contains(&not_atom),
        "entailed-false atom must re-assert its negation as a unit"
    );
    assert!(
        !contains_term(&terms, assertions[4], atom),
        "atom occurrence must be folded to a constant"
    );
}

/// Atoms that are not unconditionally entailed must never be folded.
#[test]
fn non_entailed_atom_is_untouched() {
    let mut terms = TermStore::new();
    let g = bool_var(&mut terms, "g");
    let s = bool_var(&mut terms, "s");
    let x = int_var(&mut terms, "x");
    let zero = int(&mut terms, 0);
    let one = int(&mut terms, 1);

    // Branches disagree: g -> x = 1, !g -> x = 0. Nothing is conserved.
    let not_g = terms.mk_not(g);
    let eq_x1 = terms.mk_eq(x, one);
    let eq_x0 = terms.mk_eq(x, zero);
    let c1 = terms.mk_or(vec![not_g, eq_x1]);
    let c2 = terms.mk_or(vec![g, eq_x0]);
    let def = terms.mk_eq(s, eq_x1);

    let mut assertions = vec![c1, c2, def];
    let before = assertions.clone();
    let mut pass = GuardedEqMining::new();
    let modified = pass.apply(&mut terms, &mut assertions);

    assert!(!modified, "no atom is unconditionally entailed");
    assert_eq!(assertions, before);
    assert_eq!(pass.folded_atoms, 0);
}

/// Atoms occurring only as whole top-level unit assertions are already unit
/// facts; folding them would be pure churn.
#[test]
fn top_level_only_units_are_skipped() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let z = int_var(&mut terms, "z");

    let e1 = terms.mk_eq(x, y);
    let e2 = terms.mk_eq(y, z);
    let e3 = terms.mk_eq(x, z); // entailed by e1 + e2, but top-level only

    let mut assertions = vec![e1, e2, e3];
    let before = assertions.clone();
    let mut pass = GuardedEqMining::new();
    let modified = pass.apply(&mut terms, &mut assertions);

    assert!(!modified);
    assert_eq!(assertions, before);
}

/// A pinned guard (`(assert g)`) promotes its implied-branch equalities to
/// unconditional rows.
#[test]
fn pinned_guard_promotes_branch_rows() {
    let mut terms = TermStore::new();
    let g = bool_var(&mut terms, "g");
    let s = bool_var(&mut terms, "s");
    let x = int_var(&mut terms, "x");
    let one = int(&mut terms, 1);
    let two = int(&mut terms, 2);

    let not_g = terms.mk_not(g);
    let eq_x1 = terms.mk_eq(x, one);
    let eq_x2 = terms.mk_eq(x, two);
    let c1 = terms.mk_or(vec![not_g, eq_x1]); // g -> x = 1
    let c2 = terms.mk_or(vec![g, eq_x2]); // !g -> x = 2 (clause satisfied)
    let def = terms.mk_eq(s, eq_x1);

    let mut assertions = vec![g, c1, c2, def];
    let mut pass = GuardedEqMining::new();
    let modified = pass.apply(&mut terms, &mut assertions);

    assert!(modified, "x = 1 holds because g is pinned true");
    assert!(assertions.contains(&eq_x1));
    assert!(!contains_term(&terms, assertions[3], eq_x1));
}

/// Multi-guard chain: the conservation needs rows mined from one guard to be
/// reused while processing another (fixpoint), mirroring the lustre repro.
#[test]
fn fixpoint_chains_rows_across_guards() {
    let mut terms = TermStore::new();
    let g1 = bool_var(&mut terms, "g1");
    let g2 = bool_var(&mut terms, "g2");
    let s = bool_var(&mut terms, "s");
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let a = int_var(&mut terms, "a");
    let b = int_var(&mut terms, "b");
    let one = int(&mut terms, 1);

    // Guard g1: both branches give a + b = x + y.
    //   g1 true:  a = x, b = y;   g1 false:  a = y, b = x.
    let not_g1 = terms.mk_not(g1);
    let t1a = terms.mk_eq(a, x);
    let t1b = terms.mk_eq(b, y);
    let f1a = terms.mk_eq(a, y);
    let f1b = terms.mk_eq(b, x);
    let c1 = terms.mk_or(vec![not_g1, t1a]);
    let c2 = terms.mk_or(vec![not_g1, t1b]);
    let c3 = terms.mk_or(vec![g1, f1a]);
    let c4 = terms.mk_or(vec![g1, f1b]);

    // Guard g2 relates x + y to 1 on both branches only modulo the row mined
    // from g1:
    //   g2 true:  x + y = 1 directly.
    //   g2 false: a + b = 1, which needs a + b = x + y from g1.
    let not_g2 = terms.mk_not(g2);
    let sum_xy = terms.mk_add(vec![x, y]);
    let sum_ab = terms.mk_add(vec![a, b]);
    let t2 = terms.mk_eq(sum_xy, one);
    let f2 = terms.mk_eq(sum_ab, one);
    let c5 = terms.mk_or(vec![not_g2, t2]);
    let c6 = terms.mk_or(vec![g2, f2]);

    // Target: s <-> (x + y = 1).
    let atom = terms.mk_eq(sum_xy, one);
    let def = terms.mk_eq(s, atom);
    let not_s = terms.mk_not(s);

    let mut assertions = vec![c1, c2, c3, c4, c5, c6, def, not_s];
    let mut pass = GuardedEqMining::new();
    let modified = pass.apply(&mut terms, &mut assertions);

    assert!(
        modified,
        "fixpoint must chain g1's row into g2's intersection"
    );
    assert!(assertions.contains(&atom));
    assert!(!contains_term(&terms, assertions[6], atom));
}

/// Provenance: appended unit re-assertions get the union of all sources and
/// the lengths stay aligned.
#[test]
fn apply_with_sources_appends_union_provenance() {
    let mut terms = TermStore::new();
    let g = bool_var(&mut terms, "g");
    let s = bool_var(&mut terms, "s");
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let zero = int(&mut terms, 0);
    let one = int(&mut terms, 1);

    let not_g = terms.mk_not(g);
    let eq_x1 = terms.mk_eq(x, one);
    let eq_y0 = terms.mk_eq(y, zero);
    let eq_x0 = terms.mk_eq(x, zero);
    let eq_y1 = terms.mk_eq(y, one);
    let c1 = terms.mk_or(vec![not_g, eq_x1]);
    let c2 = terms.mk_or(vec![not_g, eq_y0]);
    let c3 = terms.mk_or(vec![g, eq_x0]);
    let c4 = terms.mk_or(vec![g, eq_y1]);
    let sum = terms.mk_add(vec![x, y]);
    let atom = terms.mk_eq(sum, one);
    let def = terms.mk_eq(s, atom);

    let mut assertions = vec![c1, c2, c3, c4, def];
    let mut source_sets: Vec<Vec<TermId>> = assertions.iter().map(|&a| vec![a]).collect();
    let mut pass = GuardedEqMining::new();
    let modified = pass.apply_with_sources(&mut terms, &mut assertions, &mut source_sets);

    assert!(modified);
    assert_eq!(assertions.len(), source_sets.len());
    let unit_sources = source_sets.last().expect("appended unit has sources");
    let mut expected = vec![c1, c2, c3, c4, def];
    expected.sort_by_key(|t| t.index());
    assert_eq!(unit_sources, &expected);
}

/// Unary minus is negation: `(= 1 (+ x (- y)))` must parse as x - y = 1
/// (regression: the first cut treated `(- y)` as `+y`).
#[test]
fn unary_minus_parses_as_negation() {
    let mut terms = TermStore::new();
    let g = bool_var(&mut terms, "g");
    let s = bool_var(&mut terms, "s");
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let one = int(&mut terms, 1);

    // g true: 1 = x + (- y); g false: x = y + 1. Both mean x - y = 1.
    let not_g = terms.mk_not(g);
    let neg_y = terms.mk_neg(y);
    let sum = terms.mk_add(vec![x, neg_y]);
    let t1 = terms.mk_eq(one, sum);
    let y_plus_1 = terms.mk_add(vec![y, one]);
    let f1 = terms.mk_eq(x, y_plus_1);
    let c1 = terms.mk_or(vec![not_g, t1]);
    let c2 = terms.mk_or(vec![g, f1]);

    // s <-> (x + (- y) = 1), the conserved equation.
    let atom = terms.mk_eq(sum, one);
    let def = terms.mk_eq(s, atom);

    let mut assertions = vec![c1, c2, def];
    let mut pass = GuardedEqMining::new();
    let modified = pass.apply(&mut terms, &mut assertions);

    assert!(modified, "x - y = 1 holds on both branches");
    assert!(
        assertions.contains(&atom) || {
            // t1 and atom may intern to the same term; either unit works.
            assertions.contains(&t1)
        },
        "conserved atom must be re-asserted as a unit"
    );
}

/// Rational coefficients must be handled exactly (no floating point).
#[test]
fn exact_rational_arithmetic_on_scaled_rows() {
    let mut terms = TermStore::new();
    let g = bool_var(&mut terms, "g");
    let s = bool_var(&mut terms, "s");
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let zero = int(&mut terms, 0);
    let three = int(&mut terms, 3);
    let six = int(&mut terms, 6);

    // g true: 3x = 6 and y = 0; g false: x + y = 2 (scaled differently).
    let not_g = terms.mk_not(g);
    let three_x = terms.mk_mul(vec![three, x]);
    let t1 = terms.mk_eq(three_x, six);
    let t2 = terms.mk_eq(y, zero);
    let two = int(&mut terms, 2);
    let sum = terms.mk_add(vec![x, y]);
    let f1 = terms.mk_eq(sum, two);
    let c1 = terms.mk_or(vec![not_g, t1]);
    let c2 = terms.mk_or(vec![not_g, t2]);
    let c3 = terms.mk_or(vec![g, f1]);

    // x + y = 2 holds on both branches (true branch: x = 2, y = 0).
    let atom = terms.mk_eq(sum, two);
    let def = terms.mk_eq(s, atom);

    let mut assertions = vec![c1, c2, c3, def];
    let mut pass = GuardedEqMining::new();
    let modified = pass.apply(&mut terms, &mut assertions);

    assert!(modified, "scaled rows must intersect exactly");
    assert!(assertions.contains(&atom));
}

/// Must-fix from the keystone soundness review: an assertion REWRITTEN by
/// Phase F folding has its provenance widened to the fold justification (the
/// network's sources), not just its positional source. Without this,
/// incremental activation-depth metadata could retain a folded assertion past
/// the pop that retracts its justifiers (latent wrong-unsat).
#[test]
fn apply_with_sources_widens_rewritten_assertion_provenance() {
    let mut terms = TermStore::new();
    let g = bool_var(&mut terms, "g");
    let s = bool_var(&mut terms, "s");
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let zero = int(&mut terms, 0);
    let one = int(&mut terms, 1);

    let not_g = terms.mk_not(g);
    let eq_x1 = terms.mk_eq(x, one);
    let eq_y0 = terms.mk_eq(y, zero);
    let eq_x0 = terms.mk_eq(x, zero);
    let eq_y1 = terms.mk_eq(y, one);
    let c1 = terms.mk_or(vec![not_g, eq_x1]);
    let c2 = terms.mk_or(vec![not_g, eq_y0]);
    let c3 = terms.mk_or(vec![g, eq_x0]);
    let c4 = terms.mk_or(vec![g, eq_y1]);
    let sum = terms.mk_add(vec![x, y]);
    let atom = terms.mk_eq(sum, one);
    let def = terms.mk_eq(s, atom);

    let mut assertions = vec![c1, c2, c3, c4, def];
    let mut source_sets: Vec<Vec<TermId>> = assertions.iter().map(|&a| vec![a]).collect();
    let mut pass = GuardedEqMining::new();
    let modified = pass.apply_with_sources(&mut terms, &mut assertions, &mut source_sets);

    assert!(modified);
    assert_eq!(assertions.len(), source_sets.len());
    // `def` (index 4) is rewritten by the fold (atom -> true), so its source
    // set must now include the guard clauses that justified the fold.
    assert_ne!(assertions[4], def, "def must have been rewritten");
    for justifier in [c1, c2, c3, c4] {
        assert!(
            source_sets[4].contains(&justifier),
            "rewritten assertion's sources must include the fold justifiers"
        );
    }
    // Unchanged guard clauses keep their narrow positional provenance.
    assert_eq!(source_sets[0], vec![c1]);
}
