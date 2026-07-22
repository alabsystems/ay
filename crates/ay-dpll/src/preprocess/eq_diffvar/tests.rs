// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the EqDiffVar preprocessing pass (inc-14, #23 residual).

use super::super::PreprocessingPass;
use super::EqDiffVar;
use ay_core::term::TermData;
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

/// Guarded var-var equality network: each guarded `(= x y)` atom is rewritten
/// to `(= d 0)` with `d` defined by an unconditional inequality pair, and
/// syntactic variants of the same difference share ONE `d`.
#[test]
fn rewrites_guarded_var_var_atoms_to_shared_diff_var() {
    let mut terms = TermStore::new();
    let g = bool_var(&mut terms, "g");
    let h = bool_var(&mut terms, "h");
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");

    let not_g = terms.mk_not(g);
    let not_h = terms.mk_not(h);
    let eq_xy = terms.mk_eq(x, y);
    // Same difference written the other way around: y = x.
    let eq_yx = terms.mk_eq(y, x);
    let c1 = terms.mk_or(vec![not_g, eq_xy]);
    let c2 = terms.mk_or(vec![not_h, eq_yx]);

    let mut assertions = vec![c1, c2];
    let mut pass = EqDiffVar::new();
    let modified = pass.apply(&mut terms, &mut assertions);

    assert!(modified, "guarded var-var atoms should be rewritten");
    assert_eq!(pass.diff_vars, 1, "x-y and y-x must share one diff var");
    // (= x y) and (= y x) hash-cons to ONE atom term; the stat counts
    // distinct atom terms.
    assert_eq!(pass.rewritten_atoms, 1);
    // 2 original (rewritten) + 2 definitional inequalities.
    assert_eq!(assertions.len(), 4);
    // The var-var atoms are gone from the rewritten clauses.
    assert!(!contains_term(&terms, assertions[0], eq_xy));
    assert!(!contains_term(&terms, assertions[1], eq_yx));
    // Definitions are inequalities (NOT a unit equality, which downstream
    // VariableSubstitution would inline right back).
    for &def in &assertions[2..] {
        match terms.get(def) {
            TermData::App(sym, _) => {
                let name = sym.name();
                assert!(
                    name == "<=" || name == ">=",
                    "definition must be an inequality pair, got {name}"
                );
            }
            other => panic!("definition must be an App, got {other:?}"),
        }
    }
}

/// Atoms over the same linear form with different constants share the
/// difference variable, so `(= d 0)` / `(= d 5)` conflict directly.
#[test]
fn same_linear_form_different_constants_share_diff_var() {
    let mut terms = TermStore::new();
    let g = bool_var(&mut terms, "g");
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let five = int(&mut terms, 5);

    let not_g = terms.mk_not(g);
    let eq0 = terms.mk_eq(x, y); // x - y = 0
    let y_plus_5 = terms.mk_add(vec![y, five]);
    let eq5 = terms.mk_eq(x, y_plus_5); // x - y = 5
    let c1 = terms.mk_or(vec![not_g, eq0]);
    let c2 = terms.mk_or(vec![g, eq5]);

    let mut assertions = vec![c1, c2];
    let mut pass = EqDiffVar::new();
    assert!(pass.apply(&mut terms, &mut assertions));
    assert_eq!(pass.diff_vars, 1);
    assert_eq!(pass.rewritten_atoms, 2);
}

/// Single-variable (var-const) atoms and Bool equalities are not touched;
/// a formula with no multi-leaf Int equality atoms is left unchanged.
#[test]
fn leaves_var_const_and_bool_atoms_alone() {
    let mut terms = TermStore::new();
    let g = bool_var(&mut terms, "g");
    let h = bool_var(&mut terms, "h");
    let x = int_var(&mut terms, "x");
    let one = int(&mut terms, 1);

    let not_g = terms.mk_not(g);
    let eq_x1 = terms.mk_eq(x, one);
    let c1 = terms.mk_or(vec![not_g, eq_x1]);
    let eq_gh = terms.mk_eq(g, h);

    let mut assertions = vec![c1, eq_gh];
    let before = assertions.clone();
    let mut pass = EqDiffVar::new();
    assert!(!pass.apply(&mut terms, &mut assertions));
    assert_eq!(assertions, before);
}

/// Top-level unit equalities (whole assertions) are skipped — they are
/// variable-substitution food, not branching atoms.
#[test]
fn skips_top_level_unit_equalities() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let eq_xy = terms.mk_eq(x, y);

    let mut assertions = vec![eq_xy];
    let mut pass = EqDiffVar::new();
    assert!(!pass.apply(&mut terms, &mut assertions));
    assert_eq!(assertions, vec![eq_xy]);
}

/// A unit equality that ALSO occurs nested is rewritten everywhere
/// (equivalence rewrite: any subset of occurrences is sound, and the
/// nested occurrence is the one that prunes branching).
#[test]
fn unit_equality_with_nested_occurrence_is_rewritten() {
    let mut terms = TermStore::new();
    let g = bool_var(&mut terms, "g");
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let eq_xy = terms.mk_eq(x, y);
    let not_g = terms.mk_not(g);
    let clause = terms.mk_or(vec![not_g, eq_xy]);

    let mut assertions = vec![eq_xy, clause];
    let mut pass = EqDiffVar::new();
    assert!(pass.apply(&mut terms, &mut assertions));
    assert!(!contains_term(&terms, assertions[0], eq_xy));
    assert!(!contains_term(&terms, assertions[1], eq_xy));
}

/// Non-integral canonical rhs (2x - 2y = 1) must be SKIPPED, never folded:
/// deciding integer infeasibility belongs to the solver.
#[test]
fn skips_non_integral_rhs() {
    let mut terms = TermStore::new();
    let g = bool_var(&mut terms, "g");
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let two = int(&mut terms, 2);
    let one = int(&mut terms, 1);

    let tx = terms.mk_mul(vec![two, x]);
    let two2 = int(&mut terms, 2);
    let ty = terms.mk_mul(vec![two2, y]);
    let sub = terms.mk_sub(vec![tx, ty]);
    let atom = terms.mk_eq(sub, one);
    let not_g = terms.mk_not(g);
    let clause = terms.mk_or(vec![not_g, atom]);

    let mut assertions = vec![clause];
    let before = assertions.clone();
    let mut pass = EqDiffVar::new();
    assert!(!pass.apply(&mut terms, &mut assertions));
    assert_eq!(assertions, before);
}

/// An equality whose linear row draws a leaf from an ITE — the
/// `(cmp (Σ cᵢ·(ite bᵢ cᵢ 0)) k)` shape that pseudo-boolean / cardinality
/// constraints desugar to — must be SKIPPED, never folded. Folding it detaches
/// the reified selectors and duplicates the ITE-bearing linear form into the
/// two definitional inequalities, which thrashes the downstream LIA search to
/// a battery-failing `unknown` (repro: a negated `(_ pbeq …)`). Skipping is a
/// pure restriction of the optimization, so it never changes a verdict.
#[test]
fn skips_ite_bearing_leaves() {
    let mut terms = TermStore::new();
    let g = bool_var(&mut terms, "g");
    let b0 = bool_var(&mut terms, "b0");
    let b1 = bool_var(&mut terms, "b1");
    let one = int(&mut terms, 1);
    let zero0 = int(&mut terms, 0);
    let two = int(&mut terms, 2);
    let zero1 = int(&mut terms, 0);
    // (ite b0 1 0) + (ite b1 2 0) = 1  — a two-leaf integer row whose leaves
    // are both arithmetic ITEs (weighted cardinality indicators).
    let ite0 = terms.mk_ite(b0, one, zero0);
    let ite1 = terms.mk_ite(b1, two, zero1);
    let sum = terms.mk_add(vec![ite0, ite1]);
    let k = int(&mut terms, 1);
    let atom = terms.mk_eq(sum, k);
    let not_g = terms.mk_not(g);
    let clause = terms.mk_or(vec![not_g, atom]);

    let mut assertions = vec![clause];
    let before = assertions.clone();
    let mut pass = EqDiffVar::new();
    assert!(
        !pass.apply(&mut terms, &mut assertions),
        "an ITE-bearing equality row must not be folded"
    );
    assert_eq!(
        assertions, before,
        "the assertion set must be left untouched"
    );
    assert_eq!(pass.diff_vars, 0);
}

/// Coefficient normalization: `2x - 2y = 4` and `x - y = 2` share one diff
/// var (gcd normalization) with consistent constants.
#[test]
fn gcd_normalization_dedupes_scaled_atoms() {
    let mut terms = TermStore::new();
    let g = bool_var(&mut terms, "g");
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let two_a = int(&mut terms, 2);
    let two_b = int(&mut terms, 2);
    let four = int(&mut terms, 4);
    let two_c = int(&mut terms, 2);

    let tx = terms.mk_mul(vec![two_a, x]);
    let ty = terms.mk_mul(vec![two_b, y]);
    let sub = terms.mk_sub(vec![tx, ty]);
    let scaled = terms.mk_eq(sub, four); // 2x - 2y = 4
    let sub_xy = terms.mk_sub(vec![x, y]);
    let plain = terms.mk_eq(sub_xy, two_c); // x - y = 2
    let not_g = terms.mk_not(g);
    let c1 = terms.mk_or(vec![not_g, scaled]);
    let c2 = terms.mk_or(vec![g, plain]);

    let mut assertions = vec![c1, c2];
    let mut pass = EqDiffVar::new();
    assert!(pass.apply(&mut terms, &mut assertions));
    assert_eq!(pass.diff_vars, 1, "scaled variants must share one diff var");
    assert_eq!(pass.rewritten_atoms, 2);
    // Both clauses must now reference the SAME replacement atom.
    let TermData::App(_, args0) = terms.get(assertions[0]) else {
        panic!("clause expected")
    };
    let TermData::App(_, args1) = terms.get(assertions[1]) else {
        panic!("clause expected")
    };
    let rep0 = args0[1];
    let rep1 = args1[1];
    assert_eq!(rep0, rep1, "(= d 2) must be shared after normalization");
}

/// Idempotence (PreprocessingPass contract): a second application of the
/// pass on its own output makes no changes.
#[test]
fn second_application_is_a_no_op() {
    let mut terms = TermStore::new();
    let g = bool_var(&mut terms, "g");
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let eq_xy = terms.mk_eq(x, y);
    let not_g = terms.mk_not(g);
    let clause = terms.mk_or(vec![not_g, eq_xy]);

    let mut assertions = vec![clause];
    let mut pass = EqDiffVar::new();
    assert!(pass.apply(&mut terms, &mut assertions));
    let after_first = assertions.clone();

    let mut pass2 = EqDiffVar::new();
    assert!(!pass2.apply(&mut terms, &mut assertions));
    assert_eq!(assertions, after_first);
}

/// Provenance threading: rewritten assertions are widened to the union of
/// all original sources, and each definitional assertion carries the same
/// union (mirrors GuardedEqMining; the 171e87c incremental-session lesson).
#[test]
fn apply_with_sources_widens_provenance() {
    let mut terms = TermStore::new();
    let g = bool_var(&mut terms, "g");
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let z = int_var(&mut terms, "z");
    let one = int(&mut terms, 1);

    let eq_xy = terms.mk_eq(x, y);
    let not_g = terms.mk_not(g);
    let clause = terms.mk_or(vec![not_g, eq_xy]);
    // Unrelated assertion that is NOT rewritten.
    let z_ge_1 = terms.mk_ge(z, one);

    let src_a = terms.mk_var("srcA", Sort::Bool);
    let src_b = terms.mk_var("srcB", Sort::Bool);

    let mut assertions = vec![clause, z_ge_1];
    let mut source_sets = vec![vec![src_a], vec![src_b]];
    let mut pass = EqDiffVar::new();
    let modified = pass.apply_with_sources(&mut terms, &mut assertions, &mut source_sets);

    assert!(modified);
    assert_eq!(assertions.len(), source_sets.len());
    // The rewritten clause is justified by the union of all sources.
    assert!(source_sets[0].contains(&src_a) && source_sets[0].contains(&src_b));
    // The untouched assertion keeps its narrow provenance.
    assert_eq!(source_sets[1], vec![src_b]);
    // Every definitional assertion carries the union.
    for set in &source_sets[2..] {
        assert!(set.contains(&src_a) && set.contains(&src_b));
    }
}

/// MOESI-like miniature end-to-end shape check: a two-sided guard network
/// over distinct variable pairs becomes a var-const network over shared
/// difference variables, with one definition pair per distinct difference.
#[test]
fn moesi_like_network_reduces_to_var_const() {
    let mut terms = TermStore::new();
    let q = bool_var(&mut terms, "q");
    let a = int_var(&mut terms, "a");
    let b = int_var(&mut terms, "b");
    let c = int_var(&mut terms, "c");
    let d = int_var(&mut terms, "d");

    let not_q = terms.mk_not(q);
    let eq_ab = terms.mk_eq(a, b);
    let eq_cd = terms.mk_eq(c, d);
    let eq_ac = terms.mk_eq(a, c);
    let t1 = terms.mk_or(vec![not_q, eq_ab]);
    let t2 = terms.mk_or(vec![not_q, eq_cd]);
    let f1 = terms.mk_or(vec![q, eq_ac]);

    let mut assertions = vec![t1, t2, f1];
    let mut pass = EqDiffVar::new();
    assert!(pass.apply(&mut terms, &mut assertions));
    assert_eq!(pass.diff_vars, 3);
    assert_eq!(pass.rewritten_atoms, 3);
    // 3 rewritten + 6 definitional inequalities.
    assert_eq!(assertions.len(), 9);
    for needle in [eq_ab, eq_cd, eq_ac] {
        for &assertion in &assertions[..3] {
            assert!(!contains_term(&terms, assertion, needle));
        }
    }
}
