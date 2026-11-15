// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Indexed operators must retain their complete identity in both acceptance legs.

use super::*;
use ay_core::{ProofStep, Sort, Symbol, TheoryLemmaKind};

fn equality(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [a, b], Sort::Bool)
}

fn accepts_folded_image(terms: &mut TermStore, source: TermId, image: TermId) -> bool {
    let key = terms.mk_var("ground_symbol_len", Sort::Int);
    let value = terms.mk_int(1.into());
    let hyp = equality(terms, key, value);
    let p = terms.mk_app(Symbol::named("and"), [source, hyp], Sort::Bool);
    let clause = vec![terms.mk_not_raw(hyp), terms.mk_not_raw(p), image];
    let accepted = recognize_ground_equality_substitution(terms, &clause);
    assert_eq!(
        accepted,
        ground_substitution_image_matches(terms, p, image, &[(key, value)])
    );
    assert_eq!(accepted, strict_accepts(terms, clause));
    accepted
}

fn strict_accepts(terms: &TermStore, clause: Vec<TermId>) -> bool {
    let step = ProofStep::TheoryLemma {
        theory: "EUF".to_string(),
        clause,
        farkas: None,
        kind: TheoryLemmaKind::GroundEqualitySubstitution,
        lia: None,
    };
    let mut derived = Vec::new();
    let result = crate::checker::validate_step(terms, &mut derived, ProofId(0), &step, true, None);
    assert_eq!(derived.len(), usize::from(result.is_ok()));
    result.is_ok()
}

#[test]
fn ground_subst_preserves_extract_indices_with_a_concrete_counterexample() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("extract_x", Sort::bitvec(8));
    let zero = terms.mk_bitvec(0.into(), 1);
    let lo = terms.mk_app(Symbol::indexed("extract", vec![0, 0]), [x], Sort::bitvec(1));
    let hi = terms.mk_app(Symbol::indexed("extract", vec![1, 1]), [x], Sort::bitvec(1));
    let p = equality(&mut terms, lo, zero);
    let q = equality(&mut terms, hi, zero);
    // x=2 and len=1 satisfy the hypothesis and P, but falsify Q.
    assert_eq!(2_u8 & 1, 0);
    assert_ne!((2_u8 >> 1) & 1, 0);
    assert!(!accepts_folded_image(&mut terms, p, q));
    assert!(accepts_folded_image(&mut terms, p, p));
}

#[test]
fn ground_subst_preserves_rotation_indices() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("rotate_x", Sort::bitvec(8));
    let two = terms.mk_bitvec(2.into(), 8);
    for name in ["rotate_left", "rotate_right"] {
        let a = terms.mk_app(Symbol::indexed(name, vec![1]), [x], Sort::bitvec(8));
        let b = terms.mk_app(Symbol::indexed(name, vec![2]), [x], Sort::bitvec(8));
        let p = equality(&mut terms, a, two);
        let q = equality(&mut terms, b, two);
        assert!(!accepts_folded_image(&mut terms, p, q));
        assert!(accepts_folded_image(&mut terms, p, p));
    }
    assert_eq!(1_u8.rotate_left(1), 2);
    assert_ne!(1_u8.rotate_left(2), 2);
    assert_eq!(4_u8.rotate_right(1), 2);
    assert_ne!(4_u8.rotate_right(2), 2);
}

#[test]
fn ground_subst_distinguishes_named_and_indexed_symbols_including_empty_indices() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("symbol_x", Sort::Int);
    let named = terms.mk_app(Symbol::named("f"), [x], Sort::Bool);
    for indices in [vec![], vec![0], vec![0, 0]] {
        let indexed = terms.mk_app(Symbol::indexed("f", indices), [x], Sort::Bool);
        assert!(!accepts_folded_image(&mut terms, named, indexed));
        assert!(!accepts_folded_image(&mut terms, indexed, named));
        assert!(accepts_folded_image(&mut terms, indexed, indexed));
    }
}

#[test]
fn ground_subst_does_not_fold_indexed_symbols_with_builtin_names() {
    let mut terms = TermStore::new();
    let t = terms.mk_bool(true);
    let f = terms.mk_bool(false);
    let one = terms.mk_int(1.into());
    let two = terms.mk_int(2.into());
    for (name, args) in [
        ("and", vec![t, f]),
        ("or", vec![t, f]),
        ("not", vec![t]),
        ("=", vec![one, two]),
        ("<", vec![one, two]),
        ("<=", vec![one, two]),
        (">", vec![one, two]),
        (">=", vec![one, two]),
    ] {
        let named = terms.mk_app(Symbol::named(name), &args, Sort::Bool);
        let indexed = terms.mk_app(Symbol::indexed(name, vec![0]), &args, Sort::Bool);
        assert!(!accepts_folded_image(&mut terms, indexed, named), "{name}");
        assert!(accepts_folded_image(&mut terms, indexed, indexed), "{name}");
    }
}

#[test]
fn ground_subst_rejects_indexed_equality_as_a_substitution_hypothesis() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("hyp_x", Sort::Int);
    let one = terms.mk_int(1.into());
    let p = terms.mk_app(Symbol::named("p"), [x], Sort::Bool);
    let q = terms.mk_app(Symbol::named("p"), [one], Sort::Bool);
    for indices in [vec![], vec![0]] {
        let hyp = terms.mk_app(Symbol::indexed("=", indices), [x, one], Sort::Bool);
        let clause = vec![terms.mk_not_raw(hyp), terms.mk_not_raw(p), q];
        assert!(!recognize_ground_equality_substitution(&terms, &clause));
        assert!(!strict_accepts(&terms, clause));
    }
}

#[test]
fn ground_subst_indexed_normalization_respects_node_budget() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("budget_x", Sort::bitvec(8));
    let term = terms.mk_app(Symbol::indexed("extract", vec![0, 0]), [x], Sort::bitvec(1));
    let map = DetHashMap::default();
    let mut budget = 1;
    assert!(normalize_with_substitution(&terms, term, &map, &mut budget).is_err());
    assert_eq!(budget, 0);
    let mut budget = 2;
    assert!(normalize_with_substitution(&terms, term, &map, &mut budget).is_ok());
    assert_eq!(budget, 0);
}
