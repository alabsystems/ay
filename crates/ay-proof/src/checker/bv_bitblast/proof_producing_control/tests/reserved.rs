// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A reserved operator's deliberate abstraction never absorbs a source refusal.

use super::*;

fn leaf(term: TermId, width: u32) -> BvExpr {
    BvExpr::leaf(&format!("proof_bv_{}", term.index()), width)
}

fn assert_source_refusal(terms: &TermStore, term: TermId, reason: &str) {
    let mut lowerer = ProofProducingLowerer::new_for_lemma_validation(terms, deadline());
    let error = lowerer.lower_bv(term).unwrap_err();
    assert!(error.contains(reason), "{error:?}, expected {reason:?}");
    assert!(!lowerer.memo.contains_key(&term));
    assert!(!lowerer.used_uninterpreted_leaves);
}

#[test]
fn reserved_abstraction_preserves_source_depth_refusal() {
    let mut terms = TermStore::new();
    let mut operand = terms.mk_var("deep-operand", Sort::bitvec(9));
    for _ in 0..MAX_PROOF_PRODUCING_EXPR_DEPTH {
        operand = terms.mk_app(Symbol::named("bvnot"), [operand], Sort::bitvec(9));
    }
    let three = terms.mk_bitvec(3.into(), 9);
    let quotient = terms.mk_app(Symbol::named("bvudiv"), [operand, three], Sort::bitvec(9));
    let rotation = terms.mk_app(
        Symbol::indexed("rotate_left", vec![1]),
        [operand],
        Sort::bitvec(9),
    );
    let repeat = terms.mk_app(
        Symbol::indexed("repeat", vec![1]),
        [operand],
        Sort::bitvec(9),
    );
    for application in [quotient, rotation, repeat] {
        let equality = terms.mk_app(Symbol::named("="), [application, application], Sort::Bool);
        let mut lowerer = ProofProducingLowerer::new_for_lemma_validation(&terms, deadline());
        let error = lowerer.lower_bool(equality).unwrap_err();
        assert!(error.contains("source depth exceeds"), "{error}");
        assert!(lowerer.resource_exhausted);
        assert!(!lowerer.used_uninterpreted_leaves);
        assert!(!lowerer.memo.contains_key(&application));
        assert!(matches!(
            lower_clause(&terms, &[equality], deadline(), false, &mut || true),
            Err(Failure::Rejected(reason)) if reason.contains("source depth exceeds")
        ));
    }
}

#[test]
fn reserved_division_preserves_counted_operand_refusals() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("counted-operand", Sort::bitvec(9));
    let operand = terms.mk_app(Symbol::named("bvnot"), [x], Sort::bitvec(9));
    let three = terms.mk_bitvec(3.into(), 9);
    let quotient = terms.mk_app(Symbol::named("bvudiv"), [operand, three], Sort::bitvec(9));
    for node_cap in [true, false] {
        let mut lowerer = ProofProducingLowerer::new_for_lemma_validation(&terms, deadline());
        let reason = if node_cap {
            lowerer.visited_nodes = MAX_PROOF_PRODUCING_TERM_NODES - 1;
            format!("term DAG exceeds {MAX_PROOF_PRODUCING_TERM_NODES} nodes")
        } else {
            lowerer.visited_edges = MAX_PROOF_PRODUCING_TERM_EDGES - 2;
            format!("term DAG exceeds {MAX_PROOF_PRODUCING_TERM_EDGES} child edges")
        };
        let error = lowerer.lower_bv(quotient).unwrap_err();
        assert_eq!(error, reason);
        assert!(lowerer.resource_exhausted);
        assert!(!lowerer.used_uninterpreted_leaves);
        assert!(!lowerer.memo.contains_key(&quotient));
    }
}

#[test]
fn reserved_division_validates_arity_sorts_widths_and_nested_operators() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("operand", Sort::bitvec(9));
    let short = terms.mk_var("short-operand", Sort::bitvec(8));
    let boolean = terms.mk_var("boolean-operand", Sort::Bool);
    let unknown = terms.mk_app(Symbol::named("unknown-bv"), [x, x], Sort::bitvec(9));
    for name in ["bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod"] {
        for args in [vec![], vec![x], vec![x, x, x]] {
            let term = terms.mk_app(Symbol::named(name), args, Sort::bitvec(9));
            assert_source_refusal(&terms, term, "requires two arguments");
        }
        for (args, reason) in [
            ([x, boolean], "is Bool, not BitVec"),
            ([x, short], "width mismatch"),
            ([unknown, x], "unsupported BitVec operator `unknown-bv`"),
        ] {
            let term = terms.mk_app(Symbol::named(name), args, Sort::bitvec(9));
            assert_source_refusal(&terms, term, reason);
        }
        let term = terms.mk_app(Symbol::named(name), [x, x], Sort::bitvec(8));
        assert_source_refusal(&terms, term, "expected 8");
    }
}

#[test]
fn indexed_reserved_abstraction_validates_the_complete_application() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("indexed-operand", Sort::bitvec(9));
    let boolean = terms.mk_var("indexed-boolean", Sort::Bool);
    let unknown = terms.mk_app(Symbol::named("unknown-bv"), [x, x], Sort::bitvec(9));
    for name in ["rotate_left", "rotate_right", "repeat"] {
        for indices in [vec![], vec![1, 2]] {
            let term = terms.mk_app(Symbol::indexed(name, indices), [x], Sort::bitvec(9));
            assert_source_refusal(&terms, term, "unsupported indexed BitVec operator");
        }
        for args in [vec![], vec![x, x]] {
            let term = terms.mk_app(Symbol::indexed(name, vec![1]), args, Sort::bitvec(9));
            assert_source_refusal(&terms, term, "requires one argument");
        }
        for (arg, reason) in [
            (boolean, "is Bool, not BitVec"),
            (unknown, "unsupported BitVec operator `unknown-bv`"),
        ] {
            let term = terms.mk_app(Symbol::indexed(name, vec![1]), [arg], Sort::bitvec(9));
            assert_source_refusal(&terms, term, reason);
        }
    }
    for (name, index, width, reason) in [
        ("repeat", 0, 9, "repeat count must be positive"),
        ("repeat", u32::MAX, 9, "repeat width overflow"),
        ("repeat", 2, 9, "expected 9"),
        ("rotate_left", 1, 8, "expected 8"),
        ("rotate_right", 1, 8, "expected 8"),
    ] {
        let term = terms.mk_app(Symbol::indexed(name, vec![index]), [x], Sort::bitvec(width));
        let mut lowerer = ProofProducingLowerer::new_for_lemma_validation(&terms, deadline());
        let error = lowerer.lower_bv(term).unwrap_err();
        assert!(error.contains(reason), "{error}");
        assert!(!lowerer.memo.contains_key(&term));
        assert!(!lowerer.used_uninterpreted_leaves);
    }
}

#[test]
fn valid_reserved_terms_share_only_their_canonical_leaf() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("shared-dividend", Sort::bitvec(9));
    let y = terms.mk_var("distinct-dividend", Sort::bitvec(9));
    let divisor = terms.mk_var("shared-divisor", Sort::bitvec(9));
    for name in ["bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod"] {
        let first = terms.mk_app(Symbol::named(name), [x, divisor], Sort::bitvec(9));
        let repeated = terms.mk_app(Symbol::named(name), [x, divisor], Sort::bitvec(9));
        let distinct = terms.mk_app(Symbol::named(name), [y, divisor], Sort::bitvec(9));
        assert_eq!(first, repeated);
        assert_ne!(first, distinct);
        let equality = terms.mk_app(Symbol::named("="), [first, repeated], Sort::Bool);
        let expected = BvExpr::eq(leaf(first, 9), leaf(first, 9));
        assert_every_lowering_poll(&terms, &[equality], &expected);
        let mut lowerer = ProofProducingLowerer::new_for_lemma_validation(&terms, deadline());
        assert_eq!(lowerer.lower_bv(first).unwrap(), (leaf(first, 9), 9));
        assert_eq!(lowerer.lower_bv(distinct).unwrap(), (leaf(distinct, 9), 9));
        assert!(lowerer.used_uninterpreted_leaves);
        let mut exact = ProofProducingLowerer::new(&terms, deadline());
        assert!(exact.lower_bv(first).unwrap_err().contains(name));
        assert!(!exact.used_uninterpreted_leaves);
    }
}

#[test]
fn indexed_abstraction_is_validated_and_confined_to_lemma_lowering() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("indexed-shared", Sort::bitvec(9));
    let sum = terms.mk_app(Symbol::named("bvadd"), [x, x], Sort::bitvec(9));
    for (name, index, width) in [
        ("rotate_left", 0, 9),
        ("rotate_right", 19, 9),
        ("repeat", 2, 18),
    ] {
        let term = terms.mk_app(
            Symbol::indexed(name, vec![index]),
            [sum],
            Sort::bitvec(width),
        );
        let equality = terms.mk_app(Symbol::named("="), [term, term], Sort::Bool);
        assert_every_lowering_poll(
            &terms,
            &[equality],
            &BvExpr::eq(leaf(term, width), leaf(term, width)),
        );
        let mut lowerer = ProofProducingLowerer::new_for_lemma_validation(&terms, deadline());
        assert_eq!(lowerer.lower_bv(term).unwrap(), (leaf(term, width), width));
        // The operand was lowered, once, before the leaf was minted. It is
        // requested once, so the census keeps no memo copy of it.
        assert!(lowerer.lowered.contains(&sum));
        assert_eq!(lowerer.requests.get(&sum), Some(&1));
        assert!(!lowerer.memo.contains_key(&sum));
        lowerer.audit_census();
        for mut exact in [
            ProofProducingLowerer::new(&terms, deadline()),
            ProofProducingLowerer::new_with_uninterpreted_leaves(&terms, deadline()),
            ProofProducingLowerer::new_with_non_finite_atom_leaves(&terms, deadline()),
        ] {
            assert!(exact.lower_bv(term).unwrap_err().contains(name));
            assert!(!exact.used_uninterpreted_leaves);
        }
    }
}

#[test]
fn power_of_two_division_and_remainder_still_lower_exactly() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("exact-dividend", Sort::bitvec(8));
    let minus_one = terms.mk_bitvec(255.into(), 8);
    let closed_one = terms.mk_app(Symbol::named("bvneg"), [minus_one], Sort::bitvec(8));
    let mut divisors = vec![(closed_one, 1_u128)];
    for value in [1_u128, 2, 4, 128] {
        divisors.push((terms.mk_bitvec(value.into(), 8), value));
    }
    for name in ["bvudiv", "bvurem"] {
        for &(divisor, value) in &divisors {
            let term = terms.mk_app(Symbol::named(name), [x, divisor], Sort::bitvec(8));
            let expected = if name == "bvudiv" {
                BvExpr::lshr(
                    leaf(x, 8),
                    BvExpr::const_val(u128::from(value.trailing_zeros()), 8),
                )
            } else {
                BvExpr::and(leaf(x, 8), BvExpr::const_val(value - 1, 8))
            };
            for mut lowerer in [
                ProofProducingLowerer::new(&terms, deadline()),
                ProofProducingLowerer::new_for_lemma_validation(&terms, deadline()),
            ] {
                assert_eq!(lowerer.lower_bv(term).unwrap(), (expected.clone(), 8));
                assert!(!lowerer.used_uninterpreted_leaves);
            }
        }
    }
}
