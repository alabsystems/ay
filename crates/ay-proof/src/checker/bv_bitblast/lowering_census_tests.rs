// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The census counts the requests the lowering makes, so no term is lowered
//! twice and only a term requested more than once keeps a memo copy.
//!
//! Each test is one shape a post-landing review of the census found it
//! mis-counting (2026-09-29): a census the caps stopped, `extract` through a
//! `concat`, reads of one sparse store chain, the operands of an abstracted
//! atom, and roots of one batch that share a subterm. The last ones are the
//! shape the review of that fix found (2026-09-30), a failure below a
//! division requested again, as it stands now that lemma validation abstracts
//! a reserved operator only after its operands lower: the failure refuses the
//! lemma once, and an abstracted operator requests its operands as counted.

use std::time::{Duration, Instant};

use super::*;

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

fn bv(terms: &mut TermStore, op: &str, args: &[TermId], width: u32) -> TermId {
    terms.mk_app(Symbol::named(op), args, Sort::bitvec(width))
}

fn predicate(terms: &mut TermStore, op: &str, args: &[TermId]) -> TermId {
    terms.mk_app(Symbol::named(op), args, Sort::Bool)
}

/// `(bvmul (bvadd a b) (bvxor a c))` over fresh 8-bit names: a subterm with
/// something to re-lower.
fn product(terms: &mut TermStore, prefix: &str) -> TermId {
    let a = terms.mk_var(format!("{prefix}_a"), Sort::bitvec(8));
    let b = terms.mk_var(format!("{prefix}_b"), Sort::bitvec(8));
    let c = terms.mk_var(format!("{prefix}_c"), Sort::bitvec(8));
    let sum = bv(terms, "bvadd", &[a, b], 8);
    let mixed = bv(terms, "bvxor", &[a, c], 8);
    bv(terms, "bvmul", &[sum, mixed], 8)
}

#[test]
fn a_census_the_caps_stopped_memoizes_a_term_it_counted_only_partly() {
    let mut terms = TermStore::new();
    let shared = product(&mut terms, "p");
    let mut lowerer = ProofProducingLowerer::new(&terms, deadline());
    // The caps stopped the census after it had counted one edge into
    // `shared`; its other edges were never counted.
    lowerer.census_incomplete = true;
    lowerer.parents.insert(shared, 1);
    assert!(
        lowerer.memoizes(shared),
        "a partial count is not evidence of a single request"
    );
}

#[test]
fn the_census_never_walks_the_operands_of_an_abstracted_atom() {
    let mut terms = TermStore::new();
    // An `Int` chain with more terms than the census may count, under an
    // uninterpreted Boolean application the lowering abstracts to one leaf
    // without descending.
    let mut big = terms.mk_var("i", Sort::Int);
    for step in 0..(MAX_PROOF_PRODUCING_TERM_NODES + 64) {
        let constant = terms.mk_var(format!("k{step}"), Sort::Int);
        big = terms.mk_app(Symbol::named("+"), [big, constant], Sort::Int);
    }
    let atom = predicate(&mut terms, "f", &[big]);
    let shared = product(&mut terms, "p");
    let d = terms.mk_var("d", Sort::bitvec(8));
    let first = predicate(&mut terms, "=", &[shared, d]);
    let second = predicate(&mut terms, "bvult", &[shared, d]);
    let root = predicate(&mut terms, "and", &[first, atom, second]);

    let mut lowerer = ProofProducingLowerer::new_with_uninterpreted_leaves(&terms, deadline());
    lowerer.lower_bool(root).unwrap();
    assert!(
        !lowerer.census_seen.contains(&big),
        "walked an abstracted operand"
    );
    assert!(
        !lowerer.census_incomplete,
        "the abstracted operand exhausted the census"
    );
    lowerer.audit_census();
}

/// `(concat v_{n-1} (concat ... (concat v_1 v_0)))` of `n` 8-bit lanes, each
/// lane a product, so a re-lowered operand costs something.
fn lane_chain(terms: &mut TermStore, lanes: u32) -> TermId {
    let mut word = product(terms, "lane0");
    for lane in 1..lanes {
        let high = product(terms, &format!("lane{lane}"));
        word = bv(terms, "concat", &[high, word], 8 * (lane + 1));
    }
    word
}

fn extract(terms: &mut TermStore, source: TermId, high: u32, low: u32) -> TermId {
    terms.mk_app(
        Symbol::indexed("extract", vec![high, low]),
        [source],
        Sort::bitvec(high - low + 1),
    )
}

/// The projection as it was written before the lowering took operands out
/// of the lowered `concat`: every step lowers the chosen operand again.
fn relowering_projection(
    lowerer: &mut ProofProducingLowerer<'_, '_>,
    source: TermId,
    high: u32,
    low: u32,
) -> (BvExpr, u32) {
    let (inner, width) = lowerer.lower_bv(source).unwrap();
    let result_width = high - low + 1;
    if result_width == width {
        return (inner, width);
    }
    let TermData::App(Symbol::Named(name), args) = lowerer.terms.get(source) else {
        return (BvExpr::extract(inner, high, low), result_width);
    };
    let [left, right] = args.as_slice() else {
        return (BvExpr::extract(inner, high, low), result_width);
    };
    if name != "concat" {
        return (BvExpr::extract(inner, high, low), result_width);
    }
    let (left, right) = (*left, *right);
    let Sort::BitVec(right_sort) = lowerer.terms.sort(right) else {
        unreachable!("a concat operand is a BitVec")
    };
    let right_width = right_sort.width;
    if high < right_width {
        return relowering_projection(lowerer, right, high, low);
    }
    if low >= right_width {
        return relowering_projection(lowerer, left, high - right_width, low - right_width);
    }
    let (upper, upper_width) = relowering_projection(lowerer, left, high - right_width, 0);
    let (lower, lower_width) = relowering_projection(lowerer, right, right_width - 1, low);
    let shifted = BvExpr::shl(
        BvExpr::zero_ext(upper, lower_width),
        BvExpr::const_val(u128::from(lower_width), result_width),
    );
    (
        BvExpr::or(shifted, BvExpr::zero_ext(lower, upper_width)),
        result_width,
    )
}

#[test]
fn an_extract_through_a_concat_chain_lowers_no_operand_twice() {
    let mut terms = TermStore::new();
    let lanes = 16;
    let word = lane_chain(&mut terms, lanes);
    // Every lane, and every window that straddles two lanes.
    let mut windows = Vec::new();
    for lane in 0..lanes {
        windows.push((8 * lane + 7, 8 * lane));
    }
    for lane in 1..lanes {
        windows.push((8 * lane + 3, 8 * lane - 4));
    }
    windows.push((8 * lanes - 1, 0));
    let mut literals = Vec::new();
    for &(high, low) in &windows {
        let slice = extract(&mut terms, word, high, low);
        let name = terms.mk_var(format!("w{high}_{low}"), Sort::bitvec(high - low + 1));
        literals.push(predicate(&mut terms, "=", &[slice, name]));
    }
    let root = predicate(&mut terms, "and", &literals);

    let mut lowerer = ProofProducingLowerer::new(&terms, deadline());
    lowerer.lower_bool(root).unwrap();
    lowerer.audit_census();

    // Taking the operands out of the lowered `concat` builds the very
    // expression lowering them again built.
    for &(high, low) in &windows {
        let slice = extract(&mut terms, word, high, low);
        let mut projected = ProofProducingLowerer::new(&terms, deadline());
        let mut relowered = ProofProducingLowerer::new(&terms, deadline());
        assert_eq!(
            projected.lower_bv(slice).unwrap(),
            relowering_projection(&mut relowered, word, high, low),
            "extract {high}:{low}"
        );
    }
}

#[test]
fn reads_of_one_sparse_store_chain_lower_each_store_once() {
    let mut terms = TermStore::new();
    let width = 64;
    let sort = Sort::array(Sort::bitvec(width), Sort::bitvec(8));
    let fill = product(&mut terms, "fill");
    let mut memory = terms.mk_app(Symbol::named("const-array"), [fill], sort.clone());
    for store in 0..4 {
        let at = terms.mk_var(format!("at{store}"), Sort::bitvec(width));
        let value = product(&mut terms, &format!("value{store}"));
        memory = terms.mk_app(Symbol::named("store"), [memory, at, value], sort.clone());
    }
    let mut literals = Vec::new();
    for read in 0..3 {
        let key = terms.mk_var(format!("key{read}"), Sort::bitvec(width));
        let loaded = terms.mk_app(Symbol::named("select"), [memory, key], Sort::bitvec(8));
        let name = terms.mk_var(format!("loaded{read}"), Sort::bitvec(8));
        literals.push(predicate(&mut terms, "=", &[loaded, name]));
    }
    let root = predicate(&mut terms, "and", &literals);

    let mut lowerer = ProofProducingLowerer::new(&terms, deadline());
    lowerer.lower_bool(root).unwrap();
    lowerer.audit_census();
}

#[test]
fn the_roots_of_one_batch_are_counted_before_any_is_lowered() {
    let mut terms = TermStore::new();
    let shared = product(&mut terms, "p");
    let d = terms.mk_var("d", Sort::bitvec(8));
    let e = terms.mk_var("e", Sort::bitvec(8));
    let first = predicate(&mut terms, "=", &[shared, d]);
    let second = predicate(&mut terms, "bvult", &[shared, e]);

    let mut lowerer = ProofProducingLowerer::new(&terms, deadline());
    lowerer.lower_bool_terms(&[first, second]).unwrap();
    lowerer.audit_census();
    // Exactly the terms requested more than once are copied: the product
    // both roots share, and the variable it reads twice.
    let mut copied: Vec<usize> = lowerer.memo.keys().map(|term| term.index()).collect();
    let mut repeated: Vec<usize> = lowerer
        .requests
        .iter()
        .filter(|&(_, &made)| made > 1)
        .map(|(term, _)| term.index())
        .collect();
    copied.sort_unstable();
    repeated.sort_unstable();
    assert_eq!(copied, repeated);
    assert!(lowerer.memo.contains_key(&shared));
    assert_eq!(copied.len(), 2);
}

#[test]
fn an_operator_refused_before_its_operand_requests_nothing() {
    let mut terms = TermStore::new();
    let shared = product(&mut terms, "p");
    let rotated = terms.mk_app(
        Symbol::indexed("rotate_left", vec![1]),
        [shared],
        Sort::bitvec(8),
    );
    let repeated = terms.mk_app(
        Symbol::indexed("repeat", vec![1]),
        [shared],
        Sort::bitvec(8),
    );
    let d = terms.mk_var("d", Sort::bitvec(8));
    let first = predicate(&mut terms, "=", &[rotated, d]);
    let second = predicate(&mut terms, "=", &[repeated, d]);

    // The exact lowering refuses both operators before lowering their
    // operand, so it never requests it.
    let mut exact = ProofProducingLowerer::new(&terms, deadline());
    let error = exact.lower_bool_terms(&[first, second]).unwrap_err();
    assert!(error.contains("rotate_left"), "{error}");
    assert!(!exact.requests.contains_key(&shared));
    assert!(!exact.used_uninterpreted_leaves);

    // Validating a lemma, both become free leaves only after their operand
    // lowers: the census counted it once per operator, and it is lowered once.
    let mut lowerer = ProofProducingLowerer::new_for_lemma_validation(&terms, deadline());
    lowerer.lower_bool_terms(&[first, second]).unwrap();
    assert!(lowerer.used_uninterpreted_leaves);
    assert_eq!(lowerer.requests.get(&shared), Some(&2));
    assert!(lowerer.memo.contains_key(&shared));
    lowerer.audit_census();
}

/// `(zero_extend[7] bit)`: a 1-bit term as an 8-bit dividend.
fn widen(terms: &mut TermStore, bit: TermId) -> TermId {
    terms.mk_app(
        Symbol::indexed("zero_extend", vec![7]),
        [bit],
        Sort::bitvec(8),
    )
}

/// `n` levels of `G_k = (bvcomp (bvudiv Z c) (bvurem Z c))` with
/// `Z = (zero_extend[7] G_{k-1})`, over `G_0 = (bvcomp a b)`, which fails to
/// lower (reserved, unsupported, never abstracted). Validating a lemma, a
/// division becomes a free leaf only once both its operands lower, so the
/// failure of `G_0` refuses every level above it. Returns the top division
/// `(bvudiv Z_n c)` and `G_0`.
fn divisions_over_a_failing_operand(terms: &mut TermStore, levels: usize) -> (TermId, TermId) {
    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let c = terms.mk_var("c", Sort::bitvec(8));
    let base = bv(terms, "bvcomp", &[a, b], 1);
    let mut failing = base;
    for _ in 0..levels {
        let widened = widen(terms, failing);
        let quotient = bv(terms, "bvudiv", &[widened, c], 8);
        let remainder = bv(terms, "bvurem", &[widened, c], 8);
        failing = bv(terms, "bvcomp", &[quotient, remainder], 1);
    }
    let widened = widen(terms, failing);
    (bv(terms, "bvudiv", &[widened, c], 8), base)
}

#[test]
fn a_failure_below_a_division_refuses_the_lemma_once() {
    for levels in [0, 1, 6] {
        let mut terms = TermStore::new();
        let (top, base) = divisions_over_a_failing_operand(&mut terms, levels);
        let literal = predicate(&mut terms, "bvule", &[top, top]);
        let mut lowerer = ProofProducingLowerer::new_for_lemma_validation(&terms, deadline());
        let error = lowerer.lower_bool_terms(&[literal]).unwrap_err();
        assert!(
            error.contains("unsupported BitVec operator `bvcomp`"),
            "levels {levels}: {error}"
        );
        // No division absorbed the failure below it into a free leaf, and no
        // term was lowered twice on the way up.
        assert!(!lowerer.used_uninterpreted_leaves, "levels {levels}");
        assert_eq!(lowerer.relowerings, 0, "levels {levels}");
        assert!(!lowerer.memo.contains_key(&top), "levels {levels}");
        assert!(lowerer.failed.contains_key(&base), "levels {levels}");
        assert!(lowerer.failed.contains_key(&top), "levels {levels}");
    }
}

#[test]
fn an_abstracted_division_requests_both_operands_as_counted() {
    // Validating a lemma, a division by a non-constant lowers its dividend
    // and its divisor, then becomes a free leaf: the census counted both
    // operands of each division, and the audit is exact.
    let mut terms = TermStore::new();
    let dividend = product(&mut terms, "p");
    let c = terms.mk_var("c", Sort::bitvec(8));
    let quotient = bv(&mut terms, "bvudiv", &[dividend, c], 8);
    let remainder = bv(&mut terms, "bvsrem", &[dividend, c], 8);
    let literal = predicate(&mut terms, "=", &[quotient, remainder]);
    let mut lowerer = ProofProducingLowerer::new_for_lemma_validation(&terms, deadline());
    lowerer.lower_bool_terms(&[literal]).unwrap();
    assert!(lowerer.used_uninterpreted_leaves);
    assert_eq!(lowerer.parents.get(&dividend), Some(&2));
    assert_eq!(lowerer.requests.get(&dividend), Some(&2));
    assert_eq!(lowerer.requests.get(&c), Some(&2));
    assert!(lowerer.memo.contains_key(&dividend));
    lowerer.audit_census();
}

#[test]
fn a_lemma_over_a_deep_nest_of_failures_is_refused_without_rework() {
    // `(bvule (bvand T x) (bvor T x))` holds for every `T`, but here `T` is
    // the top of 24 levels resting on `(bvcomp a b)`, which the lowering can
    // neither express nor abstract: the lowering refuses the lemma, and it
    // lowers each term at most once on the way (before failures were
    // remembered, each level lowered the failing operand twice).
    let mut terms = TermStore::new();
    let (top, _) = divisions_over_a_failing_operand(&mut terms, 24);
    let x = terms.mk_var("x", Sort::bitvec(8));
    let meet = bv(&mut terms, "bvand", &[top, x], 8);
    let join = bv(&mut terms, "bvor", &[top, x], 8);
    let literal = predicate(&mut terms, "bvule", &[meet, join]);

    let mut lowerer = ProofProducingLowerer::new_for_lemma_validation(&terms, deadline());
    let error = lowerer.lower_bool_terms(&[literal]).unwrap_err();
    assert!(error.contains("`bvcomp`"), "{error}");
    assert!(!lowerer.used_uninterpreted_leaves);
    assert_eq!(lowerer.relowerings, 0);
    assert!(
        lowerer.constructed_expr_nodes < 1_000,
        "constructed {} nodes",
        lowerer.constructed_expr_nodes
    );
}

#[test]
fn a_lemma_over_a_deep_nest_of_abstracted_divisions_is_validated() {
    // The same lemma over 24 levels of divisions whose operands all lower:
    // every division becomes a free leaf after its operands, each term is
    // lowered once, and the valid lemma is accepted.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(8));
    let c = terms.mk_var("c", Sort::bitvec(8));
    let mut top = a;
    for _ in 0..24 {
        let quotient = bv(&mut terms, "bvudiv", &[top, c], 8);
        let remainder = bv(&mut terms, "bvsrem", &[top, c], 8);
        top = bv(&mut terms, "bvadd", &[quotient, remainder], 8);
    }
    let x = terms.mk_var("x", Sort::bitvec(8));
    let meet = bv(&mut terms, "bvand", &[top, x], 8);
    let join = bv(&mut terms, "bvor", &[top, x], 8);
    let literal = predicate(&mut terms, "bvule", &[meet, join]);

    let mut lowerer = ProofProducingLowerer::new_for_lemma_validation(&terms, deadline());
    lowerer.lower_bool_terms(&[literal]).unwrap();
    lowerer.audit_census();
    assert!(lowerer.used_uninterpreted_leaves);
    assert!(
        lowerer.constructed_expr_nodes < 1_000,
        "constructed {} nodes",
        lowerer.constructed_expr_nodes
    );
    validate_bv_bitblast(&terms, ProofId(1), &[literal], None).unwrap();
}

#[test]
fn a_failure_that_may_depend_on_more_than_the_term_is_not_remembered() {
    let mut terms = TermStore::new();
    let (top, base) = divisions_over_a_failing_operand(&mut terms, 0);
    let literal = predicate(&mut terms, "bvule", &[top, top]);
    let stops: [fn(&mut ProofProducingLowerer<'_, '_>); 2] = [
        |lowerer| lowerer.resource_exhausted = true,
        |lowerer| lowerer.cycle_refused = true,
    ];
    for stop in stops {
        let mut lowerer = ProofProducingLowerer::new_for_lemma_validation(&terms, deadline());
        stop(&mut lowerer);
        lowerer.lower_bool_terms(&[literal]).unwrap_err();
        assert!(!lowerer.failed.contains_key(&base));
    }
    // Facts installed after a failure may let the term lower: the failure
    // is forgotten, while the memo, built without facts, stays.
    let mut lowerer = ProofProducingLowerer::new_for_lemma_validation(&terms, deadline());
    lowerer.lower_bool_terms(&[literal]).unwrap_err();
    assert!(lowerer.failed.contains_key(&base));
    lowerer.install_disjoint_facts(None);
    assert!(lowerer.failed.is_empty());
}
