// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn bv_array(index_w: u32, elem_w: u32) -> Sort {
    Sort::array(Sort::bitvec(index_w), Sort::bitvec(elem_w))
}

#[test]
fn collapses_equal_index_values_into_one_cell() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", bv_array(32, 8));
    // Two spellings of index 4 at the same width must map to ONE cell; a
    // second numeric index must get its own.
    let i1 = terms.mk_bitvec(BigInt::from(4), 32);
    let i2 = terms.mk_bitvec(BigInt::from(4u64), 32);
    let j = terms.mk_bitvec(BigInt::from(5), 32);
    let s1 = terms.mk_select(a, i1);
    let s2 = terms.mk_select(a, i2);
    let s3 = terms.mk_select(a, j);
    let eq = terms.mk_eq(s1, s2);
    let eq2 = terms.mk_eq(s1, s3);
    let ne = terms.mk_not(eq2);
    let plan = plan(&mut terms, &[eq, ne]).expect("plan should fire");
    assert_eq!(plan.cells.len(), 2, "cells: {:?}", plan.cells);
    assert!(is_array_free(&terms, &plan.assertions));
}

#[test]
fn distinct_arrays_never_share_a_cell_constant() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", bv_array(32, 8));
    let b = terms.mk_var("b", bv_array(32, 8));
    let i = terms.mk_bitvec(BigInt::from(0), 32);
    let sa = terms.mk_select(a, i);
    let sb = terms.mk_select(b, i);
    let eq = terms.mk_eq(sa, sb);
    let plan = plan(&mut terms, &[eq]).expect("plan should fire");
    assert_eq!(plan.cells.len(), 2);
    assert_ne!(plan.cells[0].fresh, plan.cells[1].fresh);
}

#[test]
fn abstains_on_store() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", bv_array(32, 8));
    let i = terms.mk_bitvec(BigInt::from(0), 32);
    let v = terms.mk_bitvec(BigInt::from(7), 8);
    let st = terms.mk_store(a, i, v);
    let rd = terms.mk_select(st, i);
    let lit = terms.mk_bitvec(BigInt::from(9), 8);
    let eq = terms.mk_eq(rd, lit);
    assert!(matches!(
        plan(&mut terms, &[eq]),
        Err(FlattenAbstain::Store | FlattenAbstain::NoArrays)
    ));
}

#[test]
fn fires_on_symbolic_index() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", bv_array(32, 8));
    let i = terms.mk_var("i", Sort::bitvec(32));
    let rd = terms.mk_select(a, i);
    let lit = terms.mk_bitvec(BigInt::from(7), 8);
    let eq = terms.mk_eq(rd, lit);
    let plan = plan(&mut terms, &[eq]).expect("symbolic index must no longer abstain");
    assert_eq!(plan.cells.len(), 1);
    assert!(plan.cells[0].index_value.is_none(), "cell must be symbolic");
    assert!(is_array_free(&terms, &plan.assertions));
}

/// THE soundness test for symbolic indices. Two reads on the SAME array at two
/// SYMBOLIC indices must be tied by `(=> (= i j) (= r_i r_j))`. Without that
/// axiom the cells are independent and a model can set `i = j` while the values
/// differ — an "array" that is not a function, i.e. a false `sat`.
///
/// Deleting the `congruence_axioms` call makes this fail: the assertion list is
/// then just the rewritten original with no extra conjunct.
#[test]
fn symbolic_cells_on_one_array_get_a_congruence_axiom() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", bv_array(32, 8));
    let i = terms.mk_var("i", Sort::bitvec(32));
    let j = terms.mk_var("j", Sort::bitvec(32));
    let ri = terms.mk_select(a, i);
    let rj = terms.mk_select(a, j);
    let seven = terms.mk_bitvec(BigInt::from(7), 8);
    let nine = terms.mk_bitvec(BigInt::from(9), 8);
    let e1 = terms.mk_eq(ri, seven);
    let e2 = terms.mk_eq(rj, nine);
    let plan = plan(&mut terms, &[e1, e2]).expect("plan should fire");
    assert_eq!(plan.cells.len(), 2, "two symbolic cells");
    assert_eq!(
        plan.assertions.len(),
        3,
        "two rewritten assertions plus exactly one congruence axiom, got {:?}",
        plan.assertions
    );
    // The axiom must mention BOTH cell constants and BOTH index terms.
    let axiom = *plan.assertions.last().expect("axiom present");
    let mut seen = std::collections::HashSet::new();
    let mut stack = vec![axiom];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::App(_, args) => stack.extend_from_slice(args),
            TermData::Not(x) => stack.push(*x),
            _ => {}
        }
    }
    for needed in [i, j, plan.cells[0].fresh, plan.cells[1].fresh] {
        assert!(
            seen.contains(&needed),
            "congruence axiom must mention {needed:?}: {axiom:?}"
        );
    }
}

/// Two LITERAL cells need no axiom: distinct literal keys have distinct values,
/// so `(= i j)` is `false` and the implication is a tautology. Emitting one
/// anyway would be sound but wasteful; this pins the optimisation so a later
/// edit cannot quietly turn it into "emit nothing for any pair".
#[test]
fn literal_cell_pairs_need_no_congruence_axiom() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", bv_array(32, 8));
    let i = terms.mk_bitvec(BigInt::from(4), 32);
    let j = terms.mk_bitvec(BigInt::from(5), 32);
    let ri = terms.mk_select(a, i);
    let rj = terms.mk_select(a, j);
    let eq = terms.mk_eq(ri, rj);
    let plan = plan(&mut terms, &[eq]).expect("plan should fire");
    assert_eq!(plan.cells.len(), 2);
    assert_eq!(
        plan.assertions.len(),
        1,
        "literal/literal pairs are tautologies: {:?}",
        plan.assertions
    );
}

/// A symbolic and a literal index on one array CAN collide (the symbolic one
/// may evaluate to the literal), so that pair DOES need an axiom.
#[test]
fn mixed_literal_and_symbolic_pair_gets_an_axiom() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", bv_array(32, 8));
    let i = terms.mk_bitvec(BigInt::from(4), 32);
    let j = terms.mk_var("j", Sort::bitvec(32));
    let ri = terms.mk_select(a, i);
    let rj = terms.mk_select(a, j);
    let eq = terms.mk_eq(ri, rj);
    let plan = plan(&mut terms, &[eq]).expect("plan should fire");
    assert_eq!(plan.cells.len(), 2);
    assert_eq!(
        plan.assertions.len(),
        2,
        "mixed pair needs one axiom: {:?}",
        plan.assertions
    );
}

/// Cells on DIFFERENT arrays share nothing, so no axiom may relate them —
/// asserting `(=> (= i j) (= r_a r_b))` across arrays would be plain unsound in
/// the other direction (it would force unrelated arrays to agree).
#[test]
fn cells_on_different_arrays_are_never_related() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", bv_array(32, 8));
    let b = terms.mk_var("b", bv_array(32, 8));
    let i = terms.mk_var("i", Sort::bitvec(32));
    let ra = terms.mk_select(a, i);
    let rb = terms.mk_select(b, i);
    let eq = terms.mk_eq(ra, rb);
    let plan = plan(&mut terms, &[eq]).expect("plan should fire");
    assert_eq!(plan.cells.len(), 2);
    assert_eq!(
        plan.assertions.len(),
        1,
        "no cross-array axiom may be emitted: {:?}",
        plan.assertions
    );
}

/// The pair budget must ABSTAIN, never truncate.
///
/// A prefix of the congruence axioms is not a weaker-but-sound encoding: the
/// omitted pairs are exactly the ones left free to disagree, so truncating is a
/// wrong-`sat` generator. 65 symbolic cells give 65*64/2 = 2080 pairs, just over
/// `MAX_CONGRUENCE_PAIRS` (2048).
#[test]
fn pair_budget_overrun_abstains_rather_than_truncating() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", bv_array(32, 8));
    let mut conjuncts = Vec::new();
    for k in 0..65 {
        let i = terms.mk_var(format!("i{k}"), Sort::bitvec(32));
        let rd = terms.mk_select(a, i);
        let lit = terms.mk_bitvec(BigInt::from(k), 8);
        conjuncts.push(terms.mk_eq(rd, lit));
    }
    assert!(
        matches!(
            plan(&mut terms, &conjuncts),
            Err(FlattenAbstain::TooManyReadPairs)
        ),
        "a budget overrun must abstain, not emit a partial closure"
    );

    // 64 cells is 2016 pairs — under the cap, so the pass still fires. This
    // pins the cap as a real boundary rather than a permanent refusal.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", bv_array(32, 8));
    let mut conjuncts = Vec::new();
    for k in 0..64 {
        let i = terms.mk_var(format!("i{k}"), Sort::bitvec(32));
        let rd = terms.mk_select(a, i);
        let lit = terms.mk_bitvec(BigInt::from(k), 8);
        conjuncts.push(terms.mk_eq(rd, lit));
    }
    let built = plan(&mut terms, &conjuncts).expect("64 cells is under the cap");
    assert_eq!(built.cells.len(), 64);
    assert_eq!(
        built.assertions.len(),
        64 + 64 * 63 / 2,
        "every pair must be present, not a prefix"
    );
}

/// A symbolic index is an arbitrary term and may itself hide array structure.
/// It MUST be walked by the scan. Skipping it (dropping `stack.push(index)` in
/// `plan_cells`) lets an array-sorted term in index position bypass every side
/// condition and reach the rewrite unexamined — caught here by asserting the
/// SPECIFIC abstention, since the unscanned variant instead limps out through
/// the `ResidualArray` backstop.
#[test]
fn symbolic_index_subterm_is_scanned_for_arrays() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", bv_array(32, 8));
    let b1 = terms.mk_var("b1", bv_array(32, 32));
    let b2 = terms.mk_var("b2", bv_array(32, 32));
    let c = terms.mk_var("c", Sort::Bool);
    let k = terms.mk_bitvec(BigInt::from(1), 32);
    // index = (select (ite c b1 b2) k): an array-sorted `ite` — not a declared
    // symbol — buried inside the index. `mk_select` cannot fold this away.
    let chosen = terms.mk_ite(c, b1, b2);
    let idx = terms.mk_select(chosen, k);
    let rd = terms.mk_select(a, idx);
    let lit = terms.mk_bitvec(BigInt::from(7), 8);
    let eq = terms.mk_eq(rd, lit);
    assert!(
        matches!(
            plan(&mut terms, &[eq]),
            Err(FlattenAbstain::ArrayTermNotSymbol)
        ),
        "an array-sorted `ite` hidden in a symbolic index must be caught by the SCAN"
    );
}

/// Element sorts other than bitvector are eliminable too — the cell constant
/// simply takes the element sort.
#[test]
fn fp_element_sort_is_eliminable() {
    let mut terms = TermStore::new();
    let fp_arr = Sort::array(Sort::bitvec(32), Sort::FloatingPoint(8, 24));
    let a = terms.mk_var("a", fp_arr);
    let i = terms.mk_bitvec(BigInt::from(3), 32);
    let rd = terms.mk_select(a, i);
    // NB: compare against a DIFFERENT term. `(= rd rd)` folds to `true` and the
    // array disappears before the scan ever sees it.
    let other = terms.mk_var("other", Sort::FloatingPoint(8, 24));
    let eq = terms.mk_eq(rd, other);
    let built = plan(&mut terms, &[eq]).expect("FP element sort must be eliminable");
    assert_eq!(built.cells.len(), 1);
    assert!(is_array_free(&terms, &built.assertions));
}

/// A NESTED array element is not eliminable in one round: the outer `select`
/// would still be array-sorted, and substituting a fresh array-sorted constant
/// leaves array structure behind for the bit-blaster that cannot see it.
///
/// The abstention arrives as `ArrayTermNotSymbol` (the INNER read's base is the
/// outer `select`, not a declared symbol) rather than `ArraySortUnsupported` —
/// either way it fails closed, which is what this pins.
#[test]
fn nested_array_element_sort_still_abstains() {
    let mut terms = TermStore::new();
    let nested = Sort::array(
        Sort::bitvec(32),
        Sort::array(Sort::bitvec(32), Sort::bitvec(8)),
    );
    let m = terms.mk_var("m", nested);
    let i = terms.mk_bitvec(BigInt::from(1), 32);
    let inner = terms.mk_select(m, i);
    let j = terms.mk_bitvec(BigInt::from(2), 32);
    let rd = terms.mk_select(inner, j);
    let lit = terms.mk_bitvec(BigInt::from(7), 8);
    let eq = terms.mk_eq(rd, lit);
    assert!(matches!(
        plan(&mut terms, &[eq]),
        Err(FlattenAbstain::ArrayTermNotSymbol | FlattenAbstain::ArraySortUnsupported)
    ));
}

#[test]
fn abstains_on_array_equality() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", bv_array(32, 8));
    let b = terms.mk_var("b", bv_array(32, 8));
    let eq = terms.mk_eq(a, b);
    assert!(matches!(
        plan(&mut terms, &[eq]),
        Err(FlattenAbstain::ArrayNotOnlySelected)
    ));
}

#[test]
fn abstains_on_non_bv_array_sort() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::array(Sort::Int, Sort::bitvec(8)));
    let i = terms.mk_int(BigInt::from(0));
    let rd = terms.mk_select(a, i);
    let lit = terms.mk_bitvec(BigInt::from(7), 8);
    let eq = terms.mk_eq(rd, lit);
    assert!(matches!(
        plan(&mut terms, &[eq]),
        Err(FlattenAbstain::ArraySortUnsupported)
    ));
}

#[test]
fn abstains_when_no_array_present() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(8));
    let lit = terms.mk_bitvec(BigInt::from(7), 8);
    let eq = terms.mk_eq(x, lit);
    assert!(matches!(
        plan(&mut terms, &[eq]),
        Err(FlattenAbstain::NoArrays)
    ));
}
