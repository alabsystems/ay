// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn row_chain_rejects_wrong_root_read_endpoint() {
    let mut f = Fixture::new(2);
    let b = f.a;
    let other = f.terms.mk_var("other", array_sort());
    let (x, y, v) = (f.idx[0], f.idx[1], f.val[0]);
    let left = store(&mut f.terms, b, x, v);
    let right = store(&mut f.terms, b, y, v);
    let premise_eq = eq(&mut f.terms, left, right);
    let premise = f.terms.mk_not(premise_eq);
    let wrong_read = select(&mut f.terms, other, x);
    let conclusion = eq(&mut f.terms, v, wrong_read);
    let clause = vec![premise, conclusion];

    validate_strict(&f.terms, clause.clone(), TheoryLemmaKind::ArrayRowChain)
        .expect_err("the raw endpoint must be the exact premise-array root read");
    assert!(array_row_chain_printer_terms(&f.terms, &clause).is_none());
}

#[test]
fn row_chain_rejects_root_read_at_the_wrong_index_or_value() {
    let mut f = Fixture::new(3);
    let b = f.a;
    let (x, y, wrong_index, v, wrong_value) = (f.idx[0], f.idx[1], f.idx[2], f.val[0], f.val[1]);
    let left = store(&mut f.terms, b, x, v);
    let right = store(&mut f.terms, b, y, v);
    let premise_eq = eq(&mut f.terms, left, right);
    let premise = f.terms.mk_not(premise_eq);

    let wrong_read = select(&mut f.terms, right, wrong_index);
    let wrong_index_conclusion = eq(&mut f.terms, v, wrong_read);
    validate_strict(
        &f.terms,
        vec![premise, wrong_index_conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect_err("the folded and raw sides must use the same exact index");

    let right_read = select(&mut f.terms, right, x);
    let wrong_value_conclusion = eq(&mut f.terms, wrong_value, right_read);
    validate_strict(
        &f.terms,
        vec![premise, wrong_value_conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect_err("the folded side must end at the exact stored value");
}

#[test]
fn row_chain_rejects_read_out_with_an_unjustified_skip() {
    // NEGATIVE: same clause, minus the `(= i0 i2)` literal. With i0 = i2 the
    // left chain reads v2 at i0, so the conclusion does not follow.
    let mut f = Fixture::new(3);
    let a = f.a;
    let b = f.terms.mk_var("b", array_sort());
    let left = f.chain(a, &[0, 2]);
    let premise_eq = eq(&mut f.terms, left, b);
    let premise = f.terms.mk_not(premise_eq);
    let i0 = f.idx[0];
    let v0 = f.val[0];
    let base_read = select(&mut f.terms, b, i0);
    let conclusion = eq(&mut f.terms, v0, base_read);

    let err = validate_strict(
        &f.terms,
        vec![premise, conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect_err("an unjustified skip under an array equality must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn row_chain_rejects_read_out_without_the_array_equality_premise() {
    // NEGATIVE: drop the `(not (= L R))` premise. `v0 = (select b i0)` alone is
    // plainly falsifiable.
    let mut f = Fixture::new(3);
    let a = f.a;
    let b = f.terms.mk_var("b", array_sort());
    let _left = f.chain(a, &[0, 2]);
    let i0 = f.idx[0];
    let i2 = f.idx[2];
    let v0 = f.val[0];
    let base_read = select(&mut f.terms, b, i0);
    let conclusion = eq(&mut f.terms, v0, base_read);
    let skip = eq(&mut f.terms, i0, i2);

    let err = validate_strict(
        &f.terms,
        vec![skip, conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect_err("a read-out with no array-equality premise must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn row_chain_rejects_read_out_at_mismatched_indices() {
    // NEGATIVE: the premise arrays are read at DIFFERENT indices — the left
    // side is evaluated at i0 but the conclusion's select is at i1.
    let mut f = Fixture::new(3);
    let a = f.a;
    let b = f.terms.mk_var("b", array_sort());
    let left = f.chain(a, &[0]);
    let premise_eq = eq(&mut f.terms, left, b);
    let premise = f.terms.mk_not(premise_eq);
    let i1 = f.idx[1];
    let v0 = f.val[0];
    let other_read = select(&mut f.terms, b, i1);
    let conclusion = eq(&mut f.terms, v0, other_read);

    let err = validate_strict(
        &f.terms,
        vec![premise, conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect_err("a read-out whose two sides use different indices must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn row_chain_rejects_array_equality_used_positively() {
    // NEGATIVE: the array equality is a POSITIVE literal, so the clause reads
    // "L = R OR v0 = select(b,i0)" — satisfiable, not a tautology.
    let mut f = Fixture::new(3);
    let a = f.a;
    let b = f.terms.mk_var("b", array_sort());
    let left = f.chain(a, &[0]);
    let premise = eq(&mut f.terms, left, b);
    let i0 = f.idx[0];
    let v0 = f.val[0];
    let base_read = select(&mut f.terms, b, i0);
    let conclusion = eq(&mut f.terms, v0, base_read);

    let err = validate_strict(
        &f.terms,
        vec![premise, conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect_err("a positive array equality is not a usable premise");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn row_chain_recognizer_declines_unjustified_skip() {
    // Classifier/checker agreement on the fail-closed side.
    let mut f = Fixture::new(3);
    let a = f.a;
    let chain = f.chain(a, &[0, 1, 2]);
    let i0 = f.idx[0];
    let v0 = f.val[0];
    let read = select(&mut f.terms, chain, i0);
    let conclusion = eq(&mut f.terms, read, v0);
    let i2 = f.idx[2];
    let skip2 = eq(&mut f.terms, i0, i2);

    assert_eq!(
        recognize_array_theory_lemma(&f.terms, &[skip2, conclusion]),
        None
    );
}

#[test]
fn row_chain_recognizer_agrees_with_validator() {
    let mut f = Fixture::new(3);
    let a = f.a;
    let chain = f.chain(a, &[0, 1, 2]);
    let i0 = f.idx[0];
    let v0 = f.val[0];
    let read = select(&mut f.terms, chain, i0);
    let conclusion = eq(&mut f.terms, read, v0);
    let (i1, i2) = (f.idx[1], f.idx[2]);
    let skip1 = eq(&mut f.terms, i0, i1);
    let skip2 = eq(&mut f.terms, i0, i2);
    let clause = vec![skip2, skip1, conclusion];

    assert_eq!(
        recognize_array_theory_lemma(&f.terms, &clause),
        Some(TheoryLemmaKind::ArrayRowChain)
    );
    validate_strict(&f.terms, clause, TheoryLemmaKind::ArrayRowChain)
        .expect("recognized clause must validate");
}

// ============================================================================
// Cross-schema fail-closed guards
// ============================================================================

#[test]
fn new_array_kinds_reject_an_arbitrary_boolean_clause() {
    // The classic forgery: a bare Boolean literal labelled as an array axiom.
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    for kind in [
        TheoryLemmaKind::ArrayStorePermutation,
        TheoryLemmaKind::ArrayRowChain,
    ] {
        let err = validate_strict(&terms, vec![p], kind)
            .expect_err("a bare Boolean clause is not an array axiom");
        assert!(
            matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
            "expected InvalidTheoryLemma for {kind:?}, got {err:?}"
        );
    }
}

#[test]
fn new_array_kinds_reject_empty_clause() {
    let terms = TermStore::new();
    for kind in [
        TheoryLemmaKind::ArrayStorePermutation,
        TheoryLemmaKind::ArrayRowChain,
    ] {
        validate_strict(&terms, vec![], kind)
            .expect_err("an empty array-axiom clause must be rejected");
    }
}

// ============================================================================
// ArrayRowChain — metered strict-check work
// (fix/array-row-chain-metered-charge)
//
// `validate_array_row_chain` now debits a tight upper bound on its own work
// through the strict-check progress callback INSTEAD of the former up-front
// `~8*unfolded_work^2` `ArrayClauseSchema` precharge. These tests exercise that
// meter directly: a long genuine row chain is linear and certifies, a tight
// envelope still refuses, and an adversarial clause that would drive the
// quadratic sub-schema (B) cross product still fails closed.
// ============================================================================

/// A genuinely-linear valid row chain: a length-`n` store chain read at the
/// innermost index `i0`, with every one of the `n-1` outer skips justified by
/// its own `(= i0 i_k)` literal (accepted by sub-schema (A)).
fn long_row_chain_clause(n: usize) -> (TermStore, Vec<TermId>) {
    let mut f = Fixture::new(n);
    let a = f.a;
    let order: Vec<usize> = (0..n).collect();
    let chain = f.chain(a, &order);
    let i0 = f.idx[0];
    let v0 = f.val[0];
    let read = select(&mut f.terms, chain, i0);
    let conclusion = eq(&mut f.terms, read, v0);
    let mut clause = Vec::new();
    for k in 1..n {
        let (i0c, ik) = (f.idx[0], f.idx[k]);
        clause.push(eq(&mut f.terms, i0c, ik));
    }
    clause.push(conclusion);
    (f.terms, clause)
}

/// A long genuine row chain certifies while debiting only O(n) work — where the
/// former quadratic precharge exhausted the envelope and withheld the verdict.
#[test]
fn row_chain_metered_charge_is_linear_and_certifies_long_chains() {
    let (terms, clause) = long_row_chain_clause(1000);
    let mut debited = 0usize;
    let mut progress = |w: usize, _b: usize| {
        debited += w;
        true
    };
    array_axiom::validate_array_row_chain(&terms, ProofId(0), &clause, &mut progress)
        .expect("a long genuine row chain must certify under the metered charge");
    assert!(
        debited < 1_000_000,
        "metered row-chain work must be linear in chain length, not quadratic: {debited}"
    );
}

/// The meter is a REAL bound, not a no-op: a tight envelope refuses even a valid
/// row chain with `ResourceLimit`.
#[test]
fn row_chain_metering_fails_closed_under_a_tight_envelope() {
    let (terms, clause) = long_row_chain_clause(200);
    let budget = 100usize;
    let mut spent = 0usize;
    let mut progress = |w: usize, _b: usize| {
        spent += w;
        spent <= budget
    };
    let err = array_axiom::validate_array_row_chain(&terms, ProofId(0), &clause, &mut progress)
        .expect_err("a tight envelope must refuse the row-chain check");
    assert_eq!(err, ProofCheckError::ResourceLimit);
}

/// SOUNDNESS / MUTATION: a genuinely-expensive `ArrayRowChain`-labelled clause —
/// many array-disequality premises, many select-bearing positive equalities, and
/// long chains — would drive `matches_row_chain_under_array_eq`'s
/// `O(pos_eq_with_select * premises * n_max)` cross product. The metered charge
/// prices that cross product and fails closed under the production 350M work
/// envelope BEFORE the search runs. This is the fail-closed direction the former
/// up-front precharge guaranteed; it must survive the metered rewrite.
#[test]
fn row_chain_metering_fails_closed_on_adversarial_cross_product() {
    const PREMISES: usize = 64;
    const SELECT_EQS: usize = 64;
    const NMAX: usize = 2000;
    // 64 * SELECT_EQS * PREMISES * NMAX = 64 * 64 * 64 * 2000 well exceeds 350M.
    let production_work_envelope = 350_000_000usize;

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", array_sort());
    // One long store chain drives n_max; every premise references it.
    let mut chain = a;
    for k in 0..NMAX {
        let i = terms.mk_var(format!("ci{k}"), Sort::Int);
        let v = terms.mk_var(format!("cv{k}"), Sort::Int);
        chain = store(&mut terms, chain, i, v);
    }
    let mut clause = Vec::new();
    for j in 0..PREMISES {
        let other = terms.mk_var(format!("b{j}"), array_sort());
        let premise_eq = eq(&mut terms, chain, other);
        clause.push(terms.mk_not(premise_eq));
    }
    let x = terms.mk_var("x", Sort::Int);
    for j in 0..SELECT_EQS {
        let arr1 = terms.mk_var(format!("s1_{j}"), array_sort());
        let arr2 = terms.mk_var(format!("s2_{j}"), array_sort());
        let s1 = select(&mut terms, arr1, x);
        let s2 = select(&mut terms, arr2, x);
        clause.push(eq(&mut terms, s1, s2));
    }

    let mut spent = 0usize;
    let mut progress = |w: usize, _b: usize| {
        spent += w;
        spent <= production_work_envelope
    };
    let err = array_axiom::validate_array_row_chain(&terms, ProofId(0), &clause, &mut progress)
        .expect_err("an adversarial row-chain cross product must still fail closed");
    assert_eq!(err, ProofCheckError::ResourceLimit);
}

/// SOUNDNESS / MUTATION — metering-PREPASS spine-walk under-charge regression.
///
/// An `ArrayRowChain` lemma with MANY negated-equality literals `¬(C = aᵢ)` over
/// ONE long shared store chain `C` makes the metering prepass walk `C`'s spine
/// once PER literal — Θ(L·N) real work — even though `matches_row_chain` proper
/// does only O(L) here (no positive equality drives a chain parse). The earlier
/// formula priced only the MAXIMUM spine length (`64·L + 64·N`) and admitted that
/// Θ(L·N) walk for free: an unbounded-work DoS hole in a fail-closed resource
/// bound. Per-node metering now debits the walk as it happens and fails closed.
#[test]
fn row_chain_prepass_fails_closed_on_shared_chain_negated_equality_fanout() {
    const L: usize = 128; // negated-equality literals over the shared chain
    const N: usize = 4000; // shared chain length
    let budget = 10_000_000usize;
    // The PRE-FIX formula would have ADMITTED this: `64·L + 64·N` is far below the
    // envelope — the exact under-charge Codex constructed.
    assert!(
        64 * L + 64 * N < budget,
        "test must exhibit the under-charge shape"
    );
    // But the prepass performs Θ(L·N) spine walks, which vastly exceeds it.
    assert!(64usize.saturating_mul(L).saturating_mul(N) > budget);

    let mut terms = TermStore::new();
    let base = terms.mk_var("base", array_sort());
    let mut chain = base;
    for k in 0..N {
        let i = terms.mk_var(format!("ci{k}"), Sort::Int);
        let v = terms.mk_var(format!("cv{k}"), Sort::Int);
        chain = store(&mut terms, chain, i, v);
    }
    let mut clause = Vec::with_capacity(L);
    for j in 0..L {
        let other = terms.mk_var(format!("a{j}"), array_sort());
        let eq_term = eq(&mut terms, chain, other);
        clause.push(terms.mk_not(eq_term));
    }

    let mut spent = 0usize;
    let mut progress = |w: usize, _b: usize| {
        spent += w;
        spent <= budget
    };
    let err = array_axiom::validate_array_row_chain(&terms, ProofId(0), &clause, &mut progress)
        .expect_err("shared-chain negated-equality fan-out must fail closed on the prepass walk");
    assert_eq!(err, ProofCheckError::ResourceLimit);
}

// ============================================================================
// Store-permutation metering (fix: ArrayStorePermutation metered like RowChain).
// `validate_array_store_permutation` now debits a tight `O(L + P^2)` bound on
// its own work through the strict-check progress callback INSTEAD of the former
// up-front `~8*unfolded_work^2` (quartic-in-chain-length) `ArrayClauseSchema`
// precharge that withheld correctly-decided `storecomm` UNSATs. The verdict
// logic is unchanged; these tests exercise the added fail-closed meter directly.
// ============================================================================

/// The meter is a REAL bound: a store-chain equality candidate refuses under a
/// budget below its per-node / per-pair debit.
#[test]
fn store_permutation_metering_fails_closed_under_a_tight_envelope() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", array_sort());
    let i = terms.mk_var("i", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let chain = store(&mut terms, a, i, v);
    let other = terms.mk_var("b", array_sort());
    let lit = eq(&mut terms, chain, other);
    let clause = vec![lit];

    let budget = 10usize;
    let mut spent = 0usize;
    let mut progress = |w: usize, _b: usize| {
        spent += w;
        spent <= budget
    };
    let err =
        array_axiom::validate_array_store_permutation(&terms, ProofId(0), &clause, &mut progress)
            .expect_err("a tight envelope must refuse the store-permutation check");
    assert_eq!(err, ProofCheckError::ResourceLimit);
}

/// SOUNDNESS / MUTATION: many array-equality candidates over one long store chain
/// drive the `O(K * P^2)` all-unordered-index-pairs work. The metered charge
/// prices that and fails closed under the production 350M envelope BEFORE the
/// `O(P^2)` checks run — the fail-closed direction the former up-front precharge
/// guaranteed, which must survive the metered rewrite.
#[test]
fn store_permutation_metering_fails_closed_on_adversarial_wide_clause() {
    const N: usize = 2000; // chain length P
    const K: usize = 128; // array-equality candidates
                          // K * N^2 = 128 * 4,000,000 = 512M >> 350M.
    let production_work_envelope = 350_000_000usize;

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", array_sort());
    let mut chain = a;
    for k in 0..N {
        let i = terms.mk_var(format!("ci{k}"), Sort::Int);
        let v = terms.mk_var(format!("cv{k}"), Sort::Int);
        chain = store(&mut terms, chain, i, v);
    }
    let mut clause = Vec::new();
    for j in 0..K {
        let other = terms.mk_var(format!("b{j}"), array_sort());
        clause.push(eq(&mut terms, chain, other));
    }

    let mut spent = 0usize;
    let mut progress = |w: usize, _b: usize| {
        spent += w;
        spent <= production_work_envelope
    };
    let err =
        array_axiom::validate_array_store_permutation(&terms, ProofId(0), &clause, &mut progress)
            .expect_err("an adversarial wide store-permutation clause must fail closed");
    assert_eq!(err, ProofCheckError::ResourceLimit);
}
