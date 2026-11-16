// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The cut-chain funnel arm: an integer clause whose negation is rationally
//! satisfiable and refuted only by a CHAIN of Chvátal–Gomory roundings, which
//! every earlier integer arm declines. Before this arm it stopped at
//! `LiaGeneric` and both recorders normalized it back to `Generic`/trust.

use super::*;
use crate::proof_tracker::ProofTracker;
use num_bigint::BigInt;

/// The thirteen rows the cascade lemma's refutation uses
/// (`QF_LIA_ring_2exp16_5vars_cascade_unsat` t161), in the solver's
/// spelling: `s3 + 3m5 = 65536c4 + tail`, the carry chain, `40000 ≤ 3m_i`,
/// `c_i ≤ 1`. `tail = 1` forces `Σ 3m_i = 65536·Σ c_i + 1` with
/// `Σ c_i = 4`, and 262145 is no multiple of three; rationally satisfiable.
/// `tail = 2` is satisfied by `m = (17476, 17476, 17476, 17477, 17477)`,
/// `c_i = 1`, `s = (39320, 52392, 65464)`.
fn cascade_rows(terms: &mut TermStore, tail: i64) -> Vec<TermId> {
    let int = |terms: &mut TermStore, value: i64| terms.mk_int(BigInt::from(value));
    let s: Vec<TermId> = ["s1", "s2", "s3"]
        .iter()
        .map(|n| terms.mk_var(*n, Sort::Int))
        .collect();
    let c: Vec<TermId> = ["c1", "c2", "c3", "c4"]
        .iter()
        .map(|n| terms.mk_var(*n, Sort::Int))
        .collect();
    let m: Vec<TermId> = ["m1", "m2", "m3", "m4", "m5"]
        .iter()
        .map(|n| terms.mk_var(*n, Sort::Int))
        .collect();
    let (three, word) = (int(terms, 3), int(terms, 65536));
    let m3: Vec<TermId> = m.iter().map(|&mi| terms.mk_mul(vec![mi, three])).collect();
    let c16: Vec<TermId> = c.iter().map(|&ci| terms.mk_mul(vec![ci, word])).collect();
    let tail = int(terms, tail);
    let mut clause = Vec::new();
    for (lhs, rhs) in [
        (vec![s[2], m3[4]], vec![c16[3], tail]),
        (vec![c16[2], s[2]], vec![s[1], m3[3]]),
        (vec![c16[0], s[0]], vec![m3[0], m3[1]]),
        (vec![c16[1], s[1]], vec![s[0], m3[2]]),
    ] {
        let lhs = terms.mk_add(lhs);
        let rhs = terms.mk_add(rhs);
        let equality = terms.mk_eq(lhs, rhs);
        clause.push(terms.mk_not_raw(equality));
    }
    let (lo, one) = (int(terms, 40000), int(terms, 1));
    for &mi3 in &m3 {
        let atom = terms.mk_le(lo, mi3);
        clause.push(terms.mk_not_raw(atom));
    }
    for &ci in &c {
        let atom = terms.mk_le(ci, one);
        clause.push(terms.mk_not_raw(atom));
    }
    clause
}

/// Typed `IntCgCutChain` without reordering, by the funnel and the recorder,
/// and the strict checker's own recognizer accepts exactly that clause.
#[test]
fn funnel_types_the_cascade_lemma_as_a_cut_chain() {
    let mut terms = TermStore::new();
    let clause = cascade_rows(&mut terms, 1);
    let (kind, ordered) =
        infer_theory_lemma_kind_from_clause_terms_and_farkas(&terms, &clause, None, None);
    assert_eq!(kind, TheoryLemmaKind::IntCgCutChain);
    assert_eq!(ordered.as_ref(), clause.as_slice());
    assert!(ay_core::proof_validation::recognize_int_cg_cut_chain(
        &terms, &ordered
    ));
    let mut tracker = ProofTracker::new();
    let (kind, recorded) =
        record_funnel_classified_lemma(&mut tracker, &terms, clause.clone(), None);
    assert_eq!(kind, TheoryLemmaKind::IntCgCutChain);
    assert_eq!(recorded, clause);
}

/// NEGATIVE TWIN: a rationally infeasible integer clause the funnel's
/// payload-free rational arm can certify — with UNIT multipliers, the only
/// ones it tries — keeps the Farkas route; the cut-chain arm sits after every
/// rational arm and only ever takes the residual.
#[test]
fn a_rationally_infeasible_clause_stays_farkas() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let low = terms.mk_le(one, x);
    let high = terms.mk_le(x, zero);
    let clause = vec![terms.mk_not_raw(low), terms.mk_not_raw(high)];
    let (kind, _) =
        infer_theory_lemma_kind_from_clause_terms_and_farkas(&terms, &clause, None, None);
    assert_eq!(kind, TheoryLemmaKind::LraFarkas);
}

/// GUARD: the satisfiable twin (`tail = 2`, model in `cascade_rows`) is never
/// promoted, and a certificate-bearing conflict never flows into this
/// payload-free kind.
#[test]
fn a_satisfiable_or_certificate_bearing_clause_is_not_a_cut_chain() {
    let mut terms = TermStore::new();
    let clause = cascade_rows(&mut terms, 2);
    let (kind, _) =
        infer_theory_lemma_kind_from_clause_terms_and_farkas(&terms, &clause, None, None);
    assert_ne!(kind, TheoryLemmaKind::IntCgCutChain);
    let clause = cascade_rows(&mut terms, 1);
    let farkas = FarkasAnnotation::from_ints(&vec![1i64; clause.len()]);
    let (kind, _) =
        infer_theory_lemma_kind_from_clause_terms_and_farkas(&terms, &clause, Some(&farkas), None);
    assert_ne!(kind, TheoryLemmaKind::IntCgCutChain);
}

/// The residual includes rationally infeasible clauses whose Farkas
/// multipliers are not all one: `x + 2y ≥ 4, x ≤ 1, y ≤ 1` needs `(1, 1, 2)`,
/// the unit arm declines it, and the payload-free funnel labels it
/// `IntCgCutChain` (a cut-free chain that lowers to one checked
/// `la_generic`). Pinned so the label is deliberate; the executor's Farkas
/// reconstruction relabels it `LraFarkas`
/// (`reconstruction_relabels_a_non_unit_farkas_cut_chain`).
#[test]
fn a_non_unit_farkas_clause_reaches_the_cut_chain_arm() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let (one, two, four) = (
        terms.mk_int(BigInt::from(1)),
        terms.mk_int(BigInt::from(2)),
        terms.mk_int(BigInt::from(4)),
    );
    let two_y = terms.mk_mul(vec![y, two]);
    let sum = terms.mk_add(vec![x, two_y]);
    let low = terms.mk_le(four, sum);
    let x_le = terms.mk_le(x, one);
    let y_le = terms.mk_le(y, one);
    let clause = vec![
        terms.mk_not_raw(low),
        terms.mk_not_raw(x_le),
        terms.mk_not_raw(y_le),
    ];
    let (kind, ordered) =
        infer_theory_lemma_kind_from_clause_terms_and_farkas(&terms, &clause, None, None);
    assert_eq!(kind, TheoryLemmaKind::IntCgCutChain);
    assert_eq!(ordered.as_ref(), clause.as_slice());
    let witness = ay_core::proof_validation::lia_cut_chain_witness(&terms, &clause)
        .expect("the strict checker's witness");
    assert_eq!(witness.cuts, [] as [ay_core::proof_validation::ChainCut; 0]);
}
