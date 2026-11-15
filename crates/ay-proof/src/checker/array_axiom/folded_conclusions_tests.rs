// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Folded array-axiom conclusions: the exact clauses the array axiom sites
//! emit over a `Bool` element sort (`array_cong_select`, `store_value_cong`,
//! `row1_clause`, `row2_clause`), and their mis-instantiated twins. z3 5.1.0
//! finds the negation of every accepted clause unsat and of every rejected twin
//! sat: each twin is a genuine counterexample, not merely an unmatched shape.

use super::*;

use num_bigint::BigInt;

struct Fixture {
    terms: TermStore,
    c: TermId,
    d: TermId,
    i: TermId,
    j: TermId,
    k42: TermId,
    k07: TermId,
    k01: TermId,
    tt: TermId,
    ff: TermId,
}

fn fixture() -> Fixture {
    let mut terms = TermStore::new();
    let array = Sort::array(Sort::bitvec(32), Sort::Bool);
    let c = terms.mk_var("c", array.clone());
    let d = terms.mk_var("d", array);
    let i = terms.mk_var("i", Sort::bitvec(32));
    let j = terms.mk_var("j", Sort::bitvec(32));
    let k42 = terms.mk_bitvec(BigInt::from(0x42), 32);
    let k07 = terms.mk_bitvec(BigInt::from(0x07), 32);
    let k01 = terms.mk_bitvec(BigInt::from(0x01), 32);
    let tt = terms.mk_bool(true);
    let ff = terms.mk_bool(false);
    Fixture {
        terms,
        c,
        d,
        i,
        j,
        k42,
        k07,
        k01,
        tt,
        ff,
    }
}

impl Fixture {
    fn konst(&mut self, fill: TermId) -> TermId {
        self.terms.mk_const_array(Sort::bitvec(32), fill)
    }

    fn not_eq(&mut self, left: TermId, right: TermId) -> TermId {
        let eq = self.terms.mk_eq(left, right);
        self.terms.mk_not(eq)
    }

    /// The packed `(or ..)` unit the axiom sites record.
    fn packed(&mut self, literals: Vec<TermId>) -> Vec<TermId> {
        vec![self.terms.mk_or(literals)]
    }

    fn row_chain(&self, clause: &[TermId]) -> Result<(), ProofCheckError> {
        validate_array_row_chain(&self.terms, ProofId(0), clause, &mut |_, _| true)
    }

    fn kind(&self, clause: &[TermId]) -> Option<TheoryLemmaKind> {
        recognize_array_theory_lemma(&self.terms, clause)
    }

    /// Every twin must be refused by the validator AND left unclassified.
    fn assert_row_chain_twins_rejected(&self, twins: &[&[TermId]]) {
        for clause in twins {
            assert!(self.row_chain(clause).is_err(), "{clause:?}");
            assert_eq!(self.kind(clause), None, "{clause:?}");
        }
    }
}

/// `n2`: `store_value_cong` builds `(or (not (= c S)) (= true (select c x)))`
/// with `S = (store (const false) x true)`, and `mk_eq` folds the equality to
/// the atom. Before the fix this was `Generic`.
#[test]
fn folded_store_value_read_under_array_equality_is_row_chain() {
    let mut f = fixture();
    let k = f.konst(f.ff);
    let store = f.terms.mk_store(k, f.k42, f.tt);
    let premise = f.not_eq(f.c, store);
    let read = f.terms.mk_select(f.c, f.k42);
    let folded = f.terms.mk_eq(f.tt, read);
    assert_eq!(
        folded, read,
        "fixture premise: mk_eq folds `(= true P)` to `P`"
    );
    let clause = f.packed(vec![read, premise]);

    assert_eq!(f.row_chain(&clause), Ok(()));
    assert_eq!(f.kind(&clause), Some(TheoryLemmaKind::ArrayRowChain));
}

/// `n1`: `array_cong_select` under `c = (const true)`; `mk_select` folds the
/// constant read and `mk_eq` folds `(= (select c 7) true)`.
#[test]
fn folded_const_array_read_under_array_equality_is_row_chain() {
    let mut f = fixture();
    let k = f.konst(f.tt);
    let premise = f.not_eq(f.c, k);
    let read = f.terms.mk_select(f.c, f.k07);
    let clause = f.packed(vec![read, premise]);

    assert_eq!(f.row_chain(&clause), Ok(()));
    assert_eq!(f.kind(&clause), Some(TheoryLemmaKind::ArrayRowChain));
}

#[test]
fn folded_false_read_is_the_negated_atom() {
    let mut f = fixture();
    let k = f.konst(f.ff);
    let premise = f.not_eq(k, f.c);
    let read = f.terms.mk_select(f.c, f.k07);
    let negated = f.terms.mk_not(read);
    let clause = [premise, negated];

    assert_eq!(f.row_chain(&clause), Ok(()));
    assert_eq!(f.kind(&clause), Some(TheoryLemmaKind::ArrayRowChain));
}

/// Skipping a write needs the same justification as sub-schema (B): a carried
/// `(= j i)` guard, or two distinct interpreted indices.
#[test]
fn folded_read_skips_a_write_only_on_a_guard_or_distinct_constants() {
    let mut f = fixture();
    let k = f.konst(f.tt);
    let guarded_store = f.terms.mk_store(k, f.i, f.ff);
    let premise = f.not_eq(f.c, guarded_store);
    let read = f.terms.mk_select(f.c, f.j);
    let guard = f.terms.mk_eq(f.j, f.i);
    assert_eq!(f.row_chain(&[premise, guard, read]), Ok(()));

    let constant_store = f.terms.mk_store(k, f.k42, f.ff);
    let premise = f.not_eq(f.c, constant_store);
    let read = f.terms.mk_select(f.c, f.k07);
    assert_eq!(f.row_chain(&[premise, read]), Ok(()));
}

/// `row2_clause` over a constant base: `(or (= i j) (select (store (const
/// true) i p) j))` (the base read folds to `true`) and its `false` twin
/// `(or (= i j) (not (select (store (const false) i p) j)))`.
#[test]
fn folded_row2_over_a_constant_base_is_row_chain() {
    let mut f = fixture();
    let p = f.terms.mk_var("p", Sort::Bool);
    let guard = f.terms.mk_eq(f.i, f.j);
    let k_true = f.konst(f.tt);
    let store_true = f.terms.mk_store(k_true, f.i, p);
    let read_true = f.terms.mk_select(store_true, f.j);
    let clause = f.packed(vec![guard, read_true]);
    assert_eq!(f.row_chain(&clause), Ok(()));
    assert_eq!(f.kind(&clause), Some(TheoryLemmaKind::ArrayRowChain));

    let k_false = f.konst(f.ff);
    let store_false = f.terms.mk_store(k_false, f.i, p);
    let read_false = f.terms.mk_select(store_false, f.j);
    let negated = f.terms.mk_not(read_false);
    let clause = f.packed(vec![guard, negated]);
    assert_eq!(f.row_chain(&clause), Ok(()));
    assert_eq!(f.kind(&clause), Some(TheoryLemmaKind::ArrayRowChain));
}

/// Folded (A) through a TAKEN entry after a guarded skip:
/// `(or (= j i) (select (store (store d j true) i p) j))`.
#[test]
fn folded_chain_evaluation_through_a_taken_entry_is_row_chain() {
    let mut f = fixture();
    let p = f.terms.mk_var("p", Sort::Bool);
    let inner = f.terms.mk_store(f.d, f.j, f.tt);
    let outer = f.terms.mk_store(inner, f.i, p);
    let read = f.terms.mk_select(outer, f.j);
    let guard = f.terms.mk_eq(f.j, f.i);
    let clause = [read, guard];
    assert_eq!(f.row_chain(&clause), Ok(()));
    assert_eq!(f.kind(&clause), Some(TheoryLemmaKind::ArrayRowChain));
}

/// `row1_clause` with a Boolean constant stored: `(or (not (= i j)) (select
/// (store d i true) j))`, and its `false` twin with the mirrored guard.
/// Labelled `ArrayRowChain`.
#[test]
fn folded_row1_conditional_is_row_chain() {
    let mut f = fixture();
    let guard = f.not_eq(f.i, f.j);
    let store_true = f.terms.mk_store(f.d, f.i, f.tt);
    let read_true = f.terms.mk_select(store_true, f.j);
    let clause = f.packed(vec![guard, read_true]);
    assert_eq!(f.row_chain(&clause), Ok(()));
    assert_eq!(f.kind(&clause), Some(TheoryLemmaKind::ArrayRowChain));

    let mirrored = f.not_eq(f.j, f.i);
    let store_false = f.terms.mk_store(f.d, f.i, f.ff);
    let read_false = f.terms.mk_select(store_false, f.j);
    let negated = f.terms.mk_not(read_false);
    let clause = [negated, mirrored];
    assert_eq!(f.row_chain(&clause), Ok(()));
    assert_eq!(f.kind(&clause), Some(TheoryLemmaKind::ArrayRowChain));
}

/// `store_value_cong` over a store/store equality, folded (I):
/// `(or p (not (= (store c i p) (store d i true))))`, and with the constant on
/// the LEFT and a `false` element:
/// `(or (not p) (not (= (store c i false) (store d i p))))`.
#[test]
fn folded_same_index_store_value_is_row_chain() {
    let mut f = fixture();
    let p = f.terms.mk_var("p", Sort::Bool);
    let left = f.terms.mk_store(f.c, f.i, p);
    let right = f.terms.mk_store(f.d, f.i, f.tt);
    let premise = f.not_eq(left, right);
    let clause = f.packed(vec![p, premise]);
    assert_eq!(f.row_chain(&clause), Ok(()));
    assert_eq!(f.kind(&clause), Some(TheoryLemmaKind::ArrayRowChain));

    let left = f.terms.mk_store(f.c, f.i, f.ff);
    let right = f.terms.mk_store(f.d, f.i, p);
    let premise = f.not_eq(left, right);
    let negated = f.terms.mk_not(p);
    let clause = [negated, premise];
    assert_eq!(f.row_chain(&clause), Ok(()));
    assert_eq!(f.kind(&clause), Some(TheoryLemmaKind::ArrayRowChain));
}

// ---------- mis-instantiated twins: each must stay rejected ----------

/// The literal's polarity must name the constant the walk reaches: claiming
/// `(not (select c x))` where `S` stores `true` at `x` is a false clause.
#[test]
fn folded_read_with_the_wrong_polarity_is_rejected() {
    let mut f = fixture();
    let k = f.konst(f.ff);
    let store = f.terms.mk_store(k, f.k42, f.tt);
    let premise = f.not_eq(f.c, store);
    let read = f.terms.mk_select(f.c, f.k42);
    let negated = f.terms.mk_not(read);
    let clause = f.packed(vec![negated, premise]);

    assert!(f.row_chain(&clause).is_err());
    assert_eq!(f.kind(&clause), None);
}

/// Folded (B) twins. Without the `(= j i)` guard the write at `i` cannot be
/// skipped (when `j = i` the read is `false`); a read of an unrelated array `d`
/// is not entailed by `c = S`; and `c = d` alone decides no read.
#[test]
fn folded_read_under_array_equality_twins_are_rejected() {
    let mut f = fixture();
    let k_true = f.konst(f.tt);
    let symbolic_store = f.terms.mk_store(k_true, f.i, f.ff);
    let unguarded = f.not_eq(f.c, symbolic_store);
    let read_j = f.terms.mk_select(f.c, f.j);

    let k_false = f.konst(f.ff);
    let store = f.terms.mk_store(k_false, f.k42, f.tt);
    let premise = f.not_eq(f.c, store);
    let unrelated = f.terms.mk_select(f.d, f.k42);

    let unreduced = f.not_eq(f.c, f.d);
    let read_42 = f.terms.mk_select(f.c, f.k42);

    f.assert_row_chain_twins_rejected(&[
        &[unguarded, read_j],
        &[premise, unrelated],
        &[unreduced, read_42],
    ]);
}

/// Folded ROW1 twins. Wrong polarity: with `i = j` the read IS `true`.
/// Positive guard: with `i != j` the read is `d[j]`, unconstrained. Symbolic
/// stored value: with `i = j` the read is `p`, which may be `false`.
#[test]
fn folded_row1_twins_are_rejected() {
    let mut f = fixture();
    let p = f.terms.mk_var("p", Sort::Bool);
    let guard = f.not_eq(f.i, f.j);
    let store_true = f.terms.mk_store(f.d, f.i, f.tt);
    let read_true = f.terms.mk_select(store_true, f.j);
    let negated = f.terms.mk_not(read_true);
    let positive_guard = f.terms.mk_eq(f.i, f.j);
    let store_p = f.terms.mk_store(f.d, f.i, p);
    let read_p = f.terms.mk_select(store_p, f.j);

    f.assert_row_chain_twins_rejected(&[
        &[guard, negated],
        &[positive_guard, read_true],
        &[guard, read_p],
    ]);
}

/// Folded (A) twins. A non-constant base leaves `d[j]` unconstrained; the
/// wrong polarity contradicts the fill; without the guard `i = j` reads `p`.
#[test]
fn folded_chain_evaluation_twins_are_rejected() {
    let mut f = fixture();
    let p = f.terms.mk_var("p", Sort::Bool);
    let guard = f.terms.mk_eq(f.i, f.j);
    let store_d = f.terms.mk_store(f.d, f.i, p);
    let read_d = f.terms.mk_select(store_d, f.j);
    let k_true = f.konst(f.tt);
    let store_k = f.terms.mk_store(k_true, f.i, p);
    let read_k = f.terms.mk_select(store_k, f.j);
    let negated_k = f.terms.mk_not(read_k);

    f.assert_row_chain_twins_rejected(&[&[guard, read_d], &[guard, negated_k], &[read_k]]);
}

/// Folded (I) twins. Different write indices: the stores can be equal with
/// `p` false. Wrong polarity: equal stores force `p = true`. A literal that is
/// neither written value says nothing about `q`.
#[test]
fn folded_same_index_store_value_twins_are_rejected() {
    let mut f = fixture();
    let p = f.terms.mk_var("p", Sort::Bool);
    let q = f.terms.mk_var("q", Sort::Bool);
    let left = f.terms.mk_store(f.c, f.i, p);
    let right_j = f.terms.mk_store(f.d, f.j, f.tt);
    let premise_j = f.not_eq(left, right_j);
    let right_i = f.terms.mk_store(f.d, f.i, f.tt);
    let premise_i = f.not_eq(left, right_i);
    let negated = f.terms.mk_not(p);

    f.assert_row_chain_twins_rejected(&[&[p, premise_j], &[negated, premise_i], &[q, premise_i]]);
}

/// Deliberately NOT accepted: `a1`'s folded `array_default_congruence`
/// instance `(or (not (= S (const true))) (default S))`. The refutation's next
/// default step, the store peel, stays `Generic` (finite carrier), so
/// certifying this one alone would only replace the export's
/// undeclared-symbol refusal of `default` with an `InvalidArrayStep` (see
/// `folded_conclusions`).
#[test]
fn folded_default_congruence_stays_unclassified() {
    let mut f = fixture();
    let k_false = f.konst(f.ff);
    let s = f.terms.mk_store(k_false, f.k01, f.tt);
    let k_true = f.konst(f.tt);
    let premise = f.not_eq(s, k_true);
    let default = f.terms.mk_array_default(s);
    let clause = f.packed(vec![default, premise]);

    assert!(validate_array_default_const(&f.terms, ProofId(0), &clause).is_err());
    assert!(f.row_chain(&clause).is_err());
    assert_eq!(f.kind(&clause), None);
}

// ---------- Alethe lowering of the folded shapes ----------

fn export_single_lemma(terms: &TermStore, clause: Vec<TermId>) -> String {
    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("array", clause.clone(), TheoryLemmaKind::ArrayRowChain);
    crate::try_export_alethe_with_problem_scope_and_overrides(&proof, terms, &clause, None)
        .expect("an ArrayRowChain lemma always renders, lowered or as an honest hole")
}

/// A store-value read lowers to `cong`/`arrays_idx`/`trans`, and the derived
/// `(= (select c x) true)` is closed into the folded literal by
/// `equiv_simplify` + `equiv1` (pinned Carcara 1.1.0 accepts both spellings,
/// `(= (= P true) P)` and `(= (= true P) P)`).
#[test]
fn folded_store_value_read_lowers_through_equiv_simplify() {
    let mut f = fixture();
    let k = f.konst(f.ff);
    let store = f.terms.mk_store(k, f.k42, f.tt);
    let premise = f.not_eq(f.c, store);
    let read = f.terms.mk_select(f.c, f.k42);
    let clause = f.packed(vec![read, premise]);
    assert!(array_row_chain_printer_terms(&f.terms, &clause).is_some());

    let output = export_single_lemma(&f.terms, clause);
    assert!(!output.contains("read_over_write_chain"), "{output}");
    assert!(output.contains(":rule arrays_idx)"), "{output}");
    assert!(
        output.contains(":rule equiv_simplify)") && output.contains(":rule equiv1 "),
        "{output}"
    );
    assert!(
        output.contains("(step t0.fin (cl (select c #b")
            && output.contains(":premises (t0.fe t0.tr))"),
        "{output}"
    );
}

/// A constant-array read is certified internally but has no pinned-checker
/// primitive (`RowChainEnd::Const`), so it keeps the honest `hole`.
#[test]
fn folded_const_array_read_keeps_the_honest_fallback() {
    let mut f = fixture();
    let k = f.konst(f.tt);
    let premise = f.not_eq(f.c, k);
    let read = f.terms.mk_select(f.c, f.k07);
    let clause = f.packed(vec![read, premise]);

    let output = export_single_lemma(&f.terms, clause);
    assert!(output.contains(":rule hole)"), "{output}");
    assert!(!output.contains("equiv_simplify"), "{output}");
}

/// The printer shape mirrors the checker: a mis-polarized clause yields no
/// shape (and could not have been labelled `ArrayRowChain` in the first place).
#[test]
fn folded_read_printer_terms_refuse_the_wrong_polarity() {
    let mut f = fixture();
    let k = f.konst(f.ff);
    let store = f.terms.mk_store(k, f.k42, f.tt);
    let premise = f.not_eq(f.c, store);
    let read = f.terms.mk_select(f.c, f.k42);
    let negated = f.terms.mk_not(read);
    assert!(array_row_chain_printer_terms(&f.terms, &[premise, negated]).is_none());

    let output = export_single_lemma(&f.terms, vec![premise, negated]);
    assert!(!output.contains("equiv_simplify"), "{output}");
}

/// The read on the premise's RIGHT side, a guarded skip, and a `false`
/// element: `(or (= j i) (not (= (store (store d j false) i true) c))
/// (not (select c j)))`.
#[test]
fn guarded_right_side_false_read_lowers_through_equiv_simplify() {
    let mut f = fixture();
    let inner = f.terms.mk_store(f.d, f.j, f.ff);
    let outer = f.terms.mk_store(inner, f.i, f.tt);
    let array_eq = f.terms.mk_app(Symbol::named("="), [outer, f.c], Sort::Bool);
    let premise = f.terms.mk_not(array_eq);
    let guard = f.terms.mk_eq(f.j, f.i);
    let read = f.terms.mk_select(f.c, f.j);
    let negated = f.terms.mk_not(read);
    let clause = f.packed(vec![guard, premise, negated]);
    assert_eq!(f.row_chain(&clause), Ok(()));
    assert!(array_row_chain_printer_terms(&f.terms, &clause).is_some());

    let output = export_single_lemma(&f.terms, clause);
    assert!(output.contains(":rule arrays_row"), "{output}");
    assert!(output.contains(":rule equiv_simplify)"), "{output}");
    assert!(
        output.contains("(step t0.fin (cl (not (select c j)))"),
        "{output}"
    );
}

/// Folded (I) lowers through the (I) machinery: two `arrays_idx` reads at the
/// shared index, `cong`, `trans`, then the `equiv_simplify` closing.
#[test]
fn folded_same_index_store_value_lowers_through_equiv_simplify() {
    let mut f = fixture();
    let p = f.terms.mk_var("p", Sort::Bool);
    let left = f.terms.mk_store(f.c, f.i, p);
    let right = f.terms.mk_store(f.d, f.i, f.tt);
    let premise = f.not_eq(left, right);
    let clause = f.packed(vec![p, premise]);
    assert!(array_row_chain_printer_terms(&f.terms, &clause).is_some());

    let output = export_single_lemma(&f.terms, clause);
    assert!(!output.contains(":rule hole)"), "{output}");
    assert!(output.contains(":rule arrays_idx)"), "{output}");
    assert!(output.contains(":rule equiv_simplify)"), "{output}");
    assert!(
        output.contains("(step t0.fin (cl p) :rule resolution"),
        "{output}"
    );
}

/// Folded ROW1 and folded (A) have no lowering shape: they keep the `hole`.
#[test]
fn folded_row1_and_chain_evaluation_keep_the_honest_fallback() {
    let mut f = fixture();
    let guard = f.not_eq(f.i, f.j);
    let store = f.terms.mk_store(f.d, f.i, f.tt);
    let read = f.terms.mk_select(store, f.j);
    let row1 = f.packed(vec![guard, read]);

    let p = f.terms.mk_var("p", Sort::Bool);
    let positive_guard = f.terms.mk_eq(f.i, f.j);
    let k_true = f.konst(f.tt);
    let store_k = f.terms.mk_store(k_true, f.i, p);
    let read_k = f.terms.mk_select(store_k, f.j);
    let row2 = f.packed(vec![positive_guard, read_k]);

    for clause in [row1, row2] {
        assert!(array_row_chain_printer_terms(&f.terms, &clause).is_none());
        let output = export_single_lemma(&f.terms, clause);
        assert!(output.contains(":rule hole)"), "{output}");
        assert!(!output.contains("equiv_simplify"), "{output}");
    }
}
