// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the independent `str.len` theorem checker.
//!
//! Two load-bearing properties, mirroring `string_ground_tests`:
//!
//! 1. A genuine universally-valid `str.len` theorem (concat-length sum,
//!    empty↔zero-length, non-negativity, constant/equal length, containment
//!    bound) is ACCEPTED — these are the injected length axioms.
//! 2. A BOGUS length identity (a `+1`, a wrong operand, a `>= 1` bound, a
//!    same-polarity `or`, a wrong constant, a reversed bound) is REJECTED — a
//!    forged `string_length_lemma` cannot launder an arbitrary claim.

use super::*;
use ay_core::{ProofId, Sort, Symbol, TermId, TermStore};
use num_bigint::BigInt;

fn v(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::String)
}
fn sc(terms: &mut TermStore, s: &str) -> TermId {
    terms.mk_string(s.to_string())
}
fn int(terms: &mut TermStore, n: i64) -> TermId {
    terms.mk_int(BigInt::from(n))
}
fn len(terms: &mut TermStore, x: TermId) -> TermId {
    terms.mk_app(Symbol::named("str.len"), [x], Sort::Int)
}
fn concat(terms: &mut TermStore, xs: &[TermId]) -> TermId {
    terms.mk_app(Symbol::named("str.++"), xs, Sort::String)
}
fn add(terms: &mut TermStore, xs: &[TermId]) -> TermId {
    terms.mk_app(Symbol::named("+"), xs, Sort::Int)
}
fn eq(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [a, b], Sort::Bool)
}
fn le(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    terms.mk_app(Symbol::named("<="), [a, b], Sort::Bool)
}
fn or2(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    terms.mk_app(Symbol::named("or"), [a, b], Sort::Bool)
}
fn not(terms: &mut TermStore, a: TermId) -> TermId {
    terms.mk_not_raw(a)
}

fn accept(terms: &TermStore, t: TermId, why: &str) {
    assert!(
        recognize_string_length_lemma(terms, &[t]),
        "should ACCEPT: {why}"
    );
    validate_string_length_lemma(terms, ProofId(0), &[t])
        .unwrap_or_else(|e| panic!("strict validation must accept {why}: {e}"));
}

fn reject(terms: &TermStore, t: TermId, why: &str) {
    assert!(
        !recognize_string_length_lemma(terms, &[t]),
        "should REJECT: {why}"
    );
    let err = validate_string_length_lemma(terms, ProofId(0), &[t])
        .expect_err(&format!("strict validation must reject {why}"));
    assert!(
        format!("{err}").contains("string_length_lemma"),
        "unexpected error for {why}: {err}"
    );
}

// ── Positive: concat-length sum ─────────────────────────────────────────────

#[test]
fn concat_len_sum_accepted() {
    let mut t = TermStore::new();
    let (a, b) = (v(&mut t, "a"), v(&mut t, "b"));
    let c = concat(&mut t, &[a, b]);
    let (la, lb, lc) = (len(&mut t, a), len(&mut t, b), len(&mut t, c));
    let sum = add(&mut t, &[la, lb]);
    let ident = eq(&mut t, lc, sum);
    accept(&t, ident, "len(a++b) = len(a)+len(b)");
}

#[test]
fn concat_len_sum_permuted_and_reversed_accepted() {
    let mut t = TermStore::new();
    let (a, b) = (v(&mut t, "a"), v(&mut t, "b"));
    let c = concat(&mut t, &[a, b]);
    let (la, lb, lc) = (len(&mut t, a), len(&mut t, b), len(&mut t, c));
    // permuted sum (+ is commutative)
    let sum = add(&mut t, &[lb, la]);
    let ident = eq(&mut t, lc, sum);
    accept(&t, ident, "len(a++b) = len(b)+len(a)");
    // reversed equality (sum on the left)
    let sum2 = add(&mut t, &[la, lb]);
    let ident2 = eq(&mut t, sum2, lc);
    accept(&t, ident2, "len(a)+len(b) = len(a++b)");
}

#[test]
fn concat_len_sum_ternary_accepted() {
    let mut t = TermStore::new();
    let (a, b, d) = (v(&mut t, "a"), v(&mut t, "b"), v(&mut t, "d"));
    let c = concat(&mut t, &[a, b, d]);
    let (la, lb, ld, lc) = (
        len(&mut t, a),
        len(&mut t, b),
        len(&mut t, d),
        len(&mut t, c),
    );
    let sum = add(&mut t, &[la, lb, ld]);
    let ident = eq(&mut t, lc, sum);
    accept(&t, ident, "len(a++b++d) = len(a)+len(b)+len(d)");
}

#[test]
fn concat_len_sum_with_folded_const_operand_accepted() {
    // A folded string-constant operand may appear as its literal length.
    let mut t = TermStore::new();
    let a = v(&mut t, "a");
    let k = sc(&mut t, "hi"); // length 2
    let c = concat(&mut t, &[a, k]);
    let (la, lc) = (len(&mut t, a), len(&mut t, c));
    let two = int(&mut t, 2);
    let sum = add(&mut t, &[la, two]);
    let ident = eq(&mut t, lc, sum);
    accept(&t, ident, "len(a++\"hi\") = len(a)+2");
}

// ── Negative: concat-length sum near-misses ─────────────────────────────────

#[test]
fn concat_len_sum_plus_one_rejected() {
    let mut t = TermStore::new();
    let (a, b) = (v(&mut t, "a"), v(&mut t, "b"));
    let c = concat(&mut t, &[a, b]);
    let (la, lb, lc) = (len(&mut t, a), len(&mut t, b), len(&mut t, c));
    let one = int(&mut t, 1);
    let sum = add(&mut t, &[la, lb, one]);
    let bogus = eq(&mut t, lc, sum);
    reject(&t, bogus, "len(a++b) = len(a)+len(b)+1");
}

#[test]
fn concat_len_sum_wrong_operand_rejected() {
    let mut t = TermStore::new();
    let (a, b) = (v(&mut t, "a"), v(&mut t, "b"));
    let c = concat(&mut t, &[a, b]);
    let (la, lc) = (len(&mut t, a), len(&mut t, c));
    let sum = add(&mut t, &[la, la]); // len(a)+len(a), not len(a)+len(b)
    let bogus = eq(&mut t, lc, sum);
    reject(&t, bogus, "len(a++b) = len(a)+len(a)");
}

#[test]
fn concat_len_sum_missing_operand_rejected() {
    let mut t = TermStore::new();
    let (a, b) = (v(&mut t, "a"), v(&mut t, "b"));
    let c = concat(&mut t, &[a, b]);
    let (la, lc) = (len(&mut t, a), len(&mut t, c));
    let bogus = eq(&mut t, lc, la); // len(a++b) = len(a)
    reject(&t, bogus, "len(a++b) = len(a)");
}

#[test]
fn concat_len_sum_wrong_const_operand_rejected() {
    let mut t = TermStore::new();
    let a = v(&mut t, "a");
    let k = sc(&mut t, "hi"); // length 2
    let c = concat(&mut t, &[a, k]);
    let (la, lc) = (len(&mut t, a), len(&mut t, c));
    let three = int(&mut t, 3); // wrong: "hi" has length 2
    let sum = add(&mut t, &[la, three]);
    let bogus = eq(&mut t, lc, sum);
    reject(&t, bogus, "len(a++\"hi\") = len(a)+3");
}

// ── empty ↔ zero length ─────────────────────────────────────────────────────

#[test]
fn empty_iff_zero_both_directions_accepted() {
    let mut t = TermStore::new();
    let x = v(&mut t, "x");
    let empty = sc(&mut t, "");
    let zero = int(&mut t, 0);
    let lx = len(&mut t, x);
    // empty -> zero:  (or (not (= x "")) (= (str.len x) 0))
    let x_eq_e = eq(&mut t, x, empty);
    let not_e = not(&mut t, x_eq_e);
    let lx_eq_0 = eq(&mut t, lx, zero);
    let fwd = or2(&mut t, not_e, lx_eq_0);
    accept(&t, fwd, "x=\"\" -> len(x)=0");
    // zero -> empty:  (or (= x "") (not (= (str.len x) 0)))
    let x_eq_e2 = eq(&mut t, x, empty);
    let lx_eq_02 = eq(&mut t, lx, zero);
    let not_z = not(&mut t, lx_eq_02);
    let rev = or2(&mut t, x_eq_e2, not_z);
    accept(&t, rev, "len(x)=0 -> x=\"\"");
    // task's stated form: (or (= 0 (str.len x)) (not (= x "")))
    let zero_eq_lx = eq(&mut t, zero, lx);
    let x_eq_e3 = eq(&mut t, x, empty);
    let not_e3 = not(&mut t, x_eq_e3);
    let task_form = or2(&mut t, zero_eq_lx, not_e3);
    accept(&t, task_form, "(or (= 0 (str.len x)) (not (= x \"\")))");
}

#[test]
fn empty_iff_zero_same_polarity_rejected() {
    let mut t = TermStore::new();
    let x = v(&mut t, "x");
    let empty = sc(&mut t, "");
    let zero = int(&mut t, 0);
    let lx = len(&mut t, x);
    // both positive: (or (= x "") (= (str.len x) 0)) == p ∨ p == p, NOT a tautology
    let x_eq_e = eq(&mut t, x, empty);
    let lx_eq_0 = eq(&mut t, lx, zero);
    let both_pos = or2(&mut t, x_eq_e, lx_eq_0);
    reject(
        &t,
        both_pos,
        "(or (= x \"\") (= (str.len x) 0)) is not a tautology",
    );
    // both negated
    let x_eq_e2 = eq(&mut t, x, empty);
    let not_e = not(&mut t, x_eq_e2);
    let lx_eq_02 = eq(&mut t, lx, zero);
    let not_z = not(&mut t, lx_eq_02);
    let both_neg = or2(&mut t, not_e, not_z);
    reject(
        &t,
        both_neg,
        "(or (not (= x \"\")) (not (= (str.len x) 0)))",
    );
}

// ── non-negativity ──────────────────────────────────────────────────────────

#[test]
fn nonneg_accepted_wrong_bounds_rejected() {
    let mut t = TermStore::new();
    let x = v(&mut t, "x");
    let lx = len(&mut t, x);
    let zero = int(&mut t, 0);
    let ok = le(&mut t, zero, lx);
    accept(&t, ok, "0 <= len(x)");

    let one = int(&mut t, 1);
    let lx2 = len(&mut t, x);
    let bad_bound = le(&mut t, one, lx2);
    reject(&t, bad_bound, "1 <= len(x) is not universally valid");

    let lx3 = len(&mut t, x);
    let zero2 = int(&mut t, 0);
    let wrong_dir = le(&mut t, lx3, zero2);
    reject(&t, wrong_dir, "len(x) <= 0 is not universally valid");
}

// ── constant length ─────────────────────────────────────────────────────────

#[test]
fn const_len_accepted_wrong_rejected() {
    let mut t = TermStore::new();
    let r = sc(&mut t, "R");
    let lr = len(&mut t, r);
    let one = int(&mut t, 1);
    let ok = eq(&mut t, one, lr);
    accept(&t, ok, "1 = len(\"R\")");
    // reversed
    let lr2 = len(&mut t, r);
    let one2 = int(&mut t, 1);
    let ok2 = eq(&mut t, lr2, one2);
    accept(&t, ok2, "len(\"R\") = 1");
    // wrong constant
    let lr3 = len(&mut t, r);
    let two = int(&mut t, 2);
    let bad = eq(&mut t, two, lr3);
    reject(&t, bad, "2 = len(\"R\") is false");
}

// ── equal-length congruence ─────────────────────────────────────────────────

#[test]
fn eq_len_both_strlen_accepted() {
    let mut t = TermStore::new();
    let (s, u) = (v(&mut t, "s"), v(&mut t, "u"));
    let ls = len(&mut t, s);
    let lu = len(&mut t, u);
    let leneq = eq(&mut t, ls, lu);
    let s_eq_u = eq(&mut t, s, u);
    let not_eq = not(&mut t, s_eq_u);
    let ok = or2(&mut t, leneq, not_eq);
    accept(&t, ok, "s=u -> len(s)=len(u)");
}

#[test]
fn eq_len_const_side_accepted() {
    let mut t = TermStore::new();
    let s = v(&mut t, "s");
    let gaso = sc(&mut t, "GASO="); // length 5
    let ls = len(&mut t, s);
    let five = int(&mut t, 5);
    let leneq = eq(&mut t, ls, five);
    let s_eq_c = eq(&mut t, s, gaso);
    let not_eq = not(&mut t, s_eq_c);
    let ok = or2(&mut t, leneq, not_eq);
    accept(&t, ok, "s=\"GASO=\" -> len(s)=5");
}

#[test]
fn eq_len_wrong_subject_rejected() {
    let mut t = TermStore::new();
    let (s, u, w) = (v(&mut t, "s"), v(&mut t, "u"), v(&mut t, "w"));
    // (or (= (str.len s) (str.len w)) (not (= s u))) — w is unrelated to s=u
    let ls = len(&mut t, s);
    let lw = len(&mut t, w);
    let leneq = eq(&mut t, ls, lw);
    let s_eq_u = eq(&mut t, s, u);
    let not_eq = not(&mut t, s_eq_u);
    let bogus = or2(&mut t, leneq, not_eq);
    reject(&t, bogus, "s=u does not entail len(s)=len(w)");
}

#[test]
fn eq_len_wrong_const_rejected() {
    let mut t = TermStore::new();
    let s = v(&mut t, "s");
    let gaso = sc(&mut t, "GASO="); // length 5
    let ls = len(&mut t, s);
    let four = int(&mut t, 4); // wrong length
    let leneq = eq(&mut t, ls, four);
    let s_eq_c = eq(&mut t, s, gaso);
    let not_eq = not(&mut t, s_eq_c);
    let bogus = or2(&mut t, leneq, not_eq);
    reject(&t, bogus, "s=\"GASO=\" entails len(s)=5, not 4");
}

// ── containment length bounds ───────────────────────────────────────────────

#[test]
fn containment_bounds_accepted() {
    let mut t = TermStore::new();
    let (x, s) = (v(&mut t, "x"), v(&mut t, "s"));
    let lx = len(&mut t, x);
    let ls = len(&mut t, s);
    // contains(x, s) -> len(s) <= len(x)
    let contains = t.mk_app(Symbol::named("str.contains"), [x, s], Sort::Bool);
    let not_c = not(&mut t, contains);
    let bound = le(&mut t, ls, lx);
    let ok = or2(&mut t, not_c, bound);
    accept(&t, ok, "contains(x,s) -> len(s)<=len(x)");

    // prefixof(s, x) -> len(s) <= len(x)   (s is args[0]=part, x is args[1]=whole)
    let ls2 = len(&mut t, s);
    let lx2 = len(&mut t, x);
    let pre = t.mk_app(Symbol::named("str.prefixof"), [s, x], Sort::Bool);
    let not_p = not(&mut t, pre);
    let bound2 = le(&mut t, ls2, lx2);
    let ok2 = or2(&mut t, not_p, bound2);
    accept(&t, ok2, "prefixof(s,x) -> len(s)<=len(x)");
}

#[test]
fn containment_reversed_bound_rejected() {
    let mut t = TermStore::new();
    let (x, s) = (v(&mut t, "x"), v(&mut t, "s"));
    let lx = len(&mut t, x);
    let ls = len(&mut t, s);
    // contains(x, s) -> len(x) <= len(s)  — WRONG direction
    let contains = t.mk_app(Symbol::named("str.contains"), [x, s], Sort::Bool);
    let not_c = not(&mut t, contains);
    let bound = le(&mut t, lx, ls);
    let bogus = or2(&mut t, not_c, bound);
    reject(&t, bogus, "contains(x,s) does not entail len(x)<=len(s)");
}

// ── hygiene ─────────────────────────────────────────────────────────────────

#[test]
fn arbitrary_bool_clause_rejected() {
    let mut t = TermStore::new();
    let p = t.mk_var("p", Sort::Bool);
    let q = t.mk_var("q", Sort::Bool);
    let cl = or2(&mut t, p, q);
    reject(
        &t,
        cl,
        "an arbitrary boolean disjunction is not a str.len theorem",
    );
}

#[test]
fn ill_sorted_and_indexed_builtin_spoofs_are_rejected() {
    // `TermStore` intentionally permits raw applications. The strict proof
    // boundary therefore cannot infer built-in semantics from a matching name
    // alone: the exact named operator and its complete sort signature must
    // agree. Each near-miss below looked like `0 <= str.len(x)` to a name-only
    // recognizer but is not a well-typed SMT-LIB length theorem.
    let mut t = TermStore::new();
    let x = v(&mut t, "x");
    let zero = int(&mut t, 0);

    let wrong_sort_len = t.mk_app(Symbol::named("str.len"), [x], Sort::String);
    let wrong_sort_bound = t.mk_app(Symbol::named("<="), [zero, wrong_sort_len], Sort::Bool);
    reject(
        &t,
        wrong_sort_bound,
        "a String-sorted raw str.len application is not the Int-valued built-in",
    );

    let indexed_len = t.mk_app(Symbol::indexed("str.len", vec![0]), [x], Sort::Int);
    let indexed_len_bound = t.mk_app(Symbol::named("<="), [zero, indexed_len], Sort::Bool);
    reject(
        &t,
        indexed_len_bound,
        "an indexed symbol named str.len is not the named built-in",
    );

    let genuine_len = len(&mut t, x);
    let indexed_le = t.mk_app(
        Symbol::indexed("<=", vec![0]),
        [zero, genuine_len],
        Sort::Bool,
    );
    reject(
        &t,
        indexed_le,
        "an indexed symbol named <= is not the named built-in",
    );
}

#[test]
fn empty_clause_rejected() {
    let t = TermStore::new();
    assert!(!recognize_string_length_lemma(&t, &[]));
    validate_string_length_lemma(&t, ProofId(0), &[]).expect_err("empty clause must be rejected");
}

#[test]
fn identity_as_one_of_several_literals_accepted() {
    // A clause is a tautology if ANY literal is a valid str.len theorem.
    let mut t = TermStore::new();
    let p = t.mk_var("p", Sort::Bool);
    let x = v(&mut t, "x");
    let lx = len(&mut t, x);
    let zero = int(&mut t, 0);
    let nonneg = le(&mut t, zero, lx);
    assert!(recognize_string_length_lemma(&t, &[p, nonneg]));
    validate_string_length_lemma(&t, ProofId(0), &[p, nonneg])
        .expect("clause with a valid str.len literal is a tautology");
}
