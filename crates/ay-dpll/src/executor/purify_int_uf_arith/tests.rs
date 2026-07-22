// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::TermStore;
use ay_core::Sort;

/// An opaque Int-sorted UF application inside an arithmetic product/sum is
/// replaced by a fresh proxy variable, and a defining equality is appended.
#[test]
fn purifies_opaque_int_uf_in_arith() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let div = terms.mk_app(Symbol::named("__euclid!div"), [a, b], Sort::Int);
    let modt = terms.mk_app(Symbol::named("__euclid!mod"), [a, b], Sort::Int);
    // a = b*div + mod
    let prod = terms.mk_mul(vec![b, div]);
    let sum = terms.mk_add(vec![prod, modt]);
    let eq = terms.mk_eq(a, sum);
    let assertion = terms.mk_not(eq);

    let mut assertions = vec![assertion];
    let changed = purify_int_uf_arith(&mut terms, &mut assertions);

    assert!(
        changed,
        "pass should fire on opaque Int UF operands in arith"
    );
    // Two proxy definitions (div and mod) appended.
    assert_eq!(
        assertions.len(),
        3,
        "two proxy definitions should be appended"
    );
}

/// An opaque Int UF that appears ONLY in LINEAR arithmetic (no opaque-UF
/// nonlinear product) is left untouched — the existing Nelson-Oppen interface
/// bridge already handles these (e.g. `seq_len`, `bv2int`), and purifying them
/// perturbs otherwise-working AUFLIA/UFLIA solves. The trigger is specifically
/// an opaque UF inside a nonlinear product.
#[test]
fn leaves_linear_opaque_uf_untouched() {
    let mut terms = TermStore::new();
    let s = terms.mk_var("s", Sort::Int);
    // seq_len(s) — an opaque Int UF applied to s.
    let len = terms.mk_app(Symbol::named("seq_len"), [s], Sort::Int);
    let one = terms.mk_int(num_bigint::BigInt::from(1));
    // (>= (+ (seq_len s) 1) 0) — len appears only linearly, no product.
    let sum = terms.mk_add(vec![len, one]);
    let zero = terms.mk_int(num_bigint::BigInt::from(0));
    let assertion = terms.mk_ge(sum, zero);

    let mut assertions = vec![assertion];
    let changed = purify_int_uf_arith(&mut terms, &mut assertions);

    assert!(
        !changed,
        "linear opaque-UF occurrences must not be purified (no nonlinear product)"
    );
    assert_eq!(assertions.len(), 1);
}

/// A plain Int variable / constant inside arithmetic is left untouched.
#[test]
fn leaves_plain_int_arith_untouched() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let one = terms.mk_int(num_bigint::BigInt::from(1));
    let sum = terms.mk_add(vec![a, b, one]);
    let assertion = terms.mk_eq(a, sum);

    let mut assertions = vec![assertion];
    let changed = purify_int_uf_arith(&mut terms, &mut assertions);

    assert!(!changed, "plain Int arithmetic needs no purification");
    assert_eq!(assertions.len(), 1);
}

/// A `(mod x 3)` sitting as an ARGUMENT to an uninterpreted function `f` is
/// named with ONE fresh proxy, and EVERY occurrence — including the separate
/// top-level `(= (mod x 3) 1)` — is rewritten to that proxy, so EUF congruence
/// can link `f((mod x 3))` to `f(1)`. Exactly ONE defining equality is appended.
#[test]
fn purifies_mod_under_uf_and_rewrites_all_occurrences() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(num_bigint::BigInt::from(3));
    let one = terms.mk_int(num_bigint::BigInt::from(1));
    let modt = terms.mk_mod(x, three);
    // (= (mod x 3) 1)
    let a1 = terms.mk_eq(modt, one);
    // (= (f (mod x 3)) 9)
    let f_mod = terms.mk_app(Symbol::named("f"), [modt], Sort::Int);
    let nine = terms.mk_int(num_bigint::BigInt::from(9));
    let a2 = terms.mk_eq(f_mod, nine);

    let mut assertions = vec![a1, a2];
    let changed = purify_mod_div_uf_args(&mut terms, &mut assertions);

    assert!(changed, "mod under a UF argument should be purified");
    // Original two assertions rewritten in place + exactly ONE proxy definition.
    assert_eq!(
        assertions.len(),
        3,
        "one proxy definition should be appended"
    );
    // The interned `(mod x 3)` must no longer appear as a UF argument in the
    // rewritten `(f _)`: the proxy is a fresh Var, not a mod App.
    let rewritten_f_eq = assertions[1];
    let TermData::App(_, eq_args) = terms.get(rewritten_f_eq).clone() else {
        panic!("expected (= (f v) 9) shape");
    };
    let TermData::App(_, f_args) = terms.get(eq_args[0]).clone() else {
        panic!("expected (f v) application");
    };
    assert!(
        matches!(terms.get(f_args[0]), TermData::Var(_, _)),
        "the UF argument must be rewritten to a fresh proxy variable, not left as (mod x 3)"
    );
    // The proxy definition (last assertion) is `(= v (mod x 3))`.
    let def = assertions[2];
    let TermData::App(_, def_args) = terms.get(def).clone() else {
        panic!("expected proxy-definition equality");
    };
    assert!(
        def_args
            .iter()
            .any(|&t| matches!(terms.get(t), TermData::App(Symbol::Named(n), _) if n == "mod")),
        "the single appended definition must retain the original (mod x 3)"
    );
}

/// Two DISTINCT mod terms under a UF (`(mod x 3)` and `(mod x 4)`) get SEPARATE
/// proxies — purification never equates distinct mod terms, so congruence can
/// only fire on genuinely-equal values (no wrong-UNSAT from over-firing).
#[test]
fn distinct_mod_args_get_distinct_proxies() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(num_bigint::BigInt::from(3));
    let four = terms.mk_int(num_bigint::BigInt::from(4));
    let mod3 = terms.mk_mod(x, three);
    let mod4 = terms.mk_mod(x, four);
    let f3 = terms.mk_app(Symbol::named("f"), [mod3], Sort::Int);
    let f4 = terms.mk_app(Symbol::named("f"), [mod4], Sort::Int);
    let a = terms.mk_eq(f3, f4);

    let mut assertions = vec![a];
    let changed = purify_mod_div_uf_args(&mut terms, &mut assertions);

    assert!(changed);
    // Two distinct proxy definitions appended (one per distinct mod term).
    assert_eq!(
        assertions.len(),
        3,
        "each distinct mod-under-UF term gets its own proxy definition"
    );
}

/// A `(mod x 3)` that appears only in arithmetic / (dis)equality position — NOT
/// as a UF argument — is left untouched (mod_div_elim handles it; naming it
/// would needlessly perturb the LIA solve).
#[test]
fn leaves_mod_not_under_uf_untouched() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(num_bigint::BigInt::from(3));
    let one = terms.mk_int(num_bigint::BigInt::from(1));
    let modt = terms.mk_mod(x, three);
    // (= (mod x 3) 1) — mod is an operand of `=`, not of a UF.
    let assertion = terms.mk_eq(modt, one);

    let mut assertions = vec![assertion];
    let changed = purify_mod_div_uf_args(&mut terms, &mut assertions);

    assert!(!changed, "mod not under a UF must not be purified");
    assert_eq!(assertions.len(), 1);
}

/// A SYMBOLIC-divisor `(mod a b)` under a UF is left untouched — it travels a
/// different mod_div_elim path whose SAT machinery the proxy indirection would
/// defeat (the verification-consumer seq/datatype reducer regression). Only constant-divisor
/// mod/div under a UF is purified.
#[test]
fn leaves_symbolic_divisor_mod_under_uf_untouched() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("dividend", Sort::Int);
    let b = terms.mk_var("divisor", Sort::Int);
    let modt = terms.mk_mod(a, b); // symbolic (non-constant) divisor
    let f_mod = terms.mk_app(Symbol::named("f"), [modt], Sort::Int);
    let nine = terms.mk_int(num_bigint::BigInt::from(9));
    let assertion = terms.mk_eq(f_mod, nine);

    let mut assertions = vec![assertion];
    let changed = purify_mod_div_uf_args(&mut terms, &mut assertions);

    assert!(
        !changed,
        "symbolic-divisor mod under a UF must NOT be purified"
    );
    assert_eq!(assertions.len(), 1);
}

/// An opaque Int UF application that is NOT inside arithmetic (a bare EUF
/// equality) is left untouched — LRA already pins it as a slack there, and
/// purifying non-arith positions would needlessly perturb EUF.
#[test]
fn leaves_non_arith_uf_untouched() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let div = terms.mk_app(Symbol::named("__euclid!div"), [a, b], Sort::Int);
    let five = terms.mk_int(num_bigint::BigInt::from(5));
    // (= div 5) — div is a direct operand of `=`, not of an arith operator.
    let assertion = terms.mk_eq(div, five);

    let mut assertions = vec![assertion];
    let changed = purify_int_uf_arith(&mut terms, &mut assertions);

    assert!(!changed, "bare EUF equality operands need no purification");
    assert_eq!(assertions.len(), 1);
}
