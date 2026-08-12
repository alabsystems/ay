// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for the independent ground string/regex refutation checker.
//!
//! The two load-bearing properties:
//!
//! 1. A genuine ground non-membership refutation (`"/mod/forum/"` is not in
//!    `.*\<SCRIPT.*`) is ACCEPTED — this is the QF_S "sink" family.
//! 2. A BOGUS string lemma (a clause with no true ground literal, or one whose
//!    ground evaluation is FALSE) is REJECTED — a forged `string_ground_eval`
//!    step cannot launder an arbitrary claim into a refutation.

use super::*;
use ay_core::{ProofId, Sort, Symbol, TermStore};
use num_bigint::BigInt;

fn str_const(terms: &mut TermStore, s: &str) -> TermId {
    terms.mk_string(s.to_string())
}

fn to_re(terms: &mut TermStore, s: &str) -> TermId {
    let c = str_const(terms, s);
    terms.mk_app(Symbol::named("str.to_re"), [c], Sort::RegLan)
}

fn all_star(terms: &mut TermStore) -> TermId {
    let allchar = terms.mk_app(Symbol::named("re.allchar"), [], Sort::RegLan);
    terms.mk_app(Symbol::named("re.*"), [allchar], Sort::RegLan)
}

fn in_re(terms: &mut TermStore, s: TermId, r: TermId) -> TermId {
    terms.mk_app(Symbol::named("str.in_re"), [s, r], Sort::Bool)
}

/// The exact QF_S `slog_stranger` shape: a sink assertion says a constant is
/// in `.*\<SCRIPT.*`, which it is not.
fn stranger_sink(terms: &mut TermStore, subject: &str) -> TermId {
    let star = all_star(terms);
    let script = to_re(terms, "\\<SCRIPT");
    let tail = terms.mk_app(Symbol::named("re.++"), [script, star], Sort::RegLan);
    let re = terms.mk_app(Symbol::named("re.++"), [star, tail], Sort::RegLan);
    let s = str_const(terms, subject);
    in_re(terms, s, re)
}

#[test]
fn ground_non_membership_refutation_is_accepted() {
    let mut terms = TermStore::new();
    let membership = stranger_sink(&mut terms, "/mod/forum/");
    let refutation = terms.mk_not_raw(membership);

    assert!(
        recognize_string_ground_eval(&terms, &[refutation]),
        "the constant `/mod/forum/` is NOT in `.*\\<SCRIPT.*`, so the negated \
         membership is a ground tautology the checker must recognize"
    );
    validate_string_ground_eval(&terms, ProofId(0), &[refutation])
        .expect("strict validation must accept a true ground refutation");
}

#[test]
fn ground_membership_that_actually_holds_is_not_a_refutation() {
    let mut terms = TermStore::new();
    // `"xx\<SCRIPTyy"` IS in `.*\<SCRIPT.*`, so its NEGATION is false and the
    // checker must refuse to certify it.
    let membership = stranger_sink(&mut terms, "xx\\<SCRIPTyy");
    let refutation = terms.mk_not_raw(membership);

    assert!(
        !recognize_string_ground_eval(&terms, &[refutation]),
        "a FALSE ground literal must not be recognized"
    );
    let err = validate_string_ground_eval(&terms, ProofId(0), &[refutation])
        .expect_err("strict validation must reject a false ground claim");
    assert!(
        format!("{err}").contains("string_ground_eval"),
        "unexpected error: {err}"
    );

    // The positive direction is the true one, and IS certifiable.
    assert!(recognize_string_ground_eval(&terms, &[membership]));
}

#[test]
fn bogus_string_lemma_is_rejected() {
    let mut terms = TermStore::new();
    // A forged lemma: an arbitrary Boolean literal over uninterpreted symbols
    // wearing a string clause as camouflage. The string literal here is a
    // membership that HOLDS, so its (unnegated, non-refuting) presence must
    // not license the arbitrary literal.
    let p = terms.mk_var("p", Sort::Bool);
    let x = terms.mk_var("x", Sort::String);
    let re = to_re(&mut terms, "abc");
    let symbolic = in_re(&mut terms, x, re);
    let clause = vec![p, symbolic];

    assert!(
        !recognize_string_ground_eval(&terms, &clause),
        "a clause whose only string literal is NON-GROUND must not be \
         recognized — the checker cannot evaluate `x`"
    );
    validate_string_ground_eval(&terms, ProofId(0), &clause)
        .expect_err("strict validation must reject a forged string lemma");
}

#[test]
fn bogus_lemma_claiming_a_false_ground_fact_is_rejected() {
    let mut terms = TermStore::new();
    // `(str.in_re "abc" (str.to_re "abc"))` is TRUE, so the forged clause
    // `(cl (not (str.in_re "abc" (str.to_re "abc"))))` is FALSE — accepting it
    // would let a proof derive anything.
    let re = to_re(&mut terms, "abc");
    let s = str_const(&mut terms, "abc");
    let member = in_re(&mut terms, s, re);
    let forged = terms.mk_not_raw(member);

    assert!(!recognize_string_ground_eval(&terms, &[forged]));
    validate_string_ground_eval(&terms, ProofId(0), &[forged])
        .expect_err("a FALSE ground clause must never validate");
}

#[test]
fn empty_and_non_bool_clauses_are_rejected() {
    let mut terms = TermStore::new();
    validate_string_ground_eval(&terms, ProofId(0), &[])
        .expect_err("empty clause must be rejected");
    assert!(!recognize_string_ground_eval(&terms, &[]));

    let s = str_const(&mut terms, "abc");
    validate_string_ground_eval(&terms, ProofId(0), &[s])
        .expect_err("String-sorted literal must be rejected");
    assert!(!recognize_string_ground_eval(&terms, &[s]));
}

#[test]
fn non_string_tautology_is_not_hijacked_into_a_string_kind() {
    let mut terms = TermStore::new();
    let t = terms.mk_bool(true);
    assert!(
        !recognize_string_ground_eval(&terms, &[t]),
        "`(cl true)` has no string content; it must not be labelled a string \
         lemma even though it is trivially true"
    );
}

#[test]
fn regex_operator_semantics_match_smtlib() {
    let mut terms = TermStore::new();
    let a = to_re(&mut terms, "a");
    let b = to_re(&mut terms, "b");

    let cases: Vec<(&str, TermId, &str, bool)> = {
        let star_a = terms.mk_app(Symbol::named("re.*"), [a], Sort::RegLan);
        let plus_a = terms.mk_app(Symbol::named("re.+"), [a], Sort::RegLan);
        let opt_a = terms.mk_app(Symbol::named("re.opt"), [a], Sort::RegLan);
        let union = terms.mk_app(Symbol::named("re.union"), [a, b], Sort::RegLan);
        let inter = terms.mk_app(Symbol::named("re.inter"), [a, b], Sort::RegLan);
        let comp_a = terms.mk_app(Symbol::named("re.comp"), [a], Sort::RegLan);
        let none = terms.mk_app(Symbol::named("re.none"), [], Sort::RegLan);
        let all = terms.mk_app(Symbol::named("re.all"), [], Sort::RegLan);
        let lo = str_const(&mut terms, "a");
        let hi = str_const(&mut terms, "z");
        let range = terms.mk_app(Symbol::named("re.range"), [lo, hi], Sort::RegLan);
        let loop_2_3 = terms.mk_app(Symbol::indexed("re.loop", vec![2, 3]), [a], Sort::RegLan);
        let pow_2 = terms.mk_app(Symbol::indexed("re.^", vec![2]), [a], Sort::RegLan);
        let diff = terms.mk_app(Symbol::named("re.diff"), [range, a], Sort::RegLan);
        vec![
            ("re.* empty", star_a, "", true),
            ("re.* aaa", star_a, "aaa", true),
            ("re.* aab", star_a, "aab", false),
            ("re.+ empty", plus_a, "", false),
            ("re.+ a", plus_a, "a", true),
            ("re.opt empty", opt_a, "", true),
            ("re.opt aa", opt_a, "aa", false),
            ("re.union b", union, "b", true),
            ("re.inter a", inter, "a", false),
            ("re.comp b", comp_a, "b", true),
            ("re.comp a", comp_a, "a", false),
            ("re.none", none, "", false),
            ("re.all", all, "anything", true),
            ("re.range m", range, "m", true),
            ("re.range Z", range, "Z", false),
            ("re.loop 2..3 / a", loop_2_3, "a", false),
            ("re.loop 2..3 / aa", loop_2_3, "aa", true),
            ("re.loop 2..3 / aaaa", loop_2_3, "aaaa", false),
            ("re.^2 / aa", pow_2, "aa", true),
            ("re.^2 / aaa", pow_2, "aaa", false),
            ("re.diff m", diff, "m", true),
            ("re.diff a", diff, "a", false),
        ]
    };

    for (label, re, subject, expected) in cases {
        let s = str_const(&mut terms, subject);
        let atom = in_re(&mut terms, s, re);
        let lit = if expected {
            atom
        } else {
            terms.mk_not_raw(atom)
        };
        assert!(
            recognize_string_ground_eval(&terms, &[lit]),
            "{label}: expected `{subject}` membership == {expected}"
        );
        let opposite = if expected {
            terms.mk_not_raw(atom)
        } else {
            atom
        };
        assert!(
            !recognize_string_ground_eval(&terms, &[opposite]),
            "{label}: the opposite polarity must NOT validate"
        );
    }
}

#[test]
fn indexed_named_string_and_regex_builtins_fail_closed() {
    let mut terms = TermStore::new();
    let hello = str_const(&mut terms, "hello");
    let indexed_len = terms.mk_app(Symbol::indexed("str.len", vec![0]), [hello], Sort::Int);
    let five = terms.mk_int(5.into());
    let forged_length = terms.mk_app(Symbol::named("="), [indexed_len, five], Sort::Bool);
    assert!(!recognize_string_ground_eval(&terms, &[forged_length]));
    validate_string_ground_eval(&terms, ProofId(0), &[forged_length])
        .expect_err("an indexed identifier named `str.len` is not the named string builtin");

    let a = to_re(&mut terms, "a");
    let indexed_star = terms.mk_app(Symbol::indexed("re.*", vec![0]), [a], Sort::RegLan);
    let aaa = str_const(&mut terms, "aaa");
    let forged_regex = in_re(&mut terms, aaa, indexed_star);
    validate_string_ground_eval(&terms, ProofId(0), &[forged_regex])
        .expect_err("an indexed identifier named `re.*` is not the named regex constructor");

    // Control: genuine indexed regex repetition retains its semantics.
    let power = terms.mk_app(Symbol::indexed("re.^", vec![2]), [a], Sort::RegLan);
    let aa = str_const(&mut terms, "aa");
    let genuine_indexed_regex = in_re(&mut terms, aa, power);
    validate_string_ground_eval(&terms, ProofId(0), &[genuine_indexed_regex])
        .expect("the genuine indexed `(_ re.^ 2)` constructor must still evaluate");
}

#[test]
fn ground_string_operations_evaluate() {
    let mut terms = TermStore::new();
    let hello = str_const(&mut terms, "hello");
    let ell = str_const(&mut terms, "ell");

    // (str.contains "hello" "ell") is true.
    let contains = terms.mk_app(Symbol::named("str.contains"), [hello, ell], Sort::Bool);
    assert!(recognize_string_ground_eval(&terms, &[contains]));

    // (= (str.len "hello") 5)
    let len = terms.mk_app(Symbol::named("str.len"), [hello], Sort::Int);
    let five = terms.mk_int(5.into());
    let eq = terms.mk_app(Symbol::named("="), [len, five], Sort::Bool);
    assert!(recognize_string_ground_eval(&terms, &[eq]));

    // (= (str.len "hello") 6) is FALSE.
    let six = terms.mk_int(6.into());
    let bad = terms.mk_app(Symbol::named("="), [len, six], Sort::Bool);
    assert!(!recognize_string_ground_eval(&terms, &[bad]));

    // (= (str.++ "hel" "lo") "hello")
    let hel = str_const(&mut terms, "hel");
    let lo = str_const(&mut terms, "lo");
    let cat = terms.mk_app(Symbol::named("str.++"), [hel, lo], Sort::String);
    let eq_cat = terms.mk_app(Symbol::named("="), [cat, hello], Sort::Bool);
    assert!(recognize_string_ground_eval(&terms, &[eq_cat]));

    // (= (str.indexof "hello" "l" 0) 2)
    let l = str_const(&mut terms, "l");
    let zero = terms.mk_int(0.into());
    let idx = terms.mk_app(Symbol::named("str.indexof"), [hello, l, zero], Sort::Int);
    let two = terms.mk_int(2.into());
    let eq_idx = terms.mk_app(Symbol::named("="), [idx, two], Sort::Bool);
    assert!(recognize_string_ground_eval(&terms, &[eq_idx]));

    // (= (str.replace "hello" "l" "L") "heLlo")
    let big_l = str_const(&mut terms, "L");
    let rep = terms.mk_app(
        Symbol::named("str.replace"),
        [hello, l, big_l],
        Sort::String,
    );
    let he_l_lo = str_const(&mut terms, "heLlo");
    let eq_rep = terms.mk_app(Symbol::named("="), [rep, he_l_lo], Sort::Bool);
    assert!(recognize_string_ground_eval(&terms, &[eq_rep]));

    // (= (str.substr "hello" 1 3) "ell")
    let one = terms.mk_int(1.into());
    let three = terms.mk_int(3.into());
    let sub = terms.mk_app(
        Symbol::named("str.substr"),
        [hello, one, three],
        Sort::String,
    );
    let eq_sub = terms.mk_app(Symbol::named("="), [sub, ell], Sort::Bool);
    assert!(recognize_string_ground_eval(&terms, &[eq_sub]));
}

#[test]
fn replace_all_debits_aggregate_chars_before_output_allocation() {
    let mut terms = TermStore::new();
    let subject = str_const(&mut terms, "aaaaaaaa");
    let needle = str_const(&mut terms, "a");
    let replacement = str_const(&mut terms, "bbbbbbbb");
    let replace_all = terms.mk_app(
        Symbol::named("str.replace_all"),
        [subject, needle, replacement],
        Sort::String,
    );

    let mut eval = GroundEval::new(&terms);
    // Decoding, memoizing, and scratch-cloning the three inputs costs 51
    // chars. The 64-char result would exceed this deliberately small aggregate
    // limit and must fail before `Vec::with_capacity(64)`.
    eval.string_chars_remaining = 100;
    assert!(eval.eval(replace_all).is_none());
}

#[test]
fn cached_string_value_clone_debits_aggregate_chars() {
    let mut terms = TermStore::new();
    let value = str_const(&mut terms, "12345678");
    let mut eval = GroundEval::new(&terms);
    // Initial decoding plus the retained memo clone consumes 16 chars. Only
    // seven remain, so returning another cached eight-char clone must fail.
    eval.string_chars_remaining = 23;
    assert!(eval.eval(value).is_some());
    assert!(eval.eval(value).is_none());
}

#[test]
fn substring_near_miss_exhausts_metered_comparison_work() {
    let terms = TermStore::new();
    let mut eval = GroundEval::new(&terms);
    eval.budget = 100;
    let haystack = vec!['a'; 64];
    let mut needle = vec!['a'; 32];
    needle[31] = 'b';

    assert_eq!(eval.find_sub(&haystack, &needle, 0), None);
}

#[test]
fn large_integer_multiplication_exhausts_numeric_work_before_compute() {
    let mut terms = TermStore::new();
    let operand = (BigInt::from(1_u8) << 2047_usize) + BigInt::from(1_u8);
    let left = terms.mk_int(operand.clone());
    let right = terms.mk_int(operand);
    let product = terms.mk_app(Symbol::named("*"), [left, right], Sort::Int);
    let mut eval = GroundEval::new(&terms);

    // Both operands and their 4096-bit result bound are individually legal,
    // but the checked 2048*2048 multiplication cost exceeds the shared 4M
    // numeric budget and must fail before BigInt multiplication executes.
    assert!(eval.eval(product).is_none());
}

#[test]
fn oversized_decimal_parse_fails_before_bigint_allocation() {
    let mut terms = TermStore::new();
    let digits = str_const(&mut terms, &"9".repeat(MAX_NUMERIC_DECIMAL_DIGITS + 1));
    let to_int = terms.mk_app(Symbol::named("str.to_int"), [digits], Sort::Int);
    let mut eval = GroundEval::new(&terms);

    assert!(eval.eval(to_int).is_none());
}

#[test]
fn regex_split_transitions_consume_work_on_memo_hits() {
    let mut terms = TermStore::new();
    let first = terms.mk_app(Symbol::named("re.none"), [], Sort::RegLan);
    let second = terms.mk_app(Symbol::named("re.none"), [], Sort::RegLan);
    let concat = terms.mk_app(Symbol::named("re.++"), [first, second], Sort::RegLan);
    let mut eval = GroundEval::new(&terms);
    for split in 0..=32 {
        eval.re_memo.insert((first, 0, split), false);
    }
    // The state miss consumes the first unit. Even though every child probe is
    // a memo hit, the first split transition must consume another and fail.
    eval.budget = 1;
    assert_eq!(eval.re_concat(concat, &[first, second], 0, 0, 32), None);
}

#[test]
fn multi_literal_clause_certifies_on_its_true_ground_literal() {
    let mut terms = TermStore::new();
    // The real QF_S lemma shape: `(cl (not (= x "c")) (not (str.in_re "c" R)))`
    // — the first literal is NON-ground (mentions `x`), the second is a true
    // ground refutation. A clause with one true literal is a tautology.
    let x = terms.mk_var("literal_5", Sort::String);
    let c = str_const(&mut terms, "/mod/forum/");
    let eq = terms.mk_app(Symbol::named("="), [x, c], Sort::Bool);
    let not_eq = terms.mk_not_raw(eq);
    let membership = stranger_sink(&mut terms, "/mod/forum/");
    let not_member = terms.mk_not_raw(membership);

    assert!(recognize_string_ground_eval(&terms, &[not_eq, not_member]));
    validate_string_ground_eval(&terms, ProofId(0), &[not_eq, not_member])
        .expect("a clause with a true ground literal is a tautology");

    // Drop the true literal: the remaining clause is NOT a tautology.
    assert!(!recognize_string_ground_eval(&terms, &[not_eq]));
    validate_string_ground_eval(&terms, ProofId(0), &[not_eq])
        .expect_err("a non-ground-only clause must be rejected");
}

/// A user-declarable SPELLING must never receive native string semantics.
///
/// `ay-frontend` owns `str.to_code`: it is in `RESERVED_OP_NAMES`, so
/// `(declare-fun str.to_code (String) Int)` is rejected at elaboration and a
/// surviving application always denotes the native operator. It does NOT own
/// the invented dotted spelling `str.to.code`: that name is in neither
/// `RESERVED_OP_NAMES` nor `EXCLUDED_DECLARABLE_OP_NAMES`, no elaborator arm
/// matches it, and `declaration_requires_private_core_identity` leaves an
/// ordinary declaration holding that exact surface spelling. z3 5.0.0 agrees it
/// is not an operator — `(assert (= (str.to.code "a") 97))` is
/// `(error "unknown constant str.to.code")` — and answers `sat` for
/// `(declare-fun str.to.code (String) Int)` +
/// `(assert (not (= (str.to.code "a") 97)))`.
///
/// This evaluator used to accept four invented spellings (`str.to.code`,
/// `str.from.code`, `str.from.int`, `str.is.digit`) as aliases of the real
/// operators, which made `TheoryLemmaKind::StringGroundEval` a forgery oracle:
/// it certified `(= (str.to.code "a") 97)` as a GROUND TAUTOLOGY about a
/// function the problem had declared uninterpreted. The alias arms are gone;
/// an uninterpreted head is "not ground", so the lemma fails closed.
#[test]
fn invented_dotted_string_spellings_are_not_given_native_semantics() {
    // `(= (<head> "a") 97)` — TRUE for the real `str.to_code`, and a claim
    // about an arbitrary uninterpreted function for the dotted spelling.
    let build_to_code = |head: &str| {
        let mut terms = TermStore::new();
        let argument = str_const(&mut terms, "a");
        let applied = terms.mk_app(Symbol::named(head), [argument], Sort::Int);
        let expected = terms.mk_int(BigInt::from(97));
        let equality = terms.mk_app(Symbol::named("="), [applied, expected], Sort::Bool);
        (terms, equality)
    };
    let (terms, equality) = build_to_code("str.to_code");
    validate_string_ground_eval(&terms, ProofId(0), &[equality])
        .expect("the frontend-owned `str.to_code` must still evaluate");
    let (terms, equality) = build_to_code("str.to.code");
    validate_string_ground_eval(&terms, ProofId(0), &[equality]).expect_err(
        "`str.to.code` is an ordinary user-declarable symbol; certifying a \
         ground tautology about it would launder a wrong `unsat`",
    );

    // `(= (<head> 97) "a")` — TRUE for the real `str.from_code`.
    let build_from_code = |head: &str| {
        let mut terms = TermStore::new();
        let argument = terms.mk_int(BigInt::from(97));
        let applied = terms.mk_app(Symbol::named(head), [argument], Sort::String);
        let expected = str_const(&mut terms, "a");
        let equality = terms.mk_app(Symbol::named("="), [applied, expected], Sort::Bool);
        (terms, equality)
    };
    let (terms, equality) = build_from_code("str.from_code");
    validate_string_ground_eval(&terms, ProofId(0), &[equality])
        .expect("the frontend-owned `str.from_code` must still evaluate");
    let (terms, equality) = build_from_code("str.from.code");
    validate_string_ground_eval(&terms, ProofId(0), &[equality])
        .expect_err("`str.from.code` is an ordinary user-declarable symbol");

    // `(= (<head> 97) "97")` — TRUE for the real `str.from_int`.
    let build_from_int = |head: &str| {
        let mut terms = TermStore::new();
        let argument = terms.mk_int(BigInt::from(97));
        let applied = terms.mk_app(Symbol::named(head), [argument], Sort::String);
        let expected = str_const(&mut terms, "97");
        let equality = terms.mk_app(Symbol::named("="), [applied, expected], Sort::Bool);
        (terms, equality)
    };
    let (terms, equality) = build_from_int("str.from_int");
    validate_string_ground_eval(&terms, ProofId(0), &[equality])
        .expect("the frontend-owned `str.from_int` must still evaluate");
    let (terms, equality) = build_from_int("str.from.int");
    validate_string_ground_eval(&terms, ProofId(0), &[equality])
        .expect_err("`str.from.int` is an ordinary user-declarable symbol");

    // `(<head> "9")` — TRUE for the real `str.is_digit`.
    let build_is_digit = |head: &str| {
        let mut terms = TermStore::new();
        let argument = str_const(&mut terms, "9");
        let applied = terms.mk_app(Symbol::named(head), [argument], Sort::Bool);
        (terms, applied)
    };
    let (terms, applied) = build_is_digit("str.is_digit");
    validate_string_ground_eval(&terms, ProofId(0), &[applied])
        .expect("the frontend-owned `str.is_digit` must still evaluate");
    let (terms, applied) = build_is_digit("str.is.digit");
    validate_string_ground_eval(&terms, ProofId(0), &[applied])
        .expect_err("`str.is.digit` is an ordinary user-declarable symbol");
}
