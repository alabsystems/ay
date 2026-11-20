// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn sequence() -> Sort {
    Sort::seq(Sort::Int)
}
fn cat(terms: &mut TermStore, left: TermId, right: TermId) -> TermId {
    terms.mk_app(Symbol::named("seq.++"), [left, right], sequence())
}
fn eq(terms: &mut TermStore, left: TermId, right: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [left, right], Sort::Bool)
}

#[test]
fn seq_ground_symbolic_word_identities_preserve_order_and_multiplicity() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", sequence());
    let b = terms.mk_var("b", sequence());
    let c = terms.mk_var("c", sequence());
    let empty = terms.mk_app(Symbol::named("seq.empty"), [], sequence());
    let ab = cat(&mut terms, a, b);
    let left = cat(&mut terms, ab, c);
    let bc = cat(&mut terms, b, c);
    let right = cat(&mut terms, a, bc);
    let law = eq(&mut terms, left, right);
    assert!(recognize_seq_ground_eval(&terms, &[law]));
    let unary = terms.mk_app(Symbol::named("seq.++"), [a], sequence());
    let unary_law = eq(&mut terms, unary, a);
    assert!(recognize_seq_ground_eval(&terms, &[unary_law]));
    for (left, right) in [(empty, a), (a, empty)] {
        let word = cat(&mut terms, left, right);
        let law = eq(&mut terms, word, a);
        assert!(recognize_seq_ground_eval(&terms, &[law]));
    }
    let ba = cat(&mut terms, b, a);
    let commute = eq(&mut terms, ab, ba);
    assert!(!recognize_seq_ground_eval(&terms, &[commute]));
    let aa = cat(&mut terms, a, a);
    let duplicate = eq(&mut terms, aa, a);
    assert!(!recognize_seq_ground_eval(&terms, &[duplicate]));
    let negative = terms.mk_not_raw(law);
    assert!(!recognize_seq_ground_eval(&terms, &[negative]));
}

#[test]
fn seq_ground_units_keep_exact_elements_and_opaque_chunks() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", sequence());
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let ux = terms.mk_app(Symbol::named("seq.unit"), [x], sequence());
    let uy = terms.mk_app(Symbol::named("seq.unit"), [y], sequence());
    let empty = terms.mk_app(Symbol::named("seq.empty"), [], sequence());
    let ex = cat(&mut terms, empty, ux);
    let left = cat(&mut terms, a, ex);
    let right = cat(&mut terms, a, ux);
    let law = eq(&mut terms, left, right);
    assert!(recognize_seq_ground_eval(&terms, &[law]));
    let other = cat(&mut terms, a, uy);
    let unequal = eq(&mut terms, left, other);
    assert!(!recognize_seq_ground_eval(&terms, &[unequal]));
    let opaque = eq(&mut terms, a, ux);
    assert!(!recognize_seq_ground_eval(&terms, &[opaque]));
}

#[test]
fn seq_ground_anchored_rewrite_requires_the_same_anchor() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", sequence());
    let b = terms.mk_var("b", sequence());
    let empty = terms.mk_app(Symbol::named("seq.empty"), [], sequence());
    let left = cat(&mut terms, empty, a);
    let premise = eq(&mut terms, b, left);
    let negative = terms.mk_not_raw(premise);
    let conclusion = eq(&mut terms, b, a);
    assert!(recognize_seq_ground_eval(&terms, &[negative, conclusion]));
    let c = terms.mk_var("c", sequence());
    let unrelated = eq(&mut terms, c, a);
    assert!(!recognize_seq_ground_eval(&terms, &[negative, unrelated]));
}

#[test]
fn seq_ground_packed_clause_requires_native_typed_disjunction() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", sequence());
    let anchor = terms.mk_var("anchor", sequence());
    let empty = terms.mk_app(Symbol::named("seq.empty"), [], sequence());
    let left = cat(&mut terms, empty, a);
    let premise = eq(&mut terms, anchor, left);
    let negative = terms.mk_not_raw(premise);
    let conclusion = eq(&mut terms, anchor, a);
    let packed = terms.mk_app(Symbol::named("or"), [negative, conclusion], Sort::Bool);
    assert!(recognize_seq_ground_eval(&terms, &[packed]));
    let mut ordinary = terms.clone();
    ordinary.register_declared_function("or");
    assert!(
        !recognize_seq_ground_eval(&ordinary, &[packed]),
        "an ordinary Boolean function may return false even for this valid disjunction"
    );
    let malformed = terms.mk_app_structural(Symbol::named("or"), [negative, conclusion], Sort::Int);
    assert!(!recognize_seq_ground_eval(&terms, &[malformed]));
}

#[test]
fn seq_ground_word_identity_rejects_malformed_sorts_arities_and_slots() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", sequence());
    let invalid = terms.mk_app(Symbol::named("seq.++"), [], sequence());
    let law = eq(&mut terms, invalid, a);
    assert!(!recognize_seq_ground_eval(&terms, &[law]));
    let value = terms.mk_bool(true);
    let invalid = terms.mk_app(Symbol::named("seq.unit"), [value], sequence());
    let law = eq(&mut terms, invalid, invalid);
    assert!(!recognize_seq_ground_eval(&terms, &[law]));
    let ints = terms.mk_app(Symbol::named("seq.empty"), [], sequence());
    let booleans = terms.mk_app(Symbol::named("seq.empty"), [], Sort::seq(Sort::Bool));
    let law = eq(&mut terms, ints, booleans);
    assert!(!recognize_seq_ground_eval(&terms, &[law]));
    assert!(!recognize_seq_ground_eval(&terms, &[TermId::new(u32::MAX)]));
}

#[test]
fn seq_ground_word_normalization_bounds_cycles_and_wide_pending_frontiers() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", sequence());
    let future = TermId::new(u32::try_from(terms.len()).unwrap());
    let cycle = terms.mk_app_structural(Symbol::named("seq.++"), [future, a], sequence());
    assert_eq!(future, cycle);
    let law = eq(&mut terms, cycle, cycle);
    assert!(!recognize_seq_ground_eval(&terms, &[law]));
    let wide = terms.mk_app_structural(
        Symbol::named("seq.++"),
        vec![a; MAX_NORMALIZATION_NODES + 1],
        sequence(),
    );
    let law = eq(&mut terms, wide, wide);
    assert!(!recognize_seq_ground_eval(&terms, &[law]));
}

fn len(terms: &mut TermStore, sequence: TermId) -> TermId {
    terms.mk_app(Symbol::named("seq.len"), [sequence], Sort::Int)
}

fn member(terms: &mut TermStore, sequence: TermId, needle: TermId) -> TermId {
    terms.mk_app(
        Symbol::named("seq.contains"),
        [sequence, needle],
        Sort::Bool,
    )
}

#[test]
fn seq_ground_lengths_keep_nonnegative_chunks_and_exact_multiplicities() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", sequence());
    let b = terms.mk_var("b", sequence());
    let x = terms.mk_var("x", Sort::Int);
    let unit = terms.mk_app(Symbol::named("seq.unit"), [x], sequence());
    let word = cat(&mut terms, a, unit);
    let word_len = len(&mut terms, word);
    let a_len = len(&mut terms, a);
    let b_len = len(&mut terms, b);
    let one = terms.mk_int(1.into());
    let zero = terms.mk_int(0.into());
    let sum = terms.mk_app(Symbol::named("+"), [one, a_len], Sort::Int);
    let law = eq(&mut terms, word_len, sum);
    assert!(recognize_seq_ground_eval(&terms, &[law]));
    let wrong_sum = terms.mk_app(Symbol::named("+"), [one, b_len], Sort::Int);
    let wrong = eq(&mut terms, word_len, wrong_sum);
    assert!(!recognize_seq_ground_eval(&terms, &[wrong]));
    let nonnegative = terms.mk_app(Symbol::named("<="), [zero, a_len], Sort::Bool);
    assert!(recognize_seq_ground_eval(&terms, &[nonnegative]));
    let not_negative = terms.mk_app(Symbol::named("<"), [a_len, zero], Sort::Bool);
    let not_negative = terms.mk_not_raw(not_negative);
    assert!(recognize_seq_ground_eval(&terms, &[not_negative]));
    let strictly_positive = terms.mk_app(Symbol::named("<"), [zero, a_len], Sort::Bool);
    assert!(!recognize_seq_ground_eval(&terms, &[strictly_positive]));
    let too_large = terms.mk_app(Symbol::named("<="), [one, a_len], Sort::Bool);
    assert!(!recognize_seq_ground_eval(&terms, &[too_large]));
    let two = terms.mk_int(2.into());
    let malformed = terms.mk_app(Symbol::named("seq.len"), [unit, unit], Sort::Int);
    let wrong = eq(&mut terms, malformed, two);
    assert!(!recognize_seq_ground_eval(&terms, &[wrong]));
}

#[test]
fn seq_ground_membership_requires_the_same_prefix_element_and_singleton_needle() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", sequence());
    let b = terms.mk_var("b", sequence());
    let x = terms.mk_var("x", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let u = terms.mk_var("u", Sort::Int);
    let ux = terms.mk_app(Symbol::named("seq.unit"), [x], sequence());
    let uv = terms.mk_app(Symbol::named("seq.unit"), [v], sequence());
    let uu = terms.mk_app(Symbol::named("seq.unit"), [u], sequence());
    let word = cat(&mut terms, a, uv);
    let whole = member(&mut terms, word, ux);
    let prefix = member(&mut terms, a, ux);
    let element = eq(&mut terms, x, v);
    let disjunction = terms.mk_app(Symbol::named("or"), [prefix, element], Sort::Bool);
    let law = eq(&mut terms, disjunction, whole);
    assert!(recognize_seq_ground_eval(&terms, &[law]));
    let wrong_element = eq(&mut terms, x, u);
    let disjunction = terms.mk_app(Symbol::named("or"), [prefix, wrong_element], Sort::Bool);
    let wrong = eq(&mut terms, whole, disjunction);
    assert!(!recognize_seq_ground_eval(&terms, &[wrong]));
    let wrong_prefix = member(&mut terms, b, ux);
    let disjunction = terms.mk_app(Symbol::named("or"), [wrong_prefix, element], Sort::Bool);
    let wrong = eq(&mut terms, whole, disjunction);
    assert!(!recognize_seq_ground_eval(&terms, &[wrong]));
    let long_needle = cat(&mut terms, ux, uu);
    let whole = member(&mut terms, word, long_needle);
    let prefix = member(&mut terms, a, long_needle);
    let disjunction = terms.mk_app(Symbol::named("or"), [prefix, element], Sort::Bool);
    let wrong = eq(&mut terms, whole, disjunction);
    assert!(!recognize_seq_ground_eval(&terms, &[wrong]));
    let empty = terms.mk_app(Symbol::named("seq.empty"), [], sequence());
    let empty_contains_unit = member(&mut terms, empty, ux);
    let empty_law = terms.mk_not_raw(empty_contains_unit);
    assert!(recognize_seq_ground_eval(&terms, &[empty_law]));
    let empty_contains_empty = member(&mut terms, empty, empty);
    let wrong = terms.mk_not_raw(empty_contains_empty);
    assert!(!recognize_seq_ground_eval(&terms, &[wrong]));
}

#[test]
fn seq_ground_conjunction_requires_every_member_and_bounds_boolean_cycles() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", sequence());
    let zero = terms.mk_int(0.into());
    let a_len = len(&mut terms, a);
    let nonnegative = terms.mk_app(Symbol::named("<="), [zero, a_len], Sort::Bool);
    let empty = terms.mk_app(Symbol::named("seq.empty"), [], sequence());
    let left = cat(&mut terms, empty, a);
    let identity = eq(&mut terms, left, a);
    let conjunction = terms.mk_app(Symbol::named("and"), [identity, nonnegative], Sort::Bool);
    assert!(recognize_seq_ground_eval(&terms, &[conjunction]));
    let contradiction = terms.mk_bool(false);
    for parts in [[identity, contradiction], [contradiction, identity]] {
        let wrong = terms.mk_app(Symbol::named("and"), parts, Sort::Bool);
        assert!(!recognize_seq_ground_eval(&terms, &[wrong]));
    }
    let invalid = terms.mk_app(Symbol::named("and"), [identity, zero], Sort::Bool);
    assert!(!recognize_seq_ground_eval(&terms, &[invalid]));
    let future = TermId::new(u32::try_from(terms.len()).unwrap());
    let cycle = terms.mk_app_structural(Symbol::named("and"), [future, identity], Sort::Bool);
    assert_eq!(cycle, future);
    assert!(!recognize_seq_ground_eval(&terms, &[cycle]));
}

#[test]
fn seq_ground_original_progress_refusal_is_sticky_through_every_recognition_alternative() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", sequence());
    let empty = terms.mk_app(Symbol::named("seq.empty"), [], sequence());
    let word = cat(&mut terms, a, empty);
    let theorem = eq(&mut terms, word, a);
    let mut calls = 0;
    let mut total_work = 0usize;
    let mut total_bytes = 0usize;
    assert!(recognize_seq_ground_eval_with_progress(
        &terms,
        &[theorem],
        &mut |work, bytes| {
            calls += 1;
            total_work += work;
            total_bytes += bytes;
            true
        }
    ));
    assert!(total_work > 0 && total_bytes > 0);
    assert!(
        total_work < 20_000,
        "an identity must pay its actual small traversal"
    );
    for refusal in 0..calls {
        let mut current = 0;
        assert!(
            !recognize_seq_ground_eval_with_progress(&terms, &[theorem], &mut |_, _| {
                let admitted = current != refusal;
                current += 1;
                admitted
            }),
            "refusal at callback {refusal} must not be reset by another matcher"
        );
    }
    let mut remaining = total_work - 1;
    assert!(!recognize_seq_ground_eval_with_progress(
        &terms,
        &[theorem],
        &mut |work, _| {
            if let Some(next) = remaining.checked_sub(work) {
                remaining = next;
                true
            } else {
                false
            }
        }
    ));
}

#[test]
fn seq_ground_kernel_keeps_registered_same_spelled_user_functions_opaque() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", sequence());
    let x = terms.mk_var("x", Sort::Int);
    let unit = terms.mk_app(Symbol::named("seq.unit"), [x], sequence());
    let empty = terms.mk_app(Symbol::named("seq.empty"), [], sequence());
    let identity_word = cat(&mut terms, empty, a);
    let identity = eq(&mut terms, identity_word, a);
    let word = cat(&mut terms, a, unit);
    let word_len = len(&mut terms, word);
    let a_len = len(&mut terms, a);
    let one = terms.mk_int(1.into());
    let sum = terms.mk_app(Symbol::named("+"), [a_len, one], Sort::Int);
    let length = eq(&mut terms, word_len, sum);
    let zero = terms.mk_int(0.into());
    let nonnegative = terms.mk_app(Symbol::named("<="), [zero, a_len], Sort::Bool);
    let conjunction = terms.mk_app(Symbol::named("and"), [identity, nonnegative], Sort::Bool);
    for (operator, theorem) in [
        ("seq.empty", identity),
        ("seq.++", identity),
        ("=", identity),
        ("seq.unit", length),
        ("seq.len", length),
        ("+", length),
        ("<=", nonnegative),
        ("and", conjunction),
    ] {
        assert!(recognize_seq_ground_eval(&terms, &[theorem]));
        let mut ordinary = terms.clone();
        ordinary.register_declared_function(operator);
        assert!(
            !recognize_seq_ground_eval(&ordinary, &[theorem]),
            "ordinary {operator} cannot inherit builtin semantics"
        );
    }
    let v = terms.mk_var("v", Sort::Int);
    let appended = terms.mk_app(Symbol::named("seq.unit"), [v], sequence());
    let member_word = cat(&mut terms, a, appended);
    let whole = member(&mut terms, member_word, unit);
    let prefix = member(&mut terms, a, unit);
    let equal = eq(&mut terms, x, v);
    let disjunction = terms.mk_app(Symbol::named("or"), [prefix, equal], Sort::Bool);
    let theorem = eq(&mut terms, whole, disjunction);
    for operator in ["seq.contains", "or"] {
        assert!(recognize_seq_ground_eval(&terms, &[theorem]));
        let mut ordinary = terms.clone();
        ordinary.register_declared_function(operator);
        assert!(!recognize_seq_ground_eval(&ordinary, &[theorem]));
    }
}

#[test]
fn seq_ground_actual_strict_dispatch_uses_the_original_progress_callback() {
    use ay_core::{Proof, TheoryLemmaKind};
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", sequence());
    let empty = terms.mk_app(Symbol::named("seq.empty"), [], sequence());
    let word = cat(&mut terms, empty, a);
    let theorem = eq(&mut terms, word, a);
    let mut proof = Proof::new();
    let lemma =
        proof.add_theory_lemma_with_kind("SEQ", vec![theorem], TheoryLemmaKind::SeqGroundEval);
    let original = terms.mk_not_raw(theorem);
    let assumption = proof.add_assume(original, None);
    proof.add_resolution(Vec::new(), theorem, lemma, assumption);
    let quality = crate::check_proof_strict_with_context_and_progress(
        &proof,
        &terms,
        None,
        None,
        Some(&[original]),
        &mut |_, _| true,
    )
    .unwrap();
    assert!(quality.is_complete());
    let mut callbacks = 0;
    let mut refuse = |_: usize, _: usize| {
        callbacks += 1;
        false
    };
    let mut validation = super::super::TheoryLemmaValidation {
        terms: &terms,
        step_id: ProofId(0),
        clause: &[theorem],
        farkas: None,
        lia_ann: None,
        dt_decls: None,
        ctor_selectors: None,
        datatype_member_signatures: None,
        ext_diff: None,
        empty_sets: None,
        progress: &mut refuse,
    };
    let rejected = super::super::validate_theory_ground_and_words(
        &mut validation,
        TheoryLemmaKind::SeqGroundEval,
    );
    assert_eq!(rejected.unwrap_err(), ProofCheckError::ResourceLimit);
    assert_eq!(
        callbacks, 1,
        "do not call an original owner again after refusal"
    );
}
