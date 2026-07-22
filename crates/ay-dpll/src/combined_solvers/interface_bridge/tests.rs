// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{Sort, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;

// --- Real-sorted term tests (requested by W4:1967 / #4906) ---

#[test]
fn test_is_arith_evaluable_real_var() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    assert!(is_arith_evaluable(&terms, x));
}

#[test]
fn test_is_arith_evaluable_rational_const() {
    let mut terms = TermStore::new();
    let half = terms.mk_rational(BigRational::new(BigInt::from(1), BigInt::from(2)));
    assert!(is_arith_evaluable(&terms, half));
}

#[test]
fn test_is_arith_evaluable_real_ite() {
    let mut terms = TermStore::new();
    let cond = terms.mk_var("b", Sort::Bool);
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let ite = terms.mk_ite(cond, x, y);
    assert!(is_arith_evaluable(&terms, ite));
}

#[test]
fn test_is_arith_evaluable_real_uf_app() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    // UF application "f" with Real return sort
    let f_x = terms.mk_app(Symbol::named("f"), vec![x], Sort::Real);
    assert!(is_arith_evaluable(&terms, f_x));
}

#[test]
fn test_is_arith_evaluable_real_add() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let sum = terms.mk_add(vec![x, y]);
    assert!(is_arith_evaluable(&terms, sum));
}

// --- Int-sorted term tests (baseline) ---

#[test]
fn test_is_arith_evaluable_int_var() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    assert!(is_arith_evaluable(&terms, x));
}

#[test]
fn test_is_arith_evaluable_int_const() {
    let mut terms = TermStore::new();
    let five = terms.mk_int(BigInt::from(5));
    assert!(is_arith_evaluable(&terms, five));
}

#[test]
fn test_is_arith_evaluable_int_uf_app() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let f_x = terms.mk_app(Symbol::named("f"), vec![x], Sort::Int);
    assert!(is_arith_evaluable(&terms, f_x));
}

// --- Negative cases ---

#[test]
fn test_is_arith_evaluable_bool_var_rejected() {
    let mut terms = TermStore::new();
    let b = terms.mk_var("b", Sort::Bool);
    assert!(!is_arith_evaluable(&terms, b));
}

#[test]
fn test_is_arith_evaluable_bool_const_rejected() {
    let mut terms = TermStore::new();
    let t = terms.mk_bool(true);
    assert!(!is_arith_evaluable(&terms, t));
}

#[test]
fn test_is_arith_evaluable_bv_var_rejected() {
    let mut terms = TermStore::new();
    let bv = terms.mk_var("bv", Sort::bitvec(32));
    assert!(!is_arith_evaluable(&terms, bv));
}

#[test]
fn test_is_arith_evaluable_builtin_op_not_evaluable() {
    // Builtin boolean ops like "and" with Int sort should NOT be evaluable
    // because they are in BUILTIN_OPS but are not arithmetic ops
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    // "=" is a builtin op, so a UF-like application with name "=" should not
    // be treated as evaluable via the UF fallback path
    let eq_app = terms.mk_app(Symbol::named("="), vec![x], Sort::Int);
    assert!(!is_arith_evaluable(&terms, eq_app));
}

#[test]
fn test_is_arith_evaluable_uf_with_bool_sort_rejected() {
    // UF with Bool return sort should NOT be evaluable
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let p_x = terms.mk_app(Symbol::named("P"), vec![x], Sort::Bool);
    assert!(!is_arith_evaluable(&terms, p_x));
}

// --- collect_int_constants tests (#5970 coverage gap) ---

#[test]
fn test_collect_int_constants_registers_bare_constant() {
    let mut terms = TermStore::new();
    let five = terms.mk_int(BigInt::from(5));
    let mut bridge = InterfaceBridge::new();
    bridge.collect_int_constants(&terms, five);
    assert_eq!(bridge.int_const_terms.get(&BigInt::from(5)), Some(&five));
}

#[test]
fn test_collect_int_constants_traverses_app_children() {
    // Use a UF application f(3, 7) to prevent constant folding (mk_add would fold).
    let mut terms = TermStore::new();
    let three = terms.mk_int(BigInt::from(3));
    let seven = terms.mk_int(BigInt::from(7));
    let f_app = terms.mk_app(Symbol::named("f"), vec![three, seven], Sort::Int);
    let mut bridge = InterfaceBridge::new();
    bridge.collect_int_constants(&terms, f_app);
    assert_eq!(bridge.int_const_terms.get(&BigInt::from(3)), Some(&three));
    assert_eq!(bridge.int_const_terms.get(&BigInt::from(7)), Some(&seven));
}

#[test]
fn test_collect_int_constants_deduplicates_shared_dag_subterms() {
    // Build a DAG where the same constant TermId appears in multiple branches.
    // The visited set should prevent duplicate trail entries.
    let mut terms = TermStore::new();
    let two = terms.mk_int(BigInt::from(2));
    // f(2, 2) — same TermId arg appears twice (UF avoids constant folding)
    let f_app = terms.mk_app(Symbol::named("f"), vec![two, two], Sort::Int);
    let mut bridge = InterfaceBridge::new();
    bridge.collect_int_constants(&terms, f_app);
    assert_eq!(bridge.int_const_terms.len(), 1);
    // Trail should have exactly 1 ConstTerm entry (not 2)
    let const_entries = bridge
        .interface_trail
        .iter()
        .filter(|e| matches!(e, InterfaceTrailEntry::ConstTerm(_)))
        .count();
    assert_eq!(const_entries, 1);
}

#[test]
fn test_collect_int_constants_traverses_ite() {
    let mut terms = TermStore::new();
    let cond = terms.mk_var("b", Sort::Bool);
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let ite = terms.mk_ite(cond, one, two);
    let mut bridge = InterfaceBridge::new();
    bridge.collect_int_constants(&terms, ite);
    assert_eq!(bridge.int_const_terms.len(), 2);
    assert!(bridge.int_const_terms.contains_key(&BigInt::from(1)));
    assert!(bridge.int_const_terms.contains_key(&BigInt::from(2)));
}

#[test]
fn test_collect_real_constants_registers_rational_constant() {
    let mut terms = TermStore::new();
    let half = terms.mk_rational(BigRational::new(BigInt::from(1), BigInt::from(2)));
    let mut bridge = InterfaceBridge::new();
    bridge.collect_real_constants(&terms, half);
    assert_eq!(
        bridge
            .real_const_terms
            .get(&BigRational::new(BigInt::from(1), BigInt::from(2))),
        Some(&half)
    );
}

#[test]
fn test_collect_real_constants_promotes_int_constants_in_real_ite() {
    let mut terms = TermStore::new();
    let cond = terms.mk_var("b", Sort::Bool);
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let ite = terms.mk_ite(cond, one, two);
    let mut bridge = InterfaceBridge::new();
    bridge.collect_real_constants(&terms, ite);
    assert_eq!(bridge.real_const_terms.len(), 2);
    assert_eq!(
        bridge
            .real_const_terms
            .get(&BigRational::from(BigInt::from(1))),
        Some(&one)
    );
    assert_eq!(
        bridge
            .real_const_terms
            .get(&BigRational::from(BigInt::from(2))),
        Some(&two)
    );
}

// --- evaluate_and_propagate tests (#5970 coverage gap) ---

use ay_core::TheoryLit;

/// Helper: set up a bridge with one interface arith term and one int constant,
/// then call evaluate_and_propagate with a closure that returns the given value.
fn setup_and_propagate(
    terms: &TermStore,
    arith_term: TermId,
    const_term: TermId,
    const_value: BigInt,
    eval_value: Option<BigInt>,
    reasons: Vec<TheoryLit>,
) -> (Vec<ay_core::DiscoveredEquality>, Vec<(TermId, TermId)>) {
    let mut bridge = InterfaceBridge::new();
    bridge.interface_arith_terms.insert(arith_term);
    bridge.int_const_terms.insert(const_value, const_term);
    let get_value = |_tid: TermId| -> Option<(BigInt, Vec<TheoryLit>)> {
        eval_value.clone().map(|v| (v, reasons.clone()))
    };
    bridge.evaluate_and_propagate(terms, &get_value, false, "test")
}

fn setup_and_propagate_real(
    terms: &TermStore,
    arith_term: TermId,
    const_term: TermId,
    const_value: BigRational,
    eval_value: Option<BigRational>,
    reasons: Vec<TheoryLit>,
) -> (Vec<ay_core::DiscoveredEquality>, Vec<(TermId, TermId)>) {
    let mut bridge = InterfaceBridge::new();
    bridge.interface_arith_terms.insert(arith_term);
    bridge.real_const_terms.insert(const_value, const_term);
    let get_value = |_tid: TermId| -> Option<(BigRational, Vec<TheoryLit>)> {
        eval_value.clone().map(|v| (v, reasons.clone()))
    };
    bridge.evaluate_and_propagate_real(terms, &get_value, false, "test")
}

#[test]
fn test_evaluate_and_propagate_basic_equality() {
    // arith_term evaluates to 5, const_term for 5 exists → equality returned.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five_const = terms.mk_int(BigInt::from(5));
    let reason = TheoryLit::new(terms.mk_bool(true), true);
    let (eqs, specs) = setup_and_propagate(
        &terms,
        x,
        five_const,
        BigInt::from(5),
        Some(BigInt::from(5)),
        vec![reason],
    );
    assert_eq!(eqs.len(), 1);
    assert_eq!(eqs[0].lhs, x);
    assert_eq!(eqs[0].rhs, five_const);
    assert_eq!(specs.len(), 0);
}

#[test]
fn test_evaluate_and_propagate_no_match_returns_empty() {
    // arith_term evaluates to 3, but only constant 5 registered → no equality.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five_const = terms.mk_int(BigInt::from(5));
    let reason = TheoryLit::new(TermId(100), true);
    let (eqs, specs) = setup_and_propagate(
        &terms,
        x,
        five_const,
        BigInt::from(5),
        Some(BigInt::from(3)),
        vec![reason],
    );
    assert_eq!(eqs.len(), 0);
    assert_eq!(specs.len(), 0);
}

#[test]
fn test_evaluate_and_propagate_skips_self_equality() {
    // When arith_term IS the constant term itself, skip (trivial self-equality).
    let mut terms = TermStore::new();
    let five = terms.mk_int(BigInt::from(5));
    let reason = TheoryLit::new(TermId(100), true);
    // Use five as BOTH arith_term and const_term
    let (eqs, specs) = setup_and_propagate(
        &terms,
        five,
        five,
        BigInt::from(5),
        Some(BigInt::from(5)),
        vec![reason],
    );
    assert_eq!(eqs.len(), 0, "self-equality should be skipped");
    assert_eq!(specs.len(), 0);
}

#[test]
fn test_evaluate_and_propagate_empty_reasons_yields_speculative_pair() {
    // #6846: Empty reasons → speculative pair, not a committed equality.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five_const = terms.mk_int(BigInt::from(5));
    let (eqs, specs) = setup_and_propagate(
        &terms,
        x,
        five_const,
        BigInt::from(5),
        Some(BigInt::from(5)),
        vec![], // empty reasons
    );
    assert_eq!(
        eqs.len(),
        0,
        "empty reasons should not produce committed equality"
    );
    assert_eq!(specs.len(), 1, "should produce speculative pair");
    assert_eq!(specs[0], (x, five_const));
}

#[test]
fn test_evaluate_and_propagate_contradictory_value_guard() {
    // #6846: If an arith_term was previously propagated with const_A but now
    // evaluates to const_B, skip to prevent EUF from deriving const_A = const_B.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero_const = terms.mk_int(BigInt::from(0));
    let ten_const = terms.mk_int(BigInt::from(10));
    let reason = TheoryLit::new(terms.mk_bool(true), true);

    let mut bridge = InterfaceBridge::new();
    bridge.interface_arith_terms.insert(x);
    bridge.int_const_terms.insert(BigInt::from(0), zero_const);
    bridge.int_const_terms.insert(BigInt::from(10), ten_const);

    // First propagation: x = 0
    let get_zero = |_: TermId| Some((BigInt::from(0), vec![reason]));
    let (eqs1, _) = bridge.evaluate_and_propagate(&terms, &get_zero, false, "test");
    assert_eq!(eqs1.len(), 1, "first propagation should succeed");

    // Second propagation: x now evaluates to 10 (model changed)
    let get_ten = |_: TermId| Some((BigInt::from(10), vec![reason]));
    let (eqs2, _) = bridge.evaluate_and_propagate(&terms, &get_ten, false, "test");
    assert_eq!(eqs2.len(), 0, "contradictory value should be suppressed");
}

#[test]
fn test_evaluate_and_propagate_deduplicates_same_equality() {
    // Same (arith_term, const_term) pair should only be returned once.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five_const = terms.mk_int(BigInt::from(5));
    let reason = TheoryLit::new(terms.mk_bool(true), true);

    let mut bridge = InterfaceBridge::new();
    bridge.interface_arith_terms.insert(x);
    bridge.int_const_terms.insert(BigInt::from(5), five_const);

    let get_value = |_: TermId| Some((BigInt::from(5), vec![reason]));

    let (eqs1, _) = bridge.evaluate_and_propagate(&terms, &get_value, false, "test");
    assert_eq!(eqs1.len(), 1, "first call returns equality");

    let (eqs2, _) = bridge.evaluate_and_propagate(&terms, &get_value, false, "test");
    assert_eq!(eqs2.len(), 0, "second call deduplicates");
}

#[test]
fn test_evaluate_and_propagate_deduplicates_reasons_by_term() {
    // Reasons with duplicate term IDs should be deduplicated.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five_const = terms.mk_int(BigInt::from(5));
    let reason_a = TheoryLit::new(TermId(50), true);
    let reason_a_dup = TheoryLit::new(TermId(50), false); // same term, different polarity

    let mut bridge = InterfaceBridge::new();
    bridge.interface_arith_terms.insert(x);
    bridge.int_const_terms.insert(BigInt::from(5), five_const);

    let reasons = vec![reason_a, reason_a_dup];
    let get_value = move |_: TermId| Some((BigInt::from(5), reasons.clone()));

    let (eqs, _) = bridge.evaluate_and_propagate(&terms, &get_value, false, "test");
    assert_eq!(eqs.len(), 1);
    // After dedup_by_key on term, should have only 1 reason
    assert_eq!(
        eqs[0].reason.len(),
        1,
        "duplicate reasons should be deduplicated by term"
    );
}

#[test]
fn test_evaluate_and_propagate_unevaluable_term_returns_empty() {
    // If the evaluation closure returns None, no equality is produced.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five_const = terms.mk_int(BigInt::from(5));

    let (eqs, specs) = setup_and_propagate(
        &terms,
        x,
        five_const,
        BigInt::from(5),
        None, // unevaluable
        vec![],
    );
    assert_eq!(eqs.len(), 0);
    assert_eq!(specs.len(), 0);
}

#[test]
fn test_evaluate_and_propagate_real_basic_equality() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let half = BigRational::new(BigInt::from(1), BigInt::from(2));
    let half_const = terms.mk_rational(half.clone());
    let reason = TheoryLit::new(terms.mk_bool(true), true);

    let (eqs, specs) = setup_and_propagate_real(
        &terms,
        x,
        half_const,
        half.clone(),
        Some(half),
        vec![reason],
    );

    assert_eq!(eqs.len(), 1);
    assert_eq!(eqs[0].lhs, x);
    assert_eq!(eqs[0].rhs, half_const);
    assert_eq!(specs.len(), 0);
}

#[test]
fn test_evaluate_and_propagate_real_filters_non_bool_reasons_to_speculative_pair() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let half = BigRational::new(BigInt::from(1), BigInt::from(2));
    let half_const = terms.mk_rational(half.clone());
    let non_bool_reason = TheoryLit::new(x, true);

    let (eqs, specs) = setup_and_propagate_real(
        &terms,
        x,
        half_const,
        half.clone(),
        Some(half),
        vec![non_bool_reason],
    );

    assert_eq!(
        eqs.len(),
        0,
        "non-Boolean reasons should be filtered before emitting real equalities"
    );
    assert_eq!(
        specs,
        vec![(x, half_const)],
        "filtered-away reasons should downgrade to a speculative pair"
    );
}

#[test]
fn test_evaluate_and_propagate_real_deduplicates_reasons_by_term() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let half = BigRational::new(BigInt::from(1), BigInt::from(2));
    let half_const = terms.mk_rational(half.clone());
    let bool_reason = terms.mk_var("b", Sort::Bool);
    let reason_a = TheoryLit::new(bool_reason, true);
    let reason_a_dup = TheoryLit::new(bool_reason, false);

    let (eqs, specs) = setup_and_propagate_real(
        &terms,
        x,
        half_const,
        half.clone(),
        Some(half),
        vec![reason_a, reason_a_dup],
    );

    assert_eq!(eqs.len(), 1);
    assert_eq!(eqs[0].reason.len(), 1);
    assert_eq!(specs.len(), 0);
}

// --- #uflia-hard-mixed-eq sort scoping (#seq-replace-mixed-eq regression) ---

#[test]
fn test_track_interface_term_rejects_seq_sorted_mixed_eq_operand() {
    // Regression: a Seq-sorted equality operand that contains arithmetic
    // SUBTERMS (the `(seq.extract s 0 (- (seq.len s) 1))` shape minted by the
    // seq.replace / seq.indexof decomposition axioms, #5841/#5998) must NOT be
    // registered as a Nelson-Oppen interface ARITHMETIC term. Registering it
    // made EUF propagate Seq-vs-Seq disequalities into LIA, which requested an
    // expression split on the Seq equality; the executor cannot encode `<`/`>`
    // over Seq and fail-closed the whole solve to `unknown` on satisfiable
    // QF_SEQLIA instances (seq_replace_sat_basic_5841 et al.).
    let mut terms = TermStore::new();
    let seq_int = Sort::seq(Sort::Int);
    let s = terms.mk_var("s", seq_int.clone());
    let u = terms.mk_var("u", seq_int.clone());
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let len_s = terms.mk_app(Symbol::named("seq.len"), vec![s], Sort::Int);
    let len_m1 = terms.mk_sub(vec![len_s, one]);
    let ext = terms.mk_app(
        Symbol::named("seq.extract"),
        vec![s, zero, len_m1],
        seq_int.clone(),
    );
    let cat = terms.mk_app(Symbol::named("seq.++"), vec![u, ext], seq_int);
    let eq = terms.mk_eq(cat, u);

    let mut bridge = InterfaceBridge::new();
    bridge.track_interface_term(&terms, eq);

    assert!(
        !bridge.contains_arith_term(&cat),
        "Seq-sorted mixed-eq operand must not become an interface arith term"
    );
    assert!(
        !bridge.contains_arith_term(&ext),
        "Seq-sorted extract must not become an interface arith term"
    );
}

#[test]
fn test_track_interface_term_keeps_int_sorted_mixed_eq_operand() {
    // Control for the sort scoping above: the mathsat EufLaArithmetic hard*
    // shape `(= (Sum a b) (+ (Sum c d) y))` — an Int equality with NO pure
    // arithmetic side — must still register its UF-mixed compound side
    // (#uflia-hard-mixed-eq).
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let d = terms.mk_var("d", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let sum_ab = terms.mk_app(Symbol::named("Sum"), vec![a, b], Sort::Int);
    let sum_cd = terms.mk_app(Symbol::named("Sum"), vec![c, d], Sort::Int);
    let compound = terms.mk_add(vec![sum_cd, y]);
    let eq = terms.mk_eq(sum_ab, compound);

    let mut bridge = InterfaceBridge::new();
    bridge.track_interface_term(&terms, eq);

    assert!(
        bridge.contains_arith_term(&compound),
        "Int-sorted UF-mixed compound must still register as an interface arith term"
    );
}
