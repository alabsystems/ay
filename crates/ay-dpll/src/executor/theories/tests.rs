// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// #8529: Use deterministic hash maps in all builds.
use super::*;
use ay_bv::BvBits;
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::time::Instant;
use num_bigint::BigInt;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};
use std::time::Duration;

use crate::executor_types::UnknownReason;

use super::super::Executor;

#[test]
fn test_extract_bv_model_empty_inputs() {
    let sat_model: Vec<bool> = vec![];
    let term_bits: HashMap<TermId, BvBits> = HashMap::default();
    let terms = TermStore::new();

    let result = Executor::extract_bv_model_from_bits(&sat_model, &term_bits, 0, &terms);

    assert!(result.values.is_empty());
    assert!(result.term_to_bits.is_empty());
}

#[test]
fn test_extract_bv_model_single_8bit_var() {
    let mut terms = TermStore::new();
    let var_term = terms.mk_var("x", Sort::bitvec(8));
    let sat_model = vec![true, true, false, true, false, false, false, true];
    let bits: BvBits = (1..=8i32).collect();
    let mut term_bits = HashMap::default();
    term_bits.insert(var_term, bits);

    let result = Executor::extract_bv_model_from_bits(&sat_model, &term_bits, 0, &terms);

    assert_eq!(result.values.len(), 1);
    assert!(result.values.contains_key(&var_term));
    assert_eq!(result.values[&var_term], BigInt::from(139));
}

#[test]
fn test_extract_bv_model_negative_literals() {
    let mut terms = TermStore::new();
    let var_term = terms.mk_var("y", Sort::bitvec(4));
    let sat_model = vec![false, false, false, false];
    let bits: BvBits = vec![-1, -2, -3, -4];
    let mut term_bits = HashMap::default();
    term_bits.insert(var_term, bits);

    let result = Executor::extract_bv_model_from_bits(&sat_model, &term_bits, 0, &terms);

    assert_eq!(result.values.len(), 1);
    assert_eq!(result.values[&var_term], BigInt::from(15));
}

#[test]
fn test_extract_bv_model_with_offset() {
    let mut terms = TermStore::new();
    let var_term = terms.mk_var("z", Sort::bitvec(4));
    let sat_model = vec![
        false, false, false, false, false, true, false, true, false, false,
    ];
    let bits: BvBits = vec![1, 2, 3, 4];
    let mut term_bits = HashMap::default();
    term_bits.insert(var_term, bits);

    let result = Executor::extract_bv_model_from_bits(&sat_model, &term_bits, 5, &terms);

    assert_eq!(result.values.len(), 1);
    assert_eq!(result.values[&var_term], BigInt::from(5));
}

#[test]
fn test_extract_bv_model_filters_non_bv() {
    let mut terms = TermStore::new();
    let var_term = terms.mk_var("x", Sort::bitvec(8));
    // Non-BV-sorted term should be filtered out even if it has bits
    let int_term = terms.mk_var("n", Sort::Int);
    let sat_model = vec![true; 16];
    let bits: BvBits = (1..=8i32).collect();
    let mut term_bits = HashMap::default();
    term_bits.insert(var_term, bits);
    term_bits.insert(int_term, (9..=16i32).collect());

    let result = Executor::extract_bv_model_from_bits(&sat_model, &term_bits, 0, &terms);

    assert_eq!(result.values.len(), 1);
    assert!(result.values.contains_key(&var_term));
    assert!(!result.values.contains_key(&int_term));
}

#[test]
fn test_extract_bv_model_out_of_bounds() {
    let mut terms = TermStore::new();
    let var_term = terms.mk_var("w", Sort::bitvec(4));
    let sat_model = vec![true, false];
    let bits: BvBits = vec![1, 2, 3, 4];
    let mut term_bits = HashMap::default();
    term_bits.insert(var_term, bits);

    let result = Executor::extract_bv_model_from_bits(&sat_model, &term_bits, 0, &terms);

    assert_eq!(result.values.len(), 1);
    assert_eq!(result.values[&var_term], BigInt::from(1));
}

#[test]
fn test_array_axiom_result_struct() {
    let result = ArrayAxiomResult {
        clauses: Vec::new(),
        num_vars: 0,
    };
    assert!(result.clauses.is_empty());
    assert_eq!(result.num_vars, 0);
}

#[test]
fn test_euf_axiom_result_struct() {
    let result = EufAxiomResult {
        clauses: vec![ay_core::CnfClause::new(vec![1, 2, 3])],
        num_vars: 5,
    };
    assert_eq!(result.clauses.len(), 1);
    assert_eq!(result.num_vars, 5);
}

#[test]
fn test_theory_loop_abort_on_interrupt_control() {
    let mut exec = Executor::new();
    let interrupt = Arc::new(AtomicBool::new(false));
    exec.set_solve_controls(Some(interrupt.clone()), None);

    assert!(!exec.should_abort_theory_loop());

    interrupt.store(true, Ordering::Relaxed);
    assert!(exec.should_abort_theory_loop());
    assert!(exec.last_result().is_some_and(|r| r.is_unknown()));
    assert_eq!(exec.get_reason_unknown(), Some(UnknownReason::Interrupted));
}

#[test]
fn test_theory_loop_abort_on_expired_deadline_control() {
    let mut exec = Executor::new();
    let expired_deadline = Instant::now()
        .checked_sub(Duration::from_millis(1))
        .unwrap();
    exec.set_solve_controls(None, Some(expired_deadline));

    assert!(exec.should_abort_theory_loop());
    assert!(exec.last_result().is_some_and(|r| r.is_unknown()));
    assert_eq!(exec.get_reason_unknown(), Some(UnknownReason::Timeout));
}

// Extensionality expression-split for Array-sorted disequalities.
//
// `create_expression_split_atoms` used to return `None` for a disequality
// whose operands were neither Int nor Real, so an Array-sorted disequality
// bailed `Unknown(ExpressionSplit)`. It now skolemizes a fresh difference
// index `k` and reduces `A ≠ B` to the element-sorted `select(A,k) ≠
// select(B,k)` — the standard array extensionality axiom.

#[test]
fn test_expression_split_array_extensionality_skolemizes_diff_index() {
    let mut terms = TermStore::new();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);
    let a = terms.mk_var("A", arr_sort.clone());
    let b = terms.mk_var("B", arr_sort);
    let eq = terms.mk_eq(a, b);
    let not_eq = terms.mk_not(eq);
    let mut witness_cache = ArrayExtWitnessCache::default();

    let (le_atom, ge_atom, is_distinct) =
        create_expression_split_atoms(&mut terms, &mut witness_cache, not_eq)
            .expect("array diseq must split");
    // `not (= A B)` is asserted true when the diseq holds, so the guard is a
    // distinct-style guard.
    assert!(is_distinct);

    // le_atom = (<= (select A k) (+ (select B k) -1)).
    let le_lhs = match terms.get(le_atom) {
        TermData::App(sym, args) if sym.name() == "<=" && args.len() == 2 => args[0],
        other => panic!("expected (<= ..), got {other:?}"),
    };
    // The bounded term is select(A, k).
    let (read_array, k) = match terms.get(le_lhs) {
        TermData::App(sym, args) if sym.name() == "select" && args.len() == 2 => (args[0], args[1]),
        other => panic!("expected (select A k), got {other:?}"),
    };
    assert_eq!(read_array, a, "the left branch reads array A");
    // k is a fresh extensionality skolem of the array's index sort (Int).
    match terms.get(k) {
        TermData::Var(name, _) => assert!(
            name.starts_with(ARRAY_EXT_WITNESS_PREFIX),
            "difference index should be an AY-internal extensionality skolem, got {name}"
        ),
        other => panic!("expected skolem var, got {other:?}"),
    }
    assert_eq!(
        terms.sort(k),
        &Sort::Int,
        "difference index has the index sort"
    );

    // ge_atom is the opposite bound `select(A,k) >= select(B,k)+1`, which
    // `mk_ge` normalizes to a `<=` app. Whatever its normalized shape, it must
    // reference the SAME select(A, k) term (same skolem k) as the le branch, so
    // the two atoms are mutually-exclusive bounds on one difference witness.
    let ge_args = match terms.get(ge_atom) {
        TermData::App(sym, args) if sym.name() == "<=" && args.len() == 2 => [args[0], args[1]],
        other => panic!("expected a normalized bound app, got {other:?}"),
    };
    assert!(
        ge_args.contains(&le_lhs),
        "both branch atoms read select(A, k) with the same skolem k"
    );
    assert_ne!(le_atom, ge_atom, "the two branches are distinct bounds");
}

#[test]
fn test_expression_split_array_extensionality_dedups_skolem() {
    let mut terms = TermStore::new();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);
    let a = terms.mk_var("A", arr_sort.clone());
    let b = terms.mk_var("B", arr_sort);
    let eq = terms.mk_eq(a, b);
    let not_eq = terms.mk_not(eq);
    let mut witness_cache = ArrayExtWitnessCache::default();

    let first =
        create_expression_split_atoms(&mut terms, &mut witness_cache, not_eq).expect("split");
    let len_after_first = terms.len();
    let second =
        create_expression_split_atoms(&mut terms, &mut witness_cache, not_eq).expect("split");
    // Repeated splits on the SAME array disequality reuse the cache-owned skolem
    // and interned atoms — no fresh terms — so the split-clause dedup in
    // `encode_and_add_split_clause` keeps the clause count bounded across the
    // Nelson-Oppen fixpoint rounds.
    assert_eq!(first, second, "repeated split must be identical");
    assert_eq!(
        terms.len(),
        len_after_first,
        "repeated split must not mint fresh terms (skolem dedup)"
    );
}

#[test]
fn test_array_extensionality_witness_is_canonical_reserved_and_sort_checked() {
    let mut terms = TermStore::new();
    let index_sort = Sort::Uninterpreted("Index".to_string());
    let arr_sort = Sort::array(index_sort.clone(), Sort::Int);
    let a = terms.mk_var("A", arr_sort.clone());
    let b = terms.mk_var("B", arr_sort);
    let mut witness_cache = ArrayExtWitnessCache::default();

    let forward = array_extensionality_witness(&mut terms, &mut witness_cache, a, b)
        .expect("well-sorted array witness");
    let reverse = array_extensionality_witness(&mut terms, &mut witness_cache, b, a)
        .expect("reversed pair must reuse witness");
    assert_eq!(forward, reverse, "unordered pair must have one witness");
    assert_eq!(terms.sort(forward), &index_sort);
    let TermData::Var(name, _) = terms.get(forward) else {
        panic!("array witness must be a variable");
    };
    assert!(name.starts_with(ARRAY_EXT_WITNESS_PREFIX));
    assert!(witness_cache.matches_pair(&terms, forward, a, b));

    let c = terms.mk_var("C", Sort::array(Sort::Bool, Sort::Int));
    let d = terms.mk_var("D", Sort::array(Sort::Bool, Sort::Int));
    let preexisting = terms.mk_var("__ay_ext_diff!preexisting", Sort::Bool);
    let wrong_sorted = terms.mk_var("__ay_ext_diff!wrong-sort", Sort::Int);
    assert_eq!(terms.sort(wrong_sorted), &Sort::Int);
    let bool_witness = array_extensionality_witness(&mut terms, &mut witness_cache, c, d)
        .expect("cache must mint a fresh correctly-sorted identity");
    assert_eq!(terms.sort(bool_witness), &Sort::Bool);
    assert_ne!(bool_witness, preexisting, "must not adopt an existing name");
    assert_ne!(bool_witness, wrong_sorted, "must not adopt a wrong sort");
}

#[test]
fn test_expression_split_returns_none_for_unsplittable_sort() {
    let mut terms = TermStore::new();
    // A Bool-sorted disequality has no arithmetic/extensional branch split.
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let eq = terms.mk_eq(p, q);
    let not_eq = terms.mk_not(eq);
    let mut witness_cache = ArrayExtWitnessCache::default();
    assert!(
        create_expression_split_atoms(&mut terms, &mut witness_cache, not_eq).is_none(),
        "Bool disequality must not produce an expression split"
    );
}

#[test]
fn test_array_extensionality_cache_retires_exact_identity_and_checks_raw_roots() {
    let mut terms = TermStore::new();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);
    let a = terms.mk_var("A", arr_sort.clone());
    let b = terms.mk_var("B", arr_sort);
    let mut cache = ArrayExtWitnessCache::default();
    let witness = cache.pair(&mut terms, a, b).expect("witness");
    let select = terms.mk_select(a, witness);

    assert_eq!(
        cache.registration_violation(&terms, &[select]),
        Some(ArrayExtWitnessRootViolation::CapturedWitness(witness))
    );
    cache.begin_public_solve(&terms);
    assert!(!cache.is_active_witness(&terms, witness));
    assert_eq!(
        cache.solve_violation(&terms, &[select]),
        Some(ArrayExtWitnessRootViolation::CapturedWitness(witness))
    );
    assert_eq!(
        cache.solve_violation(&terms, &[TermId(u32::MAX)]),
        Some(ArrayExtWitnessRootViolation::InvalidTerm(TermId(u32::MAX)))
    );
}

#[test]
fn test_deep_extensionality_clause_records_active_binding_chain() {
    let mut terms = TermStore::new();
    let inner_sort = Sort::array(Sort::Bool, Sort::Int);
    let outer_sort = Sort::array(Sort::Int, inner_sort);
    let a = terms.mk_var("A", outer_sort.clone());
    let b = terms.mk_var("B", outer_sort);
    let mut cache = ArrayExtWitnessCache::default();

    let outer_witness = cache
        .deep(&mut terms, a, b, 0, Sort::Int)
        .expect("outer witness");
    let inner_a = terms.mk_select(a, outer_witness);
    let inner_b = terms.mk_select(b, outer_witness);
    let inner_witness = cache
        .deep(&mut terms, a, b, 1, Sort::Bool)
        .expect("inner witness");
    let leaf_a = terms.mk_select(inner_a, inner_witness);
    let leaf_b = terms.mk_select(inner_b, inner_witness);
    let root_eq = terms.mk_eq(a, b);
    let leaf_eq = terms.mk_eq(leaf_a, leaf_b);
    let not_leaf_eq = terms.mk_not(leaf_eq);
    let clause = terms.mk_or(vec![root_eq, not_leaf_eq]);
    let bindings = vec![
        ArrayExtWitnessBinding {
            witness: outer_witness,
            array_a: a,
            array_b: b,
        },
        ArrayExtWitnessBinding {
            witness: inner_witness,
            array_a: inner_a,
            array_b: inner_b,
        },
    ];

    assert!(cache.record_generated_clause(&terms, clause, bindings.clone()));
    assert_eq!(
        cache.generated_clause_bindings(&terms, clause),
        Some(bindings.as_slice())
    );
    assert!(cache.is_active_witness(&terms, outer_witness));
    assert!(cache.is_active_witness(&terms, inner_witness));
}
