// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::Symbol;
use num_bigint::BigInt;
use num_rational::BigRational;

use super::*;

fn test_budget(
    attempts: usize,
    proof_replays: usize,
    candidate_probes: usize,
    clause_replays: usize,
) -> CombinedDecompositionBudget {
    CombinedDecompositionBudget {
        remaining_attempts: attempts,
        remaining_replays: proof_replays,
        candidate_probes_per_clause: candidate_probes,
        replays_per_clause: clause_replays,
    }
}

/// `a=b`, `f(a)=0`, and `f(b)=1`: the ninth candidate probe is `f(a),f(b)`
/// and its arithmetic bridge is inconsistent.
fn narrow_combined_conflict(terms: &mut TermStore) -> Vec<TermId> {
    let a = terms.mk_var("a", Sort::Real);
    let b = terms.mk_var("b", Sort::Real);
    let f = Symbol::named("f");
    let fa = terms.mk_app(f.clone(), [a], Sort::Real);
    let fb = terms.mk_app(f, [b], Sort::Real);
    let zero = terms.mk_rational(BigRational::from_integer(BigInt::from(0)));
    let one = terms.mk_rational(BigRational::from_integer(BigInt::from(1)));
    let a_eq_b = terms.mk_eq_coerce(a, b);
    let fa_eq_zero = terms.mk_eq_coerce(fa, zero);
    let fb_eq_one = terms.mk_eq_coerce(fb, one);
    [a_eq_b, fa_eq_zero, fb_eq_one]
        .into_iter()
        .map(|atom| terms.mk_not(atom))
        .collect()
}

#[test]
fn clause_literal_cap_accepts_the_exact_boundary() {
    let mut terms = TermStore::new();
    let mut clause = narrow_combined_conflict(&mut terms);
    clause.rotate_left(1);
    let filler = clause[0];
    clause.resize(MAX_DECOMPOSITION_CLAUSE_LITERALS, filler);
    let mut budget = test_budget(1, 1, 1, 1);

    assert!(
        decompose_generic_combined_real_lemma(&mut terms, &clause, &mut budget).is_some(),
        "a clause exactly at the literal cap must reach decomposition"
    );
}

#[test]
fn clause_literal_cap_declines_before_term_access() {
    let mut terms = TermStore::new();
    let oversized = vec![TermId(u32::MAX); MAX_DECOMPOSITION_CLAUSE_LITERALS + 1];
    let mut budget = test_budget(1, 1, 1, 1);

    assert!(
        decompose_generic_combined_real_lemma(&mut terms, &oversized, &mut budget).is_none(),
        "cap + 1 must decline before dereferencing an untrusted term ID"
    );
    assert_eq!(
        budget.remaining_attempts, 0,
        "the proof attempt was charged"
    );
}

#[test]
fn application_arity_cap_declines_without_replay_or_synthetic_terms() {
    let mut terms = TermStore::new();
    let lhs_arguments: Vec<TermId> = (0..=MAX_CANDIDATE_APPLICATION_ARITY)
        .map(|index| terms.mk_var(format!("x{index}"), Sort::Real))
        .collect();
    let mut rhs_arguments = lhs_arguments.clone();
    let last = terms.mk_var("different", Sort::Real);
    rhs_arguments[MAX_CANDIDATE_APPLICATION_ARITY] = last;
    let f = Symbol::named("wide_f");
    let lhs = terms.mk_app(f.clone(), lhs_arguments, Sort::Real);
    let rhs = terms.mk_app(f, rhs_arguments, Sort::Real);
    let before = terms.len();
    let mut clause_budget = ClauseDecompositionBudget {
        remaining_candidate_probes: 1,
        remaining_replays: 1,
    };
    let mut budget = test_budget(1, 1, 1, 1);

    assert!(
        try_congruence_decomposition(
            &mut terms,
            &[],
            &HashMap::default(),
            lhs,
            rhs,
            &mut budget,
            &mut clause_budget,
        )
        .is_none(),
        "cap + 1 arguments must decline before cloning or replay"
    );
    assert_eq!(budget.remaining_replays, 1, "no replay was charged");
    assert_eq!(
        terms.len(),
        before,
        "decline must not intern a conclusion equality or negation"
    );
}

#[test]
fn symbol_name_cap_declines_without_replay_or_synthetic_terms() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("long_a", Sort::Real);
    let b = terms.mk_var("long_b", Sort::Real);
    let long_name = "f".repeat(MAX_CANDIDATE_SYMBOL_NAME_BYTES + 1);
    let symbol = Symbol::named(long_name);
    let lhs = terms.mk_app(symbol.clone(), [a], Sort::Real);
    let rhs = terms.mk_app(symbol, [b], Sort::Real);
    let before = terms.len();
    let mut clause_budget = ClauseDecompositionBudget {
        remaining_candidate_probes: 1,
        remaining_replays: 1,
    };
    let mut budget = test_budget(1, 1, 1, 1);

    assert!(
        try_congruence_decomposition(
            &mut terms,
            &[],
            &HashMap::default(),
            lhs,
            rhs,
            &mut budget,
            &mut clause_budget,
        )
        .is_none(),
        "an overlong symbol must decline before equality comparison or replay"
    );
    assert_eq!(budget.remaining_replays, 1, "no replay was charged");
    assert_eq!(terms.len(), before, "no synthetic terms were interned");
}

#[test]
fn candidate_probe_cap_declines_before_the_first_valid_candidate() {
    let mut terms = TermStore::new();
    let clause = narrow_combined_conflict(&mut terms);
    let mut short = test_budget(1, 1, 8, 1);
    assert!(
        decompose_generic_combined_real_lemma(&mut terms, &clause, &mut short).is_none(),
        "eight probes must stop before the valid ninth candidate"
    );
    assert_eq!(short.remaining_replays, 1, "no solver was constructed");

    let mut exact = test_budget(1, 1, 9, 1);
    assert!(
        decompose_generic_combined_real_lemma(&mut terms, &clause, &mut exact).is_some(),
        "the ninth probe must reach the certified decomposition"
    );
    assert_eq!(exact.remaining_replays, 0, "one replay was charged");
}

#[test]
fn per_clause_replay_cap_does_not_debit_the_proof_envelope() {
    let mut terms = TermStore::new();
    let clause = narrow_combined_conflict(&mut terms);
    let mut budget = test_budget(1, 1, 9, 0);

    assert!(
        decompose_generic_combined_real_lemma(&mut terms, &clause, &mut budget).is_none(),
        "a clause with no replay allowance must remain Generic"
    );
    assert_eq!(
        budget.remaining_replays, 1,
        "a rejected per-clause reservation must be atomic"
    );
}

#[test]
fn proof_attempt_cap_is_shared_and_checked_before_term_access() {
    let mut terms = TermStore::new();
    let mut budget = test_budget(1, 1, 1, 1);
    assert!(decompose_generic_combined_real_lemma(&mut terms, &[], &mut budget).is_none());
    assert_eq!(budget.remaining_attempts, 0);
    assert!(
        decompose_generic_combined_real_lemma(&mut terms, &[TermId(u32::MAX)], &mut budget,)
            .is_none(),
        "an exhausted shared attempt cap must decline before dereferencing terms"
    );
}

#[test]
fn proof_replay_cap_is_shared_and_checked_before_term_access() {
    let mut terms = TermStore::new();
    let clause = narrow_combined_conflict(&mut terms);
    let mut budget = test_budget(2, 1, 9, 1);
    assert!(decompose_generic_combined_real_lemma(&mut terms, &clause, &mut budget).is_some());
    assert_eq!(budget.remaining_replays, 0);
    assert!(
        decompose_generic_combined_real_lemma(&mut terms, &[TermId(u32::MAX)], &mut budget,)
            .is_none(),
        "an exhausted shared replay cap must decline before dereferencing terms"
    );
}

#[test]
fn replayed_farkas_is_rebound_from_permuted_nonuniform_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::from_integer(BigInt::from(0)));
    let one = terms.mk_rational(BigRational::from_integer(BigInt::from(1)));
    let three = terms.mk_rational(BigRational::from_integer(BigInt::from(3)));
    let three_x = terms.mk_mul(vec![three, x]);
    let three_x_le_zero = terms.mk_le(three_x, zero);
    let x_ge_one = terms.mk_ge(x, one);
    let not_three_x_le_zero = terms.mk_not(three_x_le_zero);
    let not_x_ge_one = terms.mk_not(x_ge_one);

    let target_clause = vec![not_three_x_le_zero, not_x_ge_one];
    let target_conflict = vec![
        TheoryLit::new(three_x_le_zero, true),
        TheoryLit::new(x_ge_one, true),
    ];
    let source_farkas = FarkasAnnotation::from_ints(&[3, 1]);
    assert!(ay_core::proof_validation::verify_farkas_conflict_lits_full(
        &terms,
        &target_conflict,
        &source_farkas,
    )
    .is_err());

    let solver_conflict = TheoryConflict::with_farkas(
        vec![
            TheoryLit::new(x_ge_one, true),
            TheoryLit::new(three_x_le_zero, true),
        ],
        source_farkas,
    );
    let rebound = rebind_replayed_farkas(&terms, &target_clause, &solver_conflict)
        .expect("permuted replay certificate should rebind by literal identity");

    assert_eq!(rebound, FarkasAnnotation::from_ints(&[1, 3]));
    ay_core::proof_validation::verify_farkas_conflict_lits_full(&terms, &target_conflict, &rebound)
        .expect("rebound certificate must validate against the exact bridge clause");
}
