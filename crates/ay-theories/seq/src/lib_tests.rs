// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::Symbol;
use ay_core::Sort;

fn make_terms() -> TermStore {
    TermStore::new()
}

#[test]
fn test_seq_solver_unit_injectivity() {
    let mut terms = make_terms();

    // Create seq.unit(a) and seq.unit(b) where a, b are Int variables
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let unit_a = terms.mk_app(Symbol::named("seq.unit"), vec![a], Sort::seq(Sort::Int));
    let unit_b = terms.mk_app(Symbol::named("seq.unit"), vec![b], Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![unit_a, unit_b], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);

    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat));

    // Should propagate a = b via Nelson-Oppen
    let eq_result = solver.propagate_equalities();
    assert_eq!(eq_result.equalities.len(), 1);
    assert_eq!(eq_result.equalities[0].lhs, a);
    assert_eq!(eq_result.equalities[0].rhs, b);
}

#[test]
fn test_seq_solver_unit_empty_conflict() {
    let mut terms = make_terms();

    let x = terms.mk_var("x", Sort::Int);
    let unit_x = terms.mk_app(Symbol::named("seq.unit"), vec![x], Sort::seq(Sort::Int));
    let empty = terms.mk_app(Symbol::named("seq.empty"), vec![], Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![unit_x, empty], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);

    let result = solver.check();
    assert!(matches!(result, TheoryResult::Unsat(_)));
}

#[test]
fn test_seq_solver_push_pop() {
    let mut terms = make_terms();

    let x = terms.mk_var("x", Sort::Int);
    let unit_x = terms.mk_app(Symbol::named("seq.unit"), vec![x], Sort::seq(Sort::Int));
    let empty = terms.mk_app(Symbol::named("seq.empty"), vec![], Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![unit_x, empty], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);

    // Push, assert conflict, check, pop
    solver.push();
    solver.assert_literal(eq, true);
    assert!(matches!(solver.check(), TheoryResult::Unsat(_)));
    solver.pop();

    // After pop, should be sat again
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn test_seq_solver_model_extraction() {
    let mut terms = make_terms();

    // s = seq.unit(5)
    let five = terms.mk_int(5.into());
    let unit_5 = terms.mk_app(Symbol::named("seq.unit"), vec![five], Sort::seq(Sort::Int));
    let s = terms.mk_var("s", Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![s, unit_5], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);
    let _ = solver.check();

    let model = solver.extract_model();
    assert!(model.values.contains_key(&s));
    assert_eq!(model.values[&s], vec!["5"]);
}

#[test]
fn test_seq_solver_empty_model() {
    let mut terms = make_terms();

    let empty = terms.mk_app(Symbol::named("seq.empty"), vec![], Sort::seq(Sort::Int));
    let s = terms.mk_var("s", Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![s, empty], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);
    let _ = solver.check();

    let model = solver.extract_model();
    assert!(model.values.contains_key(&s));
    assert!(model.values[&s].is_empty());
}

// ============================================================================
// Additional Seq tests for test coverage (#8460)
// ============================================================================

/// Fresh Seq solver should not be in conflict.
#[test]
fn test_seq_solver_fresh_is_sat() {
    let terms = make_terms();
    let mut solver = SeqSolver::new(&terms);
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "fresh seq solver should be Sat, got {result:?}"
    );
}

/// Reset should clear all caches and state.
#[test]
fn test_seq_solver_reset() {
    let mut terms = make_terms();
    let x = terms.mk_var("x", Sort::Int);
    let unit_x = terms.mk_app(Symbol::named("seq.unit"), vec![x], Sort::seq(Sort::Int));
    let empty = terms.mk_app(Symbol::named("seq.empty"), vec![], Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![unit_x, empty], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);
    assert!(matches!(solver.check(), TheoryResult::Unsat(_)));

    solver.reset();

    // After reset, solver should be clean
    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert!(solver.unit_cache.is_empty());
    assert!(solver.empty_cache.is_empty());
}

/// Unit-empty conflict reversed (empty = unit) should still detect UNSAT.
#[test]
fn test_seq_solver_empty_unit_conflict_reversed() {
    let mut terms = make_terms();
    let x = terms.mk_var("x", Sort::Int);
    let unit_x = terms.mk_app(Symbol::named("seq.unit"), vec![x], Sort::seq(Sort::Int));
    let empty = terms.mk_app(Symbol::named("seq.empty"), vec![], Sort::seq(Sort::Int));
    // Note: reversed order (empty, unit_x) vs the other test
    let eq = terms.mk_app(Symbol::named("="), vec![empty, unit_x], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "seq.empty = seq.unit(x) should be UNSAT, got {result:?}"
    );
}

/// Negated equality (NOT (unit = empty)) should NOT conflict.
#[test]
fn test_seq_solver_negated_unit_empty_sat() {
    let mut terms = make_terms();
    let x = terms.mk_var("x", Sort::Int);
    let unit_x = terms.mk_app(Symbol::named("seq.unit"), vec![x], Sort::seq(Sort::Int));
    let empty = terms.mk_app(Symbol::named("seq.empty"), vec![], Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![unit_x, empty], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    // Assert eq is FALSE (unit != empty is always valid)
    solver.assert_literal(eq, false);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "NOT (seq.unit(x) = seq.empty) should be SAT, got {result:?}"
    );
}

/// Multiple push/pop levels should correctly manage state.
#[test]
fn test_seq_solver_nested_push_pop() {
    let mut terms = make_terms();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let unit_x = terms.mk_app(Symbol::named("seq.unit"), vec![x], Sort::seq(Sort::Int));
    let unit_y = terms.mk_app(Symbol::named("seq.unit"), vec![y], Sort::seq(Sort::Int));
    let empty = terms.mk_app(Symbol::named("seq.empty"), vec![], Sort::seq(Sort::Int));
    let eq_ux_empty = terms.mk_app(Symbol::named("="), vec![unit_x, empty], Sort::Bool);
    let eq_uy_empty = terms.mk_app(Symbol::named("="), vec![unit_y, empty], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq_ux_empty);
    solver.register_atom(eq_uy_empty);

    // Level 0: nothing asserted
    assert!(matches!(solver.check(), TheoryResult::Sat));

    // Level 1: assert unit_x = empty (UNSAT)
    solver.push();
    solver.assert_literal(eq_ux_empty, true);
    assert!(matches!(solver.check(), TheoryResult::Unsat(_)));

    // Level 2: push over the conflict
    solver.push();
    solver.assert_literal(eq_uy_empty, true);
    assert!(matches!(solver.check(), TheoryResult::Unsat(_)));

    // Pop level 2
    solver.pop();
    // Should still be UNSAT from level 1
    assert!(matches!(solver.check(), TheoryResult::Unsat(_)));

    // Pop level 1
    solver.pop();
    // Should be SAT again
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

/// Concatenation model extraction: s = seq.++(seq.unit(1), seq.unit(2))
#[test]
fn test_seq_solver_concat_model() {
    let mut terms = make_terms();
    let one = terms.mk_int(1.into());
    let two = terms.mk_int(2.into());
    let unit_1 = terms.mk_app(Symbol::named("seq.unit"), vec![one], Sort::seq(Sort::Int));
    let unit_2 = terms.mk_app(Symbol::named("seq.unit"), vec![two], Sort::seq(Sort::Int));
    let concat = terms.mk_app(
        Symbol::named("seq.++"),
        vec![unit_1, unit_2],
        Sort::seq(Sort::Int),
    );
    let s = terms.mk_var("s", Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![s, concat], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);
    let _ = solver.check();

    let model = solver.extract_model();
    assert!(model.values.contains_key(&s), "s should be in model");
    assert_eq!(
        model.values[&s],
        vec!["1", "2"],
        "s should be [1, 2] from concatenation"
    );
}

/// Symbolic concat associativity: `(a++b)++c == a++(b++c)` for OPAQUE seqs.
/// Asserting the disequality must be UNSAT (structural concat law, #2779).
#[test]
fn test_seq_solver_concat_assoc_symbolic() {
    let mut terms = make_terms();
    let a = terms.mk_var("a", Sort::seq(Sort::Int));
    let b = terms.mk_var("b", Sort::seq(Sort::Int));
    let c = terms.mk_var("c", Sort::seq(Sort::Int));
    let ab = terms.mk_app(Symbol::named("seq.++"), vec![a, b], Sort::seq(Sort::Int));
    let left = terms.mk_app(Symbol::named("seq.++"), vec![ab, c], Sort::seq(Sort::Int));
    let bc = terms.mk_app(Symbol::named("seq.++"), vec![b, c], Sort::seq(Sort::Int));
    let right = terms.mk_app(Symbol::named("seq.++"), vec![a, bc], Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![left, right], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.cache_term(left);
    solver.cache_term(right);
    solver.register_atom(eq);
    solver.assert_literal(eq, false); // assert left != right
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "symbolic (a++b)++c == a++(b++c): disequality must be UNSAT, got {result:?}"
    );
}

/// SOUNDNESS CONTROL: concat is NOT commutative. `(a++b) != (b++a)` over opaque
/// seqs must remain SAT — the structural-equality rule keys on operand ORDER, so
/// it must not wrongly prove commutativity.
#[test]
fn test_seq_solver_concat_not_commutative_symbolic() {
    let mut terms = make_terms();
    let a = terms.mk_var("a", Sort::seq(Sort::Int));
    let b = terms.mk_var("b", Sort::seq(Sort::Int));
    let ab = terms.mk_app(Symbol::named("seq.++"), vec![a, b], Sort::seq(Sort::Int));
    let ba = terms.mk_app(Symbol::named("seq.++"), vec![b, a], Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![ab, ba], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.cache_term(ab);
    solver.cache_term(ba);
    solver.register_atom(eq);
    solver.assert_literal(eq, false); // assert a++b != b++a
    let result = solver.check();
    assert!(
        !matches!(result, TheoryResult::Unsat(_)),
        "a++b != b++a must NOT be refuted (concat is not commutative), got {result:?}"
    );
}

/// Shared equality: unit-empty via Nelson-Oppen should be detected.
#[test]
fn test_seq_solver_shared_equality_unit_empty_conflict() {
    let mut terms = make_terms();
    let x = terms.mk_var("x", Sort::Int);
    let unit_x = terms.mk_app(Symbol::named("seq.unit"), vec![x], Sort::seq(Sort::Int));
    let empty = terms.mk_app(Symbol::named("seq.empty"), vec![], Sort::seq(Sort::Int));

    let mut solver = SeqSolver::new(&terms);
    // Register both terms so caches are populated
    solver.cache_term(unit_x);
    solver.cache_term(empty);

    // Shared equality from N-O: unit_x = empty
    let reason = vec![TheoryLit {
        term: TermId::new(100),
        value: true,
    }];
    solver.assert_shared_equality(unit_x, empty, &reason);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "shared equality unit = empty should produce UNSAT, got {result:?}"
    );
}

/// Statistics should report Seq-specific counters.
#[test]
fn test_seq_solver_statistics() {
    let mut terms = make_terms();
    let x = terms.mk_var("x", Sort::Int);
    let unit_x = terms.mk_app(Symbol::named("seq.unit"), vec![x], Sort::seq(Sort::Int));
    let empty = terms.mk_app(Symbol::named("seq.empty"), vec![], Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![unit_x, empty], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);
    let _ = solver.check();

    let stats = solver.collect_statistics();
    let stat_names: Vec<&str> = stats.iter().map(|(n, _)| *n).collect();
    assert!(
        stat_names.contains(&"seq_unit_terms"),
        "should report seq_unit_terms stat"
    );
    assert!(
        stat_names.contains(&"seq_empty_terms"),
        "should report seq_empty_terms stat"
    );
    // We registered one unit and one empty
    let unit_count = stats
        .iter()
        .find(|(n, _)| *n == "seq_unit_terms")
        .unwrap()
        .1;
    assert!(unit_count >= 1, "should have at least 1 unit term");
    let empty_count = stats
        .iter()
        .find(|(n, _)| *n == "seq_empty_terms")
        .unwrap()
        .1;
    assert!(empty_count >= 1, "should have at least 1 empty term");
}

/// Unit injectivity with same element should NOT propagate any equality.
#[test]
fn test_seq_solver_unit_injectivity_same_element() {
    let mut terms = make_terms();
    let a = terms.mk_var("a", Sort::Int);
    let unit_a1 = terms.mk_app(Symbol::named("seq.unit"), vec![a], Sort::seq(Sort::Int));
    let unit_a2 = terms.mk_app(Symbol::named("seq.unit"), vec![a], Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![unit_a1, unit_a2], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);
    let _ = solver.check();

    // Should NOT propagate any equality since both units have the same element
    let eq_result = solver.propagate_equalities();
    assert!(
        eq_result.equalities.is_empty(),
        "unit(a) = unit(a) should not produce equality propagation (same element)"
    );
}

/// Caching seq.nth should populate the nth_cache.
#[test]
fn test_seq_solver_nth_cache() {
    let mut terms = make_terms();
    let s = terms.mk_var("s", Sort::seq(Sort::Int));
    let idx = terms.mk_int(0.into());
    let nth = terms.mk_app(Symbol::named("seq.nth"), vec![s, idx], Sort::Int);

    let mut solver = SeqSolver::new(&terms);
    solver.cache_term(nth);

    assert!(
        solver.nth_cache.contains_key(&nth),
        "seq.nth should be cached"
    );
    let (seq_arg, idx_arg) = solver.nth_cache[&nth];
    assert_eq!(seq_arg, s);
    assert_eq!(idx_arg, idx);
}

/// Caching seq.len should populate the len_cache.
#[test]
fn test_seq_solver_len_cache() {
    let mut terms = make_terms();
    let s = terms.mk_var("s", Sort::seq(Sort::Int));
    let len = terms.mk_app(Symbol::named("seq.len"), vec![s], Sort::Int);

    let mut solver = SeqSolver::new(&terms);
    solver.cache_term(len);

    assert!(
        solver.len_cache.contains_key(&len),
        "seq.len should be cached"
    );
    assert_eq!(solver.len_cache[&len], s);
}

/// Triple nested concatenation: seq.++(seq.unit(1), seq.++(seq.unit(2), seq.unit(3)))
/// should produce model [1, 2, 3].
#[test]
fn test_seq_solver_nested_concat_model() {
    let mut terms = make_terms();
    let one = terms.mk_int(1.into());
    let two = terms.mk_int(2.into());
    let three = terms.mk_int(3.into());
    let unit_1 = terms.mk_app(Symbol::named("seq.unit"), vec![one], Sort::seq(Sort::Int));
    let unit_2 = terms.mk_app(Symbol::named("seq.unit"), vec![two], Sort::seq(Sort::Int));
    let unit_3 = terms.mk_app(Symbol::named("seq.unit"), vec![three], Sort::seq(Sort::Int));
    let inner_concat = terms.mk_app(
        Symbol::named("seq.++"),
        vec![unit_2, unit_3],
        Sort::seq(Sort::Int),
    );
    let outer_concat = terms.mk_app(
        Symbol::named("seq.++"),
        vec![unit_1, inner_concat],
        Sort::seq(Sort::Int),
    );
    let s = terms.mk_var("s", Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![s, outer_concat], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);
    let _ = solver.check();

    let model = solver.extract_model();
    assert!(model.values.contains_key(&s), "s should be in model");
    assert_eq!(
        model.values[&s],
        vec!["1", "2", "3"],
        "nested concat should produce [1, 2, 3]"
    );
}

/// Concat with empty: seq.++(seq.empty, seq.unit(5)) = seq.unit(5).
#[test]
fn test_seq_solver_concat_with_empty_model() {
    let mut terms = make_terms();
    let five = terms.mk_int(5.into());
    let unit_5 = terms.mk_app(Symbol::named("seq.unit"), vec![five], Sort::seq(Sort::Int));
    let empty = terms.mk_app(Symbol::named("seq.empty"), vec![], Sort::seq(Sort::Int));
    let concat = terms.mk_app(
        Symbol::named("seq.++"),
        vec![empty, unit_5],
        Sort::seq(Sort::Int),
    );
    let s = terms.mk_var("s", Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![s, concat], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);
    let _ = solver.check();

    let model = solver.extract_model();
    assert!(model.values.contains_key(&s));
    assert_eq!(
        model.values[&s],
        vec!["5"],
        "empty ++ unit(5) should be [5]"
    );
}

/// Multiple equalities asserted: only positive ones should be active.
#[test]
fn test_seq_solver_negated_equality_no_model() {
    let mut terms = make_terms();
    let five = terms.mk_int(5.into());
    let unit_5 = terms.mk_app(Symbol::named("seq.unit"), vec![five], Sort::seq(Sort::Int));
    let s = terms.mk_var("s", Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![s, unit_5], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    // Assert the equality as FALSE (s != seq.unit(5))
    solver.assert_literal(eq, false);
    let _ = solver.check();

    let model = solver.extract_model();
    // With negated equality, we should NOT be able to determine s's value
    assert!(
        !model.values.contains_key(&s),
        "negated equality should not produce a model value for s"
    );
}

/// Shared equality for unit injectivity: unit(a) = unit(b) via N-O.
#[test]
fn test_seq_solver_shared_equality_injectivity() {
    let mut terms = make_terms();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let unit_a = terms.mk_app(Symbol::named("seq.unit"), vec![a], Sort::seq(Sort::Int));
    let unit_b = terms.mk_app(Symbol::named("seq.unit"), vec![b], Sort::seq(Sort::Int));

    let mut solver = SeqSolver::new(&terms);
    solver.cache_term(unit_a);
    solver.cache_term(unit_b);

    let reason = vec![TheoryLit {
        term: TermId::new(100),
        value: true,
    }];
    solver.assert_shared_equality(unit_a, unit_b, &reason);

    let _ = solver.check();

    // Should propagate a = b via Nelson-Oppen
    let eq_result = solver.propagate_equalities();
    assert_eq!(
        eq_result.equalities.len(),
        1,
        "shared unit equality should propagate element equality"
    );
    assert_eq!(eq_result.equalities[0].lhs, a);
    assert_eq!(eq_result.equalities[0].rhs, b);
}

/// Model extraction with boolean elements.
#[test]
fn test_seq_solver_bool_element_model() {
    let mut terms = make_terms();
    let t = terms.mk_bool(true);
    let unit_t = terms.mk_app(Symbol::named("seq.unit"), vec![t], Sort::seq(Sort::Bool));
    let s = terms.mk_var("s", Sort::seq(Sort::Bool));
    let eq = terms.mk_app(Symbol::named("="), vec![s, unit_t], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);
    let _ = solver.check();

    let model = solver.extract_model();
    assert!(model.values.contains_key(&s));
    assert_eq!(
        model.values[&s],
        vec!["true"],
        "boolean element should be formatted as 'true'"
    );
}

// ============================================================================
// Additional Seq tests for comprehensive coverage (#8460, TL68)
// ============================================================================

/// Model extraction with negative integer elements should use SMT-LIB format.
#[test]
fn test_seq_solver_negative_int_model() {
    let mut terms = make_terms();
    let neg_three = terms.mk_int((-3).into());
    let unit_neg = terms.mk_app(
        Symbol::named("seq.unit"),
        vec![neg_three],
        Sort::seq(Sort::Int),
    );
    let s = terms.mk_var("s", Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![s, unit_neg], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);
    let _ = solver.check();

    let model = solver.extract_model();
    assert!(model.values.contains_key(&s));
    assert_eq!(
        model.values[&s],
        vec!["(- 3)"],
        "negative integer should use SMT-LIB format (- 3)"
    );
}

/// Model extraction with string constant elements.
#[test]
fn test_seq_solver_string_element_model() {
    let mut terms = make_terms();
    let hello = terms.mk_string("hello".to_string());
    let unit_str = terms.mk_app(
        Symbol::named("seq.unit"),
        vec![hello],
        Sort::seq(Sort::String),
    );
    let s = terms.mk_var("s", Sort::seq(Sort::String));
    let eq = terms.mk_app(Symbol::named("="), vec![s, unit_str], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);
    let _ = solver.check();

    let model = solver.extract_model();
    assert!(model.values.contains_key(&s));
    assert_eq!(
        model.values[&s],
        vec!["\"hello\""],
        "string element should be quoted"
    );
}

/// Model extraction with rational element (numerator/denominator).
#[test]
fn test_seq_solver_rational_element_model() {
    use num_rational::BigRational;
    let mut terms = make_terms();
    let half = terms.mk_rational(BigRational::new(1.into(), 2.into()));
    let unit_rat = terms.mk_app(Symbol::named("seq.unit"), vec![half], Sort::seq(Sort::Real));
    let s = terms.mk_var("s", Sort::seq(Sort::Real));
    let eq = terms.mk_app(Symbol::named("="), vec![s, unit_rat], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);
    let _ = solver.check();

    let model = solver.extract_model();
    assert!(model.values.contains_key(&s));
    assert_eq!(
        model.values[&s],
        vec!["(/ 1 2)"],
        "rational element should use SMT-LIB fraction format"
    );
}

/// Model extraction with whole-number rational (denominator = 1).
#[test]
fn test_seq_solver_whole_rational_element_model() {
    use num_rational::BigRational;
    let mut terms = make_terms();
    let seven = terms.mk_rational(BigRational::new(7.into(), 1.into()));
    let unit_rat = terms.mk_app(
        Symbol::named("seq.unit"),
        vec![seven],
        Sort::seq(Sort::Real),
    );
    let s = terms.mk_var("s", Sort::seq(Sort::Real));
    let eq = terms.mk_app(Symbol::named("="), vec![s, unit_rat], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);
    let _ = solver.check();

    let model = solver.extract_model();
    assert!(model.values.contains_key(&s));
    assert_eq!(
        model.values[&s],
        vec!["7"],
        "whole rational should format as plain integer"
    );
}

/// Model extraction with bitvector element.
#[test]
fn test_seq_solver_bitvec_element_model() {
    let mut terms = make_terms();
    let bv_const = terms.mk_bitvec(255.into(), 8);
    let unit_bv = terms.mk_app(
        Symbol::named("seq.unit"),
        vec![bv_const],
        Sort::seq(Sort::bitvec(8)),
    );
    let s = terms.mk_var("s", Sort::seq(Sort::bitvec(8)));
    let eq = terms.mk_app(Symbol::named("="), vec![s, unit_bv], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);
    let _ = solver.check();

    let model = solver.extract_model();
    assert!(model.values.contains_key(&s));
    assert_eq!(
        model.values[&s],
        vec!["(_ bv255 8)"],
        "bitvector element should use SMT-LIB indexed format"
    );
}

/// Concat of two empties should produce empty model.
#[test]
fn test_seq_solver_concat_empty_empty_model() {
    let mut terms = make_terms();
    let empty1 = terms.mk_app(Symbol::named("seq.empty"), vec![], Sort::seq(Sort::Int));
    let empty2 = terms.mk_app(Symbol::named("seq.empty"), vec![], Sort::seq(Sort::Int));
    let concat = terms.mk_app(
        Symbol::named("seq.++"),
        vec![empty1, empty2],
        Sort::seq(Sort::Int),
    );
    let s = terms.mk_var("s", Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![s, concat], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);
    let _ = solver.check();

    let model = solver.extract_model();
    assert!(model.values.contains_key(&s));
    assert!(
        model.values[&s].is_empty(),
        "empty ++ empty should produce empty sequence"
    );
}

/// Three-arg concat: seq.++(unit(1), unit(2), unit(3)).
#[test]
fn test_seq_solver_three_arg_concat_model() {
    let mut terms = make_terms();
    let one = terms.mk_int(1.into());
    let two = terms.mk_int(2.into());
    let three = terms.mk_int(3.into());
    let unit_1 = terms.mk_app(Symbol::named("seq.unit"), vec![one], Sort::seq(Sort::Int));
    let unit_2 = terms.mk_app(Symbol::named("seq.unit"), vec![two], Sort::seq(Sort::Int));
    let unit_3 = terms.mk_app(Symbol::named("seq.unit"), vec![three], Sort::seq(Sort::Int));
    let concat = terms.mk_app(
        Symbol::named("seq.++"),
        vec![unit_1, unit_2, unit_3],
        Sort::seq(Sort::Int),
    );
    let s = terms.mk_var("s", Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![s, concat], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);
    let _ = solver.check();

    let model = solver.extract_model();
    assert!(model.values.contains_key(&s));
    assert_eq!(
        model.values[&s],
        vec!["1", "2", "3"],
        "three-arg concat should produce [1, 2, 3]"
    );
}

/// Calling check() twice without new assertions should still return Sat.
#[test]
fn test_seq_solver_idempotent_check() {
    let mut terms = make_terms();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let unit_a = terms.mk_app(Symbol::named("seq.unit"), vec![a], Sort::seq(Sort::Int));
    let unit_b = terms.mk_app(Symbol::named("seq.unit"), vec![b], Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![unit_a, unit_b], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);

    let result1 = solver.check();
    assert!(matches!(result1, TheoryResult::Sat));

    // Second check without new assertions should still be Sat
    let result2 = solver.check();
    assert!(
        matches!(result2, TheoryResult::Sat),
        "idempotent check should return Sat, got {result2:?}"
    );
}

/// Propagate returns empty when nothing is pending.
#[test]
fn test_seq_solver_propagate_empty() {
    let terms = make_terms();
    let mut solver = SeqSolver::new(&terms);
    let props = solver.propagate();
    assert!(
        props.is_empty(),
        "propagate on fresh solver should return empty"
    );
}

/// internalize_atom should cache terms just like register_atom.
#[test]
fn test_seq_solver_internalize_atom_caches() {
    let mut terms = make_terms();
    let x = terms.mk_var("x", Sort::Int);
    let unit_x = terms.mk_app(Symbol::named("seq.unit"), vec![x], Sort::seq(Sort::Int));

    let mut solver = SeqSolver::new(&terms);
    assert!(!solver.unit_cache.contains_key(&unit_x));

    solver.internalize_atom(unit_x);
    assert!(
        solver.unit_cache.contains_key(&unit_x),
        "internalize_atom should populate unit cache"
    );
}

/// Shared equality push/pop: shared equalities are backtracked correctly.
#[test]
fn test_seq_solver_shared_equality_push_pop() {
    let mut terms = make_terms();
    let x = terms.mk_var("x", Sort::Int);
    let unit_x = terms.mk_app(Symbol::named("seq.unit"), vec![x], Sort::seq(Sort::Int));
    let empty = terms.mk_app(Symbol::named("seq.empty"), vec![], Sort::seq(Sort::Int));

    let mut solver = SeqSolver::new(&terms);
    solver.cache_term(unit_x);
    solver.cache_term(empty);

    // Push scope
    solver.push();

    // Assert shared equality (unit_x = empty) -> UNSAT
    let reason = vec![TheoryLit {
        term: TermId::new(100),
        value: true,
    }];
    solver.assert_shared_equality(unit_x, empty, &reason);

    let result = solver.check();
    assert!(matches!(result, TheoryResult::Unsat(_)));

    // Pop should undo shared equality
    solver.pop();

    let result2 = solver.check();
    assert!(
        matches!(result2, TheoryResult::Sat),
        "after pop, shared equality should be removed, got {result2:?}"
    );
}

/// Extract_seq_value for symbolic variable returns None.
#[test]
fn test_seq_solver_extract_value_symbolic_returns_none() {
    let mut terms = make_terms();
    let s = terms.mk_var("s", Sort::seq(Sort::Int));

    let solver = SeqSolver::new(&terms);
    // A bare variable that is not in any cache should return None
    let result = solver.extract_seq_value(s);
    assert!(
        result.is_none(),
        "symbolic variable should not produce a concrete value"
    );
}

/// SeqModel default is empty.
#[test]
fn test_seq_model_default_empty() {
    let model = SeqModel::default();
    assert!(
        model.values.is_empty(),
        "default SeqModel should have empty values"
    );
}

/// Multiple distinct equality assertions — two equalities, one conflicting.
#[test]
fn test_seq_solver_multiple_equalities() {
    let mut terms = make_terms();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let x = terms.mk_var("x", Sort::Int);
    let unit_a = terms.mk_app(Symbol::named("seq.unit"), vec![a], Sort::seq(Sort::Int));
    let unit_b = terms.mk_app(Symbol::named("seq.unit"), vec![b], Sort::seq(Sort::Int));
    let empty = terms.mk_app(Symbol::named("seq.empty"), vec![], Sort::seq(Sort::Int));
    let unit_x = terms.mk_app(Symbol::named("seq.unit"), vec![x], Sort::seq(Sort::Int));

    // eq1: unit(a) = unit(b) -- sat, propagates a = b
    let eq1 = terms.mk_app(Symbol::named("="), vec![unit_a, unit_b], Sort::Bool);
    // eq2: unit(x) = empty -- unsat
    let eq2 = terms.mk_app(Symbol::named("="), vec![unit_x, empty], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq1);
    solver.register_atom(eq2);

    // Assert the sat equality first
    solver.assert_literal(eq1, true);
    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat));

    // Assert the conflicting equality
    solver.assert_literal(eq2, true);
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "unit(x) = empty in presence of other assertions should be UNSAT"
    );
}

/// Concat model with empty + empty + unit should produce single element.
#[test]
fn test_seq_solver_concat_empties_and_unit() {
    let mut terms = make_terms();
    let empty1 = terms.mk_app(Symbol::named("seq.empty"), vec![], Sort::seq(Sort::Int));
    let empty2 = terms.mk_app(Symbol::named("seq.empty"), vec![], Sort::seq(Sort::Int));
    let seven = terms.mk_int(7.into());
    let unit_7 = terms.mk_app(Symbol::named("seq.unit"), vec![seven], Sort::seq(Sort::Int));
    let concat = terms.mk_app(
        Symbol::named("seq.++"),
        vec![empty1, empty2, unit_7],
        Sort::seq(Sort::Int),
    );
    let s = terms.mk_var("s", Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![s, concat], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);
    let _ = solver.check();

    let model = solver.extract_model();
    assert!(model.values.contains_key(&s));
    assert_eq!(
        model.values[&s],
        vec!["7"],
        "empty ++ empty ++ unit(7) should produce [7]"
    );
}

/// Variable element in unit: model should use variable name.
#[test]
fn test_seq_solver_variable_element_model() {
    let mut terms = make_terms();
    let x = terms.mk_var("x", Sort::Int);
    let unit_x = terms.mk_app(Symbol::named("seq.unit"), vec![x], Sort::seq(Sort::Int));
    let s = terms.mk_var("s", Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![s, unit_x], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);
    let _ = solver.check();

    let model = solver.extract_model();
    assert!(model.values.contains_key(&s));
    assert_eq!(
        model.values[&s],
        vec!["x"],
        "variable element should use variable name in model"
    );
}

/// Format_term_value for an application (non-constant, non-variable) uses fallback.
#[test]
fn test_seq_solver_app_element_model_fallback() {
    let mut terms = make_terms();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    // Create an App term: (+ x y)
    let plus = terms.mk_app(Symbol::named("+"), vec![x, y], Sort::Int);
    let unit_plus = terms.mk_app(Symbol::named("seq.unit"), vec![plus], Sort::seq(Sort::Int));
    let s = terms.mk_var("s", Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![s, unit_plus], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);
    let _ = solver.check();

    let model = solver.extract_model();
    assert!(model.values.contains_key(&s));
    // App terms use the tN fallback format
    let val = &model.values[&s];
    assert_eq!(val.len(), 1, "should have exactly one element");
    assert!(
        val[0].starts_with('t'),
        "app element should use tN fallback format, got: {}",
        val[0]
    );
}

/// Unit injectivity should NOT propagate when equality is negated.
#[test]
fn test_seq_solver_negated_unit_eq_no_injectivity() {
    let mut terms = make_terms();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let unit_a = terms.mk_app(Symbol::named("seq.unit"), vec![a], Sort::seq(Sort::Int));
    let unit_b = terms.mk_app(Symbol::named("seq.unit"), vec![b], Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![unit_a, unit_b], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    // Assert the equality as FALSE
    solver.assert_literal(eq, false);
    let _ = solver.check();

    let eq_result = solver.propagate_equalities();
    assert!(
        eq_result.equalities.is_empty(),
        "negated unit equality should not propagate injectivity"
    );
}

/// Push/pop across unit injectivity: propagated equalities should be cleared on pop.
#[test]
fn test_seq_solver_push_pop_clears_injectivity_propagation() {
    let mut terms = make_terms();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let unit_a = terms.mk_app(Symbol::named("seq.unit"), vec![a], Sort::seq(Sort::Int));
    let unit_b = terms.mk_app(Symbol::named("seq.unit"), vec![b], Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![unit_a, unit_b], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);

    solver.push();
    solver.assert_literal(eq, true);
    let _ = solver.check();

    // Consume equalities from this scope
    let eq_result = solver.propagate_equalities();
    assert_eq!(eq_result.equalities.len(), 1);

    solver.pop();

    // After pop, check should not produce any new equalities
    let _ = solver.check();
    let eq_result2 = solver.propagate_equalities();
    assert!(
        eq_result2.equalities.is_empty(),
        "after pop, no injectivity equalities should be pending"
    );
}

/// Caching a non-seq equality should NOT populate seq equality cache.
#[test]
fn test_seq_solver_non_seq_equality_not_cached() {
    let mut terms = make_terms();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    // Integer equality, not Seq equality
    let eq = terms.mk_app(Symbol::named("="), vec![x, y], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.cache_term(eq);

    assert!(
        solver.equality_cache.is_empty(),
        "non-Seq equality should not be cached"
    );
}

/// Seq equality between variables should be cached.
#[test]
fn test_seq_solver_seq_equality_cached() {
    let mut terms = make_terms();
    let s1 = terms.mk_var("s1", Sort::seq(Sort::Int));
    let s2 = terms.mk_var("s2", Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![s1, s2], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.cache_term(eq);

    assert!(
        solver.equality_cache.contains_key(&eq),
        "Seq equality should be cached"
    );
    let (lhs, rhs) = solver.equality_cache[&eq];
    assert_eq!(lhs, s1);
    assert_eq!(rhs, s2);
}

/// Zero integer element model.
#[test]
fn test_seq_solver_zero_element_model() {
    let mut terms = make_terms();
    let zero = terms.mk_int(0.into());
    let unit_0 = terms.mk_app(Symbol::named("seq.unit"), vec![zero], Sort::seq(Sort::Int));
    let s = terms.mk_var("s", Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![s, unit_0], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);
    let _ = solver.check();

    let model = solver.extract_model();
    assert!(model.values.contains_key(&s));
    assert_eq!(model.values[&s], vec!["0"]);
}

/// Long concatenation: 5 units in a row.
#[test]
fn test_seq_solver_long_concat_model() {
    let mut terms = make_terms();
    let vals: Vec<_> = (10..15)
        .map(|i| {
            let n = terms.mk_int(i.into());
            terms.mk_app(Symbol::named("seq.unit"), vec![n], Sort::seq(Sort::Int))
        })
        .collect();
    // Build right-associative concat: seq.++(u10, seq.++(u11, seq.++(u12, seq.++(u13, u14))))
    let mut result = vals[4];
    for i in (0..4).rev() {
        result = terms.mk_app(
            Symbol::named("seq.++"),
            vec![vals[i], result],
            Sort::seq(Sort::Int),
        );
    }
    let s = terms.mk_var("s", Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![s, result], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);
    let _ = solver.check();

    let model = solver.extract_model();
    assert!(model.values.contains_key(&s));
    assert_eq!(
        model.values[&s],
        vec!["10", "11", "12", "13", "14"],
        "5-unit concat should produce [10, 11, 12, 13, 14]"
    );
}

/// Concat with symbolic (non-concretizable) argument returns None from extract_seq_value.
#[test]
fn test_seq_solver_concat_symbolic_no_model() {
    let mut terms = make_terms();
    let sym = terms.mk_var("sym_seq", Sort::seq(Sort::Int));
    let five = terms.mk_int(5.into());
    let unit_5 = terms.mk_app(Symbol::named("seq.unit"), vec![five], Sort::seq(Sort::Int));
    // concat(sym_seq, unit(5)) — sym_seq is symbolic, can't concretize
    let concat = terms.mk_app(
        Symbol::named("seq.++"),
        vec![sym, unit_5],
        Sort::seq(Sort::Int),
    );

    let mut solver = SeqSolver::new(&terms);
    solver.cache_term(concat);

    // The concat itself should not be concretizable because sym is symbolic
    let result = solver.extract_seq_value(concat);
    assert!(
        result.is_none(),
        "concat with symbolic argument should not be concretizable"
    );
}

/// Statistics after reset should all be zero.
#[test]
fn test_seq_solver_statistics_after_reset() {
    let mut terms = make_terms();
    let x = terms.mk_var("x", Sort::Int);
    let unit_x = terms.mk_app(Symbol::named("seq.unit"), vec![x], Sort::seq(Sort::Int));
    let empty = terms.mk_app(Symbol::named("seq.empty"), vec![], Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![unit_x, empty], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);
    let _ = solver.check();

    solver.reset();

    let stats = solver.collect_statistics();
    for (name, count) in &stats {
        assert_eq!(
            *count, 0,
            "after reset, stat {name} should be 0, got {count}"
        );
    }
}

/// Assert literal overwrites previous value for the same atom.
#[test]
fn test_seq_solver_reassert_literal() {
    let mut terms = make_terms();
    let x = terms.mk_var("x", Sort::Int);
    let unit_x = terms.mk_app(Symbol::named("seq.unit"), vec![x], Sort::seq(Sort::Int));
    let empty = terms.mk_app(Symbol::named("seq.empty"), vec![], Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![unit_x, empty], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);

    // Assert true -> UNSAT
    solver.assert_literal(eq, true);
    assert!(matches!(solver.check(), TheoryResult::Unsat(_)));

    // Reassert as false (the solver takes the latest value)
    solver.assert_literal(eq, false);
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "reasserting literal as false should make it SAT, got {result:?}"
    );
}

// ============================================================================
// Concat extensionality (seq.++ equality soundness) — regression for the
// native-seq false-SAT bug where concat(unit 1, unit 2) = concat(unit 1, unit 3)
// returned SAT instead of UNSAT.
// ============================================================================

/// Build `seq.unit(elem)` over `Seq Int`.
fn mk_unit(terms: &mut TermStore, elem: TermId) -> TermId {
    terms.mk_app(Symbol::named("seq.unit"), vec![elem], Sort::seq(Sort::Int))
}

/// Build `seq.++(a, b)` over `Seq Int`.
fn mk_concat2(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    terms.mk_app(Symbol::named("seq.++"), vec![a, b], Sort::seq(Sort::Int))
}

/// `<<1,2>> = <<1,3>>` must be UNSAT (distinct constant at index 1).
#[test]
fn test_seq_solver_concat_inequality_conflict() {
    let mut terms = make_terms();
    let one = terms.mk_int(1.into());
    let two = terms.mk_int(2.into());
    let three = terms.mk_int(3.into());

    let lhs = {
        let u1 = mk_unit(&mut terms, one);
        let u2 = mk_unit(&mut terms, two);
        mk_concat2(&mut terms, u1, u2)
    };
    let rhs = {
        let u1 = mk_unit(&mut terms, one);
        let u3 = mk_unit(&mut terms, three);
        mk_concat2(&mut terms, u1, u3)
    };
    let eq = terms.mk_app(Symbol::named("="), vec![lhs, rhs], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "concat(<<1>>,<<2>>) = concat(<<1>>,<<3>>) must be UNSAT, got {result:?}"
    );
}

/// `concat(<<9>>, <<x>>) = <<9,10>>` must propagate `x = 10` (extensionality).
#[test]
fn test_seq_solver_concat_extensionality_propagates() {
    let mut terms = make_terms();
    let nine = terms.mk_int(9.into());
    let ten = terms.mk_int(10.into());
    let x = terms.mk_var("x", Sort::Int);

    let lhs = {
        let u9 = mk_unit(&mut terms, nine);
        let ux = mk_unit(&mut terms, x);
        mk_concat2(&mut terms, u9, ux)
    };
    let rhs = {
        let u9 = mk_unit(&mut terms, nine);
        let u10 = mk_unit(&mut terms, ten);
        mk_concat2(&mut terms, u9, u10)
    };
    let eq = terms.mk_app(Symbol::named("="), vec![lhs, rhs], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "concat(<<9>>,<<x>>) = <<9,10>> should be SAT (propagating x=10), got {result:?}"
    );

    let eq_result = solver.propagate_equalities();
    assert_eq!(
        eq_result.equalities.len(),
        1,
        "should propagate exactly the index-1 equality x = 10"
    );
    let prop = &eq_result.equalities[0];
    assert!(
        (prop.lhs == x && prop.rhs == ten) || (prop.lhs == ten && prop.rhs == x),
        "propagated equality should be x = 10, got lhs={:?} rhs={:?}",
        prop.lhs,
        prop.rhs
    );
}

/// `concat(<<1>>,<<2>>) = <<1>>` must be UNSAT (length 2 != length 1).
#[test]
fn test_seq_solver_concat_length_mismatch_conflict() {
    let mut terms = make_terms();
    let one = terms.mk_int(1.into());
    let two = terms.mk_int(2.into());

    let lhs = {
        let u1 = mk_unit(&mut terms, one);
        let u2 = mk_unit(&mut terms, two);
        mk_concat2(&mut terms, u1, u2)
    };
    let rhs = mk_unit(&mut terms, one);
    let eq = terms.mk_app(Symbol::named("="), vec![lhs, rhs], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "concat(<<1>>,<<2>>) = <<1>> must be UNSAT (length mismatch), got {result:?}"
    );
}

/// `concat(<<x>>,<<y>>) = concat(<<1>>,<<2>>)` is SAT and propagates both
/// positional equalities `x = 1` and `y = 2`.
#[test]
fn test_seq_solver_concat_symbolic_extensionality() {
    let mut terms = make_terms();
    let one = terms.mk_int(1.into());
    let two = terms.mk_int(2.into());
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);

    let lhs = {
        let ux = mk_unit(&mut terms, x);
        let uy = mk_unit(&mut terms, y);
        mk_concat2(&mut terms, ux, uy)
    };
    let rhs = {
        let u1 = mk_unit(&mut terms, one);
        let u2 = mk_unit(&mut terms, two);
        mk_concat2(&mut terms, u1, u2)
    };
    let eq = terms.mk_app(Symbol::named("="), vec![lhs, rhs], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);

    assert!(matches!(solver.check(), TheoryResult::Sat));

    let eq_result = solver.propagate_equalities();
    assert_eq!(
        eq_result.equalities.len(),
        2,
        "should propagate x=1 and y=2"
    );
    let mut pairs: Vec<(TermId, TermId)> = eq_result
        .equalities
        .iter()
        .map(|e| {
            if e.lhs.0 <= e.rhs.0 {
                (e.lhs, e.rhs)
            } else {
                (e.rhs, e.lhs)
            }
        })
        .collect();
    pairs.sort_by_key(|p| (p.0 .0, p.1 .0));
    let mut want = vec![
        if x.0 <= one.0 { (x, one) } else { (one, x) },
        if y.0 <= two.0 { (y, two) } else { (two, y) },
    ];
    want.sort_by_key(|p| (p.0 .0, p.1 .0));
    assert_eq!(pairs, want, "expected positional equalities x=1, y=2");
}
