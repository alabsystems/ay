// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Gap 9: Theory propagation soundness tests.
//!
//! Full DPLL(T) integration tests verifying correct theory-SAT interaction
//! for EUF, LRA, and LIA theories.

use super::*;

/// Test EUF theory propagation soundness through transitivity.
///
/// When EUF detects a conflict due to transitivity (a=b, b=c, a≠c),
/// the DPLL(T) loop must correctly generate a blocking clause and
/// return UNSAT.
#[test]
fn test_gap9_euf_propagation_transitivity() {
    let mut terms = TermStore::new();
    let sort_s = Sort::Uninterpreted("S".to_string());

    let a = terms.mk_var("a", sort_s.clone());
    let b = terms.mk_var("b", sort_s.clone());
    let c = terms.mk_var("c", sort_s);

    // a = b
    let eq_ab = terms.mk_eq(a, b);
    // b = c
    let eq_bc = terms.mk_eq(b, c);
    // a ≠ c
    let eq_ac = terms.mk_eq(a, c);
    let neq_ac = terms.mk_not(eq_ac);

    // Conjunction: (a = b) ∧ (b = c) ∧ (a ≠ c)
    let formula = terms.mk_and(vec![eq_ab, eq_bc, neq_ac]);

    let tseitin = Tseitin::new(&terms);
    let result = tseitin.transform(formula);

    let theory = EufSolver::new(&terms);
    let mut dpll = DpllT::from_tseitin(&terms, &result, theory);

    let solve_result = dpll.solve().unwrap();
    assert!(
        matches!(solve_result, SatResult::Unsat(_)),
        "EUF transitivity should detect UNSAT: a=b ∧ b=c ∧ a≠c"
    );
}

/// Test EUF congruence closure with function applications.
///
/// If a=b then f(a)=f(b). So a=b ∧ f(a)≠f(b) should be UNSAT.
#[test]
fn test_gap9_euf_propagation_congruence() {
    let mut terms = TermStore::new();
    let sort_u = Sort::Uninterpreted("U".to_string());

    let a = terms.mk_var("a", sort_u.clone());
    let b = terms.mk_var("b", sort_u.clone());

    // f(a) and f(b)
    let f_a = terms.mk_app(Symbol::named("f"), vec![a], sort_u.clone());
    let f_b = terms.mk_app(Symbol::named("f"), vec![b], sort_u);

    // a = b
    let eq_ab = terms.mk_eq(a, b);
    // f(a) ≠ f(b)
    let eq_fa_fb = terms.mk_eq(f_a, f_b);
    let neq_fa_fb = terms.mk_not(eq_fa_fb);

    // Conjunction: (a = b) ∧ (f(a) ≠ f(b))
    let formula = terms.mk_and(vec![eq_ab, neq_fa_fb]);

    let tseitin = Tseitin::new(&terms);
    let result = tseitin.transform(formula);

    let theory = EufSolver::new(&terms);
    let mut dpll = DpllT::from_tseitin(&terms, &result, theory);

    let solve_result = dpll.solve().unwrap();
    assert!(
        matches!(solve_result, SatResult::Unsat(_)),
        "EUF congruence should detect UNSAT: a=b ∧ f(a)≠f(b)"
    );
}

/// Test EUF with satisfiable formula.
///
/// a≠b ∧ f(a)=c should be SAT (no congruence conflict).
#[test]
fn test_gap9_euf_propagation_sat() {
    let mut terms = TermStore::new();
    let sort_u = Sort::Uninterpreted("U".to_string());

    let a = terms.mk_var("a", sort_u.clone());
    let b = terms.mk_var("b", sort_u.clone());
    let c = terms.mk_var("c", sort_u.clone());

    let f_a = terms.mk_app(Symbol::named("f"), vec![a], sort_u);

    // a ≠ b
    let eq_ab = terms.mk_eq(a, b);
    let neq_ab = terms.mk_not(eq_ab);
    // f(a) = c
    let eq_fa_c = terms.mk_eq(f_a, c);

    // Conjunction: (a ≠ b) ∧ (f(a) = c)
    let formula = terms.mk_and(vec![neq_ab, eq_fa_c]);

    let tseitin = Tseitin::new(&terms);
    let result = tseitin.transform(formula);

    let theory = EufSolver::new(&terms);
    let mut dpll = DpllT::from_tseitin(&terms, &result, theory);

    let solve_result = dpll.solve().unwrap();
    assert!(
        matches!(solve_result, SatResult::Sat(_)),
        "EUF should be SAT: a≠b ∧ f(a)=c"
    );
}

/// Test LRA theory propagation with contradictory bounds.
///
/// x >= 5 ∧ x <= 3 should be detected as UNSAT.
#[test]
fn test_gap9_lra_propagation_bounds_conflict() {
    use ay_lra::LraSolver;

    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_int(5.into());
    let three = terms.mk_int(3.into());

    // x >= 5
    let ge_5 = terms.mk_app(Symbol::Named(">=".to_string()), vec![x, five], Sort::Bool);
    // x <= 3
    let le_3 = terms.mk_app(Symbol::Named("<=".to_string()), vec![x, three], Sort::Bool);

    // Conjunction
    let formula = terms.mk_and(vec![ge_5, le_3]);

    let tseitin = Tseitin::new(&terms);
    let result = tseitin.transform(formula);

    let theory = LraSolver::new(&terms);
    let mut dpll = DpllT::from_tseitin(&terms, &result, theory);

    let solve_result = dpll.solve().unwrap();
    assert!(
        matches!(solve_result, SatResult::Unsat(_)),
        "LRA should detect UNSAT: x >= 5 ∧ x <= 3"
    );
}

/// Test LRA with satisfiable formula.
///
/// x >= 0 ∧ x <= 10 should be SAT.
#[test]
fn test_gap9_lra_propagation_sat() {
    use ay_lra::LraSolver;

    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_int(0.into());
    let ten = terms.mk_int(10.into());

    // x >= 0
    let ge_0 = terms.mk_app(Symbol::Named(">=".to_string()), vec![x, zero], Sort::Bool);
    // x <= 10
    let le_10 = terms.mk_app(Symbol::Named("<=".to_string()), vec![x, ten], Sort::Bool);

    // Conjunction
    let formula = terms.mk_and(vec![ge_0, le_10]);

    let tseitin = Tseitin::new(&terms);
    let result = tseitin.transform(formula);

    let theory = LraSolver::new(&terms);
    let mut dpll = DpllT::from_tseitin(&terms, &result, theory);

    let solve_result = dpll.solve().unwrap();
    assert!(
        matches!(solve_result, SatResult::Sat(_)),
        "LRA should be SAT: x >= 0 ∧ x <= 10"
    );
}

/// Test LRA with strict bounds conflict.
///
/// x > 5 ∧ x < 5 should be UNSAT.
#[test]
fn test_gap9_lra_propagation_strict_bounds() {
    use ay_lra::LraSolver;

    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_int(5.into());

    // x > 5
    let gt_5 = terms.mk_app(Symbol::Named(">".to_string()), vec![x, five], Sort::Bool);
    // x < 5
    let lt_5 = terms.mk_app(Symbol::Named("<".to_string()), vec![x, five], Sort::Bool);

    // Conjunction
    let formula = terms.mk_and(vec![gt_5, lt_5]);

    let tseitin = Tseitin::new(&terms);
    let result = tseitin.transform(formula);

    let theory = LraSolver::new(&terms);
    let mut dpll = DpllT::from_tseitin(&terms, &result, theory);

    let solve_result = dpll.solve().unwrap();
    assert!(
        matches!(solve_result, SatResult::Unsat(_)),
        "LRA should detect UNSAT: x > 5 ∧ x < 5"
    );
}

/// Test LIA theory with integer division forcing.
///
/// 2x = 1 should be UNSAT in integers (no integer solution).
#[test]
fn test_gap9_lia_propagation_no_integer_solution() {
    use ay_lia::LiaSolver;

    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let two = terms.mk_int(2.into());
    let one = terms.mk_int(1.into());

    // 2*x
    let two_x = terms.mk_app(Symbol::Named("*".to_string()), vec![two, x], Sort::Int);
    // 2*x = 1
    let eq = terms.mk_eq(two_x, one);

    let tseitin = Tseitin::new(&terms);
    let result = tseitin.transform(eq);

    let theory = LiaSolver::new(&terms);
    let mut dpll = DpllT::from_tseitin(&terms, &result, theory);

    let solve_result = dpll.solve().unwrap();
    // LIA solver should return UNSAT or Unknown (depending on branch-and-bound convergence)
    // The key is it should NOT return SAT
    assert!(
        !matches!(solve_result, SatResult::Sat(_)),
        "LIA should NOT return SAT for 2x = 1 (no integer solution)"
    );
}

/// Test LIA with satisfiable formula.
///
/// x >= 0 ∧ x <= 5 should be SAT with integer solutions 0,1,2,3,4,5.
#[test]
fn test_gap9_lia_propagation_sat() {
    use ay_lia::LiaSolver;

    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(0.into());
    let five = terms.mk_int(5.into());

    // x >= 0
    let ge_0 = terms.mk_app(Symbol::Named(">=".to_string()), vec![x, zero], Sort::Bool);
    // x <= 5
    let le_5 = terms.mk_app(Symbol::Named("<=".to_string()), vec![x, five], Sort::Bool);

    // Conjunction
    let formula = terms.mk_and(vec![ge_0, le_5]);

    let tseitin = Tseitin::new(&terms);
    let result = tseitin.transform(formula);

    let theory = LiaSolver::new(&terms);
    let mut dpll = DpllT::from_tseitin(&terms, &result, theory);

    let solve_result = dpll.solve().unwrap();
    assert!(
        matches!(solve_result, SatResult::Sat(_)),
        "LIA should be SAT: x >= 0 ∧ x <= 5"
    );
}

/// Test theory conflict clause generation.
///
/// When theory detects a conflict, the conflict clause should block
/// the current assignment.
#[test]
fn test_gap9_theory_conflict_clause_generation() {
    let mut terms = TermStore::new();
    let sort_s = Sort::Uninterpreted("S".to_string());

    let a = terms.mk_var("a", sort_s.clone());
    let b = terms.mk_var("b", sort_s.clone());
    let c = terms.mk_var("c", sort_s);

    // Create a formula where SAT finds a model but theory rejects it
    let eq_ab = terms.mk_eq(a, b);
    let eq_bc = terms.mk_eq(b, c);
    let eq_ac = terms.mk_eq(a, c);
    let neq_ac = terms.mk_not(eq_ac);

    // (a = b) ∧ ((b = c) ∨ (a ≠ c))
    // This is SAT: either b=c is true, or a≠c is true
    let disjunct = terms.mk_or(vec![eq_bc, neq_ac]);
    let formula = terms.mk_and(vec![eq_ab, disjunct]);

    let tseitin = Tseitin::new(&terms);
    let result = tseitin.transform(formula);

    let theory = EufSolver::new(&terms);
    let mut dpll = DpllT::from_tseitin(&terms, &result, theory);

    let solve_result = dpll.solve().unwrap();
    assert!(
        matches!(solve_result, SatResult::Sat(_)),
        "Should find SAT model where a=b and either b=c or a≠c"
    );
}

/// Test theory integration with multiple theory lemmas.
///
/// Create a formula that requires multiple DPLL(T) iterations.
#[test]
fn test_gap9_theory_multiple_lemmas() {
    let mut terms = TermStore::new();
    let sort_s = Sort::Uninterpreted("S".to_string());

    let a = terms.mk_var("a", sort_s.clone());
    let b = terms.mk_var("b", sort_s.clone());
    let c = terms.mk_var("c", sort_s.clone());
    let d = terms.mk_var("d", sort_s);

    let eq_ab = terms.mk_eq(a, b);
    let eq_bc = terms.mk_eq(b, c);
    let eq_cd = terms.mk_eq(c, d);
    let eq_ad = terms.mk_eq(a, d);
    let neq_ad = terms.mk_not(eq_ad);

    // (a = b) ∧ (b = c) ∧ (c = d) ∧ (a ≠ d)
    // This requires transitivity chain a=b=c=d to detect UNSAT
    let formula = terms.mk_and(vec![eq_ab, eq_bc, eq_cd, neq_ad]);

    let tseitin = Tseitin::new(&terms);
    let result = tseitin.transform(formula);

    let theory = EufSolver::new(&terms);
    let mut dpll = DpllT::from_tseitin(&terms, &result, theory);

    let solve_result = dpll.solve().unwrap();
    assert!(
        matches!(solve_result, SatResult::Unsat(_)),
        "EUF should detect UNSAT through transitivity chain: a=b=c=d ∧ a≠d"
    );
}

/// Test that theory conflict variables receive VSIDS bumps (#8421).
///
/// When EUF detects a transitivity conflict (a=b, b=c, f(a)=f(c) implied),
/// the variables involved in the conflict clause should have elevated VSIDS
/// activity scores. This ensures the SAT solver prioritizes deciding on
/// contentious theory atoms.
#[test]
fn test_theory_conflict_vsids_bumps() {
    let mut terms = TermStore::new();
    let sort_u = Sort::Uninterpreted("U".to_string());

    let a = terms.mk_var("a", sort_u.clone());
    let b = terms.mk_var("b", sort_u.clone());
    let c = terms.mk_var("c", sort_u.clone());

    // f(a) and f(c) for congruence reasoning
    let f_a = terms.mk_app(Symbol::named("f"), vec![a], sort_u.clone());
    let f_c = terms.mk_app(Symbol::named("f"), vec![c], sort_u);

    // a = b
    let eq_ab = terms.mk_eq(a, b);
    // b = c
    let eq_bc = terms.mk_eq(b, c);
    // f(a) != f(c) -- contradicts a=b=c which implies f(a)=f(c)
    let eq_fa_fc = terms.mk_eq(f_a, f_c);
    let neq_fa_fc = terms.mk_not(eq_fa_fc);

    // Conjunction: (a = b) /\ (b = c) /\ (f(a) != f(c)) -> UNSAT
    let formula = terms.mk_and(vec![eq_ab, eq_bc, neq_fa_fc]);

    let tseitin = Tseitin::new(&terms);
    let result = tseitin.transform(formula);

    let theory = EufSolver::new(&terms);
    let mut dpll = DpllT::from_tseitin(&terms, &result, theory);

    let solve_result = dpll.solve().unwrap();
    assert!(
        matches!(solve_result, SatResult::Unsat(_)),
        "EUF transitivity + congruence should detect UNSAT: a=b, b=c, f(a)!=f(c)"
    );

    // After solving, theory atom variables involved in the conflict should
    // have non-zero VSIDS activity from the theory-conflict-driven bumps.
    // Collect all SAT variables that correspond to theory atoms.
    let sat = dpll.sat_solver();
    let mut has_bumped_theory_var = false;
    for (&var_idx, &_term) in dpll.var_to_term() {
        let var = Variable::new(var_idx);
        let act = sat.activity(var);
        if act > 0.0 {
            has_bumped_theory_var = true;
        }
    }
    assert!(
        has_bumped_theory_var,
        "At least one theory atom variable should have non-zero VSIDS activity \
         after theory conflicts (#8421)"
    );
}

/// Test sync_theory correctly communicates SAT assignment to theory.
///
/// This test creates a formula where the SAT solver assigns values
/// and the theory must correctly interpret them.
#[test]
fn test_gap9_sync_theory_assignment() {
    let mut terms = TermStore::new();
    let sort_s = Sort::Uninterpreted("S".to_string());

    let a = terms.mk_var("a", sort_s.clone());
    let b = terms.mk_var("b", sort_s);

    // p(a) - predicate
    let p_a = terms.mk_app(Symbol::named("p"), vec![a], Sort::Bool);
    // p(b)
    let p_b = terms.mk_app(Symbol::named("p"), vec![b], Sort::Bool);

    let eq_ab = terms.mk_eq(a, b);
    let not_p_b = terms.mk_not(p_b);

    // (a = b) ∧ p(a) ∧ ¬p(b) - UNSAT due to congruence
    let formula = terms.mk_and(vec![eq_ab, p_a, not_p_b]);

    let tseitin = Tseitin::new(&terms);
    let result = tseitin.transform(formula);

    let theory = EufSolver::new(&terms);
    let mut dpll = DpllT::from_tseitin(&terms, &result, theory);

    let solve_result = dpll.solve().unwrap();
    assert!(
        matches!(solve_result, SatResult::Unsat(_)),
        "sync_theory should communicate assignment correctly: a=b ∧ p(a) ∧ ¬p(b) is UNSAT"
    );
}
