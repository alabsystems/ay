// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core DPLL(T) tests: propositional SAT/UNSAT, literal conversion,
//! theory atom registration, and learned clause preservation.

use super::*;

struct EmptyConflictTheory;

impl TheorySolver for EmptyConflictTheory {
    fn assert_literal(&mut self, _literal: TermId, _value: bool) {}

    fn check(&mut self) -> TheoryResult {
        TheoryResult::Unsat(vec![])
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        vec![]
    }

    fn push(&mut self) {}

    fn pop(&mut self) {}

    fn reset(&mut self) {}
}

#[test]
fn test_propositional_sat() {
    let mut solver = SmtSolver::new();

    // Create (a ∨ b) ∧ (¬a ∨ b) - should be SAT with b=true
    let a = solver.terms.mk_var("a", Sort::Bool);
    let b = solver.terms.mk_var("b", Sort::Bool);
    let not_a = solver.terms.mk_not(a);

    let or1 = solver.terms.mk_or(vec![a, b]);
    let or2 = solver.terms.mk_or(vec![not_a, b]);
    let formula = solver.terms.mk_and(vec![or1, or2]);

    solver.assert(formula);

    let result = solver.solve_propositional();
    assert!(matches!(result, SatResult::Sat(_)));
}

#[test]
fn test_propositional_unsat() {
    let mut solver = SmtSolver::new();

    // Create a ∧ ¬a - should be UNSAT
    let a = solver.terms.mk_var("a", Sort::Bool);
    let not_a = solver.terms.mk_not(a);
    let formula = solver.terms.mk_and(vec![a, not_a]);

    solver.assert(formula);

    let result = solver.solve_propositional();
    assert!(matches!(result, SatResult::Unsat(_)));
}

#[test]
fn test_dpll_empty_formula() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(0, theory);

    let result = dpll.solve().unwrap();
    assert!(matches!(result, SatResult::Sat(_)));
}

#[test]
fn test_dpll_set_random_seed_forwards_to_sat_solver() {
    let mut dpll = DpllT::new(0, PropositionalTheory);
    dpll.set_random_seed(42);
    assert_eq!(dpll.sat_solver().random_seed(), 42);
}

#[test]
fn test_dpll_diagnostic_trace_emits_round_and_summary_events() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("dpll_diag.jsonl");

    let mut dpll = DpllT::new(0, PropositionalTheory);
    dpll.enable_dpll_diagnostic_trace(path.to_str().expect("utf8 path"))
        .expect("enable diagnostic trace");

    let result = dpll.solve().unwrap();
    assert!(matches!(result, SatResult::Sat(_)));

    let contents = std::fs::read_to_string(path).expect("read diagnostic trace");
    let lines: Vec<serde_json::Value> = contents
        .lines()
        .map(|line| serde_json::from_str(line).expect("valid json line"))
        .collect();

    assert!(
        lines.len() >= 3,
        "expected header + at least round + summary, got {} lines",
        lines.len()
    );
    assert_eq!(lines[0]["type"], "header");
    assert!(
        lines[1..].iter().any(|event| event["type"] == "dpll_round"),
        "missing dpll_round event: {lines:?}"
    );
    assert!(
        lines[1..]
            .iter()
            .any(|event| event["type"] == "solve_summary"),
        "missing solve_summary event: {lines:?}"
    );
}

#[test]
fn test_dpll_tla_trace_emits_header_and_steps() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("dpll_tla.jsonl");

    let mut dpll = DpllT::new(0, PropositionalTheory);
    dpll.enable_dpll_tla_trace(
        path.to_str().expect("utf8 path"),
        "dpll_t_test",
        &[
            "round",
            "satResult",
            "theoryResult",
            "satConflicts",
            "satDecisions",
            "theoryConflicts",
            "theoryPropagations",
        ],
    );

    let result = dpll.solve().unwrap();
    assert!(matches!(result, SatResult::Sat(_)));

    let contents = std::fs::read_to_string(path).expect("read dpll tla trace");
    let lines: Vec<serde_json::Value> = contents
        .lines()
        .map(|line| serde_json::from_str(line).expect("valid json line"))
        .collect();

    assert!(lines.len() >= 3, "expected header + init + solve step");
    assert_eq!(lines[0]["type"], "header");
    assert_eq!(lines[0]["module"], "dpll_t_test");
    assert_eq!(lines[1]["type"], "step");
    assert_eq!(lines[2]["type"], "step");
    assert_eq!(lines[2]["action"]["name"], "DeclareSat");
}

#[test]
fn test_empty_theory_conflict_returns_unknown_instead_of_panicking() {
    let mut dpll = DpllT::new(0, EmptyConflictTheory);

    let solve_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| dpll.solve()))
        .expect("DpllT::check_theory should degrade invalid conflicts to Unknown")
        .unwrap();

    assert!(matches!(solve_result, SatResult::Unknown));
}

#[test]
fn test_register_theory_atom_freezes_sat_variable() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(3, theory);
    for (term, var) in [
        (TermId::new(42), 1),
        (TermId::new(3), 2),
        (TermId::new(7), 0),
        (TermId::new(42), 1),
    ] {
        dpll.register_theory_atom(term, var);
    }
    assert!(dpll.sat_solver().is_frozen(Variable::new(0)));
    assert!(dpll.sat_solver().is_frozen(Variable::new(1)));
    assert!(dpll.sat_solver().is_frozen(Variable::new(2)));
    assert_eq!(
        dpll.theory_atoms.as_slice(),
        &[TermId::new(42), TermId::new(3), TermId::new(7)]
    );
}

#[test]
fn test_from_tseitin_freezes_theory_atoms() {
    let mut terms = TermStore::new();
    let sort_s = Sort::Uninterpreted("S".to_string());
    let a = terms.mk_var("a", sort_s.clone());
    let b = terms.mk_var("b", sort_s);
    let eq_ab = terms.mk_eq(a, b);

    let tseitin = Tseitin::new(&terms);
    let result = tseitin.transform(eq_ab);
    let theory = PropositionalTheory;
    let dpll = DpllT::from_tseitin(&terms, &result, theory);

    let eq_var = dpll
        .var_for_term(eq_ab)
        .expect("Tseitin equality atom should have a SAT variable");
    assert!(dpll.sat_solver().is_frozen(eq_var));
}

#[test]
fn test_cnf_literal_conversion() {
    // Test positive literal
    let cnf_lit: CnfLit = 5;
    let sat_lit = Literal::from_dimacs(cnf_lit);
    assert_eq!(sat_lit.variable().id(), 4); // 0-indexed
    assert!(sat_lit.is_positive());

    let back = sat_lit_to_cnf_lit(sat_lit);
    assert_eq!(back, cnf_lit);

    // Test negative literal
    let cnf_lit: CnfLit = -3;
    let sat_lit = Literal::from_dimacs(cnf_lit);
    assert_eq!(sat_lit.variable().id(), 2); // 0-indexed
    assert!(!sat_lit.is_positive());

    let back = sat_lit_to_cnf_lit(sat_lit);
    assert_eq!(back, cnf_lit);
}

#[test]
fn test_simple_cnf() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(3, theory);

    // Add clause: (1 ∨ 2)
    dpll.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);

    // Add clause: (¬1 ∨ 2)
    dpll.add_clause(vec![
        Literal::negative(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);

    // Add clause: (¬2 ∨ 3)
    dpll.add_clause(vec![
        Literal::negative(Variable::new(1)),
        Literal::positive(Variable::new(2)),
    ]);

    let result = dpll.solve().unwrap();
    assert!(matches!(result, SatResult::Sat(_)));
}

#[test]
fn test_unsat_cnf() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(1, theory);

    // Add clause: (1)
    dpll.add_clause(vec![Literal::positive(Variable::new(0))]);

    // Add clause: (¬1)
    dpll.add_clause(vec![Literal::negative(Variable::new(0))]);

    let result = dpll.solve().unwrap();
    assert!(matches!(result, SatResult::Unsat(_)));
}

#[test]
fn test_dpll_euf_predicate_congruence_unsat() {
    let mut terms = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = terms.mk_var("a", u.clone());
    let b = terms.mk_var("b", u);

    // (= a b) ∧ p(a) ∧ ¬p(b) is UNSAT in EUF.
    let eq_ab = terms.mk_eq(a, b);
    let p_a = terms.mk_app(Symbol::named("p"), vec![a], Sort::Bool);
    let p_b = terms.mk_app(Symbol::named("p"), vec![b], Sort::Bool);
    let not_p_b = terms.mk_not(p_b);

    let formula = terms.mk_and(vec![eq_ab, p_a, not_p_b]);

    let tseitin = Tseitin::new(&terms);
    let result = tseitin.transform(formula);

    let theory = EufSolver::new(&terms);
    let mut dpll = DpllT::from_tseitin(&terms, &result, theory);

    let solve_result = dpll.solve().unwrap();
    assert!(matches!(solve_result, SatResult::Unsat(_)));
}

/// Test that learned clause preservation works correctly.
///
/// This test would have caught the LIA branch-and-bound bug where
/// learned clauses were lost between iterations because DpllT was
/// recreated fresh each time.
///
/// The bug: When solve_lia() recreated DpllT for each branch-and-bound
/// iteration, all learned clauses were lost. This caused the solver
/// to re-explore the same conflicting assignments repeatedly, leading
/// to infinite loops instead of converging to UNSAT.
///
/// The fix: Add get_learned_clauses() and add_learned_clauses() to
/// preserve learned clauses across solver recreations.
#[test]
fn test_learned_clause_preservation() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(3, theory);

    // Create a simple formula
    dpll.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);
    dpll.add_clause(vec![
        Literal::negative(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);

    // Solve first
    let result = dpll.solve().unwrap();
    assert!(matches!(result, SatResult::Sat(_)));

    // Extract learned clauses (may be empty for simple SAT formulas)
    let learned = dpll.get_learned_clauses();

    // Create a new solver and add the same clauses
    let theory2 = PropositionalTheory;
    let mut dpll2 = DpllT::new(3, theory2);

    dpll2.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);
    dpll2.add_clause(vec![
        Literal::negative(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);

    // Add the learned clauses from the first solve
    dpll2.add_learned_clauses(learned);

    // The second solve should also return SAT
    let result2 = dpll2.solve().unwrap();
    assert!(matches!(result2, SatResult::Sat(_)));
}

/// Test that get_learned_clauses and add_learned_clauses work together.
///
/// This is a regression test for the branch-and-bound bug:
/// The API for preserving learned clauses must work correctly
/// to prevent infinite loops in LIA solving.
#[test]
fn test_learned_clauses_api() {
    // Create a solver and solve a formula
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(2, theory);

    dpll.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);

    let result = dpll.solve().unwrap();
    assert!(matches!(result, SatResult::Sat(_)));

    // Get learned clauses (API should work even if empty)
    let learned = dpll.get_learned_clauses();

    // Create new solver and add learned clauses
    let theory2 = PropositionalTheory;
    let mut dpll2 = DpllT::new(2, theory2);
    dpll2.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);

    // This should not crash even if learned is empty
    dpll2.add_learned_clauses(learned);

    // Should still be SAT
    let result2 = dpll2.solve().unwrap();
    assert!(matches!(result2, SatResult::Sat(_)));
}

/// Regression test for #4797: add_learned_clauses must not panic when learned
/// clauses reference variables beyond the new solver's num_vars.
///
/// In branch-and-bound, the previous solver instance may have allocated extra
/// SAT variables (e.g., from split atoms applied during solving). When those
/// learned clauses are replayed into a fresh solver with fewer variables,
/// add_learned_clauses must expand num_vars to accommodate them.
#[test]
fn test_add_learned_clauses_expands_num_vars() {
    // Create a solver with 5 variables and solve to generate learned clauses
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(5, theory);

    // Add clauses that force conflicts (leading to learned clauses)
    dpll.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
        Literal::positive(Variable::new(2)),
    ]);
    dpll.add_clause(vec![
        Literal::negative(Variable::new(0)),
        Literal::positive(Variable::new(3)),
    ]);
    dpll.add_clause(vec![
        Literal::negative(Variable::new(1)),
        Literal::positive(Variable::new(4)),
    ]);
    dpll.add_clause(vec![
        Literal::negative(Variable::new(3)),
        Literal::negative(Variable::new(4)),
    ]);

    let _ = dpll.solve().unwrap();

    // Manually create learned clauses referencing variable 4
    // (simulating branch-and-bound split atoms)
    let synthetic_learned = vec![vec![
        Literal::positive(Variable::new(3)),
        Literal::negative(Variable::new(4)),
    ]];

    // Create a new solver with only 3 variables -- fewer than the learned
    // clauses need. Without the #4797 fix, this would panic with:
    // "BUG: add_clause_watched_impl: literal variable out of range"
    let theory2 = PropositionalTheory;
    let mut dpll2 = DpllT::new(3, theory2);
    dpll2.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);

    // This must not panic -- add_learned_clauses should expand num_vars.
    dpll2.add_learned_clauses(synthetic_learned);

    // The solver should still work correctly
    let result = dpll2.solve().unwrap();
    assert!(matches!(result, SatResult::Sat(_)));
}

// --- #6825 regression: UFLIA atoms under nested And must be discovered ---

/// Build the exact failing seed from #6825:
///   f(x2) = 0  AND  f(x0) >= 2  AND  x2 = x0
/// using the same nested-And shape as the proptest shrunk case:
///   And([eq_fx2_0, And([ge_fx0_2, eq_x2_x0])])
fn build_6825_formula(terms: &mut TermStore) -> (TermId, TermId, TermId, TermId) {
    let x0 = terms.mk_var("x0", Sort::Int);
    let x2 = terms.mk_var("x2", Sort::Int);

    let f = Symbol::named("f");

    // f(x0), f(x2)
    let f_x0 = terms.mk_app(f.clone(), vec![x0], Sort::Int);
    let f_x2 = terms.mk_app(f, vec![x2], Sort::Int);

    // Atom 0: f(x0) >= 2
    let two = terms.mk_int(2.into());
    let ge_fx0_2 = terms.mk_app(Symbol::Named(">=".to_string()), vec![f_x0, two], Sort::Bool);

    // Atom 1: x2 = x0
    let eq_x2_x0 = terms.mk_eq(x2, x0);

    // Atom 3: f(x2) = 0
    let zero = terms.mk_int(0.into());
    let eq_fx2_0 = terms.mk_eq(f_x2, zero);

    // Boolean structure matching proptest shrunk case:
    // And([Atom(3), And([Atom(0), Atom(1)])])
    let inner_and = terms.mk_and(vec![ge_fx0_2, eq_x2_x0]);
    let formula = terms.mk_and(vec![eq_fx2_0, inner_and]);

    (formula, ge_fx0_2, eq_x2_x0, eq_fx2_0)
}

/// Packet 0, test 1: verify that all 3 active theory atoms have SAT variables
/// and are frozen/registered after from_tseitin(). (#6825)
#[test]
fn test_from_tseitin_collects_all_nested_uflia_atoms() {
    use crate::combined_solvers::combiner::TheoryCombiner;

    let mut terms = TermStore::new();
    let (formula, ge_fx0_2, eq_x2_x0, eq_fx2_0) = build_6825_formula(&mut terms);

    let tseitin = Tseitin::new(&terms);
    let cnf = tseitin.transform(formula);

    let theory = TheoryCombiner::uf_lia(&terms);
    let dpll = DpllT::from_tseitin(&terms, &cnf, theory);

    // All 3 theory atoms must have SAT variables.
    let var_ge = dpll.var_for_term(ge_fx0_2);
    let var_eq_x = dpll.var_for_term(eq_x2_x0);
    let var_eq_f = dpll.var_for_term(eq_fx2_0);

    assert!(
        var_ge.is_some(),
        "#6825: f(x0) >= 2 must have a SAT variable after from_tseitin"
    );
    assert!(
        var_eq_x.is_some(),
        "#6825: x2 = x0 must have a SAT variable after from_tseitin"
    );
    assert!(
        var_eq_f.is_some(),
        "#6825: f(x2) = 0 must have a SAT variable after from_tseitin"
    );

    // All 3 must be in the theory_atoms list.
    assert!(
        dpll.theory_atoms.contains(&ge_fx0_2),
        "#6825: f(x0) >= 2 must be a registered theory atom"
    );
    assert!(
        dpll.theory_atoms.contains(&eq_x2_x0),
        "#6825: x2 = x0 must be a registered theory atom"
    );
    assert!(
        dpll.theory_atoms.contains(&eq_fx2_0),
        "#6825: f(x2) = 0 must be a registered theory atom"
    );

    // All 3 must be frozen.
    assert!(
        dpll.sat_solver().is_frozen(var_ge.unwrap()),
        "#6825: f(x0) >= 2 SAT variable must be frozen"
    );
    assert!(
        dpll.sat_solver().is_frozen(var_eq_x.unwrap()),
        "#6825: x2 = x0 SAT variable must be frozen"
    );
    assert!(
        dpll.sat_solver().is_frozen(var_eq_f.unwrap()),
        "#6825: f(x2) = 0 SAT variable must be frozen"
    );
}

/// Test that reorder is disabled for large DPLL(T) instances (#8118).
///
/// When `from_tseitin` receives a formula with >50K variables, the
/// construction path should disable the Kissat-style VMTF queue reorder
/// because the O(n log n) overhead exceeds the benefit on large instances.
#[test]
fn test_from_tseitin_disables_reorder_for_large_instances() {
    let mut terms = TermStore::new();
    // Create a formula that produces >50K variables.
    // We need at least 50_001 vars in the TseitinResult. Build a large
    // conjunction of propositional variables.
    let num_vars = 60_000;
    let vars: Vec<TermId> = (0..num_vars)
        .map(|i| terms.mk_var(format!("v{i}"), Sort::Bool))
        .collect();
    let formula = terms.mk_and(vars);

    let tseitin = Tseitin::new(&terms);
    let cnf = tseitin.transform(formula);
    assert!(
        cnf.num_vars as usize > 50_000,
        "Test requires >50K vars, got {}",
        cnf.num_vars
    );

    let theory = PropositionalTheory;
    let dpll = DpllT::from_tseitin(&terms, &cnf, theory);

    assert!(
        !dpll.sat_solver().is_reorder_enabled(),
        "#8118: reorder should be disabled for large DPLL(T) instances (>50K vars)"
    );
    // Conditioning and preprocessing should also be disabled (existing behavior).
    assert!(
        !dpll.sat_solver().is_condition_enabled(),
        "conditioning should be disabled in DPLL(T) mode"
    );
}

/// Test that reorder remains enabled for small DPLL(T) instances (#8118).
#[test]
fn test_from_tseitin_keeps_reorder_for_small_instances() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let formula = terms.mk_and(vec![a, b]);

    let tseitin = Tseitin::new(&terms);
    let cnf = tseitin.transform(formula);
    assert!((cnf.num_vars as usize) < 50_000, "Test requires <50K vars");

    let theory = PropositionalTheory;
    let dpll = DpllT::from_tseitin(&terms, &cnf, theory);

    assert!(
        dpll.sat_solver().is_reorder_enabled(),
        "#8118: reorder should remain enabled for small DPLL(T) instances"
    );
}

/// Packet 0, test 2: the full solve must return UNSAT, not SAT. (#6825)
#[test]
fn test_from_tseitin_uflia_congruence_seed_unsat() {
    use crate::combined_solvers::combiner::TheoryCombiner;

    let mut terms = TermStore::new();
    let (formula, _, _, _) = build_6825_formula(&mut terms);

    let tseitin = Tseitin::new(&terms);
    let cnf = tseitin.transform(formula);

    let theory = TheoryCombiner::uf_lia(&terms);
    let mut dpll = DpllT::from_tseitin(&terms, &cnf, theory);
    let result = dpll.solve().unwrap();

    // Must be UNSAT:
    //   x2 = x0  →  f(x2) = f(x0) (congruence)
    //   f(x2) = 0  →  f(x0) = 0
    //   f(x0) >= 2 contradicts f(x0) = 0
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "#6825: UFLIA congruence seed must be UNSAT, got {result:?}"
    );
}
