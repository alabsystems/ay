// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Simple bounds-based LIA oracle.
/// For a single integer variable x with constraints `x <= b` and `x >= b`,
/// computes the intersection of bounds and checks if an integer exists in that range.
///
/// This avoids complex term store mutations by directly reasoning about bounds.
fn lia_bounds_satisfiable(atom_specs: &[LraAtomSpec], assignment: &[bool], used: &[usize]) -> bool {
    // For a single variable x:
    // - x <= b constraints give upper bounds
    // - x >= b constraints give lower bounds
    //
    // The formula is SAT iff max(lower bounds) <= min(upper bounds)

    let mut lower = i64::MIN; // max of all lower bounds
    let mut upper = i64::MAX; // min of all upper bounds

    for &atom_idx in used {
        let spec = &atom_specs[atom_idx];
        let val = assignment[atom_idx];
        let bound = i64::from(spec.bound);

        match (spec.cmp, val) {
            (LraCmp::Le, true) => {
                // x <= bound is TRUE -> upper bound
                upper = upper.min(bound);
            }
            (LraCmp::Le, false) => {
                // x <= bound is FALSE -> x > bound -> x >= bound+1
                lower = lower.max(bound + 1);
            }
            (LraCmp::Ge, true) => {
                // x >= bound is TRUE -> lower bound
                lower = lower.max(bound);
            }
            (LraCmp::Ge, false) => {
                // x >= bound is FALSE -> x < bound -> x <= bound-1
                upper = upper.min(bound - 1);
            }
        }
    }

    // For integers, satisfiable iff there exists an integer in [lower, upper]
    lower <= upper
}

/// Brute-force oracle for LIA with direct bounds computation.
fn brute_force_expected_lia(atom_specs: &[LraAtomSpec], expr: &BoolExpr) -> Expected {
    let used = expr.used_atoms(atom_specs.len());
    let num_used = used.len();
    debug_assert!(num_used > 0);
    debug_assert!(num_used <= 20, "brute force bound");

    for mask in 0u64..(1u64 << num_used) {
        let mut assignment = vec![false; atom_specs.len()];
        for (bit, &atom_idx) in used.iter().enumerate() {
            assignment[atom_idx] = ((mask >> bit) & 1) == 1;
        }

        if !expr.eval(&assignment) {
            continue;
        }

        // Check bounds satisfiability directly
        if lia_bounds_satisfiable(atom_specs, &assignment, &used) {
            return Expected::Sat;
        }
    }

    Expected::Unsat
}

// LIA case: integer bounds on a single variable x
#[derive(Clone, Debug)]
struct LiaCase {
    atom_specs: Vec<LraAtomSpec>, // Reuse LraAtomSpec but interpret for integers
    expr: BoolExpr,
}

fn lia_case_strategy() -> impl Strategy<Value = LiaCase> {
    (1usize..=5usize) // Fewer atoms due to split complexity
        .prop_flat_map(|num_atoms| {
            (
                prop::collection::vec(lra_atom_spec_strategy(), num_atoms),
                bool_expr_strategy(num_atoms),
            )
        })
        .prop_map(|(atom_specs, expr)| LiaCase { atom_specs, expr })
}

proptest! {
    // Default: 256 cases with shrinking enabled for better failure diagnosis.
    // Override with PROPTEST_CASES=1000 for thorough testing.
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// LIA proptest - tests soundness of LIA integration.
    ///
    /// Note: The basic solve() returns Unknown for NeedSplit cases.
    /// This test verifies soundness (no wrong answers) rather than completeness.
    /// For full LIA with split handling, see the executor tests.
    #[test]
    #[timeout(180000)]
    fn proptest_gap9_lia_random_theory_formulas(
        case in lia_case_strategy()
    ) {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);

        let atom_terms = case
            .atom_specs
            .iter()
            .map(|spec| {
                let op = match spec.cmp {
                    LraCmp::Le => "<=",
                    LraCmp::Ge => ">=",
                };
                let bound_term = terms.mk_int(i64::from(spec.bound).into());
                terms.mk_app(Symbol::Named(op.to_string()), vec![x, bound_term], Sort::Bool)
            })
            .collect::<Vec<_>>();

        let formula = build_bool_term(&mut terms, &atom_terms, &case.expr);

        let tseitin = Tseitin::new(&terms);
        let cnf = tseitin.transform(formula);

        let theory = LiaSolver::new(&terms);
        let mut dpll = DpllT::from_tseitin(&terms, &cnf, theory);
        let got = dpll.solve().unwrap();

        // Use simplified bounds-based oracle
        let expected = brute_force_expected_lia(&case.atom_specs, &case.expr);

        // Verify soundness: solver should never give wrong definite answers.
        // Unknown is acceptable for cases that would need NeedSplit.
        match (expected, got) {
            (Expected::Sat, SatResult::Sat(_)) => {}
            (Expected::Unsat, SatResult::Unsat(_)) => {}
            // Unknown is acceptable - solver is incomplete for NeedSplit cases
            (_, SatResult::Unknown) => {}
            (Expected::Sat, SatResult::Unsat(_)) => {
                prop_assert!(false, "LIA UNSOUND: expected SAT, got UNSAT");
            }
            (Expected::Unsat, SatResult::Sat(_)) => {
                prop_assert!(false, "LIA UNSOUND: expected UNSAT, got SAT");
            }
            #[allow(unreachable_patterns)]
            (_, _) => {}
        }
    }

    /// LIA proptest with split handling via solve_step + manual split atom creation.
    ///
    /// Demonstrates the solve_step/apply_split pattern for LIA by pre-computing all possible
    /// split atoms for a bounded set of integer values.
    ///
    /// See #1389 for tracking the completeness gap.
    #[test]
    #[timeout(180000)]
    fn proptest_gap9_lia_with_split_handling(
        case in lia_case_strategy()
    ) {
        use num_traits::ToPrimitive;
        use ay_dpll::SolveStepResult;

        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);

        let atom_terms = case
            .atom_specs
            .iter()
            .map(|spec| {
                let op = match spec.cmp {
                    LraCmp::Le => "<=",
                    LraCmp::Ge => ">=",
                };
                let bound_term = terms.mk_int(i64::from(spec.bound).into());
                terms.mk_app(Symbol::Named(op.to_string()), vec![x, bound_term], Sort::Bool)
            })
            .collect::<Vec<_>>();

        let formula = build_bool_term(&mut terms, &atom_terms, &case.expr);

        let tseitin = Tseitin::new(&terms);
        let cnf = tseitin.transform(formula);

        // Pre-compute split atoms for all integer values in [-10, 10].
        // For 1-var LIA with small bounds, this covers all possible splits.
        let mut split_atoms: std::collections::HashMap<i64, (TermId, TermId)> =
            std::collections::HashMap::new();
        for floor_val in -10i64..=10 {
            let ceil_val = floor_val + 1;
            let floor_term = terms.mk_int(floor_val.into());
            let ceil_term = terms.mk_int(ceil_val.into());
            let le_atom = terms.mk_le(x, floor_term);
            let ge_atom = terms.mk_ge(x, ceil_term);
            split_atoms.insert(floor_val, (le_atom, ge_atom));
        }

        // Now solve with split handling using solve_step
        let theory = LiaSolver::new(&terms);
        let mut dpll = DpllT::from_tseitin(&terms, &cnf, theory);

        let got = loop {
            match dpll.solve_step().unwrap() {
                SolveStepResult::Done(result) => break result,
                SolveStepResult::NeedSplit(split) => {
                    // Look up pre-computed atoms
                    let floor_i64: i64 = split.floor.to_i64().unwrap_or(0);
                    if let Some(&(le_atom, ge_atom)) = split_atoms.get(&floor_i64) {
                        dpll.apply_split(le_atom, ge_atom);
                    } else {
                        // Split value out of range - return Unknown
                        break SatResult::Unknown;
                    }
                }
                SolveStepResult::NeedDisequalitySplit(_) => {
                    // Disequality splits not handled in this test
                    break SatResult::Unknown;
                }
                SolveStepResult::NeedExpressionSplit(_) => {
                    // Expression splits not handled in this test
                    break SatResult::Unknown;
                }
                #[allow(unreachable_patterns)]
                _ => {
                    // Other step results (string lemmas, future variants) are
                    // not relevant to this LIA-only test.
                    break SatResult::Unknown;
                }
            }
        };

        // Use simplified bounds-based oracle
        let expected = brute_force_expected_lia(&case.atom_specs, &case.expr);

        // Verify soundness: solver should never give wrong definite answers.
        // Unknown is acceptable for edge cases (splits outside pre-computed range).
        match (expected, got) {
            (Expected::Sat, SatResult::Sat(_)) => {}
            (Expected::Unsat, SatResult::Unsat(_)) => {}
            // Unknown is acceptable for splits outside our pre-computed range
            (_exp, SatResult::Unknown) => {}
            (Expected::Sat, SatResult::Unsat(_)) => {
                prop_assert!(false, "LIA with splits UNSOUND: expected SAT, got UNSAT");
            }
            (Expected::Unsat, SatResult::Sat(_)) => {
                prop_assert!(false, "LIA with splits UNSOUND: expected UNSAT, got SAT");
            }
            #[allow(unreachable_patterns)]
            (_, _) => {}
        }
    }
}
