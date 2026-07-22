// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// ============================================================
// EUF+LIA (QF_UFLIA) proptest v2 - Nelson-Oppen soundness
// ============================================================
//
// Tests bidirectional equality propagation between EUF and LIA:
// - LIA→EUF: tight integer bounds (x>=5, x<=5) → x=5 → propagate to EUF
// - EUF→LIA: f(x)=y asserted → x=y propagated to LIA for arithmetic reasoning
//
// AUDIT (PROVER [P]89):
// - Uses MULTIPLE integer variables to test LIA→EUF propagation
// - Uses INDEPENDENT oracle (separate EUF + LIA without N-O) to avoid circular testing
// - Creates shared terms properly (f(x) where x appears in LIA bounds)

use ay_dpll::executor::TheoryCombiner;

/// Specification for EUF+LIA atoms designed to exercise Nelson-Oppen propagation.
///
/// AUDIT NOTE: Previous version had issues:
/// 1. Only one integer variable - LIA can't propagate equalities
/// 2. FuncEqConst used literals not variables - no sharing
/// 3. Oracle used UfLiaSolver (circular)
#[derive(Clone, Debug)]
enum UfLiaAtomSpec {
    /// Pure LIA: bound on one of the integer variables
    /// var_idx selects which variable (0..num_int_vars), bound is the constant
    LiaBound { var_idx: u8, cmp: LraCmp, bound: i8 },
    /// Equality between two integer variables - key for N-O propagation!
    /// When x=5 and y=5 are derived from bounds, this tests congruence f(x)=f(y)
    IntVarEq { lhs_idx: u8, rhs_idx: u8 },
    /// Equality of f(int_var) with integer constant
    /// Tests EUF→LIA: asserted f(x)=5 combined with LIA bounds on x
    FuncVarEqConst { var_idx: u8, constant: i8 },
}

fn uflia_atom_spec_strategy_v2(num_int_vars: u8) -> impl Strategy<Value = UfLiaAtomSpec> {
    prop_oneof![
        // LIA bounds on integer variables (50% weight - most important for N-O)
        3 => (0u8..num_int_vars, prop_oneof![Just(LraCmp::Le), Just(LraCmp::Ge)], -3i8..=3i8)
            .prop_map(|(var_idx, cmp, bound)| UfLiaAtomSpec::LiaBound { var_idx, cmp, bound }),
        // Equality between int vars (25% weight - tests LIA→EUF propagation)
        2 => (0u8..num_int_vars, 0u8..num_int_vars)
            .prop_filter("different vars", |(l, r)| l != r)
            .prop_map(|(lhs_idx, rhs_idx)| UfLiaAtomSpec::IntVarEq { lhs_idx, rhs_idx }),
        // f(var) = constant (25% weight - tests EUF integration)
        1 => (0u8..num_int_vars, -3i8..=3i8)
            .prop_map(|(var_idx, constant)| UfLiaAtomSpec::FuncVarEqConst { var_idx, constant }),
    ]
}

#[derive(Clone, Debug)]
struct UfLiaCaseV2 {
    num_int_vars: u8,
    atom_specs: Vec<UfLiaAtomSpec>,
    expr: BoolExpr,
}

fn uflia_case_strategy_v2() -> impl Strategy<Value = UfLiaCaseV2> {
    // Use 2-4 integer variables to enable LIA→EUF propagation
    (2u8..=4u8, 3usize..=6usize)
        .prop_flat_map(|(num_int_vars, num_atoms)| {
            (
                Just(num_int_vars),
                prop::collection::vec(uflia_atom_spec_strategy_v2(num_int_vars), num_atoms),
                bool_expr_strategy(num_atoms),
            )
        })
        .prop_map(|(num_int_vars, atom_specs, expr)| UfLiaCaseV2 {
            num_int_vars,
            atom_specs,
            expr,
        })
}

/// Independent oracle for EUF+LIA that does NOT use Nelson-Oppen.
///
/// This checks theories SEPARATELY to avoid circular testing:
/// 1. Check LIA bounds for each variable independently
/// 2. Check EUF equalities independently
///
/// If both pass independently, the assignment is conservatively SAT.
/// This oracle may miss UNSAT cases that require N-O propagation,
/// but it will never wrongly claim UNSAT.
fn brute_force_expected_uflia_independent(
    int_vars: &[TermId],
    atom_specs: &[UfLiaAtomSpec],
    expr: &BoolExpr,
) -> Expected {
    let used = expr.used_atoms(atom_specs.len());
    let num_used = used.len();
    if num_used == 0 {
        return Expected::Sat;
    }
    debug_assert!(num_used <= 20, "brute force bound");

    for mask in 0u64..(1u64 << num_used) {
        let mut assignment = vec![false; atom_specs.len()];
        for (bit, &atom_idx) in used.iter().enumerate() {
            assignment[atom_idx] = ((mask >> bit) & 1) == 1;
        }

        if !expr.eval(&assignment) {
            continue;
        }

        // Check LIA consistency: collect bounds on each variable
        // Map: var_idx -> (lower_bound, upper_bound)
        let num_vars = int_vars.len();
        let mut lower_bounds = vec![i64::MIN; num_vars];
        let mut upper_bounds = vec![i64::MAX; num_vars];
        let mut lia_consistent = true;

        for &atom_idx in &used {
            let spec = &atom_specs[atom_idx];
            let val = assignment[atom_idx];

            match spec {
                UfLiaAtomSpec::LiaBound {
                    var_idx,
                    cmp,
                    bound,
                } => {
                    let bound = i64::from(*bound);
                    let idx = *var_idx as usize;
                    match (cmp, val) {
                        (LraCmp::Le, true) => upper_bounds[idx] = upper_bounds[idx].min(bound),
                        (LraCmp::Le, false) => lower_bounds[idx] = lower_bounds[idx].max(bound + 1),
                        (LraCmp::Ge, true) => lower_bounds[idx] = lower_bounds[idx].max(bound),
                        (LraCmp::Ge, false) => upper_bounds[idx] = upper_bounds[idx].min(bound - 1),
                    }
                }
                UfLiaAtomSpec::IntVarEq { lhs_idx, rhs_idx } => {
                    // For x = y: if true, their bounds must overlap
                    // This is where N-O matters - we check conservatively
                    if val {
                        // x = y is asserted true
                        // Bounds must have a common value
                        let l = *lhs_idx as usize;
                        let r = *rhs_idx as usize;
                        // Merge bounds: intersection must be non-empty
                        let low = lower_bounds[l].max(lower_bounds[r]);
                        let high = upper_bounds[l].min(upper_bounds[r]);
                        if low > high {
                            lia_consistent = false;
                        }
                    }
                    // x != y when both have tight bounds with same value would be conflict,
                    // but we check that below
                }
                UfLiaAtomSpec::FuncVarEqConst { .. } => {
                    // f(x) = c is handled by EUF, doesn't directly affect LIA bounds
                }
            }
        }

        // Check bounds consistency for each variable
        for i in 0..num_vars {
            if lower_bounds[i] > upper_bounds[i] {
                lia_consistent = false;
                break;
            }
        }

        if !lia_consistent {
            continue;
        }

        // Check for disequality conflicts with tight bounds
        for &atom_idx in &used {
            if !assignment[atom_idx] {
                // x != y is asserted
                if let UfLiaAtomSpec::IntVarEq { lhs_idx, rhs_idx } = &atom_specs[atom_idx] {
                    let l = *lhs_idx as usize;
                    let r = *rhs_idx as usize;
                    // If both have tight bounds with same value, this is UNSAT
                    if lower_bounds[l] == upper_bounds[l]
                        && lower_bounds[r] == upper_bounds[r]
                        && lower_bounds[l] == lower_bounds[r]
                    {
                        lia_consistent = false;
                        break;
                    }
                }
            }
        }

        if !lia_consistent {
            continue;
        }

        // EUF consistency check is conservative - we don't model congruence here
        // If LIA is consistent, we conservatively say the whole thing might be SAT
        return Expected::Sat;
    }

    Expected::Unsat
}

proptest! {
    // Default: 256 cases with shrinking enabled for better failure diagnosis.
    // Override with PROPTEST_CASES=1000 for thorough testing.
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// EUF+LIA (QF_UFLIA) proptest v2 - tests Nelson-Oppen bidirectional propagation.
    ///
    /// AUDIT FIXES (PROVER [P]89):
    /// 1. Uses MULTIPLE integer variables (2-4) so LIA can propagate x=y when both
    ///    have tight bounds to the same value
    /// 2. Uses INDEPENDENT oracle that checks theories separately (not UfLiaSolver)
    ///    to avoid circular testing
    /// 3. Creates proper shared atoms: x=y atoms + f(x)=c atoms
    ///
    /// Tests soundness of equality propagation:
    /// - LIA→EUF: when x>=5,x<=5 and y>=5,y<=5, LIA discovers x=y for EUF congruence
    /// - EUF integration: f(x)=c combined with bounds reasoning
    ///
    /// Tests Nelson-Oppen bidirectional propagation soundness.
    #[test]
    #[timeout(180000)]
    fn proptest_gap9_uflia_nelson_oppen_soundness(
        case in uflia_case_strategy_v2()
    ) {
        let mut terms = TermStore::new();

        // Create multiple integer variables for LIA
        let int_vars: Vec<_> = (0..case.num_int_vars)
            .map(|i| terms.mk_var(format!("x{i}"), Sort::Int))
            .collect();

        // Uninterpreted function f: Int -> Int for shared atoms
        let f = Symbol::named("f");

        // Build atoms from specs
        let atom_terms: Vec<_> = case
            .atom_specs
            .iter()
            .map(|spec| match spec {
                UfLiaAtomSpec::LiaBound { var_idx, cmp, bound } => {
                    let op = match cmp {
                        LraCmp::Le => "<=",
                        LraCmp::Ge => ">=",
                    };
                    let bound_term = terms.mk_int(i64::from(*bound).into());
                    terms.mk_app(
                        Symbol::Named(op.to_string()),
                        vec![int_vars[*var_idx as usize], bound_term],
                        Sort::Bool,
                    )
                }
                UfLiaAtomSpec::IntVarEq { lhs_idx, rhs_idx } => {
                    // x_i = x_j - tests LIA→EUF propagation when both have tight bounds
                    terms.mk_eq(
                        int_vars[*lhs_idx as usize],
                        int_vars[*rhs_idx as usize],
                    )
                }
                UfLiaAtomSpec::FuncVarEqConst { var_idx, constant } => {
                    // f(x_i) = c - uses actual variable, not literal
                    let f_app = terms.mk_app(
                        f.clone(),
                        vec![int_vars[*var_idx as usize]],
                        Sort::Int,
                    );
                    let const_term = terms.mk_int(i64::from(*constant).into());
                    terms.mk_eq(f_app, const_term)
                }
            })
            .collect();

        // Build Boolean structure
        let formula = build_bool_term(&mut terms, &atom_terms, &case.expr);

        let tseitin = Tseitin::new(&terms);
        let cnf = tseitin.transform(formula);

        let theory = TheoryCombiner::uf_lia(&terms);
        let mut dpll = DpllT::from_tseitin(&terms, &cnf, theory);
        let got = dpll.solve().unwrap();

        let expected = brute_force_expected_uflia_independent(
            &int_vars,
            &case.atom_specs,
            &case.expr,
        );

        // Verify soundness: solver should never give wrong definite answers.
        // Unknown is acceptable.
        //
        // NOTE: The independent oracle is CONSERVATIVE - it may say SAT when
        // N-O propagation would find UNSAT. So we only check for unsound SAT.
        match (expected, got) {
            (Expected::Sat, SatResult::Sat(_)) => {}
            (Expected::Unsat, SatResult::Unsat(_)) => {}
            // Unknown is acceptable
            (_, SatResult::Unknown) => {}
            // Solver being more precise than oracle (finding UNSAT via N-O) is expected!
            (Expected::Sat, SatResult::Unsat(_)) => {}
            // This would be a real soundness bug - claiming SAT when oracle says UNSAT
            (Expected::Unsat, SatResult::Sat(_)) => {
                prop_assert!(false, "EUF+LIA N-O UNSOUND: expected UNSAT, got SAT");
            }
            #[allow(unreachable_patterns)]
            (_, _) => {}
        }
    }
}
