// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// ============================================================
// EUF+LIA proptest v3 - targets congruence-derived equality propagation (Issue #319)
// ============================================================
//
// The v2 proptest only tests LIA bounds on raw integer variables.
// This v3 proptest adds LIA bounds on FUNCTION APPLICATIONS (f(x) < 0),
// which exercises the bug pattern from #319:
//   - a = b (asserted)
//   - f(a) < 0 (LIA bound on function application)
//   - f(b) >= 0 (LIA bound on different function application)
// Congruence closure derives f(a) = f(b), but this must propagate to LIA.

use ay_dpll::executor::TheoryCombiner;

/// Specification for EUF+LIA atoms v3 - includes LIA bounds on function applications.
///
/// Issue #319 coverage: This atom type was MISSING from v2, allowing the
/// congruence-to-LIA propagation bug to go undetected.
#[derive(Clone, Debug)]
enum UfLiaAtomSpecV3 {
    /// Pure LIA: bound on integer variable
    LiaBound { var_idx: u8, cmp: LraCmp, bound: i8 },
    /// Equality between two integer variables
    IntVarEq { lhs_idx: u8, rhs_idx: u8 },
    /// f(int_var) = constant (EUF equality)
    FuncVarEqConst { var_idx: u8, constant: i8 },
    /// NEW: LIA bound on function application f(int_var)
    /// This is critical for #319 - tests congruence-derived equality propagation
    LiaBoundOnFunc { var_idx: u8, cmp: LraCmp, bound: i8 },
}

fn uflia_atom_spec_strategy_v3(num_int_vars: u8) -> impl Strategy<Value = UfLiaAtomSpecV3> {
    prop_oneof![
        // LIA bounds on integer variables (30% weight)
        3 => (0u8..num_int_vars, prop_oneof![Just(LraCmp::Le), Just(LraCmp::Ge)], -3i8..=3i8)
            .prop_map(|(var_idx, cmp, bound)| UfLiaAtomSpecV3::LiaBound { var_idx, cmp, bound }),
        // Equality between int vars (20% weight - triggers congruence)
        2 => (0u8..num_int_vars, 0u8..num_int_vars)
            .prop_filter("different vars", |(l, r)| l != r)
            .prop_map(|(lhs_idx, rhs_idx)| UfLiaAtomSpecV3::IntVarEq { lhs_idx, rhs_idx }),
        // f(var) = constant (20% weight)
        2 => (0u8..num_int_vars, -3i8..=3i8)
            .prop_map(|(var_idx, constant)| UfLiaAtomSpecV3::FuncVarEqConst { var_idx, constant }),
        // NEW: LIA bounds on f(var) (30% weight - critical for #319!)
        // This generates atoms like f(x) < 0 or f(x) >= 5
        3 => (0u8..num_int_vars, prop_oneof![Just(LraCmp::Le), Just(LraCmp::Ge)], -3i8..=3i8)
            .prop_map(|(var_idx, cmp, bound)| UfLiaAtomSpecV3::LiaBoundOnFunc { var_idx, cmp, bound }),
    ]
}

#[derive(Clone, Debug)]
struct UfLiaCaseV3 {
    num_int_vars: u8,
    atom_specs: Vec<UfLiaAtomSpecV3>,
    expr: BoolExpr,
}

fn uflia_case_strategy_v3() -> impl Strategy<Value = UfLiaCaseV3> {
    // Use 2-3 integer variables to enable congruence-derived equality propagation
    (2u8..=3u8, 3usize..=5usize)
        .prop_flat_map(|(num_int_vars, num_atoms)| {
            (
                Just(num_int_vars),
                prop::collection::vec(uflia_atom_spec_strategy_v3(num_int_vars), num_atoms),
                bool_expr_strategy(num_atoms),
            )
        })
        .prop_map(|(num_int_vars, atom_specs, expr)| UfLiaCaseV3 {
            num_int_vars,
            atom_specs,
            expr,
        })
}

/// Oracle for EUF+LIA v3 that models function application bounds.
///
/// For LiaBoundOnFunc atoms, we track bounds on each f(x_i) as a separate
/// "synthetic variable". When x_i = x_j is asserted, we merge their f() bounds.
fn brute_force_expected_uflia_v3(
    atom_specs: &[UfLiaAtomSpecV3],
    num_int_vars: u8,
    expr: &BoolExpr,
) -> Expected {
    let used = expr.used_atoms(atom_specs.len());
    let num_used = used.len();
    if num_used == 0 {
        return Expected::Sat;
    }
    debug_assert!(num_used <= 20, "brute force bound");

    let n = num_int_vars as usize;

    for mask in 0u64..(1u64 << num_used) {
        let mut assignment = vec![false; atom_specs.len()];
        for (bit, &atom_idx) in used.iter().enumerate() {
            assignment[atom_idx] = ((mask >> bit) & 1) == 1;
        }

        if !expr.eval(&assignment) {
            continue;
        }

        // Track bounds on int variables
        let mut var_lower = vec![i64::MIN; n];
        let mut var_upper = vec![i64::MAX; n];

        // Track bounds on function applications f(x_i)
        let mut func_lower = vec![i64::MIN; n];
        let mut func_upper = vec![i64::MAX; n];

        // Track which variables are known equal (union-find style but simple)
        // For simplicity, track equality sets
        let mut eq_sets: Vec<Vec<usize>> = (0..n).map(|i| vec![i]).collect();

        let mut is_consistent = true;

        // First pass: collect var equalities
        for &atom_idx in &used {
            let val = assignment[atom_idx];
            if let UfLiaAtomSpecV3::IntVarEq { lhs_idx, rhs_idx } = &atom_specs[atom_idx] {
                let l = *lhs_idx as usize;
                let r = *rhs_idx as usize;
                if val {
                    // x_l = x_r: merge their equivalence sets
                    // Find sets containing l and r
                    let mut l_set_idx = None;
                    let mut r_set_idx = None;
                    for (idx, set) in eq_sets.iter().enumerate() {
                        if set.contains(&l) {
                            l_set_idx = Some(idx);
                        }
                        if set.contains(&r) {
                            r_set_idx = Some(idx);
                        }
                    }
                    if let (Some(li), Some(ri)) = (l_set_idx, r_set_idx) {
                        if li != ri {
                            // Merge sets
                            let (smaller, larger) = if li < ri { (li, ri) } else { (ri, li) };
                            let merged = eq_sets.remove(larger);
                            eq_sets[smaller].extend(merged);
                        }
                    }
                }
            }
        }

        // Second pass: collect bounds
        for &atom_idx in &used {
            let spec = &atom_specs[atom_idx];
            let val = assignment[atom_idx];

            match spec {
                UfLiaAtomSpecV3::LiaBound {
                    var_idx,
                    cmp,
                    bound,
                } => {
                    let bound = i64::from(*bound);
                    let idx = *var_idx as usize;
                    match (cmp, val) {
                        (LraCmp::Le, true) => var_upper[idx] = var_upper[idx].min(bound),
                        (LraCmp::Le, false) => var_lower[idx] = var_lower[idx].max(bound + 1),
                        (LraCmp::Ge, true) => var_lower[idx] = var_lower[idx].max(bound),
                        (LraCmp::Ge, false) => var_upper[idx] = var_upper[idx].min(bound - 1),
                    }
                }
                UfLiaAtomSpecV3::LiaBoundOnFunc {
                    var_idx,
                    cmp,
                    bound,
                } => {
                    let bound = i64::from(*bound);
                    let idx = *var_idx as usize;
                    match (cmp, val) {
                        (LraCmp::Le, true) => func_upper[idx] = func_upper[idx].min(bound),
                        (LraCmp::Le, false) => func_lower[idx] = func_lower[idx].max(bound + 1),
                        (LraCmp::Ge, true) => func_lower[idx] = func_lower[idx].max(bound),
                        (LraCmp::Ge, false) => func_upper[idx] = func_upper[idx].min(bound - 1),
                    }
                }
                UfLiaAtomSpecV3::IntVarEq { .. } => {
                    // Already handled above
                }
                UfLiaAtomSpecV3::FuncVarEqConst { var_idx, constant } => {
                    // f(x_i) = c: tight bounds on f(x_i)
                    let idx = *var_idx as usize;
                    let c = i64::from(*constant);
                    if val {
                        func_lower[idx] = func_lower[idx].max(c);
                        func_upper[idx] = func_upper[idx].min(c);
                    }
                    // f(x_i) != c: doesn't constrain bounds in our simple model
                }
            }
        }

        // Check var bounds consistency
        for i in 0..n {
            if var_lower[i] > var_upper[i] {
                is_consistent = false;
                break;
            }
        }

        if !is_consistent {
            continue;
        }

        // CRITICAL: Merge function bounds for equal variables (congruence!)
        // If x_i = x_j, then f(x_i) = f(x_j), so their bounds must be merged
        for set in &eq_sets {
            if set.len() > 1 {
                // Find the tightest bounds across all equal variables
                let mut merged_lower = i64::MIN;
                let mut merged_upper = i64::MAX;
                for &idx in set {
                    merged_lower = merged_lower.max(func_lower[idx]);
                    merged_upper = merged_upper.min(func_upper[idx]);
                }
                // Check consistency
                if merged_lower > merged_upper {
                    is_consistent = false;
                    break;
                }
            }
        }

        if !is_consistent {
            continue;
        }

        // Check individual func bounds
        for i in 0..n {
            if func_lower[i] > func_upper[i] {
                is_consistent = false;
                break;
            }
        }

        if !is_consistent {
            continue;
        }

        // Check disequality conflicts for tight bounds
        for &atom_idx in &used {
            if !assignment[atom_idx] {
                if let UfLiaAtomSpecV3::IntVarEq { lhs_idx, rhs_idx } = &atom_specs[atom_idx] {
                    let l = *lhs_idx as usize;
                    let r = *rhs_idx as usize;
                    // x_l != x_r: if both have tight bounds with same value, conflict
                    if var_lower[l] == var_upper[l]
                        && var_lower[r] == var_upper[r]
                        && var_lower[l] == var_lower[r]
                    {
                        is_consistent = false;
                        break;
                    }
                }
            }
        }

        if is_consistent {
            return Expected::Sat;
        }
    }

    Expected::Unsat
}

proptest! {
    // Default: 256 cases with shrinking enabled for better failure diagnosis.
    // Override with PROPTEST_CASES=1000 for thorough testing.
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// EUF+LIA (QF_UFLIA) proptest v3 - targets congruence-derived equality propagation.
    ///
    /// CRITICAL: This test catches Issue #319 by generating LIA bounds on function
    /// applications (f(x) < 0), not just on raw integer variables.
    ///
    /// Bug pattern:
    ///   - a = b (asserted equality)
    ///   - f(a) < 0 (LIA bound on function application)
    ///   - f(b) >= 0 (LIA bound on different function application)
    ///
    /// From a=b, congruence closure should derive f(a)=f(b). This equality must
    /// propagate to LIA so it knows f(a) and f(b) are the same integer value.
    /// Without this propagation, LIA sees independent constraints and reports SAT.
    ///
    /// The oracle models congruence correctly by merging function bounds when
    /// variable equalities are asserted.
    ///
    /// Fixed by #319: EUF now propagates congruence-derived equalities to N-O.
    #[test]
    #[timeout(180000)]
    fn proptest_gap9_uflia_congruence_to_lia(
        case in uflia_case_strategy_v3()
    ) {
        let mut terms = TermStore::new();

        // Create multiple integer variables for LIA
        let int_vars: Vec<_> = (0..case.num_int_vars)
            .map(|i| terms.mk_var(format!("x{i}"), Sort::Int))
            .collect();

        // Uninterpreted function f: Int -> Int
        let f = Symbol::named("f");

        // Build atoms from specs
        let atom_terms: Vec<_> = case
            .atom_specs
            .iter()
            .map(|spec| match spec {
                UfLiaAtomSpecV3::LiaBound { var_idx, cmp, bound } => {
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
                UfLiaAtomSpecV3::IntVarEq { lhs_idx, rhs_idx } => {
                    terms.mk_eq(
                        int_vars[*lhs_idx as usize],
                        int_vars[*rhs_idx as usize],
                    )
                }
                UfLiaAtomSpecV3::FuncVarEqConst { var_idx, constant } => {
                    let f_app = terms.mk_app(
                        f.clone(),
                        vec![int_vars[*var_idx as usize]],
                        Sort::Int,
                    );
                    let const_term = terms.mk_int(i64::from(*constant).into());
                    terms.mk_eq(f_app, const_term)
                }
                UfLiaAtomSpecV3::LiaBoundOnFunc { var_idx, cmp, bound } => {
                    // CRITICAL: LIA bound on f(x), not on x
                    // This is what v2 was missing!
                    let f_app = terms.mk_app(
                        f.clone(),
                        vec![int_vars[*var_idx as usize]],
                        Sort::Int,
                    );
                    let op = match cmp {
                        LraCmp::Le => "<=",
                        LraCmp::Ge => ">=",
                    };
                    let bound_term = terms.mk_int(i64::from(*bound).into());
                    terms.mk_app(
                        Symbol::Named(op.to_string()),
                        vec![f_app, bound_term],
                        Sort::Bool,
                    )
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

        let expected = brute_force_expected_uflia_v3(
            &case.atom_specs,
            case.num_int_vars,
            &case.expr,
        );

        // Verify soundness: solver should never give wrong definite answers.
        match (expected, got) {
            (Expected::Sat, SatResult::Sat(_)) => {}
            (Expected::Unsat, SatResult::Unsat(_)) => {}
            // Unknown is acceptable
            (_, SatResult::Unknown) => {}
            // Solver being more precise than oracle is acceptable
            (Expected::Sat, SatResult::Unsat(_)) => {}
            // This would be a real soundness bug - claiming SAT when oracle says UNSAT
            (Expected::Unsat, SatResult::Sat(_)) => {
                prop_assert!(false, "EUF+LIA congruence-to-LIA UNSOUND: expected UNSAT, got SAT");
            }
            #[allow(unreachable_patterns)]
            (_, _) => {}
        }
    }
}
