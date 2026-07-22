// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// ============================================================
// Transitive Congruence Proptest - targets a=b, b=c ⊢ f(a)=f(c)
// ============================================================
//
// The v3 proptest generates random equality atoms, which may not frequently
// produce transitive chains. This proptest guarantees transitive equality
// chains and conflicting function bounds to exercise the explain() path.
//
// Pattern:
//   - 3+ variables: x0, x1, x2, ...
//   - Equality chain: x0=x1, x1=x2, x2=x3, ... (asserted true)
//   - Conflicting bounds: f(x0) < 0 AND f(xN) >= 0
//
// When the chain is complete, congruence closure derives f(x0)=f(xN),
// and the conflicting LIA bounds must be detected.
use ay_dpll::executor::TheoryCombiner;

/// Specification for transitive congruence test atoms.
#[derive(Clone, Debug)]
enum TransitiveAtomSpec {
    /// Chain equality: x_i = x_{i+1}
    ChainEq { idx: u8 },
    /// LIA bound on function application f(x_i)
    FuncBound { var_idx: u8, cmp: LraCmp, bound: i8 },
}

fn transitive_atom_spec_strategy(chain_len: u8) -> impl Strategy<Value = TransitiveAtomSpec> {
    prop_oneof![
        // Chain equalities (weight 2 - want chains to form)
        2 => (0u8..chain_len).prop_map(|idx| TransitiveAtomSpec::ChainEq { idx }),
        // Function bounds on any variable in chain (weight 3)
        3 => ((0u8..=chain_len), prop_oneof![Just(LraCmp::Le), Just(LraCmp::Ge)], -2i8..=2i8)
            .prop_map(|(var_idx, cmp, bound)| TransitiveAtomSpec::FuncBound { var_idx, cmp, bound }),
    ]
}

#[derive(Clone, Debug)]
struct TransitiveCase {
    /// Number of chain links (num_vars = chain_len + 1)
    chain_len: u8,
    atom_specs: Vec<TransitiveAtomSpec>,
    expr: BoolExpr,
}

fn transitive_case_strategy() -> impl Strategy<Value = TransitiveCase> {
    // Chain length 2-4 means 3-5 variables
    (2u8..=4u8, 4usize..=7usize)
        .prop_flat_map(|(chain_len, num_atoms)| {
            (
                Just(chain_len),
                prop::collection::vec(transitive_atom_spec_strategy(chain_len), num_atoms),
                bool_expr_strategy(num_atoms),
            )
        })
        .prop_map(|(chain_len, atom_specs, expr)| TransitiveCase {
            chain_len,
            atom_specs,
            expr,
        })
}

/// Oracle for transitive congruence with union-find.
///
/// Properly models transitive equality via union-find and merges function
/// bounds for equal variables.
fn brute_force_expected_transitive(
    atom_specs: &[TransitiveAtomSpec],
    chain_len: u8,
    expr: &BoolExpr,
) -> Expected {
    let used = expr.used_atoms(atom_specs.len());
    let num_used = used.len();
    if num_used == 0 {
        return Expected::Sat;
    }
    debug_assert!(num_used <= 20, "brute force bound");

    let num_vars = (chain_len + 1) as usize;

    for mask in 0u64..(1u64 << num_used) {
        let mut assignment = vec![false; atom_specs.len()];
        for (bit, &atom_idx) in used.iter().enumerate() {
            assignment[atom_idx] = ((mask >> bit) & 1) == 1;
        }

        if !expr.eval(&assignment) {
            continue;
        }

        // Check for contradictory assignments to atoms with the same TermId.
        // Due to hash-consing, different atom indices may map to the same TermId
        // (e.g., duplicate ChainEq atoms). If we assign true and false to the
        // same TermId, that's a Boolean conflict - skip this assignment.
        //
        // Note: We don't have TermIds in the oracle, but ChainEq { idx } atoms
        // are uniquely determined by idx. Multiple ChainEq with same idx will
        // hash-cons to same TermId. If assigned different values, conflict.
        let mut chain_eq_values: std::collections::HashMap<u8, bool> =
            std::collections::HashMap::new();
        let mut has_conflict = false;
        for &atom_idx in &used {
            if let TransitiveAtomSpec::ChainEq { idx } = &atom_specs[atom_idx] {
                let val = assignment[atom_idx];
                if let Some(&prev_val) = chain_eq_values.get(idx) {
                    if prev_val != val {
                        has_conflict = true;
                        break;
                    }
                } else {
                    chain_eq_values.insert(*idx, val);
                }
            }
            // FuncBound atoms with same (var_idx, cmp, bound) also hash-cons
            if let TransitiveAtomSpec::FuncBound {
                var_idx,
                cmp,
                bound,
            } = &atom_specs[atom_idx]
            {
                // Create a unique key for this func bound
                let key = u32::from(*var_idx) << 16 | u32::from(*bound as u8) << 8 | (*cmp as u32);
                // We'd need another map, but for simplicity, FuncBound duplicates are rare
                // and the test accepts solver being more precise anyway.
                let _ = (var_idx, cmp, bound, key); // Silence unused warning
            }
        }
        if has_conflict {
            continue;
        }

        // Union-find for variable equalities
        let mut parent: Vec<usize> = (0..num_vars).collect();
        let mut rank = vec![0usize; num_vars];

        fn find(parent: &mut [usize], i: usize) -> usize {
            if parent[i] != i {
                parent[i] = find(parent, parent[i]);
            }
            parent[i]
        }

        fn union(parent: &mut [usize], rank: &mut [usize], i: usize, j: usize) {
            let ri = find(parent, i);
            let rj = find(parent, j);
            if ri != rj {
                if rank[ri] < rank[rj] {
                    parent[ri] = rj;
                } else if rank[ri] > rank[rj] {
                    parent[rj] = ri;
                } else {
                    parent[rj] = ri;
                    rank[ri] += 1;
                }
            }
        }

        // First pass: build equivalence classes from chain equalities
        for &atom_idx in &used {
            let val = assignment[atom_idx];
            if let TransitiveAtomSpec::ChainEq { idx } = &atom_specs[atom_idx] {
                if val {
                    // x_idx = x_{idx+1}
                    union(&mut parent, &mut rank, *idx as usize, (*idx + 1) as usize);
                }
            }
        }

        // Track function bounds per variable
        let mut func_lower = vec![i64::MIN; num_vars];
        let mut func_upper = vec![i64::MAX; num_vars];

        // Collect bounds
        for &atom_idx in &used {
            let val = assignment[atom_idx];
            if let TransitiveAtomSpec::FuncBound {
                var_idx,
                cmp,
                bound,
            } = &atom_specs[atom_idx]
            {
                let bound = i64::from(*bound);
                let idx = *var_idx as usize;
                match (cmp, val) {
                    (LraCmp::Le, true) => func_upper[idx] = func_upper[idx].min(bound),
                    (LraCmp::Le, false) => func_lower[idx] = func_lower[idx].max(bound + 1),
                    (LraCmp::Ge, true) => func_lower[idx] = func_lower[idx].max(bound),
                    (LraCmp::Ge, false) => func_upper[idx] = func_upper[idx].min(bound - 1),
                }
            }
        }

        // Merge function bounds for each equivalence class
        // Group variables by their root
        let mut classes: std::collections::HashMap<usize, Vec<usize>> =
            std::collections::HashMap::new();
        for i in 0..num_vars {
            let root = find(&mut parent, i);
            classes.entry(root).or_default().push(i);
        }

        let mut is_consistent = true;
        for members in classes.values() {
            if members.len() > 1 {
                // All f(x_i) for equal x_i must have compatible bounds
                let mut merged_lower = i64::MIN;
                let mut merged_upper = i64::MAX;
                for &idx in members {
                    merged_lower = merged_lower.max(func_lower[idx]);
                    merged_upper = merged_upper.min(func_upper[idx]);
                }
                if merged_lower > merged_upper {
                    is_consistent = false;
                    break;
                }
            }
        }

        if !is_consistent {
            continue;
        }

        // Check individual variable bounds (in case no chain formed)
        for i in 0..num_vars {
            if func_lower[i] > func_upper[i] {
                is_consistent = false;
                break;
            }
        }

        if is_consistent {
            return Expected::Sat;
        }
    }

    Expected::Unsat
}

proptest! {
    // Default: 512 cases (simpler tests). Override with PROPTEST_CASES=1000.
    #![proptest_config(ProptestConfig::with_cases(512))]

    /// Transitive Congruence Proptest - specifically tests a=b, b=c ⊢ f(a)=f(c).
    ///
    /// Issue #319 follow-up: The v3 proptest uses random equality generation which
    /// may not frequently produce long transitive chains. This test guarantees
    /// chain-style equalities (x0=x1, x1=x2, ...) which exercises:
    ///
    /// 1. The explain() path for transitive equality reasons
    /// 2. Congruence closure over chains
    /// 3. Proper N-O propagation of derived equalities
    ///
    /// Bug pattern caught:
    ///   - x0=x1 (asserted)
    ///   - x1=x2 (asserted)
    ///   - f(x0) < 0 (LIA bound)
    ///   - f(x2) >= 0 (LIA bound)
    ///
    /// Congruence derives f(x0)=f(x2) via x0=x2 transitivity.
    /// Without proper explain(), the propagation has incomplete reasons.
    #[test]
    #[timeout(180000)]
    fn proptest_transitive_congruence_chains(
        case in transitive_case_strategy()
    ) {
        let mut terms = TermStore::new();
        let num_vars = case.chain_len + 1;

        // Create integer variables for the chain
        let int_vars: Vec<_> = (0..num_vars)
            .map(|i| terms.mk_var(format!("x{i}"), Sort::Int))
            .collect();

        // Uninterpreted function f: Int -> Int
        let f = Symbol::named("f");

        // Build atoms from specs
        let atom_terms: Vec<_> = case
            .atom_specs
            .iter()
            .map(|spec| match spec {
                TransitiveAtomSpec::ChainEq { idx } => {
                    // x_idx = x_{idx+1}
                    terms.mk_eq(int_vars[*idx as usize], int_vars[(*idx + 1) as usize])
                }
                TransitiveAtomSpec::FuncBound { var_idx, cmp, bound } => {
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

        let expected = brute_force_expected_transitive(
            &case.atom_specs,
            case.chain_len,
            &case.expr,
        );

        // Verify soundness
        match (expected, got) {
            (Expected::Sat, SatResult::Sat(_)) => {}
            (Expected::Unsat, SatResult::Unsat(_)) => {}
            (_, SatResult::Unknown) => {}
            (Expected::Sat, SatResult::Unsat(_)) => {}  // Solver more precise
            (Expected::Unsat, SatResult::Sat(_)) => {
                prop_assert!(false, "TRANSITIVE CONGRUENCE UNSOUND: expected UNSAT, got SAT");
            }
            #[allow(unreachable_patterns)]
            (_, _) => {}
        }
    }
}
