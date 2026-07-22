// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// ============================================================
// Arrays+EUF proptest
// ============================================================

use ay_arrays::ArraySolver;

/// Combined Arrays+EUF theory solver for testing.
/// Arrays relies on EUF for equality reasoning on indices and values.
struct CombinedArraysEuf<'a> {
    arrays: ArraySolver<'a>,
    euf: EufSolver<'a>,
}

impl<'a> CombinedArraysEuf<'a> {
    fn new(terms: &'a TermStore) -> Self {
        CombinedArraysEuf {
            arrays: ArraySolver::new(terms),
            euf: EufSolver::new(terms),
        }
    }
}

impl TheorySolver for CombinedArraysEuf<'_> {
    fn assert_literal(&mut self, literal: TermId, value: bool) {
        self.arrays.assert_literal(literal, value);
        self.euf.assert_literal(literal, value);
    }

    fn check(&mut self) -> TheoryResult {
        // Check EUF first (handles equalities)
        match self.euf.check() {
            TheoryResult::Unsat(reasons) => return TheoryResult::Unsat(reasons),
            TheoryResult::UnsatWithFarkas(c) => return TheoryResult::UnsatWithFarkas(c),
            TheoryResult::Unknown => return TheoryResult::Unknown,
            TheoryResult::NeedSplit(s) => return TheoryResult::NeedSplit(s),
            TheoryResult::NeedDisequalitySplit(s) => return TheoryResult::NeedDisequalitySplit(s),
            TheoryResult::NeedExpressionSplit(s) => return TheoryResult::NeedExpressionSplit(s),
            TheoryResult::NeedStringLemma(s) => return TheoryResult::NeedStringLemma(s),
            TheoryResult::NeedModelEquality(e) => return TheoryResult::NeedModelEquality(e),
            TheoryResult::NeedModelEqualities(es) => return TheoryResult::NeedModelEqualities(es),
            TheoryResult::NeedLemmas(l) => return TheoryResult::NeedLemmas(l),
            TheoryResult::Sat => {}
            // Wildcard covers future variants from #[non_exhaustive].
            _ => return TheoryResult::Unknown,
        }
        // Then check array axioms
        self.arrays.check()
    }

    fn propagate(&mut self) -> Vec<ay_core::TheoryPropagation> {
        let mut props = self.euf.propagate();
        props.extend(self.arrays.propagate());
        props
    }

    fn push(&mut self) {
        self.arrays.push();
        self.euf.push();
    }

    fn pop(&mut self) {
        self.arrays.pop();
        self.euf.pop();
    }

    fn reset(&mut self) {
        self.arrays.reset();
        self.euf.reset();
    }
}

// Note: ArrayTermSpec is reserved for future use with more complex array term generation.
// Currently we generate atoms directly using ArrayAtomSpec.

/// Specification for array equality atoms.
#[derive(Clone, Debug)]
struct ArrayAtomSpec {
    /// Index for left select
    lhs_idx: u8,
    /// Index for right select
    rhs_idx: u8,
    /// Whether there's a store on left side
    lhs_has_store: Option<(u8, u8)>, // (store_idx, store_val_idx)
    /// Whether there's a store on right side
    rhs_has_store: Option<(u8, u8)>,
}

fn array_atom_spec_strategy(num_indices: u8) -> impl Strategy<Value = ArrayAtomSpec> {
    (
        0..num_indices,
        0..num_indices,
        proptest::option::of((0..num_indices, 0..num_indices)),
        proptest::option::of((0..num_indices, 0..num_indices)),
    )
        .prop_map(
            |(lhs_idx, rhs_idx, lhs_has_store, rhs_has_store)| ArrayAtomSpec {
                lhs_idx,
                rhs_idx,
                lhs_has_store,
                rhs_has_store,
            },
        )
}

#[derive(Clone, Debug)]
struct ArraysEufCase {
    num_indices: u8,
    atom_specs: Vec<ArrayAtomSpec>,
    expr: BoolExpr,
}

fn arrays_euf_case_strategy() -> impl Strategy<Value = ArraysEufCase> {
    (2u8..=4u8, 2usize..=5usize)
        .prop_flat_map(|(num_indices, num_atoms)| {
            (
                Just(num_indices),
                prop::collection::vec(array_atom_spec_strategy(num_indices), num_atoms),
                bool_expr_strategy(num_atoms),
            )
        })
        .prop_map(|(num_indices, atom_specs, expr)| ArraysEufCase {
            num_indices,
            atom_specs,
            expr,
        })
}

// Note: build_array_term is reserved for future use with recursive ArrayTermSpec.
// Currently we generate atoms directly in the proptest.

/// Brute-force oracle for Arrays+EUF.
/// Uses the combined theory solver to check array axiom consistency.
fn brute_force_expected_arrays_euf(
    terms: &TermStore,
    atoms: &[TermId],
    expr: &BoolExpr,
) -> Expected {
    let used = expr.used_atoms(atoms.len());
    let num_used = used.len();
    if num_used == 0 {
        return Expected::Sat;
    }
    debug_assert!(num_used <= 20, "brute force bound");

    for mask in 0u64..(1u64 << num_used) {
        let mut assignment = vec![false; atoms.len()];
        for (bit, &atom_idx) in used.iter().enumerate() {
            assignment[atom_idx] = ((mask >> bit) & 1) == 1;
        }

        if !expr.eval(&assignment) {
            continue;
        }

        // Check for contradictory assignments to atoms with the same TermId.
        // Due to hash-consing, different atom indices may map to the same TermId.
        let mut term_to_value: std::collections::HashMap<TermId, bool> =
            std::collections::HashMap::new();
        let mut has_conflict = false;
        for &atom_idx in &used {
            let term_id = atoms[atom_idx];
            let value = assignment[atom_idx];
            if let Some(&prev_value) = term_to_value.get(&term_id) {
                if prev_value != value {
                    has_conflict = true;
                    break;
                }
            } else {
                term_to_value.insert(term_id, value);
            }
        }
        if has_conflict {
            continue;
        }

        // Check consistency using the combined theory solver
        let mut theory = CombinedArraysEuf::new(terms);
        for &atom_idx in &used {
            theory.assert_literal(atoms[atom_idx], assignment[atom_idx]);
        }

        match theory.check() {
            TheoryResult::Sat => return Expected::Sat,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => continue,
            TheoryResult::Unknown
            | TheoryResult::NeedSplit(_)
            | TheoryResult::NeedDisequalitySplit(_)
            | TheoryResult::NeedExpressionSplit(_)
            | TheoryResult::NeedStringLemma(_)
            | TheoryResult::NeedModelEquality(_)
            | TheoryResult::NeedModelEqualities(_)
            | TheoryResult::NeedLemmas(_) => {
                // Conservative: treat as possibly SAT
                return Expected::Sat;
            }
            // Wildcard covers future variants from #[non_exhaustive].
            // Conservative: treat unknown variants as possibly SAT to avoid
            // false soundness alarms.
            _ => return Expected::Sat,
        }
    }

    Expected::Unsat
}

proptest! {
    // Default: 256 cases with shrinking enabled for better failure diagnosis.
    // Override with PROPTEST_CASES=1000 for thorough testing.
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// Arrays+EUF proptest - tests integration of array theory with EUF.
    ///
    /// Tests the read-over-write axioms:
    /// - ROW1: select(store(a, i, v), i) = v
    /// - ROW2: i ≠ j → select(store(a, i, v), j) = select(a, j)
    #[test]
    #[timeout(180000)]
    fn proptest_gap9_arrays_euf_combined_formulas(
        case in arrays_euf_case_strategy()
    ) {
        let mut terms = TermStore::new();

        // Create array sort and base array
        let elem_sort = Sort::Int;
        let arr_sort = Sort::array(Sort::Int, elem_sort);
        let base_array = terms.mk_var("arr", arr_sort);

        // Create index and value variables
        let indices: Vec<_> = (0..case.num_indices)
            .map(|i| terms.mk_var(format!("i{i}"), Sort::Int))
            .collect();
        let values: Vec<_> = (0..case.num_indices)
            .map(|i| terms.mk_var(format!("v{i}"), Sort::Int))
            .collect();

        // Build equality atoms from specs
        let atom_terms: Vec<_> = case
            .atom_specs
            .iter()
            .map(|spec| {
                // Build LHS: either select(arr, idx) or select(store(arr, store_idx, store_val), idx)
                let lhs_arr = match spec.lhs_has_store {
                    Some((store_idx, store_val_idx)) => {
                        terms.mk_store(base_array, indices[store_idx as usize], values[store_val_idx as usize])
                    }
                    None => base_array,
                };
                let lhs = terms.mk_select(lhs_arr, indices[spec.lhs_idx as usize]);

                // Build RHS: either select(arr, idx) or select(store(arr, store_idx, store_val), idx)
                let rhs_arr = match spec.rhs_has_store {
                    Some((store_idx, store_val_idx)) => {
                        terms.mk_store(base_array, indices[store_idx as usize], values[store_val_idx as usize])
                    }
                    None => base_array,
                };
                let rhs = terms.mk_select(rhs_arr, indices[spec.rhs_idx as usize]);

                terms.mk_eq(lhs, rhs)
            })
            .collect();

        // Build Boolean structure
        let formula = build_bool_term(&mut terms, &atom_terms, &case.expr);

        let tseitin = Tseitin::new(&terms);
        let cnf = tseitin.transform(formula);

        let theory = CombinedArraysEuf::new(&terms);
        let mut dpll = DpllT::from_tseitin(&terms, &cnf, theory);
        let got = dpll.solve().unwrap();

        let expected = brute_force_expected_arrays_euf(
            &terms,
            &atom_terms,
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
            // This would be a real soundness bug
            (Expected::Unsat, SatResult::Sat(_)) => {
                prop_assert!(false, "Arrays+EUF UNSOUND: expected UNSAT, got SAT");
            }
            #[allow(unreachable_patterns)]
            (_, _) => {}
        }
    }
}
