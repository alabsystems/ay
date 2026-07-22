// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// NIA (Non-linear Integer Arithmetic) proptest theory integration.
//
// Generates small nonlinear formulas over 2 integer variables x, y with
// monomials x*y and x^2, cross-checks DPLL(T) against a brute-force oracle
// that enumerates integer values in a bounded range.
//
// Part of #3512

use ay_nia::NiaSolver;

/// Comparison operators for NIA atoms.
#[derive(Clone, Copy, Debug)]
enum NiaCmp {
    Le,
    Ge,
}

/// Specifies a nonlinear atom: `term cmp bound` where term is one of x*y, x^2,
/// or a linear term (x, y).
#[derive(Clone, Debug)]
enum NiaTermKind {
    /// x * y
    Product,
    /// x * x
    Square,
    /// A single variable (0 = x, 1 = y)
    Linear(usize),
}

#[derive(Clone, Debug)]
struct NiaAtomSpec {
    term: NiaTermKind,
    cmp: NiaCmp,
    bound: i8,
}

fn nia_atom_spec_strategy() -> impl Strategy<Value = NiaAtomSpec> {
    (
        prop_oneof![
            Just(NiaTermKind::Product),
            Just(NiaTermKind::Square),
            Just(NiaTermKind::Linear(0)),
            Just(NiaTermKind::Linear(1)),
        ],
        prop_oneof![Just(NiaCmp::Le), Just(NiaCmp::Ge)],
        -3i8..=3i8,
    )
        .prop_map(|(term, cmp, bound)| NiaAtomSpec { term, cmp, bound })
}

/// NIA case: atoms over two integer variables x and y.
#[derive(Clone, Debug)]
struct NiaCase {
    atom_specs: Vec<NiaAtomSpec>,
    expr: BoolExpr,
}

fn nia_case_strategy() -> impl Strategy<Value = NiaCase> {
    (1usize..=4usize)
        .prop_flat_map(|num_atoms| {
            (
                prop::collection::vec(nia_atom_spec_strategy(), num_atoms),
                bool_expr_strategy(num_atoms),
            )
        })
        .prop_map(|(atom_specs, expr)| NiaCase { atom_specs, expr })
}

/// Evaluate an NIA term at given integer values for (x, y).
fn eval_nia_term(term: &NiaTermKind, x_val: i64, y_val: i64) -> i64 {
    match term {
        NiaTermKind::Product => x_val.saturating_mul(y_val),
        NiaTermKind::Square => x_val.saturating_mul(x_val),
        NiaTermKind::Linear(0) => x_val,
        NiaTermKind::Linear(1) => y_val,
        NiaTermKind::Linear(_) => unreachable!(),
    }
}

/// Check if a Boolean assignment to atoms is theory-satisfiable by enumerating
/// integer values in [-5, 5] for both x and y.
fn nia_theory_satisfiable(atom_specs: &[NiaAtomSpec], assignment: &[bool], used: &[usize]) -> bool {
    for x_val in -5i64..=5 {
        for y_val in -5i64..=5 {
            let mut all_ok = true;
            for &atom_idx in used {
                let spec = &atom_specs[atom_idx];
                let val = assignment[atom_idx];
                let term_val = eval_nia_term(&spec.term, x_val, y_val);
                let bound = i64::from(spec.bound);

                let holds = match spec.cmp {
                    NiaCmp::Le => term_val <= bound,
                    NiaCmp::Ge => term_val >= bound,
                };

                if holds != val {
                    all_ok = false;
                    break;
                }
            }
            if all_ok {
                return true;
            }
        }
    }
    false
}

/// Brute-force oracle for NIA: enumerate Boolean assignments, then integer values.
fn brute_force_expected_nia(atom_specs: &[NiaAtomSpec], expr: &BoolExpr) -> Expected {
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

        if nia_theory_satisfiable(atom_specs, &assignment, &used) {
            return Expected::Sat;
        }
    }

    Expected::Unsat
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    /// NIA proptest: soundness of NIA DPLL(T) integration.
    ///
    /// NIA is incomplete (QF_NIA is undecidable), so Unknown is always acceptable.
    /// Soundness violations: claiming SAT when formula is UNSAT, or vice versa.
    #[test]
    #[timeout(180000)]
    fn proptest_nia_random_theory_formulas(
        case in nia_case_strategy()
    ) {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);

        // Pre-build nonlinear terms
        let xy = terms.mk_mul(vec![x, y]);
        let xx = terms.mk_mul(vec![x, x]);

        let atom_terms = case
            .atom_specs
            .iter()
            .map(|spec| {
                let op = match spec.cmp {
                    NiaCmp::Le => "<=",
                    NiaCmp::Ge => ">=",
                };
                let lhs = match &spec.term {
                    NiaTermKind::Product => xy,
                    NiaTermKind::Square => xx,
                    NiaTermKind::Linear(0) => x,
                    NiaTermKind::Linear(1) => y,
                    NiaTermKind::Linear(_) => unreachable!(),
                };
                let bound_term = terms.mk_int(i64::from(spec.bound).into());
                terms.mk_app(
                    Symbol::Named(op.to_string()),
                    vec![lhs, bound_term],
                    Sort::Bool,
                )
            })
            .collect::<Vec<_>>();

        let formula = build_bool_term(&mut terms, &atom_terms, &case.expr);

        let tseitin = Tseitin::new(&terms);
        let cnf = tseitin.transform(formula);

        let theory = NiaSolver::new(&terms);
        let mut dpll = DpllT::from_tseitin(&terms, &cnf, theory);
        let got = dpll.solve().unwrap();

        let expected = brute_force_expected_nia(&case.atom_specs, &case.expr);

        match (expected, got) {
            (Expected::Sat, SatResult::Sat(_)) => {}
            (Expected::Unsat, SatResult::Unsat(_)) => {}
            // Unknown is always acceptable for NIA (incomplete theory)
            (_, SatResult::Unknown) => {}
            (Expected::Sat, SatResult::Unsat(_)) => {
                prop_assert!(false, "NIA UNSOUND: expected SAT, got UNSAT");
            }
            (Expected::Unsat, SatResult::Sat(_)) => {
                prop_assert!(false, "NIA UNSOUND: expected UNSAT, got SAT");
            }
            #[allow(unreachable_patterns)]
            (_, _) => {}
        }
    }
}
