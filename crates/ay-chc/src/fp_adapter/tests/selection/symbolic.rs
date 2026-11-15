// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Symbolic mux semantics; native test results are not CHC/proof credentials.

use super::*;

struct Fixture {
    terms: TermStore,
    roots: [TermId; 4],
    sources: [TermId; 3],
    targets: [ChcVar; 3],
}

#[test]
fn symbolic_condition_and_both_free_arms_select_exact_words_under_one_owner() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut poll = || {
        if Instant::now() >= end {
            ControlFlow::Break(StopReason::Deadline)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut budget = WorkBudget::new(10_000_000_000, &mut poll);
    for form in [IteForm::Direct, IteForm::Named] {
        for width in [0, 32, 64] {
            for condition in [false, true] {
                for correct in [true, false] {
                    // Bounded test fixture scratch, on the SAME original ledger.
                    budget.admit(4096, 32_768).unwrap();
                    let fixture = fixture(form, width, condition, correct);
                    assert_eq!(native_truth(&fixture, &mut budget), correct);
                    drop(fixture);
                    budget.charge(0).unwrap();
                }
            }
        }
    }
}

fn fixture(form: IteForm, width: u32, condition: bool, correct: bool) -> Fixture {
    let mut terms = TermStore::new();
    let (sort, target_sort) = match width {
        0 => (Sort::Bool, crate::ChcSort::Bool),
        32 => (Sort::FloatingPoint(8, 24), crate::ChcSort::BitVec(32)),
        64 => (Sort::FloatingPoint(11, 53), crate::ChcSort::BitVec(64)),
        _ => panic!("bounded symbolic fixture format"),
    };
    let c = terms.mk_var("symbolic_condition", Sort::Bool);
    let a = terms.mk_var("symbolic_left", sort.clone());
    let b = terms.mk_var("symbolic_right", sort);
    let selected = selection_choose(&mut terms, form, c, a, b);
    let condition_root = if condition { c } else { terms.mk_not_raw(c) };
    let other_roots = if width == 0 {
        let yes = terms.mk_bool(true);
        let no = terms.mk_bool(false);
        let left = predicate(&mut terms, "=", &[a, yes]);
        let right = predicate(&mut terms, "=", &[b, no]);
        let expected = if correct { condition } else { !condition };
        let output = if expected {
            selected
        } else {
            terms.mk_not_raw(selected)
        };
        [left, right, output]
    } else {
        // Independent manual +1/-1 words, never computed by the mux under test.
        let (one, sign) = if width == 32 {
            (0x3f800000u64, 1u64 << 31)
        } else {
            (0x3ff0000000000000u64, 1u64 << 63)
        };
        let left = fp_constant(&mut terms, one, width);
        let right = fp_constant(&mut terms, sign | one, width);
        let expected = if condition { one } else { sign | one };
        let expected = fp_constant(
            &mut terms,
            if correct { expected } else { expected ^ 1 },
            width,
        );
        [
            predicate(&mut terms, "=", &[a, left]),
            predicate(&mut terms, "=", &[b, right]),
            predicate(&mut terms, "=", &[selected, expected]),
        ]
    };
    Fixture {
        terms,
        roots: [
            condition_root,
            other_roots[0],
            other_roots[1],
            other_roots[2],
        ],
        sources: [c, a, b],
        targets: [
            ChcVar::new("symbolic_condition", crate::ChcSort::Bool),
            ChcVar::new("symbolic_left", target_sort.clone()),
            ChcVar::new("symbolic_right", target_sort),
        ],
    }
}

fn native_truth(fixture: &Fixture, budget: &mut WorkBudget<'_>) -> bool {
    use ay_sat::{Literal, SatResult, Solver};
    let inputs = [
        FpInputBinding {
            source: fixture.sources[0],
            target: &fixture.targets[0],
        },
        FpInputBinding {
            source: fixture.sources[1],
            target: &fixture.targets[1],
        },
        FpInputBinding {
            source: fixture.sources[2],
            target: &fixture.targets[2],
        },
    ];
    let plan = source::plan(&fixture.terms, &fixture.roots, &inputs, budget).unwrap();
    plan.prepay(budget).unwrap();
    let built = encoding::build(&fixture.terms, &fixture.roots, &plan, budget).unwrap();
    let vars = (built.encoding.cache.next_var - 1) as usize;
    assert!(vars <= plan.gates && built.encoding.clauses.len() <= plan.clauses);
    assert_eq!(built.roots.len(), fixture.roots.len());
    let condition = built.encoding.cache.bool_input_lits[&fixture.sources[0]];
    // Free, distinct arms forbid constant/equal-arm simplification. This check
    // runs BEFORE root units are installed, so those cannot fake mux coverage.
    let mut condition_clauses = 0usize;
    for clause in &built.encoding.clauses {
        budget.charge(1 + clause.literals().len()).unwrap();
        if clause
            .literals()
            .iter()
            .any(|&lit| lit == condition || lit == -condition)
        {
            condition_clauses += 1;
        }
    }
    assert!(
        condition_clauses >= 4,
        "selection must emit genuine symbolic mux clauses"
    );
    // Test-only native installation is prepaid, without a second allowance.
    let records = vars + built.encoding.clauses.len() + built.roots.len();
    budget.admit(records * 64, records * 512).unwrap();
    let mut sat = Solver::new(vars);
    for clause in &built.encoding.clauses {
        budget.charge(0).unwrap();
        sat.add_clause(
            clause
                .literals()
                .iter()
                .map(|&lit| Literal::from_dimacs(lit))
                .collect(),
        );
    }
    for &root in &built.roots {
        budget.charge(0).unwrap();
        sat.add_clause(vec![Literal::from_dimacs(root)]);
    }
    let result = {
        let ledger = std::cell::RefCell::new(&mut *budget);
        sat.solve_interruptible(|| ledger.borrow_mut().charge(1).is_err())
            .into_inner()
    };
    let truth = match result {
        SatResult::Sat(model) => {
            let value = |lit: i32| model[(lit.unsigned_abs() - 1) as usize] == (lit > 0);
            for &root in &built.roots {
                budget.charge(1).unwrap();
                assert!(value(root));
            }
            for clause in &built.encoding.clauses {
                budget.charge(1 + clause.literals().len()).unwrap();
                assert!(clause.literals().iter().any(|&lit| value(lit)));
            }
            true
        }
        SatResult::Unsat(_) => false,
        _ => panic!("symbolic selection control requires a definitive native result"),
    };
    drop(sat);
    drop(built);
    budget.charge(0).unwrap();
    truth
}
