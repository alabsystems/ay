// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::cell::Cell;
use std::ops::ControlFlow;

use ay_core::original_query::{QueryError, StopReason, WorkBudget};
use ay_core::term::{Symbol, TermData, TermId, TermStore};
use ay_core::Sort;

use super::*;

mod division;
mod numeric;
mod remainder;
mod repeated_roots;
mod rounded;
mod selection;
mod semantics;
mod source_controls;

fn fp_constant(terms: &mut TermStore, bits: u64, width: u32) -> TermId {
    let (eb, sb) = if width == 32 { (8, 24) } else { (11, 53) };
    let bits = terms.mk_bitvec(bits.into(), width);
    terms.mk_app(
        Symbol::indexed("to_fp", vec![eb, sb]),
        [bits],
        Sort::FloatingPoint(eb, sb),
    )
}

fn predicate(terms: &mut TermStore, name: &str, args: &[TermId]) -> TermId {
    terms.mk_app(Symbol::named(name), args, Sort::Bool)
}

fn bindings<'a>(source: TermId, target: &'a ChcVar) -> [FpInputBinding<'a>; 1] {
    [FpInputBinding { source, target }]
}

fn simple(terms: &mut TermStore) -> (TermId, TermId, ChcVar) {
    let input = terms.mk_var("original_x", Sort::FloatingPoint(11, 53));
    let root = predicate(terms, "fp.isNormal", &[input]);
    (
        input,
        root,
        ChcVar::new("original_x", crate::ChcSort::BitVec(64)),
    )
}

#[test]
fn original_raw_word_is_linked_lsb_first_and_all_roots_are_retained() {
    let mut terms = TermStore::new();
    let (input, root, target) = simple(&mut terms);
    let inputs = bindings(input, &target);
    let roots = [root, root];
    let namespace = ChcProblem::new();
    let mut checkpoint = || ControlFlow::Continue(());
    let mut budget = WorkBudget::new(10_000_000_000, &mut checkpoint);
    let output = lower_fp_clause(&terms, &roots, &inputs, &namespace, &mut budget).unwrap();
    assert_eq!(output.source_roots(), &roots);
    assert!(std::ptr::eq(output.source_terms(), &raw const terms));
    assert!(std::ptr::eq(
        output.source_namespace(),
        &raw const namespace
    ));
    let ChcExpr::Op(crate::ChcOp::And, constraints) = output.constraint() else {
        panic!()
    };
    assert!(output
        .auxiliary_variables()
        .iter()
        .all(|v| v.sort == crate::ChcSort::Bool));
    let mut linked_bits = Vec::new();
    for constraint in constraints.iter().rev().take(64).rev() {
        let ChcExpr::Op(crate::ChcOp::Eq, link) = constraint.as_ref() else {
            panic!()
        };
        let ChcExpr::Op(crate::ChcOp::Eq, value) = link[1].as_ref() else {
            panic!()
        };
        let ChcExpr::Op(crate::ChcOp::BvExtract(hi, lo), word) = value[0].as_ref() else {
            panic!()
        };
        assert_eq!(hi, lo);
        assert_eq!(word[0].as_ref(), &ChcExpr::Var(target.clone()));
        assert_eq!(value[1].as_ref(), &ChcExpr::BitVec(1, 1));
        linked_bits.push(*lo);
    }
    assert_eq!(linked_bits, (0..64).collect::<Vec<_>>());
}

#[test]
fn every_literal_rounding_mode_and_format_is_authentic_before_native_entry() {
    for (eb, sb) in [(8, 24), (11, 53)] {
        for rm in ay_fp::RM_ORDER {
            for op in ["fp.add", "fp.sub", "fp.mul"] {
                let mut terms = TermStore::new();
                let x = terms.mk_var("x", Sort::FloatingPoint(eb, sb));
                let y = terms.mk_var("y", Sort::FloatingPoint(eb, sb));
                let mode = terms.mk_app(
                    Symbol::named(rm.name()),
                    [],
                    Sort::Uninterpreted("RoundingMode".into()),
                );
                let result =
                    terms.mk_app(Symbol::named(op), [mode, x, y], Sort::FloatingPoint(eb, sb));
                let root = predicate(&mut terms, "=", &[result, x]);
                let targets = [
                    ChcVar::new("x", crate::ChcSort::BitVec(eb + sb)),
                    ChcVar::new("y", crate::ChcSort::BitVec(eb + sb)),
                ];
                let inputs = [
                    FpInputBinding {
                        source: x,
                        target: &targets[0],
                    },
                    FpInputBinding {
                        source: y,
                        target: &targets[1],
                    },
                ];
                let mut checkpoint = || ControlFlow::Continue(());
                let mut budget = WorkBudget::new(10_000_000_000, &mut checkpoint);
                let plan = source::plan(&terms, &[root], &inputs, &mut budget).unwrap();
                assert!(plan.gates >= 262_144);
                assert!(plan.occurrences >= 6);
            }
        }
    }
}

#[test]
fn native_and_whole_transfer_match_complete_legacy_cnf_without_new_gates() {
    let mut terms = TermStore::new();
    let (input, root, target) = simple(&mut terms);
    let inputs = bindings(input, &target);
    let mut checkpoint = || ControlFlow::Continue(());
    let mut budget = WorkBudget::new(10_000_000_000, &mut checkpoint);
    let plan = source::plan(&terms, &[root], &inputs, &mut budget).unwrap();
    plan.prepay(&mut budget).unwrap();
    let built = encoding::build(&terms, &[root], &plan, &mut budget).unwrap();
    let mut legacy = ay_fp::FpSolver::new(&terms);
    let expected_root = legacy.bitblast_is_normal(input);
    assert_eq!(built.roots, [expected_root]);
    assert_eq!(built.encoding.clauses.as_slice(), legacy.clauses());
    let expected_cache = legacy.export_cache();
    assert_eq!(built.encoding.cache.next_var, expected_cache.next_var);
    let actual_fp = &built.encoding.cache.term_to_fp[&input];
    let expected_fp = &expected_cache.term_to_fp[&input];
    assert_eq!(actual_fp.sign, expected_fp.sign);
    assert_eq!(actual_fp.exponent, expected_fp.exponent);
    assert_eq!(actual_fp.significand, expected_fp.significand);
    let clause_count = built.encoding.clauses.len();
    let variables = built.encoding.cache.next_var - 1;
    let (constraint, auxiliary) = transfer::run(built, &inputs, &plan, &mut budget).unwrap();
    let ChcExpr::Op(crate::ChcOp::And, entries) = &constraint else {
        panic!()
    };
    assert_eq!(entries.len(), clause_count + 1 + 64);
    assert_eq!(auxiliary.len(), variables as usize);
}

#[test]
fn entry_cancellation_and_low_resources_poison_the_same_original_budget() {
    let mut terms = TermStore::new();
    let (input, root, target) = simple(&mut terms);
    let inputs = bindings(input, &target);
    let namespace = ChcProblem::new();
    let stopped = Cell::new(true);
    let mut checkpoint = || {
        if stopped.get() {
            ControlFlow::Break(StopReason::Cancelled)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut budget = WorkBudget::new(10_000_000_000, &mut checkpoint);
    assert!(matches!(
        lower_fp_clause(&terms, &[root], &inputs, &namespace, &mut budget),
        Err(FpAdapterError::Owner(QueryError::Interrupted(
            StopReason::Cancelled
        )))
    ));
    stopped.set(false);
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    );
    let permit = Cell::new(false);
    let mut admission = |_, bytes| {
        if bytes != 0 && !permit.get() {
            Err(QueryError::Exhausted)
        } else {
            Ok(())
        }
    };
    let mut budget = WorkBudget::with_admission(10_000_000_000, &mut admission);
    assert!(matches!(
        lower_fp_clause(&terms, &[root], &inputs, &namespace, &mut budget),
        Err(FpAdapterError::Owner(QueryError::Exhausted))
    ));
    permit.set(true);
    assert_eq!(budget.charge(0), Err(QueryError::Exhausted));
    let mut checkpoint = || ControlFlow::Continue(());
    let mut budget = WorkBudget::new(10_000_000_000, &mut checkpoint);
    let invalid_envelope = source::Plan {
        gates: 0,
        clauses: 0,
        occurrences: 1,
    };
    assert!(matches!(
        encoding::build(&terms, &[root], &invalid_envelope, &mut budget),
        Err(FpAdapterError::Owner(QueryError::Exhausted))
    ));
    assert_eq!(budget.charge(0), Err(QueryError::Exhausted));
}

#[test]
fn final_original_owner_veto_returns_no_complete_data_and_stays_latched() {
    let mut terms = TermStore::new();
    let (input, root, target) = simple(&mut terms);
    let inputs = bindings(input, &target);
    let namespace = ChcProblem::new();
    let calls = Cell::new(0usize);
    let mut count = || {
        calls.set(calls.get() + 1);
        ControlFlow::Continue(())
    };
    let mut budget = WorkBudget::new(10_000_000_000, &mut count);
    assert!(lower_fp_clause(&terms, &[root], &inputs, &namespace, &mut budget).is_ok());
    let final_call = calls.get();
    let calls = Cell::new(0usize);
    let mut stop = || {
        calls.set(calls.get() + 1);
        if calls.get() == final_call {
            ControlFlow::Break(StopReason::Deadline)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut budget = WorkBudget::new(10_000_000_000, &mut stop);
    assert!(matches!(
        lower_fp_clause(&terms, &[root], &inputs, &namespace, &mut budget),
        Err(FpAdapterError::Owner(QueryError::Interrupted(
            StopReason::Deadline
        )))
    ));
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Interrupted(StopReason::Deadline))
    );
}

#[derive(Clone, Copy)]
enum IteForm {
    Direct,
    Named,
}

fn selection_choose(
    terms: &mut TermStore,
    form: IteForm,
    c: TermId,
    a: TermId,
    b: TermId,
) -> TermId {
    match form {
        IteForm::Direct => terms.mk_ite_raw(c, a, b),
        IteForm::Named => {
            let sort = terms.sort(a).clone();
            terms.mk_app(Symbol::named("ite"), [c, a, b], sort)
        }
    }
}

fn selection_native_truth(terms: &TermStore, root: TermId, budget: &mut WorkBudget<'_>) -> bool {
    use ay_sat::{Literal, SatResult, Solver};
    let plan = source::plan(terms, &[root], &[], budget).unwrap();
    plan.prepay(budget).unwrap();
    let built = encoding::build(terms, &[root], &plan, budget).unwrap();
    let vars = (built.encoding.cache.next_var - 1) as usize;
    assert!(vars <= plan.gates && built.encoding.clauses.len() <= plan.clauses);
    // Test-only SAT installation is separately prepaid on the SAME ledger.
    let records = vars + built.encoding.clauses.len() + 1;
    budget.admit(records * 64, records * 512).unwrap();
    let mut sat = Solver::new(vars);
    for clause in &built.encoding.clauses {
        budget.charge(0).unwrap();
        sat.add_clause(
            clause
                .literals()
                .iter()
                .map(|&l| Literal::from_dimacs(l))
                .collect(),
        );
    }
    sat.add_clause(vec![Literal::from_dimacs(built.roots[0])]);
    let result = {
        let ledger = std::cell::RefCell::new(&mut *budget);
        sat.solve_interruptible(|| ledger.borrow_mut().charge(1).is_err())
            .into_inner()
    };
    let truth = match result {
        SatResult::Sat(model) => {
            let value = |lit: i32| model[(lit.unsigned_abs() - 1) as usize] == (lit > 0);
            assert!(value(built.roots[0]));
            assert!(built
                .encoding
                .clauses
                .iter()
                .all(|c| c.literals().iter().any(|&l| value(l))));
            true
        }
        SatResult::Unsat(_) => false,
        _ => panic!("selection control requires a definitive native result"),
    };
    drop(sat);
    drop(built);
    budget.charge(0).unwrap();
    truth
}

fn selection_error(terms: &TermStore, root: TermId) -> FpAdapterError {
    let namespace = ChcProblem::new();
    let mut checkpoint = || ControlFlow::Continue(());
    let mut budget = WorkBudget::new(10_000_000_000, &mut checkpoint);
    match lower_fp_clause(terms, &[root], &[], &namespace, &mut budget) {
        Ok(_) => panic!("malformed/unsupported complete source must refuse"),
        Err(error) => error,
    }
}

fn selection_constant(terms: &mut TermStore) -> TermId {
    let c = terms.mk_bool(true);
    let a = terms.mk_bool(true);
    let b = terms.mk_bool(false);
    selection_choose(terms, IteForm::Direct, c, a, b)
}
