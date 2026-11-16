// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
#![allow(clippy::unwrap_used)]

use super::*;
use crate::api::Logic;

mod native;

fn parsed(text: &str) -> Solver {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    solver.set_term_memory_limit(Some(64 * 1024 * 1024));
    solver.parse_smtlib2(text).unwrap();
    solver
}

#[test]
fn requests_use_parsed_source_signatures_without_native_handles_or_term_growth() {
    let solver = parsed(
        "(declare-fun |f with space| (Bool (_ BitVec 72)) (_ BitVec 136))
        (declare-fun zero () (_ BitVec 128))",
    );
    assert!(solver.declared_variables().next().is_none());
    let before = solver.terms().len();
    let requests = solver
        .scalar_function_requests(&["zero", "f with space"])
        .unwrap();
    assert_eq!(requests[0], ("zero", [].as_slice(), &Sort::bitvec(128)));
    assert_eq!(requests[1].0, "f with space");
    assert_eq!(requests[1].1, [Sort::Bool, Sort::bitvec(72)]);
    assert_eq!(requests[1].2, &Sort::bitvec(136));
    assert!(std::ptr::eq(
        requests[1].2,
        &raw const solver
            .executor
            .context()
            .symbol_info("f with space")
            .unwrap()
            .sort
    ));
    assert!(solver.scalar_function_requests(&["zero", "zero"]).is_err());
    assert!(solver
        .scalar_function_requests(&["zero", "missing"])
        .is_err());
    assert!(solver
        .scalar_function_requests(&["|f with space|"])
        .is_err());
    assert_eq!(before, solver.terms().len());
}

#[test]
fn adopted_original_functions_remain_eligible_but_definitions_and_non_scalar_sorts_refuse() {
    let mut solver = parsed(
        "(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (assert (forall ((x (_ BitVec 8))) (= (f x) (bvadd x #x01))))
        (define-fun defined ((x (_ BitVec 8))) (_ BitVec 8) x)
        (declare-fun relation ((_ BitVec 8)) Bool)
        (declare-fun integer (Int) (_ BitVec 8))
        (declare-fun array ((Array (_ BitVec 8) Bool)) (_ BitVec 8))
        (declare-fun f_over (Bool) (_ BitVec 8))
        (declare-fun f_over ((_ BitVec 8)) (_ BitVec 8))",
    );
    assert!(solver.scalar_function_requests(&["f"]).is_ok());
    solver.try_declare_const("native", Sort::bitvec(8)).unwrap();
    for name in [
        "defined", "relation", "integer", "array", "f_over", "native",
    ] {
        assert!(solver.scalar_function_requests(&[name]).is_err(), "{name}");
    }
}

#[test]
fn lookup_tracks_scope_redeclarations_and_missing_sat_state() {
    let mut solver = parsed("");
    assert!(matches!(
        solver.try_get_named_scalar_function_models(&[]),
        Err(SolverError::NoResult)
    ));
    solver.try_push().unwrap();
    solver
        .parse_smtlib2("(declare-fun f ((_ BitVec 8)) (_ BitVec 8))")
        .unwrap();
    assert_eq!(
        solver.scalar_function_requests(&["f"]).unwrap()[0].2,
        &Sort::bitvec(8)
    );
    solver.try_pop().unwrap();
    assert!(solver.scalar_function_requests(&["f"]).is_err());
    solver
        .parse_smtlib2("(declare-fun f (Bool) (_ BitVec 136))")
        .unwrap();
    let requests = solver.scalar_function_requests(&["f"]).unwrap();
    assert_eq!(requests[0].1, [Sort::Bool]);
    assert_eq!(requests[0].2, &Sort::bitvec(136));
}

#[test]
fn request_and_signature_limits_are_shared_exact_and_refuse_wide_metadata() {
    let names: Vec<_> = (0..MAX_FUNCTIONS)
        .map(|index| format!("f{index}"))
        .collect();
    let borrowed: Vec<_> = names.iter().map(String::as_str).collect();
    assert!(SignatureBudget::default().names(&borrowed).is_ok());
    assert!(SignatureBudget::default()
        .names(&vec!["f"; MAX_FUNCTIONS + 1])
        .is_err());
    let exact = "x".repeat(MAX_REQUEST_BYTES / 2 - 1);
    assert!(SignatureBudget::default().names(&[&exact]).is_ok());
    assert!(SignatureBudget::default().names(&[&(exact + "x")]).is_err());
    let mut measured = SignatureBudget::default();
    measured
        .sort(&Sort::bitvec(MAX_API_BITVECTOR_WIDTH))
        .unwrap();
    let (work, bytes) = (measured.work, measured.bytes);
    let mut exact = SignatureBudget {
        work: MAX_SIGNATURE_WORK - work,
        bytes: MAX_SIGNATURE_BYTES - bytes,
    };
    exact.sort(&Sort::bitvec(MAX_API_BITVECTOR_WIDTH)).unwrap();
    assert_eq!(
        (exact.work, exact.bytes),
        (MAX_SIGNATURE_WORK, MAX_SIGNATURE_BYTES)
    );
    assert!(exact.sort(&Sort::Bool).is_err());
    for sort in [
        Sort::bitvec(0),
        Sort::bitvec(MAX_API_BITVECTOR_WIDTH + 1),
        Sort::bitvec(u32::MAX),
        Sort::array(Sort::Bool, Sort::Bool),
    ] {
        assert!(SignatureBudget::default().sort(&sort).is_err());
    }
}

#[test]
fn interrupted_or_memory_refused_request_cannot_reach_the_model_printer() {
    let mut solver = parsed("(declare-fun f () (_ BitVec 8))");
    solver.interrupt();
    assert!(solver.scalar_function_requests(&["f"]).is_err());
    solver.interrupt_handle().store(false, Ordering::Relaxed);
    assert!(solver.scalar_function_requests(&["f"]).is_ok());
    solver.set_term_memory_limit(Some(1));
    assert!(solver.scalar_function_requests(&["f"]).is_err());
}
