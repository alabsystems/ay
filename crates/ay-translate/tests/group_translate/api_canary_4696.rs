// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! API compatibility canary for #4696 consumer-facing ay-translate re-exports.
//!
//! Downstream repos should be able to depend on `ay-translate` without pulling
//! `ay-dpll` directly just to name solver/result/model/diagnostic types.

use std::any::TypeId;

use ay_translate::{
    AnnotatedCoreLiteral, AnnotatedUnsatCore, ArraySort, AssignmentReason, BitVecSort,
    CongruenceReason, CongruenceStep, CounterexampleStyle, DatatypeConstructor, DatatypeField,
    DatatypeSort, Executor, ExecutorError, FpSpecialKind, FuncDecl, IncrementalCoreEvolution,
    Logic, Model, ModelProvenance, ModelValue, SmtProofCertificate, SolveDetails, SolveResult,
    Solver, SolverError, Sort, Statistics, Term, TermKind, TheoryAttribution, TranslationContext,
    UnknownReason, VariableProvenance, VerificationLevel, VerificationSummary, VerifiedModel,
    VerifiedSolveResult,
};

fn assert_public_type<T: 'static>() {
    let _ = TypeId::of::<T>();
}

#[test]
fn canary_reexported_solver_types_compile() {
    assert_public_type::<ArraySort>();
    assert_public_type::<BitVecSort>();
    assert_public_type::<DatatypeConstructor>();
    assert_public_type::<DatatypeField>();
    assert_public_type::<DatatypeSort>();
    assert_public_type::<Executor>();
    assert_public_type::<ExecutorError>();
    assert_public_type::<FuncDecl>();
    assert_public_type::<Model>();
    assert_public_type::<ModelValue>();
    assert_public_type::<SolveDetails>();
    assert_public_type::<Solver>();
    assert_public_type::<SolverError>();
    assert_public_type::<Statistics>();
    assert_public_type::<Term>();
    assert_public_type::<TranslationContext<String>>();
    assert_public_type::<VerificationSummary>();
    assert_public_type::<VerifiedModel>();
    assert_public_type::<VerifiedSolveResult>();
    // Phase 5 explainability types (#8153)
    assert_public_type::<AnnotatedUnsatCore>();
    assert_public_type::<AnnotatedCoreLiteral>();
    assert_public_type::<TheoryAttribution>();
    // Phase 6 incremental types (#8154)
    assert_public_type::<IncrementalCoreEvolution>();
    assert_public_type::<SmtProofCertificate>();
    // Phase 5 model provenance types (#8153)
    assert_public_type::<AssignmentReason>();
    assert_public_type::<CongruenceReason>();
    assert_public_type::<CongruenceStep>();
    assert_public_type::<ModelProvenance>();
    assert_public_type::<VariableProvenance>();

    let _ = CounterexampleStyle::Minimal;
    let _ = FpSpecialKind::NaN;
    let _ = UnknownReason::Timeout;
    let _ = VerificationLevel::Trusted;
}

#[test]
fn canary_reexported_enums_and_solver_path_stay_stable() {
    let err = ExecutorError::UnsupportedLogic("QF_FAKE".into());
    assert!(
        err.to_string().starts_with("unsupported logic: QF_FAKE"),
        "UnsupportedLogic error should start with the logic name, got: {err}"
    );
    assert_eq!(CounterexampleStyle::default(), CounterexampleStyle::Minimal);
    assert_eq!(UnknownReason::Timeout.to_string(), "timeout");
    assert!(VerificationLevel::Trusted.is_trusted_only());

    #[allow(deprecated)]
    let mut ctx: TranslationContext<String> = TranslationContext::new(Logic::QfLia);
    let x = ctx.get_or_declare("x".to_string(), "x", Sort::Int);
    let zero = ctx.int_const(0);
    let gt_zero = ctx.solver().try_gt(x, zero).expect("x > 0");
    ctx.assert_term(gt_zero);

    let result: VerifiedSolveResult = ctx.check_sat();
    assert_eq!(*result.result(), SolveResult::Sat);
    assert!(result.is_sat(), "simple integer inequality should be SAT");
    assert_eq!(ctx.solver().term_kind(zero), TermKind::Const);

    let stats = Statistics::new();
    assert_eq!(stats.get_int("conflicts"), Some(0));
}
