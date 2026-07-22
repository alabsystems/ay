// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(deprecated)]

//! Regression test for #6302: TermTranslator works with both host types.

use ay_translate::ops::{self, Comparison, NaryBoolOp};
use ay_translate::{
    Logic, Solver, Sort, Term, TermTranslator, TranslationContext, TranslationSession,
    TranslationState, TranslationTermHost,
};

#[derive(Debug, Clone)]
enum Expr {
    Int(i64),
    Var(String),
    And(Vec<Self>),
    Cmp(Comparison, Box<Self>, Box<Self>),
}

struct TestTranslator;

impl TermTranslator for TestTranslator {
    type Expr = Expr;
    type VarKey = String;
    type Error = String;

    fn translate<H: TranslationTermHost<Self::VarKey>>(
        &self,
        ctx: &mut H,
        expr: &Self::Expr,
    ) -> Result<Term, Self::Error> {
        match expr {
            Expr::Int(n) => Ok(ctx.solver().int_const(*n)),
            Expr::Var(name) => Ok(ctx.get_or_declare(name.clone(), name, Sort::Int)),
            Expr::And(items) => {
                let mut terms = Vec::with_capacity(items.len());
                for item in items {
                    terms.push(self.translate(ctx, item)?);
                }
                Ok(ops::bool_nary(ctx, NaryBoolOp::And, &terms))
            }
            Expr::Cmp(op, a, b) => {
                let a = self.translate(ctx, a)?;
                let b = self.translate(ctx, b)?;
                Ok(ops::compare(ctx, *op, a, b))
            }
        }
    }
}

/// Same translator produces SAT via both TranslationContext and TranslationSession.
#[test]
fn test_dual_host_sat() {
    let tr = TestTranslator;

    // x > 0 && x < 10
    let formula = Expr::And(vec![
        Expr::Cmp(
            Comparison::Gt,
            Box::new(Expr::Var("x".into())),
            Box::new(Expr::Int(0)),
        ),
        Expr::Cmp(
            Comparison::Lt,
            Box::new(Expr::Var("x".into())),
            Box::new(Expr::Int(10)),
        ),
    ]);

    // Path 1: TranslationContext (owning host)
    let result_ctx = {
        let mut ctx: TranslationContext<String> = TranslationContext::new(Logic::QfLia);
        let term = tr
            .translate(&mut ctx, &formula)
            .expect("translate with ctx");
        ctx.assert_term(term);
        ctx.check_sat().is_sat()
    };

    // Path 2: TranslationSession (borrowed host)
    let result_session = {
        let mut solver = Solver::try_new(Logic::QfLia).expect("QfLia");
        let mut state = TranslationState::new();
        let mut session = TranslationSession::new(&mut solver, &mut state);
        let term = tr
            .translate(&mut session, &formula)
            .expect("translate with session");
        session.solver().try_assert_term(term).expect("assert");
        session.solver().check_sat().is_sat()
    };

    assert!(result_ctx, "owning host should return SAT");
    assert!(result_session, "borrowed host should return SAT");
}

/// Same translator produces UNSAT via both hosts.
#[test]
fn test_dual_host_unsat() {
    let tr = TestTranslator;

    // x > 0 && x < 0 (contradiction)
    let formula = Expr::And(vec![
        Expr::Cmp(
            Comparison::Gt,
            Box::new(Expr::Var("x".into())),
            Box::new(Expr::Int(0)),
        ),
        Expr::Cmp(
            Comparison::Lt,
            Box::new(Expr::Var("x".into())),
            Box::new(Expr::Int(0)),
        ),
    ]);

    // Path 1: TranslationContext
    let result_ctx = {
        let mut ctx: TranslationContext<String> = TranslationContext::new(Logic::QfLia);
        let term = tr
            .translate(&mut ctx, &formula)
            .expect("translate with ctx");
        ctx.assert_term(term);
        ctx.check_sat().is_unsat()
    };

    // Path 2: TranslationSession
    let result_session = {
        let mut solver = Solver::try_new(Logic::QfLia).expect("QfLia");
        let mut state = TranslationState::new();
        let mut session = TranslationSession::new(&mut solver, &mut state);
        let term = tr
            .translate(&mut session, &formula)
            .expect("translate with session");
        session.solver().try_assert_term(term).expect("assert");
        session.solver().check_sat().is_unsat()
    };

    assert!(result_ctx, "owning host should return UNSAT");
    assert!(result_session, "borrowed host should return UNSAT");
}
