// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for #4696: TranslationState embedded in a consumer encoder.
//!
//! Verifies:
//! 1. Variable declarations are reused across multiple borrowed sessions.
//! 2. Function declarations are reused across multiple borrowed sessions.
//! 3. Encoder-local metadata stays outside TranslationState.
//! 4. Push/pop works through the borrowed session.

use std::collections::HashMap;

use ay_translate::ops::{self, Comparison};
use ay_translate::{
    FuncDecl, Logic, Solver, Sort, Term, TermTranslator, TranslationSession, TranslationState,
    TranslationTermHost,
};

/// deductive-checks-style encoder: solver and translation state as siblings, with
/// domain metadata kept on the encoder itself.
struct TestEncoder {
    solver: Solver,
    translate: TranslationState<String>,
    var_sorts: HashMap<String, Sort>,
}

impl TestEncoder {
    fn new() -> Self {
        Self {
            solver: Solver::try_new(Logic::QfUflia).expect("solver"),
            translate: TranslationState::new(),
            var_sorts: HashMap::new(),
        }
    }

    fn session(&mut self) -> TranslationSession<'_, String> {
        TranslationSession::new(&mut self.solver, &mut self.translate)
    }
}

// --- Minimal expression AST ---

#[derive(Debug, Clone)]
enum Expr {
    Int(i64),
    Var(String),
    Cmp(Comparison, Box<Self>, Box<Self>),
    App(String, Vec<Self>),
}

struct Tr;

impl TermTranslator for Tr {
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
            Expr::Cmp(op, a, b) => {
                let a = self.translate(ctx, a)?;
                let b = self.translate(ctx, b)?;
                Ok(ops::compare(ctx, *op, a, b))
            }
            Expr::App(name, args) => {
                let domain: Vec<Sort> = args.iter().map(|_| Sort::Int).collect();
                let func = ctx.declare_or_get_fun(name, &domain, Sort::Int);
                let mut arg_terms = Vec::with_capacity(args.len());
                for a in args {
                    arg_terms.push(self.translate(ctx, a)?);
                }
                ctx.solver()
                    .try_apply(&func, &arg_terms)
                    .map_err(|e| e.to_string())
            }
        }
    }
}

/// Variable declarations are reused across multiple borrowed sessions.
#[test]
fn test_var_cache_stable_across_sessions() {
    let mut enc = TestEncoder::new();
    let tr = Tr;

    // Session 1: declare x.
    {
        let mut session = enc.session();
        let _term = tr
            .translate(&mut session, &Expr::Var("x".into()))
            .expect("translate x");
    }
    assert_eq!(enc.translate.var_count(), 1);

    // Session 2: reuse x, declare y.
    {
        let mut session = enc.session();
        let _x = tr
            .translate(&mut session, &Expr::Var("x".into()))
            .expect("translate x again");
        let _y = tr
            .translate(&mut session, &Expr::Var("y".into()))
            .expect("translate y");
    }
    assert_eq!(enc.translate.var_count(), 2, "x reused, y added — total 2");

    // The same variable name returns the same Term handle.
    let x1 = enc.translate.get_var("x");
    let x2 = enc.translate.get_var("x");
    assert_eq!(x1, x2, "same variable key returns same Term");
}

/// Function declarations are reused across multiple borrowed sessions.
#[test]
fn test_func_cache_stable_across_sessions() {
    let mut enc = TestEncoder::new();
    let tr = Tr;

    // Session 1: declare f(Int) -> Int.
    let func1: FuncDecl;
    {
        let mut session = enc.session();
        let _term = tr
            .translate(&mut session, &Expr::App("f".into(), vec![Expr::Int(42)]))
            .expect("translate f(42)");
        func1 = enc.translate.get_func("f").expect("f declared").clone();
    }
    assert_eq!(enc.translate.func_count(), 1);

    // Session 2: reuse f, declare g.
    let func1_again: FuncDecl;
    {
        let mut session = enc.session();
        let _term = tr
            .translate(&mut session, &Expr::App("f".into(), vec![Expr::Int(7)]))
            .expect("translate f(7)");
        let _g = tr
            .translate(
                &mut session,
                &Expr::App("g".into(), vec![Expr::Int(1), Expr::Int(2)]),
            )
            .expect("translate g(1,2)");
        func1_again = enc.translate.get_func("f").expect("f still there").clone();
    }
    assert_eq!(enc.translate.func_count(), 2, "f reused, g added — total 2");
    assert_eq!(
        func1, func1_again,
        "same function name returns same FuncDecl"
    );
}

/// Encoder-local metadata stays outside TranslationState.
#[test]
fn test_encoder_metadata_independent() {
    let mut enc = TestEncoder::new();
    let tr = Tr;

    // Record domain metadata before lowering.
    enc.var_sorts.insert("x".into(), Sort::Int);
    enc.var_sorts.insert("flag".into(), Sort::Bool);

    // Translation session does not touch var_sorts.
    {
        let mut session = enc.session();
        let _term = tr
            .translate(&mut session, &Expr::Var("x".into()))
            .expect("translate");
    }

    assert_eq!(enc.var_sorts.len(), 2, "domain metadata untouched");
    assert_eq!(enc.var_sorts["flag"], Sort::Bool);
}

/// Push/pop works through the borrowed session.
#[test]
fn test_push_pop_through_session() {
    let mut enc = TestEncoder::new();
    let tr = Tr;

    // Assert x > 0.
    {
        let mut session = enc.session();
        let term = tr
            .translate(
                &mut session,
                &Expr::Cmp(
                    Comparison::Gt,
                    Box::new(Expr::Var("x".into())),
                    Box::new(Expr::Int(0)),
                ),
            )
            .expect("x > 0");
        session.assert_term(term);
    }
    assert!(enc.solver.check_sat().is_sat(), "x > 0 is SAT");

    // Push, add x < 0, check UNSAT, pop.
    enc.solver.try_push().expect("push");
    {
        let mut session = enc.session();
        let term = tr
            .translate(
                &mut session,
                &Expr::Cmp(
                    Comparison::Lt,
                    Box::new(Expr::Var("x".into())),
                    Box::new(Expr::Int(0)),
                ),
            )
            .expect("x < 0");
        session.assert_term(term);
    }
    assert!(enc.solver.check_sat().is_unsat(), "x > 0 && x < 0 is UNSAT");

    enc.solver.try_pop().expect("pop");
    assert!(enc.solver.check_sat().is_sat(), "after pop: x > 0 is SAT");
}
