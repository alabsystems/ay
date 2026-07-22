// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Minimal translation example for ay consumers.
//!
//! Run:
//!   cargo run -p ay-translate --example simple_translate

use ay_translate::ops::{self, Comparison, NaryBoolOp};
use ay_translate::{
    Logic, Sort, SortTranslator, Term, TermTranslator, TranslationContext, TranslationTermHost,
};

#[derive(Debug, Clone, Copy)]
enum MySort {
    Bool,
    Int,
}

#[derive(Debug, Clone)]
enum Expr {
    Bool(bool),
    Int(i64),
    Var { name: String, sort: MySort },
    Not(Box<Self>),
    And(Vec<Self>),
    Add(Box<Self>, Box<Self>),
    Cmp(Comparison, Box<Self>, Box<Self>),
}

#[derive(Debug, thiserror::Error)]
#[error("{0}")]
struct TranslateError(String);

#[derive(Default)]
struct Translator;

impl SortTranslator for Translator {
    type Sort = MySort;
    type Error = TranslateError;

    fn translate_sort(&self, sort: &Self::Sort) -> Result<Sort, Self::Error> {
        Ok(match sort {
            MySort::Bool => Sort::Bool,
            MySort::Int => Sort::Int,
        })
    }
}

impl TermTranslator for Translator {
    type Expr = Expr;
    type VarKey = String;
    type Error = TranslateError;

    fn translate<H: TranslationTermHost<Self::VarKey>>(
        &self,
        ctx: &mut H,
        expr: &Self::Expr,
    ) -> Result<Term, Self::Error> {
        match expr {
            Expr::Bool(b) => Ok(ctx.solver().bool_const(*b)),
            Expr::Int(n) => Ok(ctx.solver().int_const(*n)),
            Expr::Var { name, sort } => {
                let ay_sort = self.translate_sort(sort)?;
                Ok(ctx.get_or_declare(name.clone(), name, ay_sort))
            }
            Expr::Not(inner) => {
                let inner = self.translate(ctx, inner)?;
                Ok(ops::bool_not(ctx, inner))
            }
            Expr::And(items) => {
                if items.is_empty() {
                    return Ok(ctx.solver().bool_const(true));
                }
                let mut terms = Vec::with_capacity(items.len());
                for item in items {
                    terms.push(self.translate(ctx, item)?);
                }
                Ok(ops::bool_nary(ctx, NaryBoolOp::And, &terms))
            }
            Expr::Add(a, b) => {
                let a = self.translate(ctx, a)?;
                let b = self.translate(ctx, b)?;
                Ok(ops::arith::add(ctx, a, b))
            }
            Expr::Cmp(op, a, b) => {
                let a = self.translate(ctx, a)?;
                let b = self.translate(ctx, b)?;
                Ok(ops::compare(ctx, *op, a, b))
            }
        }
    }
}

fn expr_var(name: &str, sort: MySort) -> Expr {
    Expr::Var {
        name: name.to_string(),
        sort,
    }
}

fn main() -> Result<(), TranslateError> {
    let tr = Translator;
    #[allow(deprecated)]
    let mut ctx: TranslationContext<String> = TranslationContext::new(Logic::QfLia);

    // Sanity: 1 + 2 = 3 is satisfiable (exercises Expr::Add).
    let one_plus_two_eq_three = Expr::Cmp(
        Comparison::Eq,
        Box::new(Expr::Add(Box::new(Expr::Int(1)), Box::new(Expr::Int(2)))),
        Box::new(Expr::Int(3)),
    );
    let term = tr.translate(&mut ctx, &one_plus_two_eq_three)?;
    ctx.assert_term(term);

    // Example: x > 0 && x < 10 is satisfiable.
    let x = expr_var("x", MySort::Int);
    let gt0 = Expr::Cmp(Comparison::Gt, Box::new(x.clone()), Box::new(Expr::Int(0)));
    let lt10 = Expr::Cmp(Comparison::Lt, Box::new(x.clone()), Box::new(Expr::Int(10)));
    let in_range = Expr::And(vec![gt0, lt10, Expr::Bool(true)]);
    let in_range = tr.translate(&mut ctx, &in_range)?;
    ctx.assert_term(in_range);
    let result = ctx.check_sat();
    if !result.is_sat() {
        return Err(TranslateError(format!("expected Sat, got {result:?}")));
    }

    // Example: b && !b is unsatisfiable (exercises MySort::Bool + Expr::Not).
    ctx.push();
    let b = expr_var("b", MySort::Bool);
    let b_and_not_b = Expr::And(vec![b.clone(), Expr::Not(Box::new(b))]);
    let term = tr.translate(&mut ctx, &b_and_not_b)?;
    ctx.assert_term(term);
    let result = ctx.check_sat();
    if !result.is_unsat() {
        return Err(TranslateError(format!("expected Unsat, got {result:?}")));
    }
    ctx.pop();

    // Example: (x = 0) && (x > 0) is unsatisfiable.
    ctx.push();
    let eq0 = Expr::Cmp(Comparison::Eq, Box::new(x.clone()), Box::new(Expr::Int(0)));
    let gt0 = Expr::Cmp(Comparison::Gt, Box::new(x), Box::new(Expr::Int(0)));
    let term = tr.translate(&mut ctx, &Expr::And(vec![eq0, gt0]))?;
    ctx.assert_term(term);
    let result = ctx.check_sat();
    if !result.is_unsat() {
        return Err(TranslateError(format!("expected Unsat, got {result:?}")));
    }
    ctx.pop();

    Ok(())
}
