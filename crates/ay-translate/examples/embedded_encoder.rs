// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Embedded encoder example for deductive-checks/verification-consumer-style consumers.
//!
//! This example shows how to embed `TranslationState` into an existing encoder
//! that also owns domain-specific metadata (sort tracking, diagnostics, etc.).
//! The key pattern: keep `solver` and `translate` as sibling fields, construct
//! a short-lived `TranslationSession` inside methods that lower terms, and keep
//! all domain metadata on the encoder itself.
//!
//! Run:
//!   cargo run -p ay-translate --example embedded_encoder

use std::collections::HashMap;

use ay_translate::ops::{self, Comparison};
use ay_translate::{
    Logic, Solver, Sort, Term, TermTranslator, TranslationSession, TranslationState,
    TranslationTermHost,
};

/// A deductive-checks-style encoder that owns a solver, translation state, and additional
/// domain metadata that stays outside the translation layer.
struct EmbeddedEncoder {
    solver: Solver,
    translate: TranslationState<String>,
    /// Domain metadata: tracks the sort of each declared variable.
    /// This stays on the encoder, not in `TranslationState`.
    var_sorts: HashMap<String, Sort>,
    /// Domain metadata: counts how many assertions have been made.
    assertion_count: usize,
}

impl EmbeddedEncoder {
    fn new(logic: Logic) -> Self {
        Self {
            solver: Solver::try_new(logic).expect("solver creation"),
            translate: TranslationState::new(),
            var_sorts: HashMap::new(),
            assertion_count: 0,
        }
    }

    /// Create a borrowed translation session for a single lowering pass.
    fn session(&mut self) -> TranslationSession<'_, String> {
        TranslationSession::new(&mut self.solver, &mut self.translate)
    }

    /// Lower a consumer expression and assert it.
    fn assert_expr(&mut self, translator: &Translator, expr: &Expr) {
        // Record sort metadata on the encoder before lowering.
        collect_var_sorts(expr, &mut self.var_sorts);

        // Create a short-lived session for the lowering pass.
        let mut session = self.session();
        let term = translator
            .translate(&mut session, expr)
            .expect("translation");
        session.try_assert_term(term).expect("assert");
        self.assertion_count += 1;
    }

    /// Check satisfiability through the owned solver.
    fn check_sat(&mut self) -> bool {
        self.solver.check_sat().is_sat()
    }

    fn push(&mut self) {
        self.solver.try_push().expect("push");
    }

    fn pop(&mut self) {
        self.solver.try_pop().expect("pop");
    }
}

// --- Consumer AST and translator (same as simple_translate) ---

#[derive(Debug, Clone)]
enum Expr {
    Int(i64),
    Var { name: String, sort: Sort },
    Cmp(Comparison, Box<Self>, Box<Self>),
}

fn var(name: &str, sort: Sort) -> Expr {
    Expr::Var {
        name: name.to_string(),
        sort,
    }
}

struct Translator;

impl TermTranslator for Translator {
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
            Expr::Var { name, sort } => Ok(ctx.get_or_declare(name.clone(), name, sort.clone())),
            Expr::Cmp(op, a, b) => {
                let a = self.translate(ctx, a)?;
                let b = self.translate(ctx, b)?;
                Ok(ops::compare(ctx, *op, a, b))
            }
        }
    }
}

/// Collect variable sorts from an expression tree into the encoder's metadata.
fn collect_var_sorts(expr: &Expr, sorts: &mut HashMap<String, Sort>) {
    match expr {
        Expr::Var { name, sort } => {
            sorts.insert(name.clone(), sort.clone());
        }
        Expr::Cmp(_, a, b) => {
            collect_var_sorts(a, sorts);
            collect_var_sorts(b, sorts);
        }
        Expr::Int(_) => {}
    }
}

fn main() {
    let translator = Translator;
    let mut enc = EmbeddedEncoder::new(Logic::QfLia);

    // 1. Assert x > 0 — SAT.
    let x = var("x", Sort::Int);
    enc.assert_expr(
        &translator,
        &Expr::Cmp(Comparison::Gt, Box::new(x.clone()), Box::new(Expr::Int(0))),
    );
    assert!(enc.check_sat(), "x > 0 should be SAT");

    // Variable cache is reused: declaring x again returns the same Term.
    assert_eq!(enc.translate.var_count(), 1, "x declared once");

    // Domain metadata is preserved on the encoder.
    assert_eq!(enc.var_sorts.len(), 1);
    assert_eq!(enc.var_sorts["x"], Sort::Int);
    assert_eq!(enc.assertion_count, 1);

    // 2. Add y < 10 in a push/pop scope — still SAT.
    enc.push();
    let y = var("y", Sort::Int);
    enc.assert_expr(
        &translator,
        &Expr::Cmp(Comparison::Lt, Box::new(y), Box::new(Expr::Int(10))),
    );
    assert!(enc.check_sat(), "x > 0 && y < 10 should be SAT");
    assert_eq!(enc.translate.var_count(), 2, "x and y both declared");
    enc.pop();

    // 3. Add x < 0 (contradicts x > 0) — UNSAT.
    enc.push();
    enc.assert_expr(
        &translator,
        &Expr::Cmp(Comparison::Lt, Box::new(x), Box::new(Expr::Int(0))),
    );
    assert!(!enc.check_sat(), "x > 0 && x < 0 should be UNSAT");
    enc.pop();

    // Domain metadata accumulated across all lowering passes.
    assert_eq!(enc.var_sorts.len(), 2, "x and y in sort map");
    assert_eq!(enc.assertion_count, 3);
}
