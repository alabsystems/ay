// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Implicant extraction from formulas under partial models.
//!
//! An implicant is a conjunction of literals that is satisfied by the model
//! and implies the original formula.

use crate::{ChcExpr, ChcOp, ChcSort, SmtValue};
use ay_core::kani_compat::DetHashMap as FxHashMap;

use super::{Literal, Mbp};

impl Mbp {
    /// Extract an implicant from a formula under a model
    ///
    /// An implicant is a conjunction of literals that:
    /// 1. Is satisfied by the model
    /// 2. Implies the original formula
    pub(crate) fn get_implicant(
        &self,
        formula: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
    ) -> Vec<Literal> {
        let mut literals = Vec::new();
        self.collect_implicant(formula, model, &mut literals);
        literals
    }

    pub(super) fn collect_implicant(
        &self,
        formula: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
        literals: &mut Vec<Literal>,
    ) {
        crate::expr::maybe_grow_expr_stack(|| {
            if crate::expr::ExprDepthGuard::check().is_none() {
                return;
            }
            match formula {
                ChcExpr::Bool(true) => {}
                ChcExpr::Bool(false) => {
                    // This shouldn't happen if model satisfies formula
                }
                ChcExpr::Op(ChcOp::And, args) => {
                    for arg in args {
                        self.collect_implicant(arg, model, literals);
                    }
                }
                ChcExpr::Op(ChcOp::Or, args) => {
                    // Pick one satisfied disjunct if we can find one
                    for arg in args {
                        if self.eval_bool(arg, model) == Some(true) {
                            self.collect_implicant(arg, model, literals);
                            return;
                        }
                    }
                    // No definitely-true branch: either all false (shouldn't happen if model
                    // satisfies formula) or at least one unknown due to partial model.
                    // Keep the whole Or as a literal to preserve soundness - implicant must
                    // imply the original formula even when evaluation is incomplete.
                    // See #720: previously this dropped the Or entirely, weakening the implicant.
                    literals.push(Literal::new(formula.clone(), true));
                }
                ChcExpr::Op(ChcOp::Implies, args) if args.len() == 2 => {
                    let antecedent = args[0].as_ref();
                    let consequent = args[1].as_ref();

                    match self.eval_bool(antecedent, model) {
                        Some(false) => {
                            let neg = ChcExpr::not(antecedent.clone());
                            self.collect_implicant(&neg, model, literals);
                        }
                        Some(true) => {
                            self.collect_implicant(consequent, model, literals);
                        }
                        None => {
                            // If consequent is definitely true, implication holds regardless of the antecedent.
                            if self.eval_bool(consequent, model) == Some(true) {
                                self.collect_implicant(consequent, model, literals);
                            } else {
                                // Can't pick a safe conjunction to imply the implication.
                                literals.push(Literal::new(formula.clone(), true));
                            }
                        }
                    }
                }
                ChcExpr::Op(ChcOp::Iff, args) if args.len() == 2 => {
                    let a = args[0].as_ref();
                    let b = args[1].as_ref();

                    match (self.eval_bool(a, model), self.eval_bool(b, model)) {
                        (Some(true), Some(true)) => {
                            self.collect_implicant(a, model, literals);
                            self.collect_implicant(b, model, literals);
                        }
                        (Some(false), Some(false)) => {
                            let na = ChcExpr::not(a.clone());
                            let nb = ChcExpr::not(b.clone());
                            self.collect_implicant(&na, model, literals);
                            self.collect_implicant(&nb, model, literals);
                        }
                        _ => {
                            literals.push(Literal::new(formula.clone(), true));
                        }
                    }
                }
                ChcExpr::Op(ChcOp::Ite, args)
                    if args.len() == 3 && formula.sort() == ChcSort::Bool =>
                {
                    let cond = args[0].as_ref();
                    let then_ = args[1].as_ref();
                    let else_ = args[2].as_ref();

                    match self.eval_bool(cond, model) {
                        Some(true) => {
                            self.collect_implicant(cond, model, literals);
                            self.collect_implicant(then_, model, literals);
                        }
                        Some(false) => {
                            let ncond = ChcExpr::not(cond.clone());
                            self.collect_implicant(&ncond, model, literals);
                            self.collect_implicant(else_, model, literals);
                        }
                        None => {
                            // Can't choose a conjunction without knowing the guard.
                            literals.push(Literal::new(formula.clone(), true));
                        }
                    }
                }
                ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                    let inner = args[0].as_ref();
                    if self.is_atom(inner) {
                        literals.push(Literal::new(inner.clone(), false));
                    } else {
                        // Push NNF inward
                        match inner {
                            ChcExpr::Op(ChcOp::And, inner_args) => {
                                // not(a and b) = not(a) or not(b) - pick one false conjunct
                                for arg in inner_args {
                                    if self.eval_bool(arg, model) == Some(false) {
                                        self.collect_implicant(
                                            &ChcExpr::not(arg.as_ref().clone()),
                                            model,
                                            literals,
                                        );
                                        return;
                                    }
                                }
                                // No definitely-false conjunct found. Same situation as Or:
                                // keep the whole Not(And(...)) to preserve soundness.
                                // See #720: parallel fix for Not(And) case.
                                literals.push(Literal::new(formula.clone(), true));
                            }
                            ChcExpr::Op(ChcOp::Or, inner_args) => {
                                // not(a or b) = not(a) and not(b)
                                for arg in inner_args {
                                    self.collect_implicant(
                                        &ChcExpr::not(arg.as_ref().clone()),
                                        model,
                                        literals,
                                    );
                                }
                            }
                            ChcExpr::Op(ChcOp::Not, inner_inner) if inner_inner.len() == 1 => {
                                // not(not(a)) = a
                                self.collect_implicant(&inner_inner[0], model, literals);
                            }
                            _ => {
                                // Treat as atom
                                literals.push(Literal::new(inner.clone(), false));
                            }
                        }
                    }
                }
                _ => {
                    // Atomic formula
                    if self.is_atom(formula) {
                        literals.push(Literal::new(formula.clone(), true));
                    }
                }
            }
        });
    }

    /// Check if an expression is an atomic formula (not And/Or/Not/Implies)
    pub(super) fn is_atom(&self, expr: &ChcExpr) -> bool {
        match expr {
            ChcExpr::Bool(_) => true,
            ChcExpr::Var(v) => v.sort == ChcSort::Bool,
            ChcExpr::Op(op, _) => matches!(
                op,
                ChcOp::Eq
                    | ChcOp::Ne
                    | ChcOp::Lt
                    | ChcOp::Le
                    | ChcOp::Gt
                    | ChcOp::Ge
                    | ChcOp::BvULt
                    | ChcOp::BvULe
                    | ChcOp::BvUGt
                    | ChcOp::BvUGe
                    | ChcOp::BvSLt
                    | ChcOp::BvSLe
                    | ChcOp::BvSGt
                    | ChcOp::BvSGe
            ),
            ChcExpr::FuncApp(_, sort, _) => *sort == ChcSort::Bool,
            _ => false,
        }
    }
}
