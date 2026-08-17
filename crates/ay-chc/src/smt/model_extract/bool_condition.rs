// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Boolean-condition evaluation from SMT model values.

use super::{maybe_grow_expr_stack, FxHashMap, SmtContext, SmtValue, TermId};

impl SmtContext {
    /// Evaluate a boolean condition from the model.
    ///
    /// Returns `Some(true)` / `Some(false)` when the condition can be resolved,
    /// `None` when it cannot be determined from the model values.
    pub(super) fn eval_bool_condition(
        &self,
        cond: TermId,
        values: &FxHashMap<String, SmtValue>,
        lia_model: &Option<ay_lia::LiaModel>,
    ) -> Option<bool> {
        maybe_grow_expr_stack(|| self.eval_bool_condition_inner(cond, values, lia_model))
    }

    fn eval_bool_condition_inner(
        &self,
        cond: TermId,
        values: &FxHashMap<String, SmtValue>,
        lia_model: &Option<ay_lia::LiaModel>,
    ) -> Option<bool> {
        use ay_core::term::{Constant, Symbol, TermData};
        match self.terms.get(cond) {
            TermData::Const(Constant::Bool(b)) => Some(*b),
            TermData::Var(name, _) => {
                if let Some(SmtValue::Bool(b)) = values.get(name) {
                    return Some(*b);
                }
                None
            }
            TermData::Not(inner) => self
                .eval_bool_condition(*inner, values, lia_model)
                .map(|b| !b),
            TermData::App(Symbol::Named(name), args) => {
                match name.as_str() {
                    ">=" | "<=" | ">" | "<" if args.len() == 2 => {
                        let lhs = self.get_term_value(args[0], values, lia_model)?;
                        let rhs = self.get_term_value(args[1], values, lia_model)?;
                        Some(match name.as_str() {
                            ">=" => lhs >= rhs,
                            "<=" => lhs <= rhs,
                            ">" => lhs > rhs,
                            "<" => lhs < rhs,
                            _ => return None, // Guarded by outer match; defensive (#6091)
                        })
                    }
                    "=" if args.len() == 2 => {
                        // Try integer equality
                        if let (Some(lhs), Some(rhs)) = (
                            self.get_term_value(args[0], values, lia_model),
                            self.get_term_value(args[1], values, lia_model),
                        ) {
                            return Some(lhs == rhs);
                        }
                        // Try boolean equality
                        if let (Some(l), Some(r)) = (
                            self.eval_bool_condition(args[0], values, lia_model),
                            self.eval_bool_condition(args[1], values, lia_model),
                        ) {
                            return Some(l == r);
                        }
                        None
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }
}
