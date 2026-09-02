// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model extraction and term-to-expression conversion.

mod bool_condition;

use super::context::SmtContext;
use super::types::{SmtResult, SmtValue};
use crate::term_bridge::sort::core_sort_to_chc_strict;
use std::sync::Arc;

use crate::expr::{maybe_grow_expr_stack, ChcOp};
use crate::{ChcExpr, ChcVar};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::term::{Constant, TermData};
use ay_core::TermId;
use num_bigint::BigInt;
use num_traits::ToPrimitive;

impl SmtContext {
    pub(crate) fn term_to_chc_expr(&self, term: TermId) -> Option<ChcExpr> {
        fn bigint_to_i64_exact(v: &BigInt) -> Option<i64> {
            v.to_i64()
        }

        fn go(
            ctx: &SmtContext,
            term: TermId,
            memo: &mut FxHashMap<TermId, ChcExpr>,
        ) -> Option<ChcExpr> {
            maybe_grow_expr_stack(|| go_inner(ctx, term, memo))
        }

        fn go_inner(
            ctx: &SmtContext,
            term: TermId,
            memo: &mut FxHashMap<TermId, ChcExpr>,
        ) -> Option<ChcExpr> {
            if let Some(e) = memo.get(&term) {
                return Some(e.clone());
            }

            let expr = match ctx.terms.get(term) {
                TermData::Const(Constant::Bool(b)) => ChcExpr::Bool(*b),
                // Phase-2 BigInt escape: beyond-i128 solver constants re-enter
                // the symbolic lane as Horner trees (exact) instead of
                // aborting the whole extraction fail-closed.
                TermData::Const(Constant::Int(n)) => ChcExpr::from_bigint(n.clone()),
                TermData::Const(Constant::Rational(r)) => {
                    let mut num = bigint_to_i64_exact(r.0.numer())?;
                    let mut denom = bigint_to_i64_exact(r.0.denom())?;
                    if denom == 0 {
                        return None;
                    }
                    if denom < 0 {
                        num = -num;
                        denom = -denom;
                    }
                    ChcExpr::Real(num, denom)
                }
                TermData::Const(Constant::BitVec { value, width }) => {
                    // Core terms use BigInt storage. Normalize through the
                    // exact model-value path so even a non-canonical negative
                    // residue is reconstructed modulo 2^width rather than
                    // being rejected by `to_biguint`.
                    SmtValue::bitvec_from_bigint(value.clone(), *width).bitvec_to_chc_expr()?
                }
                TermData::Const(Constant::String(_)) => return None,
                TermData::Var(name, _) => {
                    let chc_sort = core_sort_to_chc_strict(ctx.terms.sort(term))?;
                    // #6100: term names are sort-qualified; recover original
                    // CHC name via reverse map for correct roundtrip.
                    let original = ctx.original_var_name(name);
                    ChcExpr::Var(ChcVar::new(original.to_owned(), chc_sort))
                }
                TermData::Not(inner) => ChcExpr::not(go(ctx, *inner, memo)?),
                TermData::Ite(c, t, e) => {
                    ChcExpr::ite(go(ctx, *c, memo)?, go(ctx, *t, memo)?, go(ctx, *e, memo)?)
                }
                TermData::Let(_bindings, body) => {
                    // Let bindings should be expanded before reaching model
                    // extraction (TermData::Let comment: "after expansion this
                    // should not appear"). When they do appear, convert the body
                    // — the TermId DAG is referentially transparent so the body
                    // already references the bound values directly (#6097).
                    return go(ctx, *body, memo);
                }
                TermData::Forall(..) | TermData::Exists(..) => return None,
                TermData::App(sym, args) => {
                    let name = sym.name();
                    match name {
                        "and" => args
                            .iter()
                            .copied()
                            .map(|a| go(ctx, a, memo))
                            .reduce(|a, b| Some(ChcExpr::and(a?, b?)))??,
                        "or" => args
                            .iter()
                            .copied()
                            .map(|a| go(ctx, a, memo))
                            .reduce(|a, b| Some(ChcExpr::or(a?, b?)))??,
                        "=>" => {
                            if args.len() != 2 {
                                return None;
                            }
                            ChcExpr::implies(go(ctx, args[0], memo)?, go(ctx, args[1], memo)?)
                        }
                        "=" => {
                            if args.len() != 2 {
                                return None;
                            }
                            ChcExpr::eq(go(ctx, args[0], memo)?, go(ctx, args[1], memo)?)
                        }
                        "distinct" => {
                            if args.len() != 2 {
                                return None;
                            }
                            ChcExpr::ne(go(ctx, args[0], memo)?, go(ctx, args[1], memo)?)
                        }
                        "<" => {
                            if args.len() != 2 {
                                return None;
                            }
                            ChcExpr::lt(go(ctx, args[0], memo)?, go(ctx, args[1], memo)?)
                        }
                        "<=" => {
                            if args.len() != 2 {
                                return None;
                            }
                            ChcExpr::le(go(ctx, args[0], memo)?, go(ctx, args[1], memo)?)
                        }
                        ">" => {
                            if args.len() != 2 {
                                return None;
                            }
                            ChcExpr::gt(go(ctx, args[0], memo)?, go(ctx, args[1], memo)?)
                        }
                        ">=" => {
                            if args.len() != 2 {
                                return None;
                            }
                            ChcExpr::ge(go(ctx, args[0], memo)?, go(ctx, args[1], memo)?)
                        }
                        "+" => args
                            .iter()
                            .copied()
                            .map(|a| go(ctx, a, memo))
                            .reduce(|a, b| Some(ChcExpr::add(a?, b?)))??,
                        "-" => {
                            if args.is_empty() {
                                return None;
                            }
                            let first = go(ctx, args[0], memo)?;
                            if args.len() == 1 {
                                ChcExpr::neg(first)
                            } else {
                                args.iter()
                                    .copied()
                                    .skip(1)
                                    .map(|a| go(ctx, a, memo))
                                    .try_fold(first, |acc, a| Some(ChcExpr::sub(acc, a?)))?
                            }
                        }
                        "*" => {
                            if args.len() != 2 {
                                return None;
                            }
                            ChcExpr::mul(go(ctx, args[0], memo)?, go(ctx, args[1], memo)?)
                        }
                        "div" | "intdiv" => {
                            if args.len() != 2 {
                                return None;
                            }
                            ChcExpr::Op(
                                ChcOp::Div,
                                vec![
                                    Arc::new(go(ctx, args[0], memo)?),
                                    Arc::new(go(ctx, args[1], memo)?),
                                ],
                            )
                        }
                        "mod" => {
                            if args.len() != 2 {
                                return None;
                            }
                            ChcExpr::mod_op(go(ctx, args[0], memo)?, go(ctx, args[1], memo)?)
                        }
                        "neg" => {
                            if args.len() != 1 {
                                return None;
                            }
                            ChcExpr::neg(go(ctx, args[0], memo)?)
                        }
                        "select" => {
                            if args.len() != 2 {
                                return None;
                            }
                            ChcExpr::select(go(ctx, args[0], memo)?, go(ctx, args[1], memo)?)
                        }
                        "store" => {
                            if args.len() != 3 {
                                return None;
                            }
                            ChcExpr::store(
                                go(ctx, args[0], memo)?,
                                go(ctx, args[1], memo)?,
                                go(ctx, args[2], memo)?,
                            )
                        }
                        // BV binary operations
                        "bvadd" | "bvsub" | "bvmul" | "bvudiv" | "bvurem" | "bvsdiv" | "bvsrem"
                        | "bvsmod" | "bvand" | "bvor" | "bvxor" | "bvnand" | "bvnor" | "bvxnor"
                        | "bvshl" | "bvlshr" | "bvashr" => {
                            if args.len() != 2 {
                                return None;
                            }
                            let op = match name {
                                "bvadd" => ChcOp::BvAdd,
                                "bvsub" => ChcOp::BvSub,
                                "bvmul" => ChcOp::BvMul,
                                "bvudiv" => ChcOp::BvUDiv,
                                "bvurem" => ChcOp::BvURem,
                                "bvsdiv" => ChcOp::BvSDiv,
                                "bvsrem" => ChcOp::BvSRem,
                                "bvsmod" => ChcOp::BvSMod,
                                "bvand" => ChcOp::BvAnd,
                                "bvor" => ChcOp::BvOr,
                                "bvxor" => ChcOp::BvXor,
                                "bvnand" => ChcOp::BvNand,
                                "bvnor" => ChcOp::BvNor,
                                "bvxnor" => ChcOp::BvXnor,
                                "bvshl" => ChcOp::BvShl,
                                "bvlshr" => ChcOp::BvLShr,
                                "bvashr" => ChcOp::BvAShr,
                                _ => return None, // Guarded by outer match; defensive (#6091)
                            };
                            let a = go(ctx, args[0], memo)?;
                            let b = go(ctx, args[1], memo)?;
                            ChcExpr::Op(op, vec![Arc::new(a), Arc::new(b)])
                        }
                        // BV unary operations
                        "bvnot" | "bvneg" => {
                            if args.len() != 1 {
                                return None;
                            }
                            let op = if name == "bvnot" {
                                ChcOp::BvNot
                            } else {
                                ChcOp::BvNeg
                            };
                            let a = go(ctx, args[0], memo)?;
                            ChcExpr::Op(op, vec![Arc::new(a)])
                        }
                        // BV comparison operations
                        "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt"
                        | "bvsge" => {
                            if args.len() != 2 {
                                return None;
                            }
                            let op = match name {
                                "bvult" => ChcOp::BvULt,
                                "bvule" => ChcOp::BvULe,
                                "bvugt" => ChcOp::BvUGt,
                                "bvuge" => ChcOp::BvUGe,
                                "bvslt" => ChcOp::BvSLt,
                                "bvsle" => ChcOp::BvSLe,
                                "bvsgt" => ChcOp::BvSGt,
                                "bvsge" => ChcOp::BvSGe,
                                _ => return None, // Guarded by outer match; defensive (#6091)
                            };
                            let a = go(ctx, args[0], memo)?;
                            let b = go(ctx, args[1], memo)?;
                            ChcExpr::Op(op, vec![Arc::new(a), Arc::new(b)])
                        }
                        // BV concat
                        "concat" => {
                            if args.len() != 2 {
                                return None;
                            }
                            let a = go(ctx, args[0], memo)?;
                            let b = go(ctx, args[1], memo)?;
                            ChcExpr::Op(ChcOp::BvConcat, vec![Arc::new(a), Arc::new(b)])
                        }
                        // BV/Int conversion (inserted by sort coercion in convert.rs)
                        "bv2nat" | "bv2int" => {
                            if args.len() != 1 {
                                return None;
                            }
                            let a = go(ctx, args[0], memo)?;
                            ChcExpr::Op(ChcOp::Bv2Nat, vec![Arc::new(a)])
                        }
                        "int2bv" => {
                            if args.len() != 1 {
                                return None;
                            }
                            // int2bv is an indexed operator: (_ int2bv W).
                            // Extract width from Symbol::Indexed indices.
                            let width = match sym {
                                ay_core::term::Symbol::Indexed(_, indices)
                                    if !indices.is_empty() =>
                                {
                                    indices[0]
                                }
                                _ => return None,
                            };
                            let a = go(ctx, args[0], memo)?;
                            ChcExpr::Op(ChcOp::Int2Bv(width), vec![Arc::new(a)])
                        }
                        _ => {
                            // Check if this is a DT constructor/selector/tester (#7016).
                            ctx.try_dt_app_to_chc_expr(name, args, |a| go(ctx, a, memo))?
                        }
                    }
                }
                // Unknown TermData variant; cannot extract model (#6091).
                _ => return None,
            };

            memo.insert(term, expr.clone());
            Some(expr)
        }

        let mut memo: FxHashMap<TermId, ChcExpr> = FxHashMap::default();
        go(self, term, &mut memo)
    }

    /// Get the value of a term from the model (recursive evaluation of compound expressions)
    pub(super) fn get_term_value(
        &self,
        term: TermId,
        values: &FxHashMap<String, SmtValue>,
        lia_model: &Option<ay_lia::LiaModel>,
    ) -> Option<i128> {
        maybe_grow_expr_stack(|| self.get_term_value_inner(term, values, lia_model))
    }

    fn get_term_value_inner(
        &self,
        term: TermId,
        values: &FxHashMap<String, SmtValue>,
        lia_model: &Option<ay_lia::LiaModel>,
    ) -> Option<i128> {
        use ay_core::term::{Constant, TermData};

        match self.terms.get(term) {
            TermData::Const(Constant::Int(n)) => n.to_i128(),
            TermData::Const(_) => None,
            TermData::Var(name, _) => {
                // #6100: term names are sort-qualified; values uses original
                // CHC names. Try original name first, fall back to qualified.
                let original = self.original_var_name(name);
                if let Some(SmtValue::Int(v)) = values.get(original).or_else(|| values.get(name)) {
                    return Some(*v);
                }
                // Try LIA model — return None on overflow (#3827)
                if let Some(m) = lia_model {
                    if let Some(v) = m.values.get(&term) {
                        return v.to_i128();
                    }
                }
                None
            }
            TermData::App(sym, args) => {
                // Evaluate compound expressions recursively
                let sym_name = sym.name();
                match sym_name {
                    "+" => {
                        // Addition: evaluate all args and sum (checked arithmetic)
                        let mut sum: i128 = 0;
                        for &arg in args {
                            let val = self.get_term_value(arg, values, lia_model)?;
                            sum = sum.checked_add(val)?;
                        }
                        Some(sum)
                    }
                    "-" => {
                        // Subtraction: first arg minus rest (checked arithmetic)
                        if args.is_empty() {
                            return None;
                        }
                        let first = self.get_term_value(args[0], values, lia_model)?;
                        if args.len() == 1 {
                            // Unary negation
                            return first.checked_neg();
                        }
                        let mut result = first;
                        for &arg in args.iter().skip(1) {
                            let val = self.get_term_value(arg, values, lia_model)?;
                            result = result.checked_sub(val)?;
                        }
                        Some(result)
                    }
                    "*" => {
                        // Multiplication: product of all args (checked arithmetic)
                        let mut product: i128 = 1;
                        for &arg in args {
                            let val = self.get_term_value(arg, values, lia_model)?;
                            product = product.checked_mul(val)?;
                        }
                        Some(product)
                    }
                    "div" | "intdiv" => {
                        // SMT-LIB Euclidean division: a = b*q + r, 0 <= r < |b|
                        if args.len() != 2 {
                            return None;
                        }
                        let lhs = self.get_term_value(args[0], values, lia_model)?;
                        let rhs = self.get_term_value(args[1], values, lia_model)?;
                        if rhs == 0 {
                            return None;
                        }
                        crate::expr::smt_euclid_div(lhs, rhs)
                    }
                    "mod" => {
                        // SMT-LIB Euclidean remainder: always non-negative
                        if args.len() != 2 {
                            return None;
                        }
                        let lhs = self.get_term_value(args[0], values, lia_model)?;
                        let rhs = self.get_term_value(args[1], values, lia_model)?;
                        if rhs == 0 {
                            return None;
                        }
                        crate::expr::smt_euclid_mod(lhs, rhs)
                    }
                    "neg" => {
                        // Negation (checked arithmetic)
                        if args.len() != 1 {
                            return None;
                        }
                        let val = self.get_term_value(args[0], values, lia_model)?;
                        val.checked_neg()
                    }
                    _ => {
                        // Unknown operation - try LIA model directly (#3827: return None on overflow)
                        if let Some(m) = lia_model {
                            if let Some(v) = m.values.get(&term) {
                                return v.to_i128();
                            }
                        }
                        None
                    }
                }
            }
            TermData::Ite(cond, then_term, else_term) => {
                // First try LIA model for the whole ITE term (#3827: return None on overflow)
                if let Some(m) = lia_model {
                    if let Some(v) = m.values.get(&term) {
                        return v.to_i128();
                    }
                }
                // Evaluate condition to pick the correct branch (#3744)
                match self.eval_bool_condition(*cond, values, lia_model) {
                    Some(true) => self.get_term_value(*then_term, values, lia_model),
                    Some(false) => self.get_term_value(*else_term, values, lia_model),
                    // Can't determine condition — returning either branch would be
                    // unsound for model verification.
                    None => None,
                }
            }
            TermData::Not(_) => {
                // Boolean negation - not an integer value
                None
            }
            TermData::Let(_, body) => {
                // Let expression - evaluate the body
                self.get_term_value(*body, values, lia_model)
            }
            TermData::Forall(..) | TermData::Exists(..) => {
                // Quantifiers don't have integer values
                None
            }
            // Unknown TermData variant; no integer value (#6091).
            _ => None,
        }
    }

    /// Check if `formula` implies `conclusion` (i.e., formula /\ not(conclusion) is UNSAT)
    pub fn check_implies(&mut self, formula: &ChcExpr, conclusion: &ChcExpr) -> bool {
        // Check: formula /\ not(conclusion) is UNSAT?
        let not_conclusion = ChcExpr::not(conclusion.clone());
        let query = ChcExpr::and(formula.clone(), not_conclusion);

        matches!(
            self.check_sat(&query),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        )
    }

    /// Check if `formula` is satisfiable and return a model if so
    pub fn get_model(&mut self, formula: &ChcExpr) -> Option<FxHashMap<String, SmtValue>> {
        match self.check_sat(formula) {
            SmtResult::Sat(model) => Some(model),
            _ => None,
        }
    }
}

#[cfg(test)]
#[path = "model_extract_tests.rs"]
mod tests;
