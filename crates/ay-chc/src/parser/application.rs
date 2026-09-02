// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Operator/application decoding for the CHC parser.
//!
//! Owns the big dispatch table mapping SMT-LIB function names to `ChcExpr`
//! constructors. Handles arithmetic, bitvector, array, boolean, and user-
//! defined function applications.

use super::bitvector::infer_bv_width_from_expr;
use super::ChcParser;
use crate::{ChcError, ChcExpr, ChcOp, ChcResult, ChcSort, MAX_BITVECTOR_WIDTH};
use std::sync::Arc;

impl ChcParser {
    /// Parse a chainable SMT-LIB operator (=, <, <=, >, >=).
    ///
    /// `(op a b c)` desugars to `(and (op a b) (op b c))`.
    pub(super) fn parse_chainable(
        op: &str,
        args: Vec<ChcExpr>,
        bin: fn(ChcExpr, ChcExpr) -> ChcExpr,
    ) -> ChcResult<ChcExpr> {
        if args.len() < 2 {
            return Err(ChcError::Parse(format!(
                "'{op}' requires at least 2 arguments"
            )));
        }
        if args.len() == 2 {
            let mut iter = args.into_iter();
            let a = Self::next_checked(&mut iter, op)?;
            let b = Self::next_checked(&mut iter, op)?;
            Ok(bin(a, b))
        } else {
            let chain: Vec<ChcExpr> = args
                .windows(2)
                .map(|w| bin(w[0].clone(), w[1].clone()))
                .collect();
            Ok(ChcExpr::and_all(chain))
        }
    }

    pub(super) fn next_checked<I>(iter: &mut I, op: &str) -> ChcResult<ChcExpr>
    where
        I: Iterator<Item = ChcExpr>,
    {
        iter.next().ok_or_else(|| {
            ChcError::Parse(format!(
                "Internal parser error: '{op}' arity check mismatch"
            ))
        })
    }

    fn rational_constant(expr: &ChcExpr) -> Option<(i128, i128)> {
        match expr {
            ChcExpr::Int(n) => Some((i128::from(*n), 1)),
            ChcExpr::Real(n, d) => Some((i128::from(*n), i128::from(*d))),
            ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
                let (n, d) = Self::rational_constant(args[0].as_ref())?;
                n.checked_neg().map(|neg| (neg, d))
            }
            _ => None,
        }
    }

    fn checked_mul_i128(a: i128, b: i128, context: &str) -> ChcResult<i128> {
        a.checked_mul(b)
            .ok_or_else(|| ChcError::Parse(format!("{context} overflow")))
    }

    fn coerce_to_real_expr(expr: ChcExpr) -> ChcResult<ChcExpr> {
        match &expr {
            // i128-lockstep: `Real` stays (i64, i64); an integer literal beyond
            // i64 cannot be coerced — fail-closed parse error, never truncate.
            ChcExpr::Int(n) => Ok(ChcExpr::Real(
                i64::try_from(*n).map_err(|_| {
                    ChcError::Parse("integer literal out of i64 range for Real coercion".into())
                })?,
                1,
            )),
            ChcExpr::Real(_, _) => Ok(expr),
            ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
                let cond = args[0].as_ref().clone();
                let then_val = Self::coerce_to_real_expr(args[1].as_ref().clone())?;
                let else_val = Self::coerce_to_real_expr(args[2].as_ref().clone())?;
                Ok(ChcExpr::ite(cond, then_val, else_val))
            }
            _ => match Self::arithmetic_sort(&expr)? {
                ChcSort::Real => Ok(expr),
                ChcSort::Int => Ok(ChcExpr::FuncApp(
                    "to_real".to_string(),
                    ChcSort::Real,
                    vec![Arc::new(expr)],
                )),
                sort => Err(ChcError::Parse(format!(
                    "'to_real' requires Int or Real argument, got {sort}"
                ))),
            },
        }
    }

    fn arithmetic_sort(expr: &ChcExpr) -> ChcResult<ChcSort> {
        match expr {
            ChcExpr::Int(_) => Ok(ChcSort::Int),
            ChcExpr::Real(_, _) => Ok(ChcSort::Real),
            ChcExpr::Var(v) => Ok(v.sort.clone()),
            ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
                Self::arithmetic_sort(args[0].as_ref())
            }
            ChcExpr::Op(ChcOp::Add | ChcOp::Sub | ChcOp::Mul | ChcOp::Div, args) => {
                let mut saw_real = false;
                for arg in args {
                    match Self::arithmetic_sort(arg.as_ref())? {
                        ChcSort::Real => saw_real = true,
                        ChcSort::Int => {}
                        sort => {
                            return Err(ChcError::Parse(format!(
                                "Arithmetic expression contains non-numeric sort {sort}"
                            )));
                        }
                    }
                }
                Ok(if saw_real {
                    ChcSort::Real
                } else {
                    ChcSort::Int
                })
            }
            ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
                let then_sort = Self::arithmetic_sort(args[1].as_ref())?;
                let else_sort = Self::arithmetic_sort(args[2].as_ref())?;
                match (&then_sort, &else_sort) {
                    (ChcSort::Int, ChcSort::Int) => Ok(ChcSort::Int),
                    (ChcSort::Real, ChcSort::Real)
                    | (ChcSort::Int, ChcSort::Real)
                    | (ChcSort::Real, ChcSort::Int) => Ok(ChcSort::Real),
                    _ if Self::sorts_compatible(&then_sort, &else_sort) => Ok(then_sort),
                    _ => Err(ChcError::Parse(format!(
                        "ITE branch sort mismatch: then {then_sort}, else {else_sort}"
                    ))),
                }
            }
            other => Ok(other.sort()),
        }
    }

    fn parse_to_real(args: Vec<ChcExpr>) -> ChcResult<ChcExpr> {
        if args.len() != 1 {
            return Err(ChcError::Parse(
                "'to_real' requires exactly 1 argument".into(),
            ));
        }
        let mut iter = args.into_iter();
        Self::coerce_to_real_expr(Self::next_checked(&mut iter, "to_real")?)
    }

    fn parse_to_int(args: Vec<ChcExpr>) -> ChcResult<ChcExpr> {
        if args.len() != 1 {
            return Err(ChcError::Parse(
                "'to_int' requires exactly 1 argument".into(),
            ));
        }
        let mut iter = args.into_iter();
        let arg = Self::coerce_to_real_expr(Self::next_checked(&mut iter, "to_int")?)?;
        Ok(ChcExpr::FuncApp(
            "to_int".to_string(),
            ChcSort::Int,
            vec![Arc::new(arg)],
        ))
    }

    fn parse_is_int(args: Vec<ChcExpr>) -> ChcResult<ChcExpr> {
        if args.len() != 1 {
            return Err(ChcError::Parse(
                "'is_int' requires exactly 1 argument".into(),
            ));
        }
        let mut iter = args.into_iter();
        let arg = Self::coerce_to_real_expr(Self::next_checked(&mut iter, "is_int")?)?;
        Ok(ChcExpr::FuncApp(
            "is_int".to_string(),
            ChcSort::Bool,
            vec![Arc::new(arg)],
        ))
    }

    fn parse_binary_real_division(numer_expr: ChcExpr, denom_expr: ChcExpr) -> ChcResult<ChcExpr> {
        if let Some((numer_num, numer_den)) = Self::rational_constant(&numer_expr) {
            if let Some((denom_num, denom_den)) = Self::rational_constant(&denom_expr) {
                if denom_num != 0 {
                    let n =
                        Self::checked_mul_i128(numer_num, denom_den, "Real division numerator")?;
                    let d =
                        Self::checked_mul_i128(numer_den, denom_num, "Real division denominator")?;
                    return Self::normalize_rational_i128(n, d);
                }
            }
        }

        if let Some((denom_num, denom_den)) = Self::rational_constant(&denom_expr) {
            if denom_num != 0 {
                let scale = Self::normalize_rational_i128(denom_den, denom_num)?;
                if scale == ChcExpr::Real(1, 1) {
                    return Self::coerce_to_real_expr(numer_expr);
                }
                return Ok(ChcExpr::mul(scale, Self::coerce_to_real_expr(numer_expr)?));
            }
        }

        Ok(ChcExpr::Op(
            ChcOp::Div,
            vec![
                Arc::new(Self::coerce_to_real_expr(numer_expr)?),
                Arc::new(Self::coerce_to_real_expr(denom_expr)?),
            ],
        ))
    }

    fn parse_real_division(args: Vec<ChcExpr>) -> ChcResult<ChcExpr> {
        if args.len() < 2 {
            return Err(ChcError::Parse("'/' requires at least 2 arguments".into()));
        }
        let mut iter = args.into_iter();
        let first = Self::next_checked(&mut iter, "/")?;
        iter.try_fold(first, Self::parse_binary_real_division)
    }

    fn coerce_arg_to_sort(expr: ChcExpr, expected: &ChcSort, context: &str) -> ChcResult<ChcExpr> {
        if matches!(expected, ChcSort::Real) {
            return Self::coerce_to_real_expr(expr);
        }
        let actual = Self::arithmetic_sort(&expr)?;
        if Self::sorts_compatible(expected, &actual) {
            Ok(expr)
        } else {
            Err(ChcError::Parse(format!(
                "{context} expected argument sort {expected}, got {actual}"
            )))
        }
    }

    fn coerce_args_to_sorts(
        args: Vec<ChcExpr>,
        expected_sorts: &[ChcSort],
        context: &str,
    ) -> ChcResult<Vec<ChcExpr>> {
        if args.len() != expected_sorts.len() {
            return Err(ChcError::Parse(format!(
                "{context} expects {} arguments, got {}",
                expected_sorts.len(),
                args.len()
            )));
        }
        args.into_iter()
            .zip(expected_sorts.iter())
            .map(|(arg, expected)| Self::coerce_arg_to_sort(arg, expected, context))
            .collect()
    }

    /// Parse function application
    pub(super) fn parse_application(&mut self, func: &str) -> ChcResult<ChcExpr> {
        let mut args = Vec::new();

        // Track POLARITY while descending so `parse_quantifier_expr` can tell a
        // legitimate implicit-universal wrapper from a body-position `forall`
        // (which weakens its guard when stripped) or a head-position `exists`
        // (which strengthens, and could fabricate a proof).
        //
        //   not        -> flips its argument
        //   =>         -> flips the antecedent, preserves the consequent
        //   and / or   -> preserve
        //   everything else (ite conditions, Bool `=`/`distinct`/`xor`, ...)
        //                -> MIXED (0); a quantifier there is not safely strippable
        let outer_polarity = self.polarity;
        let mut arg_index = 0usize;
        loop {
            self.skip_whitespace_and_comments();
            if self.peek_char() == Some(')') {
                break;
            }
            self.polarity = match func {
                "not" => -outer_polarity,
                "=>" | "implies" => {
                    // `=>` is checked to be binary below; antecedent is arg 0.
                    if arg_index == 0 {
                        -outer_polarity
                    } else {
                        outer_polarity
                    }
                }
                "and" | "or" => outer_polarity,
                _ => 0,
            };
            let parsed = self.parse_expr();
            self.polarity = outer_polarity;
            args.push(parsed?);
            arg_index += 1;
        }
        self.polarity = outer_polarity;
        self.expect_char(')')?;

        // Map function names to operations
        match func {
            "not" => {
                if args.len() != 1 {
                    return Err(ChcError::Parse("'not' requires exactly 1 argument".into()));
                }
                let mut iter = args.into_iter();
                Ok(ChcExpr::not(Self::next_checked(&mut iter, "not")?))
            }
            "and" => Ok(ChcExpr::and_all(args)),
            "or" => Ok(ChcExpr::or_all(args)),
            "=>" | "implies" => {
                if args.len() != 2 {
                    return Err(ChcError::Parse("'=>' requires exactly 2 arguments".into()));
                }
                let mut iter = args.into_iter();
                let a = Self::next_checked(&mut iter, "=>")?;
                let b = Self::next_checked(&mut iter, "=>")?;
                Ok(ChcExpr::implies(a, b))
            }
            // SMT-LIB 2.6 chainable operators: (op a b c) → (and (op a b) (op b c))
            "=" => Self::parse_chainable("=", args, ChcExpr::eq),
            "<" => Self::parse_chainable("<", args, ChcExpr::lt),
            "<=" => Self::parse_chainable("<=", args, ChcExpr::le),
            ">" => Self::parse_chainable(">", args, ChcExpr::gt),
            ">=" => Self::parse_chainable(">=", args, ChcExpr::ge),
            "distinct" => {
                // Pairwise: (distinct a b c) → (and (!= a b) (!= a c) (!= b c))
                if args.len() < 2 {
                    return Err(ChcError::Parse(
                        "'distinct' requires at least 2 arguments".into(),
                    ));
                }
                if args.len() == 2 {
                    let mut iter = args.into_iter();
                    let a = Self::next_checked(&mut iter, "distinct")?;
                    let b = Self::next_checked(&mut iter, "distinct")?;
                    Ok(ChcExpr::ne(a, b))
                } else {
                    let mut pairs = Vec::new();
                    for i in 0..args.len() {
                        for j in (i + 1)..args.len() {
                            pairs.push(ChcExpr::ne(args[i].clone(), args[j].clone()));
                        }
                    }
                    Ok(ChcExpr::and_all(pairs))
                }
            }
            "+" => {
                if args.is_empty() {
                    Ok(ChcExpr::int(0))
                } else {
                    let mut iter = args.into_iter();
                    let first = Self::next_checked(&mut iter, "+")?;
                    Ok(iter.fold(first, ChcExpr::add))
                }
            }
            "-" => {
                if args.is_empty() {
                    return Err(ChcError::Parse("'-' requires at least 1 argument".into()));
                }
                if args.len() == 1 {
                    let mut iter = args.into_iter();
                    Ok(ChcExpr::neg(Self::next_checked(&mut iter, "-")?))
                } else {
                    let mut iter = args.into_iter();
                    let first = Self::next_checked(&mut iter, "-")?;
                    Ok(iter.fold(first, ChcExpr::sub))
                }
            }
            "*" => {
                if args.is_empty() {
                    Ok(ChcExpr::int(1))
                } else {
                    let mut iter = args.into_iter();
                    let first = Self::next_checked(&mut iter, "*")?;
                    Ok(iter.fold(first, ChcExpr::mul))
                }
            }
            "/" => Self::parse_real_division(args),
            "div" => {
                if args.len() != 2 {
                    return Err(ChcError::Parse("'div' requires exactly 2 arguments".into()));
                }
                let mut iter = args.into_iter();
                let a = Self::next_checked(&mut iter, "div")?;
                let b = Self::next_checked(&mut iter, "div")?;
                let sort_a = Self::arithmetic_sort(&a)?;
                let sort_b = Self::arithmetic_sort(&b)?;
                if sort_a != ChcSort::Int || sort_b != ChcSort::Int {
                    return Err(ChcError::Parse(format!(
                        "'div' requires Int arguments, got {sort_a} and {sort_b}"
                    )));
                }
                Ok(ChcExpr::Op(ChcOp::Div, vec![Arc::new(a), Arc::new(b)]))
            }
            "mod" => {
                if args.len() != 2 {
                    return Err(ChcError::Parse("'mod' requires exactly 2 arguments".into()));
                }
                let mut iter = args.into_iter();
                let a = Self::next_checked(&mut iter, "mod")?;
                let b = Self::next_checked(&mut iter, "mod")?;
                let sort_a = Self::arithmetic_sort(&a)?;
                let sort_b = Self::arithmetic_sort(&b)?;
                if sort_a != ChcSort::Int || sort_b != ChcSort::Int {
                    return Err(ChcError::Parse(format!(
                        "'mod' requires Int arguments, got {sort_a} and {sort_b}"
                    )));
                }
                Ok(ChcExpr::Op(ChcOp::Mod, vec![Arc::new(a), Arc::new(b)]))
            }
            "ite" => {
                if args.len() != 3 {
                    return Err(ChcError::Parse("'ite' requires exactly 3 arguments".into()));
                }
                let mut iter = args.into_iter();
                let cond = Self::next_checked(&mut iter, "ite")?;
                let then_val = Self::next_checked(&mut iter, "ite")?;
                let else_val = Self::next_checked(&mut iter, "ite")?;
                Ok(ChcExpr::ite(cond, then_val, else_val))
            }
            "to_real" => Self::parse_to_real(args),
            "to_int" => Self::parse_to_int(args),
            "is_int" => Self::parse_is_int(args),
            "select" => {
                if args.len() != 2 {
                    return Err(ChcError::Parse(
                        "'select' requires exactly 2 arguments".into(),
                    ));
                }
                let mut iter = args.into_iter();
                let arr = Self::next_checked(&mut iter, "select")?;
                let idx = Self::next_checked(&mut iter, "select")?;
                Ok(ChcExpr::select(arr, idx))
            }
            "store" => {
                if args.len() != 3 {
                    return Err(ChcError::Parse(
                        "'store' requires exactly 3 arguments".into(),
                    ));
                }
                let mut iter = args.into_iter();
                let arr = Self::next_checked(&mut iter, "store")?;
                let idx = Self::next_checked(&mut iter, "store")?;
                let val = Self::next_checked(&mut iter, "store")?;
                Ok(ChcExpr::store(arr, idx, val))
            }
            "true" => Ok(ChcExpr::Bool(true)),
            "false" => Ok(ChcExpr::Bool(false)),
            // Bitvector binary arithmetic/bitwise/shift operations
            // bvadd/bvmul/bvand/bvor/bvxor are left-associative per SMT-LIB (#5445)
            "bvadd" | "bvsub" | "bvmul" | "bvudiv" | "bvurem" | "bvsdiv" | "bvsrem" | "bvsmod"
            | "bvand" | "bvor" | "bvxor" | "bvnand" | "bvnor" | "bvxnor" | "bvshl" | "bvlshr"
            | "bvashr" => {
                let left_assoc = matches!(func, "bvadd" | "bvmul" | "bvand" | "bvor" | "bvxor");
                if args.len() < 2 || (!left_assoc && args.len() != 2) {
                    let msg = if left_assoc {
                        "at least 2"
                    } else {
                        "exactly 2"
                    };
                    return Err(ChcError::Parse(format!(
                        "'{func}' requires {msg} arguments"
                    )));
                }
                let op = match func {
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
                    _ => {
                        return Err(ChcError::Parse(format!("Unexpected BV operator: {func}")));
                    }
                };
                // Left-associative fold: (op a b c) => (op (op a b) c)
                let mut result = ChcExpr::Op(
                    op,
                    vec![Arc::new(args[0].clone()), Arc::new(args[1].clone())],
                );
                for arg in &args[2..] {
                    result = ChcExpr::Op(op, vec![Arc::new(result), Arc::new(arg.clone())]);
                }
                Ok(result)
            }
            // Bitvector unary operations
            "bvnot" | "bvneg" | "bv2nat" | "bv2int" => {
                if args.len() != 1 {
                    return Err(ChcError::Parse(format!(
                        "'{func}' requires exactly 1 argument"
                    )));
                }
                let op = match func {
                    "bvnot" => ChcOp::BvNot,
                    "bvneg" => ChcOp::BvNeg,
                    "bv2nat" | "bv2int" => ChcOp::Bv2Nat,
                    _ => {
                        return Err(ChcError::Parse(format!(
                            "Unexpected unary BV operator: {func}"
                        )));
                    }
                };
                let args_arc: Vec<Arc<ChcExpr>> = args.into_iter().map(Arc::new).collect();
                Ok(ChcExpr::Op(op, args_arc))
            }
            // Bitvector comparison operations (return Bool)
            "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge" => {
                if args.len() != 2 {
                    return Err(ChcError::Parse(format!(
                        "'{func}' requires exactly 2 arguments"
                    )));
                }
                let op = match func {
                    "bvult" => ChcOp::BvULt,
                    "bvule" => ChcOp::BvULe,
                    "bvugt" => ChcOp::BvUGt,
                    "bvuge" => ChcOp::BvUGe,
                    "bvslt" => ChcOp::BvSLt,
                    "bvsle" => ChcOp::BvSLe,
                    "bvsgt" => ChcOp::BvSGt,
                    "bvsge" => ChcOp::BvSGe,
                    _ => {
                        return Err(ChcError::Parse(format!(
                            "Unexpected BV comparison operator: {func}"
                        )));
                    }
                };
                let args_arc: Vec<Arc<ChcExpr>> = args.into_iter().map(Arc::new).collect();
                Ok(ChcExpr::Op(op, args_arc))
            }
            // bvcomp: bitwise comparison, returns BitVec(1)
            "bvcomp" => {
                if args.len() != 2 {
                    return Err(ChcError::Parse(
                        "'bvcomp' requires exactly 2 arguments".into(),
                    ));
                }
                let args_arc: Vec<Arc<ChcExpr>> = args.into_iter().map(Arc::new).collect();
                Ok(ChcExpr::Op(ChcOp::BvComp, args_arc))
            }
            // Z3-specific "safe division" BV operators that handle division-by-zero.
            // bvsrem_i(a,b) = ite(b=0, a, bvsrem(a,b))
            // bvurem_i(a,b) = ite(b=0, a, bvurem(a,b))
            // bvsmod_i(a,b) = ite(b=0, a, bvsmod(a,b))
            // bvsdiv_i(a,b) = ite(b=0, ite(bvslt(a,0), 1, -1), bvsdiv(a,b))
            // bvudiv_i(a,b) = ite(b=0, -1, bvudiv(a,b)) where -1 = all-ones BV
            "bvsrem_i" | "bvurem_i" | "bvsdiv_i" | "bvudiv_i" | "bvsmod_i" => {
                if args.len() != 2 {
                    return Err(ChcError::Parse(format!(
                        "'{func}' requires exactly 2 arguments"
                    )));
                }
                let a = args[0].clone();
                let b = args[1].clone();
                // Infer width from operands for zero literal construction.
                let a_width = infer_bv_width_from_expr(&a);
                let b_width = infer_bv_width_from_expr(&b);
                let width = match (a_width, b_width) {
                    (Some(a_width), Some(b_width)) if a_width == b_width => a_width,
                    (Some(a_width), Some(b_width)) => {
                        return Err(ChcError::Parse(format!(
                            "'{func}' requires equal-width bitvector operands, got {a_width} and {b_width}"
                        )));
                    }
                    _ => {
                        return Err(ChcError::Parse(format!(
                            "'{func}' requires bitvector operands with known width"
                        )));
                    }
                };
                let zero = ChcExpr::BitVec(0, width);
                let b_is_zero = ChcExpr::eq(b.clone(), zero);
                let (default_val, core_op) = match func {
                    "bvsrem_i" => (a.clone(), ChcOp::BvSRem),
                    "bvurem_i" => (a.clone(), ChcOp::BvURem),
                    "bvsmod_i" => (a.clone(), ChcOp::BvSMod),
                    "bvudiv_i" => {
                        // -1 as all-ones bitvector
                        (Self::make_all_ones_bv(width), ChcOp::BvUDiv)
                    }
                    "bvsdiv_i" => {
                        // ite(bvslt(a, 0), 1, -1) — simplified to 0 for CHC contexts
                        // where division-by-zero is typically unreachable.
                        let one = ChcExpr::BitVec(1, width);
                        let neg_one = Self::make_all_ones_bv(width);
                        let a_neg = ChcExpr::Op(
                            ChcOp::BvSLt,
                            vec![Arc::new(a.clone()), Arc::new(ChcExpr::BitVec(0, width))],
                        );
                        (ChcExpr::ite(a_neg, one, neg_one), ChcOp::BvSDiv)
                    }
                    _ => unreachable!(),
                };
                let core_result = ChcExpr::Op(core_op, vec![Arc::new(a), Arc::new(b)]);
                Ok(ChcExpr::ite(b_is_zero, default_val, core_result))
            }
            // concat: variadic bitvector concatenation
            "concat" => {
                if args.len() < 2 {
                    return Err(ChcError::Parse(
                        "'concat' requires at least 2 arguments".into(),
                    ));
                }
                // `concat` is binary in the internal AST/evaluator. Preserve
                // the parser's variadic convenience by folding left-to-right,
                // while bounding the accumulated result width.
                let mut args = args.into_iter();
                let mut result = Self::next_checked(&mut args, "concat")?;
                let mut result_width = infer_bv_width_from_expr(&result).ok_or_else(|| {
                    ChcError::Parse("'concat' requires bitvector arguments".into())
                })?;
                for arg in args {
                    let arg_width = infer_bv_width_from_expr(&arg).ok_or_else(|| {
                        ChcError::Parse("'concat' requires bitvector arguments".into())
                    })?;
                    result_width = result_width.checked_add(arg_width).ok_or_else(|| {
                        ChcError::Parse("'concat' result width overflows u32".into())
                    })?;
                    if result_width > MAX_BITVECTOR_WIDTH {
                        return Err(ChcError::Parse(format!(
                            "'concat' result width {result_width} exceeds the supported maximum {MAX_BITVECTOR_WIDTH}"
                        )));
                    }
                    result = ChcExpr::Op(ChcOp::BvConcat, vec![Arc::new(result), Arc::new(arg)]);
                }
                Ok(result)
            }
            _ => {
                // Check if it's a predicate application
                if let Some((pred_id, sorts)) = self.predicates.get(func).cloned() {
                    let args =
                        Self::coerce_args_to_sorts(args, &sorts, &format!("Predicate '{func}'"))?;
                    // It's a predicate application - create PredicateApp expression
                    Ok(ChcExpr::predicate_app(func, pred_id, args))
                } else if let Some((ret_sort, arg_sorts)) = self
                    .resolve_function_signature(
                        func,
                        &args.iter().map(ChcExpr::sort).collect::<Vec<_>>(),
                    )?
                    .or_else(|| self.functions.get(func).cloned())
                {
                    let args = Self::coerce_args_to_sorts(
                        args,
                        &arg_sorts,
                        &format!("Function '{func}'"),
                    )?;
                    // It's a declared function (constructor, selector, or tester).
                    let args_arc: Vec<Arc<ChcExpr>> = args.into_iter().map(Arc::new).collect();
                    Ok(ChcExpr::FuncApp(func.to_string(), ret_sort, args_arc))
                } else {
                    // Unknown function - fail with error (fixes #352)
                    Err(ChcError::Parse(format!(
                        "Unknown function application: '{func}'. Only built-in ops and declared predicates are supported in ay-chc."
                    )))
                }
            }
        }
    }
}
