// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expression parsing for the invariant parser.
//!
//! Recursive-descent parser for SMT-LIB expressions: boolean connectives,
//! arithmetic operators, array operations, let-bindings, and literals.

use super::InvariantParser;
use crate::error::ChcError;
use crate::expr::maybe_grow_expr_stack;
use crate::{ChcExpr, ChcOp, ChcResult, ChcSort, ChcVar};
use std::sync::Arc;

impl<'a> InvariantParser<'a> {
    pub(super) fn parse_expr(&mut self, vars: &[ChcVar]) -> ChcResult<ChcExpr> {
        // Stacker protection: invariant expressions from PDR can be deeply nested
        // when CHC problems have many predicates with many args (#6847).
        maybe_grow_expr_stack(|| self.parse_expr_inner(vars))
    }

    fn parse_expr_inner(&mut self, vars: &[ChcVar]) -> ChcResult<ChcExpr> {
        self.skip_whitespace_and_comments();

        match self.peek_char() {
            Some('(') => {
                self.pos += 1;
                self.skip_whitespace_and_comments();

                // Higher-order application like ((as const (Array Int Int)) value)
                if self.peek_char() == Some('(') {
                    let head = self.parse_expr(vars)?;
                    self.skip_whitespace_and_comments();

                    let args = self.parse_expr_list(vars)?;
                    self.expect_char(')')?;

                    return match head {
                        ChcExpr::ConstArrayMarker(ref key_sort) => {
                            if args.len() != 1 {
                                Err(ChcError::Parse(
                                    "(as const ...) requires exactly 1 argument".into(),
                                ))
                            } else {
                                Ok(ChcExpr::const_array(
                                    key_sort.clone(),
                                    args.into_iter().next().ok_or_else(|| {
                                        ChcError::Parse("(as const ...) missing argument".into())
                                    })?,
                                ))
                            }
                        }
                        ChcExpr::Op(op, ref existing_args) if existing_args.is_empty() => {
                            if args.len() != 1 {
                                Err(ChcError::Parse(format!(
                                    "indexed bitvector operator {op:?} requires exactly 1 argument"
                                )))
                            } else {
                                Ok(ChcExpr::Op(op, args.into_iter().map(Arc::new).collect()))
                            }
                        }
                        ChcExpr::IsTesterMarker(ref constructor) => {
                            if args.len() != 1 {
                                Err(ChcError::Parse(
                                    "(_ is ...) requires exactly 1 argument".into(),
                                ))
                            } else {
                                Ok(ChcExpr::FuncApp(
                                    format!("is-{constructor}"),
                                    ChcSort::Bool,
                                    args.into_iter().map(Arc::new).collect(),
                                ))
                            }
                        }
                        ChcExpr::FuncApp(ref name, _, ref existing_args)
                            if existing_args.is_empty() =>
                        {
                            let Some((return_sort, _)) = self.function_signature(name, args.len())
                            else {
                                return Err(ChcError::Parse(format!(
                                    "qualified function `{name}` has the wrong arity"
                                )));
                            };
                            Ok(ChcExpr::FuncApp(
                                name.clone(),
                                return_sort.clone(),
                                args.into_iter().map(Arc::new).collect(),
                            ))
                        }
                        _ => Err(ChcError::Parse(
                            "Unsupported higher-order application".into(),
                        )),
                    };
                }

                let op = self.parse_symbol()?;
                self.skip_whitespace_and_comments();

                match op.as_str() {
                    "_" => self.parse_indexed_identifier(),
                    "as" => {
                        let name = self.parse_symbol()?;
                        self.skip_whitespace_and_comments();

                        match name.as_str() {
                            "const" => {
                                let sort = self.parse_sort()?;
                                let key_sort = match &sort {
                                    ChcSort::Array(ks, _) => ks.as_ref().clone(),
                                    _ => {
                                        return Err(ChcError::Parse(format!(
                                            "Expected array sort in (as const ...), got: {sort:?}"
                                        )));
                                    }
                                };
                                self.skip_whitespace_and_comments();
                                self.expect_char(')')?;
                                Ok(ChcExpr::ConstArrayMarker(key_sort))
                            }
                            _ => {
                                let annotated_sort = self.parse_sort()?;
                                self.skip_whitespace_and_comments();
                                self.expect_char(')')?;
                                let Some((return_sort, _)) = self.function_sigs.get(&name) else {
                                    return Err(ChcError::Parse(format!(
                                        "unknown qualified function `{name}`"
                                    )));
                                };
                                if !super::sorts_compatible(return_sort, &annotated_sort) {
                                    return Err(ChcError::Parse(format!(
                                        "qualified function `{name}` returns {return_sort}, not {annotated_sort}"
                                    )));
                                }
                                Ok(ChcExpr::FuncApp(name, return_sort.clone(), Vec::new()))
                            }
                        }
                    }
                    "let" => {
                        // Parse: (let ((var expr) ...) body)
                        self.expect_char('(')?;
                        let mut let_bindings: Vec<(ChcVar, ChcExpr)> = Vec::new();
                        loop {
                            self.skip_whitespace_and_comments();
                            if self.peek_char() == Some(')') {
                                break;
                            }
                            self.expect_char('(')?;
                            self.skip_whitespace_and_comments();
                            let binding_name = self.parse_symbol()?;
                            self.skip_whitespace_and_comments();
                            let binding_expr = self.parse_expr(vars)?;
                            self.skip_whitespace_and_comments();
                            self.expect_char(')')?;
                            let_bindings.push((
                                ChcVar::new(binding_name, binding_expr.sort()),
                                binding_expr,
                            ));
                        }
                        self.expect_char(')')?; // close binding list
                        self.skip_whitespace_and_comments();

                        // Let bindings shadow outer variables of the same name.
                        let mut extended_vars: Vec<ChcVar> =
                            let_bindings.iter().map(|(v, _)| v.clone()).collect();
                        extended_vars.extend_from_slice(vars);

                        let body = self.parse_expr(&extended_vars)?;
                        self.skip_whitespace_and_comments();
                        self.expect_char(')')?;

                        // Let bindings are simultaneous (SMT-LIB): substitute all at once.
                        Ok(body.substitute(&let_bindings))
                    }
                    "not" => {
                        let arg = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        self.expect_char(')')?;
                        Ok(ChcExpr::not(arg))
                    }
                    "and" => {
                        let args = self.parse_expr_list(vars)?;
                        self.expect_char(')')?;
                        Ok(ChcExpr::and_all(args))
                    }
                    "or" => {
                        let args = self.parse_expr_list(vars)?;
                        self.expect_char(')')?;
                        Ok(ChcExpr::or_all(args))
                    }
                    "=>" => {
                        let a = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        let b = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        self.expect_char(')')?;
                        Ok(ChcExpr::implies(a, b))
                    }
                    "=" => {
                        let args = self.parse_expr_list(vars)?;
                        self.expect_char(')')?;
                        match args.len() {
                            0 | 1 => Ok(ChcExpr::Bool(true)),
                            2 => Ok(ChcExpr::eq(args[0].clone(), args[1].clone())),
                            _ => {
                                let mut conj: Option<ChcExpr> = None;
                                for w in args.windows(2) {
                                    let eq = ChcExpr::eq(w[0].clone(), w[1].clone());
                                    conj = Some(match conj {
                                        Some(prev) => ChcExpr::and(prev, eq),
                                        None => eq,
                                    });
                                }
                                Ok(conj.unwrap_or(ChcExpr::Bool(true)))
                            }
                        }
                    }
                    "distinct" => {
                        let args = self.parse_expr_list(vars)?;
                        self.expect_char(')')?;
                        match args.len() {
                            0 | 1 => Ok(ChcExpr::Bool(true)),
                            2 => Ok(ChcExpr::ne(args[0].clone(), args[1].clone())),
                            _ => {
                                let mut conj: Option<ChcExpr> = None;
                                for i in 0..args.len() {
                                    for j in (i + 1)..args.len() {
                                        let ne = ChcExpr::ne(args[i].clone(), args[j].clone());
                                        conj = Some(match conj {
                                            Some(prev) => ChcExpr::and(prev, ne),
                                            None => ne,
                                        });
                                    }
                                }
                                Ok(conj.unwrap_or(ChcExpr::Bool(true)))
                            }
                        }
                    }
                    "<" => {
                        let args = self.parse_expr_list(vars)?;
                        self.expect_char(')')?;
                        match args.len() {
                            0 | 1 => Ok(ChcExpr::Bool(true)),
                            _ => {
                                let mut conj: Option<ChcExpr> = None;
                                for w in args.windows(2) {
                                    let lt = ChcExpr::lt(w[0].clone(), w[1].clone());
                                    conj = Some(match conj {
                                        Some(prev) => ChcExpr::and(prev, lt),
                                        None => lt,
                                    });
                                }
                                Ok(conj.unwrap_or(ChcExpr::Bool(true)))
                            }
                        }
                    }
                    "<=" => {
                        let args = self.parse_expr_list(vars)?;
                        self.expect_char(')')?;
                        match args.len() {
                            0 | 1 => Ok(ChcExpr::Bool(true)),
                            _ => {
                                let mut conj: Option<ChcExpr> = None;
                                for w in args.windows(2) {
                                    let le = ChcExpr::le(w[0].clone(), w[1].clone());
                                    conj = Some(match conj {
                                        Some(prev) => ChcExpr::and(prev, le),
                                        None => le,
                                    });
                                }
                                Ok(conj.unwrap_or(ChcExpr::Bool(true)))
                            }
                        }
                    }
                    ">" => {
                        let args = self.parse_expr_list(vars)?;
                        self.expect_char(')')?;
                        match args.len() {
                            0 | 1 => Ok(ChcExpr::Bool(true)),
                            _ => {
                                let mut conj: Option<ChcExpr> = None;
                                for w in args.windows(2) {
                                    let gt = ChcExpr::gt(w[0].clone(), w[1].clone());
                                    conj = Some(match conj {
                                        Some(prev) => ChcExpr::and(prev, gt),
                                        None => gt,
                                    });
                                }
                                Ok(conj.unwrap_or(ChcExpr::Bool(true)))
                            }
                        }
                    }
                    ">=" => {
                        let args = self.parse_expr_list(vars)?;
                        self.expect_char(')')?;
                        match args.len() {
                            0 | 1 => Ok(ChcExpr::Bool(true)),
                            _ => {
                                let mut conj: Option<ChcExpr> = None;
                                for w in args.windows(2) {
                                    let ge = ChcExpr::ge(w[0].clone(), w[1].clone());
                                    conj = Some(match conj {
                                        Some(prev) => ChcExpr::and(prev, ge),
                                        None => ge,
                                    });
                                }
                                Ok(conj.unwrap_or(ChcExpr::Bool(true)))
                            }
                        }
                    }
                    "+" => {
                        let args = self.parse_expr_list(vars)?;
                        self.expect_char(')')?;
                        if args.is_empty() {
                            Ok(ChcExpr::int(0))
                        } else {
                            args.into_iter().reduce(ChcExpr::add).ok_or_else(|| {
                                ChcError::Parse("'+' requires at least 1 argument".into())
                            })
                        }
                    }
                    "-" => {
                        let args = self.parse_expr_list(vars)?;
                        self.expect_char(')')?;
                        match args.len() {
                            0 => Err(ChcError::Parse("'-' expects at least 1 argument".into())),
                            1 => Ok(ChcExpr::neg(args.into_iter().next().ok_or_else(|| {
                                ChcError::Parse("'-' missing argument".into())
                            })?)),
                            _ => {
                                let mut it = args.into_iter();
                                let mut acc = it.next().ok_or_else(|| {
                                    ChcError::Parse("'-' missing first argument".into())
                                })?;
                                for a in it {
                                    acc = ChcExpr::sub(acc, a);
                                }
                                Ok(acc)
                            }
                        }
                    }
                    "*" => {
                        let args = self.parse_expr_list(vars)?;
                        self.expect_char(')')?;
                        if args.is_empty() {
                            Ok(ChcExpr::int(1))
                        } else {
                            args.into_iter().reduce(ChcExpr::mul).ok_or_else(|| {
                                ChcError::Parse("'*' requires at least 1 argument".into())
                            })
                        }
                    }
                    "div" => {
                        let a = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        let b = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        self.expect_char(')')?;
                        Ok(ChcExpr::Op(ChcOp::Div, vec![Arc::new(a), Arc::new(b)]))
                    }
                    "mod" => {
                        let a = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        let b = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        self.expect_char(')')?;
                        Ok(ChcExpr::Op(ChcOp::Mod, vec![Arc::new(a), Arc::new(b)]))
                    }
                    "ite" => {
                        let cond = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        let then_ = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        let else_ = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        self.expect_char(')')?;
                        Ok(ChcExpr::ite(cond, then_, else_))
                    }
                    "select" => {
                        let arr = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        let idx = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        self.expect_char(')')?;
                        Ok(ChcExpr::select(arr, idx))
                    }
                    "store" => {
                        let arr = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        let idx = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        let val = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        self.expect_char(')')?;
                        Ok(ChcExpr::store(arr, idx, val))
                    }
                    "bvadd" | "bvsub" | "bvmul" | "bvudiv" | "bvurem" | "bvsdiv" | "bvsrem"
                    | "bvsmod" | "bvand" | "bvor" | "bvxor" | "bvnand" | "bvnor" | "bvxnor"
                    | "bvshl" | "bvlshr" | "bvashr" | "bvult" | "bvule" | "bvugt" | "bvuge"
                    | "bvslt" | "bvsle" | "bvsgt" | "bvsge" | "bvcomp" | "concat" | "bvnot"
                    | "bvneg" | "bv2nat" | "bv2int" => self.parse_named_bv_application(&op, vars),
                    "/" => {
                        // Real division: (/ num denom)
                        let num = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        let denom = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        self.expect_char(')')?;
                        // If both are integers (possibly with explicit unary negation), create Real
                        // i128-lockstep: ChcExpr::Real is i64-based; constants outside i64
                        // range fall through to the generic Div representation below.
                        if let (ChcExpr::Int(n), ChcExpr::Int(d)) = (&num, &denom) {
                            if let (Ok(n), Ok(d)) = (i64::try_from(*n), i64::try_from(*d)) {
                                return Ok(ChcExpr::Real(n, d));
                            }
                        }
                        if let (ChcExpr::Op(ChcOp::Neg, args), ChcExpr::Int(d)) = (&num, &denom) {
                            if args.len() == 1 {
                                if let ChcExpr::Int(n) = args[0].as_ref() {
                                    if let (Some(Ok(n)), Ok(d)) =
                                        (n.checked_neg().map(i64::try_from), i64::try_from(*d))
                                    {
                                        return Ok(ChcExpr::Real(n, d));
                                    }
                                }
                            }
                        }
                        Ok(ChcExpr::Op(
                            ChcOp::Div,
                            vec![Arc::new(num), Arc::new(denom)],
                        ))
                    }
                    _ => {
                        let args = self.parse_expr_list(vars)?;
                        self.expect_char(')')?;
                        let ret_sort = self
                            .function_signature(&op, args.len())
                            .map(|(ret, _)| ret.clone())
                            .unwrap_or(ChcSort::Int);
                        Ok(ChcExpr::FuncApp(
                            op,
                            ret_sort,
                            args.into_iter().map(Arc::new).collect(),
                        ))
                    }
                }
            }
            Some(c) if c.is_ascii_digit() => {
                let num = self.parse_numeral()?;
                Ok(ChcExpr::int(num))
            }
            Some('-') => {
                // Negative number
                self.pos += 1;
                let num = self.parse_numeral()?;
                Ok(ChcExpr::int(-num))
            }
            Some(_) => {
                let name = self.parse_symbol()?;
                match name.as_str() {
                    "true" => Ok(ChcExpr::Bool(true)),
                    "false" => Ok(ChcExpr::Bool(false)),
                    _ => {
                        // Look up in vars
                        for var in vars {
                            if var.name == name {
                                return Ok(ChcExpr::var(var.clone()));
                            }
                        }
                        if let Some((ret_sort, _)) = self.function_signature(&name, 0) {
                            return Ok(ChcExpr::FuncApp(name, ret_sort.clone(), Vec::new()));
                        }
                        // Unknown variable - create with Int sort as default
                        Ok(ChcExpr::var(ChcVar::new(name, ChcSort::Int)))
                    }
                }
            }
            None => Err(ChcError::Parse("Unexpected end of input".into())),
        }
    }

    fn parse_named_bv_application(&mut self, name: &str, vars: &[ChcVar]) -> ChcResult<ChcExpr> {
        let args = self.parse_expr_list(vars)?;
        self.expect_char(')')?;
        let (op, expected_arity) = match name {
            "bvadd" => (ChcOp::BvAdd, 2),
            "bvsub" => (ChcOp::BvSub, 2),
            "bvmul" => (ChcOp::BvMul, 2),
            "bvudiv" => (ChcOp::BvUDiv, 2),
            "bvurem" => (ChcOp::BvURem, 2),
            "bvsdiv" => (ChcOp::BvSDiv, 2),
            "bvsrem" => (ChcOp::BvSRem, 2),
            "bvsmod" => (ChcOp::BvSMod, 2),
            "bvand" => (ChcOp::BvAnd, 2),
            "bvor" => (ChcOp::BvOr, 2),
            "bvxor" => (ChcOp::BvXor, 2),
            "bvnand" => (ChcOp::BvNand, 2),
            "bvnor" => (ChcOp::BvNor, 2),
            "bvxnor" => (ChcOp::BvXnor, 2),
            "bvnot" => (ChcOp::BvNot, 1),
            "bvneg" => (ChcOp::BvNeg, 1),
            "bvshl" => (ChcOp::BvShl, 2),
            "bvlshr" => (ChcOp::BvLShr, 2),
            "bvashr" => (ChcOp::BvAShr, 2),
            "bvult" => (ChcOp::BvULt, 2),
            "bvule" => (ChcOp::BvULe, 2),
            "bvugt" => (ChcOp::BvUGt, 2),
            "bvuge" => (ChcOp::BvUGe, 2),
            "bvslt" => (ChcOp::BvSLt, 2),
            "bvsle" => (ChcOp::BvSLe, 2),
            "bvsgt" => (ChcOp::BvSGt, 2),
            "bvsge" => (ChcOp::BvSGe, 2),
            "bvcomp" => (ChcOp::BvComp, 2),
            "concat" => (ChcOp::BvConcat, 2),
            "bv2nat" | "bv2int" => (ChcOp::Bv2Nat, 1),
            _ => {
                return Err(ChcError::Parse(format!(
                    "unsupported bitvector operator `{name}`"
                )));
            }
        };
        if args.len() != expected_arity {
            return Err(ChcError::Parse(format!(
                "`{name}` requires exactly {expected_arity} arguments"
            )));
        }
        Ok(ChcExpr::Op(op, args.into_iter().map(Arc::new).collect()))
    }

    fn parse_indexed_identifier(&mut self) -> ChcResult<ChcExpr> {
        self.skip_whitespace_and_comments();
        let name = self.parse_symbol()?;
        self.skip_whitespace_and_comments();
        let mut indices = Vec::new();
        while self.peek_char() != Some(')') {
            indices.push(self.parse_symbol()?);
            self.skip_whitespace_and_comments();
        }
        self.expect_char(')')?;

        if let Some(decimal) = name.strip_prefix("bv") {
            if decimal.is_empty() || !decimal.chars().all(|character| character.is_ascii_digit()) {
                return Err(ChcError::Parse(format!(
                    "invalid indexed bitvector literal `{name}`"
                )));
            }
            if indices.len() != 1 {
                return Err(ChcError::Parse(
                    "indexed bitvector literal requires exactly one width".into(),
                ));
            }
            let value = decimal.parse::<u128>().map_err(|_| {
                ChcError::Parse("indexed bitvector literal value exceeds u128".into())
            })?;
            let width = parse_bounded_bv_index(&indices[0], "bitvector width")?;
            if width == 0 {
                return Err(ChcError::Parse(
                    "indexed bitvector literal width must be positive".into(),
                ));
            }
            if width < u128::BITS && value >= (1_u128 << width) {
                return Err(ChcError::Parse(format!(
                    "indexed bitvector literal value {value} does not fit width {width}"
                )));
            }
            return Ok(ChcExpr::BitVec(value, width));
        }

        let op = match name.as_str() {
            "extract" => {
                if indices.len() != 2 {
                    return Err(ChcError::Parse(
                        "(_ extract hi lo) requires exactly 2 indices".into(),
                    ));
                }
                let high = parse_bounded_bv_index(&indices[0], "extract high index")?;
                let low = parse_bounded_bv_index(&indices[1], "extract low index")?;
                if high < low {
                    return Err(ChcError::Parse(format!(
                        "extract high index {high} is below low index {low}"
                    )));
                }
                ChcOp::BvExtract(high, low)
            }
            "zero_extend" => {
                if indices.len() != 1 {
                    return Err(ChcError::Parse(format!(
                        "(_ {name} n) requires exactly 1 index"
                    )));
                }
                ChcOp::BvZeroExtend(parse_bounded_bv_index(&indices[0], name.as_str())?)
            }
            "sign_extend" => {
                if indices.len() != 1 {
                    return Err(ChcError::Parse(format!(
                        "(_ {name} n) requires exactly 1 index"
                    )));
                }
                ChcOp::BvSignExtend(parse_bounded_bv_index(&indices[0], name.as_str())?)
            }
            "rotate_left" => {
                if indices.len() != 1 {
                    return Err(ChcError::Parse(format!(
                        "(_ {name} n) requires exactly 1 index"
                    )));
                }
                ChcOp::BvRotateLeft(parse_bounded_bv_index(&indices[0], name.as_str())?)
            }
            "rotate_right" => {
                if indices.len() != 1 {
                    return Err(ChcError::Parse(format!(
                        "(_ {name} n) requires exactly 1 index"
                    )));
                }
                ChcOp::BvRotateRight(parse_bounded_bv_index(&indices[0], name.as_str())?)
            }
            "repeat" => {
                if indices.len() != 1 {
                    return Err(ChcError::Parse(format!(
                        "(_ {name} n) requires exactly 1 index"
                    )));
                }
                let repeat = parse_bounded_bv_index(&indices[0], name.as_str())?;
                if repeat == 0 {
                    return Err(ChcError::Parse(
                        "bitvector repeat count must be positive".into(),
                    ));
                }
                ChcOp::BvRepeat(repeat)
            }
            "int2bv" => {
                if indices.len() != 1 {
                    return Err(ChcError::Parse(format!(
                        "(_ {name} n) requires exactly 1 index"
                    )));
                }
                let width = parse_bounded_bv_index(&indices[0], name.as_str())?;
                if width == 0 {
                    return Err(ChcError::Parse("int2bv width must be positive".into()));
                }
                ChcOp::Int2Bv(width)
            }
            "is" => {
                if indices.len() != 1 {
                    return Err(ChcError::Parse(
                        "(_ is Constructor) requires exactly 1 constructor".into(),
                    ));
                }
                return Ok(ChcExpr::IsTesterMarker(indices.remove(0)));
            }
            _ => {
                return Err(ChcError::Parse(format!(
                    "unknown indexed identifier `{name}`"
                )));
            }
        };
        Ok(ChcExpr::Op(op, Vec::new()))
    }
}

fn parse_bounded_bv_index(text: &str, label: &str) -> ChcResult<u32> {
    const MAX_BV_INDEX: u32 = 1 << 20;
    let value = text
        .parse::<u32>()
        .map_err(|_| ChcError::Parse(format!("invalid {label}: `{text}`")))?;
    if value > MAX_BV_INDEX {
        return Err(ChcError::Parse(format!(
            "{label} {value} exceeds the maximum supported {MAX_BV_INDEX}"
        )));
    }
    Ok(value)
}
