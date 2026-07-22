// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV semantic model validation.
//!
//! This module evaluates asserted BV formulas against an extracted `BvModel`.
//! It is intentionally independent from the CNF clauses produced by bit-blasting,
//! so it can catch disagreements between BV semantics and a satisfying SAT model.

use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;

use crate::{BvModel, BV_STACK_RED_ZONE, BV_STACK_SIZE};

// #8529-style deterministic map for the evaluation memo.
use ay_core::kani_compat::DetHashMap;

/// Some-only evaluation memo over the hash-consed term DAG. The `BvModel` env
/// is immutable for the lifetime of one memo (one `validate_bv_assertions`
/// call / one public evaluate call), so cached `Some` results are exact.
/// Without it, shared subterms are re-evaluated once per tree PATH --
/// exponential in sharing depth (the DAG->tree pathology; this validator
/// dominated post-solve time on a 30M-clause BMC instance).
#[derive(Default)]
struct BvValMemo {
    bv: DetHashMap<TermId, BigInt>,
    boolean: DetHashMap<TermId, bool>,
}

fn eval_bool_memo(
    terms: &TermStore,
    term: TermId,
    model: &BvModel,
    memo: &mut BvValMemo,
) -> Option<bool> {
    if let Some(&b) = memo.boolean.get(&term) {
        return Some(b);
    }
    let result = eval_bool(terms, term, model, memo);
    if let Some(b) = result {
        memo.boolean.insert(term, b);
    }
    result
}

fn eval_bv_memo(
    terms: &TermStore,
    term: TermId,
    model: &BvModel,
    memo: &mut BvValMemo,
) -> Option<BigInt> {
    if let Some(v) = memo.bv.get(&term) {
        return Some(v.clone());
    }
    let result = stacker::maybe_grow(BV_STACK_RED_ZONE, BV_STACK_SIZE, || {
        eval_bv(terms, term, model, memo)
    });
    if let Some(v) = &result {
        memo.bv.insert(term, v.clone());
    }
    result
}

/// A semantic BV assertion validation failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BvValidationError {
    /// Index in the assertion slice passed to `validate_bv_assertions`.
    pub assertion_index: usize,
    /// Term id of the assertion that evaluated to false.
    pub assertion: TermId,
}

/// Validate all evaluable BV assertions against a `BvModel`.
///
/// Returns the number of assertions checked. Assertions outside the bounded BV
/// validation slice are skipped; any evaluable assertion that returns `false`
/// is reported as an error.
pub fn validate_bv_assertions(
    terms: &TermStore,
    assertions: &[TermId],
    model: &BvModel,
) -> Result<usize, BvValidationError> {
    let mut checked = 0;
    // One memo across ALL assertions: the model is immutable here, and
    // assertions share subterms heavily on BMC instances.
    let mut memo = BvValMemo::default();
    for (index, &assertion) in assertions.iter().enumerate() {
        if let Some(value) = eval_bool_memo(terms, assertion, model, &mut memo) {
            checked += 1;
            if !value {
                return Err(BvValidationError {
                    assertion_index: index,
                    assertion,
                });
            }
        }
    }
    Ok(checked)
}

/// Evaluate a Bool assertion in the bounded BV validation slice.
///
/// Supports Boolean structure (`not`, `and`, `or`, `=>`, `xor`, Bool `ite`) and
/// BV predicates (`=`, unsigned/signed comparisons) whose BV subterms are
/// evaluable under the supplied model.
pub fn evaluate_bv_assertion(terms: &TermStore, term: TermId, model: &BvModel) -> Option<bool> {
    let mut memo = BvValMemo::default();
    eval_bool_memo(terms, term, model, &mut memo)
}

/// Evaluate a bitvector expression under a `BvModel`.
///
/// The result is normalized to the expression's declared bit width. Returns
/// `None` for unsupported terms or missing model values.
pub fn evaluate_bv_expr(terms: &TermStore, term: TermId, model: &BvModel) -> Option<BigInt> {
    let mut memo = BvValMemo::default();
    eval_bv_memo(terms, term, model, &mut memo)
}

fn eval_bool(
    terms: &TermStore,
    term: TermId,
    model: &BvModel,
    memo: &mut BvValMemo,
) -> Option<bool> {
    stacker::maybe_grow(BV_STACK_RED_ZONE, BV_STACK_SIZE, || match terms.get(term) {
        TermData::Const(Constant::Bool(value)) => Some(*value),
        TermData::Var(_, _) if *terms.sort(term) == Sort::Bool => {
            model.bool_overrides.get(&term).copied()
        }
        TermData::Not(inner) => eval_bool_memo(terms, *inner, model, memo).map(|value| !value),
        TermData::Ite(cond, then_term, else_term) if *terms.sort(term) == Sort::Bool => {
            let branch = if eval_bool_memo(terms, *cond, model, memo)? {
                *then_term
            } else {
                *else_term
            };
            eval_bool_memo(terms, branch, model, memo)
        }
        TermData::App(sym, args) if *terms.sort(term) == Sort::Bool => {
            eval_bool_app(terms, sym, args, model, memo)
        }
        _ => None,
    })
}

fn eval_bool_app(
    terms: &TermStore,
    sym: &Symbol,
    args: &[TermId],
    model: &BvModel,
    memo: &mut BvValMemo,
) -> Option<bool> {
    match sym.name() {
        "and" => {
            let mut result = true;
            for &arg in args {
                result &= eval_bool_memo(terms, arg, model, memo)?;
            }
            Some(result)
        }
        "or" => {
            let mut result = false;
            for &arg in args {
                result |= eval_bool_memo(terms, arg, model, memo)?;
            }
            Some(result)
        }
        "xor" if args.len() == 2 => Some(
            eval_bool_memo(terms, args[0], model, memo)?
                ^ eval_bool_memo(terms, args[1], model, memo)?,
        ),
        "=>" if args.len() == 2 => Some(
            !eval_bool_memo(terms, args[0], model, memo)?
                || eval_bool_memo(terms, args[1], model, memo)?,
        ),
        "=" if args.len() == 2 && *terms.sort(args[0]) == Sort::Bool => Some(
            eval_bool_memo(terms, args[0], model, memo)?
                == eval_bool_memo(terms, args[1], model, memo)?,
        ),
        "ite" if args.len() == 3 => {
            let branch = if eval_bool_memo(terms, args[0], model, memo)? {
                args[1]
            } else {
                args[2]
            };
            eval_bool_memo(terms, branch, model, memo)
        }
        "=" if args.len() == 2 && matches!(terms.sort(args[0]), Sort::BitVec(_)) => {
            let lhs = eval_bv_memo(terms, args[0], model, memo)?;
            let rhs = eval_bv_memo(terms, args[1], model, memo)?;
            Some(lhs == rhs)
        }
        "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge"
            if args.len() == 2 =>
        {
            eval_bv_comparison(terms, sym.name(), args[0], args[1], model, memo)
        }
        _ => None,
    }
}

fn eval_bv(
    terms: &TermStore,
    term: TermId,
    model: &BvModel,
    memo: &mut BvValMemo,
) -> Option<BigInt> {
    match terms.get(term) {
        TermData::Var(_, _) => model.values.get(&term).cloned(),
        TermData::Const(Constant::BitVec { value, width }) => Some(mask(value.clone(), *width)),
        TermData::Ite(cond, then_term, else_term)
            if matches!(terms.sort(term), Sort::BitVec(_)) =>
        {
            let branch = if eval_bool_memo(terms, *cond, model, memo)? {
                *then_term
            } else {
                *else_term
            };
            eval_bv_memo(terms, branch, model, memo)
        }
        TermData::App(sym, args) => eval_bv_app(terms, term, sym, args, model, memo),
        _ => None,
    }
}

fn eval_bv_app(
    terms: &TermStore,
    term: TermId,
    sym: &Symbol,
    args: &[TermId],
    model: &BvModel,
    memo: &mut BvValMemo,
) -> Option<BigInt> {
    let Sort::BitVec(bv) = terms.sort(term) else {
        return None;
    };
    let width = bv.width;
    let modulus = BigInt::from(1u64) << width;
    let name = sym.name();
    let result = match name {
        "bvadd" => {
            let mut sum = BigInt::from(0u64);
            for &arg in args {
                sum += eval_bv_memo(terms, arg, model, memo)?;
            }
            sum
        }
        "bvsub" if args.len() == 2 => {
            eval_bv_memo(terms, args[0], model, memo)? - eval_bv_memo(terms, args[1], model, memo)?
        }
        "bvmul" => {
            let mut product = BigInt::from(1u64);
            for &arg in args {
                product *= eval_bv_memo(terms, arg, model, memo)?;
            }
            product
        }
        "bvneg" if args.len() == 1 => -eval_bv_memo(terms, args[0], model, memo)?,
        "bvand" => {
            let mut result = if args.is_empty() {
                all_ones(width)
            } else {
                eval_bv_memo(terms, args[0], model, memo)?
            };
            for &arg in &args[1..] {
                result &= eval_bv_memo(terms, arg, model, memo)?;
            }
            result
        }
        "bvor" => {
            let mut result = BigInt::from(0u64);
            for &arg in args {
                result |= eval_bv_memo(terms, arg, model, memo)?;
            }
            result
        }
        "bvxor" => {
            let mut result = BigInt::from(0u64);
            for &arg in args {
                result ^= eval_bv_memo(terms, arg, model, memo)?;
            }
            result
        }
        "bvnot" if args.len() == 1 => eval_bv_memo(terms, args[0], model, memo)? ^ all_ones(width),
        "bvnand" if args.len() == 2 => {
            (eval_bv_memo(terms, args[0], model, memo)?
                & eval_bv_memo(terms, args[1], model, memo)?)
                ^ all_ones(width)
        }
        "bvnor" if args.len() == 2 => {
            (eval_bv_memo(terms, args[0], model, memo)?
                | eval_bv_memo(terms, args[1], model, memo)?)
                ^ all_ones(width)
        }
        "bvxnor" if args.len() == 2 => {
            (eval_bv_memo(terms, args[0], model, memo)?
                ^ eval_bv_memo(terms, args[1], model, memo)?)
                ^ all_ones(width)
        }
        "bvudiv" if args.len() == 2 => {
            let lhs = eval_bv_memo(terms, args[0], model, memo)?;
            let rhs = eval_bv_memo(terms, args[1], model, memo)?;
            if rhs == BigInt::from(0u64) {
                all_ones(width)
            } else {
                lhs / rhs
            }
        }
        "bvurem" if args.len() == 2 => {
            let lhs = eval_bv_memo(terms, args[0], model, memo)?;
            let rhs = eval_bv_memo(terms, args[1], model, memo)?;
            if rhs == BigInt::from(0u64) {
                lhs
            } else {
                lhs % rhs
            }
        }
        "bvsdiv" if args.len() == 2 => {
            let lhs = to_signed(eval_bv_memo(terms, args[0], model, memo)?, width);
            let rhs = to_signed(eval_bv_memo(terms, args[1], model, memo)?, width);
            if rhs == BigInt::from(0i64) {
                if lhs >= BigInt::from(0i64) {
                    all_ones(width)
                } else {
                    BigInt::from(1u64)
                }
            } else {
                lhs / rhs
            }
        }
        "bvsrem" if args.len() == 2 => {
            let lhs_u = eval_bv_memo(terms, args[0], model, memo)?;
            let rhs_u = eval_bv_memo(terms, args[1], model, memo)?;
            let lhs = to_signed(lhs_u.clone(), width);
            let rhs = to_signed(rhs_u, width);
            if rhs == BigInt::from(0i64) {
                lhs_u
            } else {
                lhs % rhs
            }
        }
        "bvsmod" if args.len() == 2 => {
            let lhs_u = eval_bv_memo(terms, args[0], model, memo)?;
            let rhs_u = eval_bv_memo(terms, args[1], model, memo)?;
            let lhs = to_signed(lhs_u.clone(), width);
            let rhs = to_signed(rhs_u, width);
            if rhs == BigInt::from(0i64) {
                lhs_u
            } else {
                let rem = &lhs % &rhs;
                if rem != BigInt::from(0i64)
                    && ((lhs < BigInt::from(0i64)) != (rhs < BigInt::from(0i64)))
                {
                    rem + rhs
                } else {
                    rem
                }
            }
        }
        "concat" if args.len() == 2 => {
            let high = eval_bv_memo(terms, args[0], model, memo)?;
            let low = eval_bv_memo(terms, args[1], model, memo)?;
            let Sort::BitVec(low_bv) = terms.sort(args[1]) else {
                return None;
            };
            (high << low_bv.width) | low
        }
        "extract" if args.len() == 1 => {
            let Symbol::Indexed(_, indices) = sym else {
                return None;
            };
            if indices.len() != 2 {
                return None;
            }
            let high = indices[0] as usize;
            let low = indices[1] as usize;
            let value = eval_bv_memo(terms, args[0], model, memo)?;
            (value >> low) & ((BigInt::from(1u64) << (high - low + 1)) - 1)
        }
        "zero_extend" if args.len() == 1 => eval_bv_memo(terms, args[0], model, memo)?,
        "sign_extend" if args.len() == 1 => {
            let value = eval_bv_memo(terms, args[0], model, memo)?;
            let Sort::BitVec(arg_bv) = terms.sort(args[0]) else {
                return None;
            };
            to_signed(value, arg_bv.width)
        }
        "repeat" if args.len() == 1 => {
            let Symbol::Indexed(_, indices) = sym else {
                return None;
            };
            let count = *indices.first()? as usize;
            let value = eval_bv_memo(terms, args[0], model, memo)?;
            let Sort::BitVec(arg_bv) = terms.sort(args[0]) else {
                return None;
            };
            let mut result = BigInt::from(0u64);
            for _ in 0..count {
                result = (result << arg_bv.width) | &value;
            }
            result
        }
        "rotate_left" if args.len() == 1 => {
            let Symbol::Indexed(_, indices) = sym else {
                return None;
            };
            if width == 0 {
                return Some(BigInt::from(0u64));
            }
            let value = eval_bv_memo(terms, args[0], model, memo)?;
            let shift = *indices.first()? % width;
            if shift == 0 {
                value
            } else {
                ((&value << shift) | (&value >> (width - shift))) & all_ones(width)
            }
        }
        "rotate_right" if args.len() == 1 => {
            let Symbol::Indexed(_, indices) = sym else {
                return None;
            };
            if width == 0 {
                return Some(BigInt::from(0u64));
            }
            let value = eval_bv_memo(terms, args[0], model, memo)?;
            let shift = *indices.first()? % width;
            if shift == 0 {
                value
            } else {
                ((&value >> shift) | (&value << (width - shift))) & all_ones(width)
            }
        }
        "bvshl" if args.len() == 2 => {
            let value = eval_bv_memo(terms, args[0], model, memo)?;
            let shift = shift_amount(eval_bv_memo(terms, args[1], model, memo)?, width);
            if shift >= width {
                BigInt::from(0u64)
            } else {
                value << shift
            }
        }
        "bvlshr" if args.len() == 2 => {
            let value = eval_bv_memo(terms, args[0], model, memo)?;
            let shift = shift_amount(eval_bv_memo(terms, args[1], model, memo)?, width);
            if shift >= width {
                BigInt::from(0u64)
            } else {
                value >> shift
            }
        }
        "bvashr" if args.len() == 2 => {
            let value = to_signed(eval_bv_memo(terms, args[0], model, memo)?, width);
            let shift = shift_amount(eval_bv_memo(terms, args[1], model, memo)?, width);
            if shift >= width {
                if value < BigInt::from(0i64) {
                    all_ones(width)
                } else {
                    BigInt::from(0u64)
                }
            } else {
                value >> shift
            }
        }
        "bvcomp" if args.len() == 2 => {
            if eval_bv_memo(terms, args[0], model, memo)?
                == eval_bv_memo(terms, args[1], model, memo)?
            {
                BigInt::from(1u64)
            } else {
                BigInt::from(0u64)
            }
        }
        _ => return None,
    };
    Some(mask(result % &modulus, width))
}

fn eval_bv_comparison(
    terms: &TermStore,
    name: &str,
    lhs: TermId,
    rhs: TermId,
    model: &BvModel,
    memo: &mut BvValMemo,
) -> Option<bool> {
    let Sort::BitVec(bv) = terms.sort(lhs) else {
        return None;
    };
    if terms.sort(lhs) != terms.sort(rhs) {
        return None;
    }
    let width = bv.width;
    let lhs_value = mask(eval_bv_memo(terms, lhs, model, memo)?, width);
    let rhs_value = mask(eval_bv_memo(terms, rhs, model, memo)?, width);
    match name {
        "bvult" => Some(lhs_value < rhs_value),
        "bvule" => Some(lhs_value <= rhs_value),
        "bvugt" => Some(lhs_value > rhs_value),
        "bvuge" => Some(lhs_value >= rhs_value),
        "bvslt" => Some(to_signed(lhs_value, width) < to_signed(rhs_value, width)),
        "bvsle" => Some(to_signed(lhs_value, width) <= to_signed(rhs_value, width)),
        "bvsgt" => Some(to_signed(lhs_value, width) > to_signed(rhs_value, width)),
        "bvsge" => Some(to_signed(lhs_value, width) >= to_signed(rhs_value, width)),
        _ => None,
    }
}

fn mask(value: BigInt, width: u32) -> BigInt {
    let modulus = BigInt::from(1u64) << width;
    ((value % &modulus) + &modulus) % &modulus
}

fn all_ones(width: u32) -> BigInt {
    (BigInt::from(1u64) << width) - 1
}

fn to_signed(value: BigInt, width: u32) -> BigInt {
    if width == 0 {
        return BigInt::from(0u64);
    }
    let modulus = BigInt::from(1u64) << width;
    let normalized = mask(value, width);
    let sign_bit = BigInt::from(1u64) << (width - 1);
    if normalized >= sign_bit {
        normalized - modulus
    } else {
        normalized
    }
}

fn shift_amount(value: BigInt, width: u32) -> u32 {
    value.try_into().unwrap_or(width)
}
