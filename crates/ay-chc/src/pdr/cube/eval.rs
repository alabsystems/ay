// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expression evaluation using model values.
//!
//! Contains `value_expr_from_model` (evaluate expression to constant under a
//! model) and `try_eval_const` (evaluate ground constant expressions).

use crate::{ChcExpr, ChcOp, ChcSort, SmtValue};
use ay_core::kani_compat::DetHashMap as FxHashMap;

/// Evaluate an expression to a constant using model values.
///
/// Returns `Some(ChcExpr::Int(n))` or `Some(ChcExpr::Bool(b))` if the expression
/// can be fully evaluated, `None` otherwise.
///
/// # Evaluation rules
///
/// - Variables are looked up in the model; missing variables return `None`
/// - Arithmetic operations are evaluated with overflow checking
/// - Boolean operations short-circuit where possible
pub(in crate::pdr) fn value_expr_from_model(
    arg: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
) -> Option<ChcExpr> {
    fn eval_int(expr: &ChcExpr, model: &FxHashMap<String, SmtValue>) -> Option<i128> {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Int(n) => Some(*n),
            // #5523: Handle BV constants as integers for evaluation.
            ChcExpr::BitVec(v, _w) => i128::try_from(*v).ok(),
            // Missing variables return None — callers decide how to handle
            // partial models. Defaulting to 0 is unsound for predecessor
            // extraction (#3004).
            ChcExpr::Var(v) => match model.get(&v.name) {
                Some(SmtValue::Int(n)) => Some(*n),
                Some(SmtValue::BitVec(n, _w)) => i128::try_from(*n).ok(),
                _ => None,
            },
            ChcExpr::Op(op, args) => match op {
                ChcOp::Add => {
                    let mut acc: i128 = 0;
                    for arg in args {
                        acc = acc.checked_add(eval_int(arg, model)?)?;
                    }
                    Some(acc)
                }
                ChcOp::Sub => {
                    if args.is_empty() {
                        return None;
                    }
                    let first = eval_int(&args[0], model)?;
                    if args.len() == 1 {
                        return first.checked_neg();
                    }
                    let mut acc = first;
                    for arg in &args[1..] {
                        acc = acc.checked_sub(eval_int(arg, model)?)?;
                    }
                    Some(acc)
                }
                ChcOp::Mul => {
                    let mut acc: i128 = 1;
                    for arg in args {
                        acc = acc.checked_mul(eval_int(arg, model)?)?;
                    }
                    Some(acc)
                }
                ChcOp::Div => {
                    if args.len() != 2 {
                        return None;
                    }
                    let lhs = eval_int(&args[0], model)?;
                    let rhs = eval_int(&args[1], model)?;
                    if rhs == 0 {
                        return None;
                    }
                    lhs.checked_div_euclid(rhs)
                }
                ChcOp::Mod => {
                    if args.len() != 2 {
                        return None;
                    }
                    let lhs = eval_int(&args[0], model)?;
                    let rhs = eval_int(&args[1], model)?;
                    if rhs == 0 {
                        return None;
                    }
                    lhs.checked_rem_euclid(rhs)
                }
                ChcOp::Neg => {
                    if args.len() != 1 {
                        return None;
                    }
                    let v = eval_int(&args[0], model)?;
                    v.checked_neg()
                }
                ChcOp::Ite => {
                    if args.len() != 3 {
                        return None;
                    }
                    let cond = eval_bool(&args[0], model)?;
                    if cond {
                        eval_int(&args[1], model)
                    } else {
                        eval_int(&args[2], model)
                    }
                }
                _ => None,
            },
            _ => None,
        })
    }

    /// Compare two numeric expressions under a model, returning their ordering.
    /// Handles Int/Real mixed comparisons via rational cross-multiplication.
    fn compare_numeric(
        a: &ChcExpr,
        b: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<std::cmp::Ordering> {
        if a.sort() == ChcSort::Real || b.sort() == ChcSort::Real {
            let (an, ad) = eval_real(a, model)?;
            let (bn, bd) = eval_real(b, model)?;
            // Compare a_n/a_d vs b_n/b_d via cross-multiply.
            // Must account for sign of denominators.
            // Numerators/denominators are i64-ranged (ChcExpr::Real is i64-based),
            // so i128 products cannot overflow.
            let lhs = i128::from(an) * i128::from(bd);
            let rhs = i128::from(bn) * i128::from(ad);
            let sign = i128::from(ad).signum() * i128::from(bd).signum();
            Some(if sign > 0 {
                lhs.cmp(&rhs)
            } else {
                rhs.cmp(&lhs)
            })
        } else {
            Some(eval_int(a, model)?.cmp(&eval_int(b, model)?))
        }
    }

    fn eval_bool(expr: &ChcExpr, model: &FxHashMap<String, SmtValue>) -> Option<bool> {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Bool(b) => Some(*b),
            ChcExpr::Var(v) => match model.get(&v.name) {
                Some(SmtValue::Bool(b)) => Some(*b),
                Some(
                    SmtValue::Int(_)
                    | SmtValue::BigInt(_)
                    | SmtValue::Real(_)
                    | SmtValue::BitVec(_, _)
                    | SmtValue::Opaque(_)
                    | SmtValue::ConstArray(_)
                    | SmtValue::ArrayMap { .. }
                    | SmtValue::Datatype(..),
                ) => None,
                None => None,
            },
            ChcExpr::Op(op, args) => match op {
                ChcOp::Not if args.len() == 1 => Some(!eval_bool(&args[0], model)?),
                ChcOp::And => {
                    for arg in args {
                        if !eval_bool(arg, model)? {
                            return Some(false);
                        }
                    }
                    Some(true)
                }
                ChcOp::Or => {
                    for arg in args {
                        if eval_bool(arg, model)? {
                            return Some(true);
                        }
                    }
                    Some(false)
                }
                ChcOp::Implies if args.len() == 2 => {
                    Some(!eval_bool(&args[0], model)? || eval_bool(&args[1], model)?)
                }
                ChcOp::Iff if args.len() == 2 => {
                    Some(eval_bool(&args[0], model)? == eval_bool(&args[1], model)?)
                }
                ChcOp::Eq | ChcOp::Ne if args.len() == 2 => {
                    let eq = match (args[0].sort(), args[1].sort()) {
                        (ChcSort::Bool, ChcSort::Bool) => {
                            eval_bool(&args[0], model)? == eval_bool(&args[1], model)?
                        }
                        (ChcSort::Real, _) | (_, ChcSort::Real) | (ChcSort::Int, ChcSort::Int) => {
                            compare_numeric(&args[0], &args[1], model)? == std::cmp::Ordering::Equal
                        }
                        // BV equality: eval_int handles BitVec constants and model values.
                        (ChcSort::BitVec(_), _) | (_, ChcSort::BitVec(_)) => {
                            eval_int(&args[0], model)? == eval_int(&args[1], model)?
                        }
                        _ => return None,
                    };
                    Some(if *op == ChcOp::Eq { eq } else { !eq })
                }
                ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge if args.len() == 2 => {
                    let cmp = compare_numeric(&args[0], &args[1], model)?;
                    match op {
                        ChcOp::Lt => Some(cmp == std::cmp::Ordering::Less),
                        ChcOp::Le => Some(cmp != std::cmp::Ordering::Greater),
                        ChcOp::Gt => Some(cmp == std::cmp::Ordering::Greater),
                        ChcOp::Ge => Some(cmp != std::cmp::Ordering::Less),
                        _ => None, // #6091: defensive
                    }
                }
                ChcOp::Ite if args.len() == 3 => {
                    if eval_bool(&args[0], model)? {
                        eval_bool(&args[1], model)
                    } else {
                        eval_bool(&args[2], model)
                    }
                }
                _ => None,
            },
            _ => None,
        })
    }

    fn eval_real(expr: &ChcExpr, model: &FxHashMap<String, SmtValue>) -> Option<(i64, i64)> {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Real(n, d) => Some((*n, *d)),
            // i128-lockstep: ChcExpr::Real is i64-based; skip Int constants
            // outside i64 range rather than truncating.
            ChcExpr::Int(n) => Some((i64::try_from(*n).ok()?, 1)),
            ChcExpr::Var(v) => match model.get(&v.name) {
                Some(SmtValue::Real(r)) => {
                    use num_traits::ToPrimitive;
                    let n = r.numer().to_i64()?;
                    let d = r.denom().to_i64()?;
                    Some((n, d))
                }
                // i128-lockstep: ChcExpr::Real is i64-based; skip model Ints
                // outside i64 range rather than truncating.
                Some(SmtValue::Int(n)) => Some((i64::try_from(*n).ok()?, 1)),
                _ => None,
            },
            ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
                let (n, d) = eval_real(&args[0], model)?;
                Some((n.checked_neg()?, d))
            }
            ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
                let cond = eval_bool(&args[0], model)?;
                if cond {
                    eval_real(&args[1], model)
                } else {
                    eval_real(&args[2], model)
                }
            }
            _ => None,
        })
    }

    let result = match arg.sort() {
        ChcSort::Bool => Some(ChcExpr::Bool(eval_bool(arg, model)?)),
        ChcSort::Int => Some(ChcExpr::Int(eval_int(arg, model)?)),
        ChcSort::Real => {
            let (n, d) = eval_real(arg, model)?;
            Some(ChcExpr::Real(n, d))
        }
        ChcSort::BitVec(w) => {
            // BV values: evaluate as integer, convert back to BitVec.
            // eval_int already handles ChcExpr::BitVec and SmtValue::BitVec.
            let val = eval_int(arg, model)?;
            // i128-lockstep: preserve the pre-widening i64 domain for the
            // bit-pattern conversion; skip values outside i64 range.
            let val = i64::try_from(val).ok()?;
            Some(ChcExpr::BitVec(val as u128, w))
        }
        _ => None,
    };
    // Postcondition: result sort must match input sort
    debug_assert!(
        result.as_ref().is_none_or(|r| r.sort() == arg.sort()),
        "BUG: value_expr_from_model sort mismatch: input={:?}, result={:?}",
        arg.sort(),
        result.as_ref().map(ChcExpr::sort),
    );
    result
}

/// Try to evaluate a constant expression to an i128.
///
/// Handles: Int(n), Neg(n), unary minus (- n), nested negation, sums, products, etc.
pub(in crate::pdr) fn try_eval_const(expr: &ChcExpr) -> Option<i128> {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::Int(n) => Some(*n),
        // Handle Neg operator: (- n) represented as Op(Neg, [n])
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
            try_eval_const(&args[0]).and_then(i128::checked_neg)
        }
        ChcExpr::Op(ChcOp::Sub, args) if args.len() == 1 => {
            // Unary minus: (- n) as Sub
            try_eval_const(&args[0]).and_then(i128::checked_neg)
        }
        ChcExpr::Op(ChcOp::Add, args) => {
            // Sum of constants
            let mut acc: i128 = 0;
            for arg in args {
                acc = acc.checked_add(try_eval_const(arg)?)?;
            }
            Some(acc)
        }
        ChcExpr::Op(ChcOp::Sub, args) if args.len() >= 2 => {
            // Subtraction: a - b - c ...
            let mut acc = try_eval_const(&args[0])?;
            for arg in &args[1..] {
                acc = acc.checked_sub(try_eval_const(arg)?)?;
            }
            Some(acc)
        }
        ChcExpr::Op(ChcOp::Mul, args) => {
            // Product of constants
            let mut acc: i128 = 1;
            for arg in args {
                acc = acc.checked_mul(try_eval_const(arg)?)?;
            }
            Some(acc)
        }
        _ => None,
    })
}
