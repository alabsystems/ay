// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Narrow bridge from execute_direct into ay-translate Packet 1C ops.

use std::any::Any;
use std::collections::BTreeMap;
use std::panic::{self, AssertUnwindSafe};

use ay_dpll::api::Term;
use ay_translate::ops::{
    self, arith, array, bv, seq, seq::SeqPredicate, string, string::StrPredicate, uf, Comparison,
    NaryBoolOp,
};
use ay_translate::TranslationSession;

use super::context::ExecutionContext;
use super::translate::{translate_expr, translate_sort};
use super::ExecuteError;
use crate::expr::{Expr, ExprValue};
use crate::sort::Sort;

type Session<'a> = TranslationSession<'a, String>;

/// Reject a reserved symbol name BEFORE it reaches the declaration APIs.
///
/// `Solver::declare_const`/`declare_fun`/`fresh_var` refuse a reserved name (an
/// `__ay_`-namespaced or builtin theory-operator spelling) by PANICKING — their
/// fallible `try_*` twins return `SolverError::InvalidArgument`, but the
/// `ay-translate` session methods this bridge calls are infallible and take the
/// panicking path. A panic here unwinds into whatever process embeds ay: in the
/// Trust compiler it printed a full ICE report for every Rust program with a
/// local named `fp`. A rejected declaration is a RECOVERABLE input error, so
/// surface it as `ExecuteError` — every caller of `execute_direct` already has
/// to handle one — instead of aborting the host.
fn reject_reserved_symbol(name: &str, operation: &str) -> Result<(), ExecuteError> {
    if ay_frontend::is_reserved_symbol(name) {
        return Err(ExecuteError::ConstraintExecution(format!(
            "{operation}: symbol name '{name}' is reserved (an ay builtin \
             theory-operator name or the internal `__ay_` namespace) and cannot be declared"
        )));
    }
    Ok(())
}

/// Reject only ay's INTERNAL symbol namespace.
///
/// Used where the surrounding API legitimately accepts some reserved spellings
/// (see [`declare_fun`]) but never an `__ay_` identity — minting one would let a
/// caller forge a solver-internal symbol.
fn reject_internal_namespace(name: &str, operation: &str) -> Result<(), ExecuteError> {
    if name.starts_with("__ay_") {
        return Err(ExecuteError::ConstraintExecution(format!(
            "{operation}: symbol name '{name}' enters ay's internal `__ay_` namespace"
        )));
    }
    Ok(())
}

pub(super) fn declare_const(
    ctx: &mut ExecutionContext,
    name: &str,
    sort: &Sort,
) -> Result<(), ExecuteError> {
    reject_reserved_symbol(name, "declare_const")?;
    let api_sort = translate_sort(sort)?;
    {
        let mut session = ctx.session();
        let _ = session
            .try_get_or_declare(name.to_string(), name, api_sort)
            .map_err(|error| {
                ExecuteError::ConstraintExecution(format!("declare_const: {error}"))
            })?;
    }

    Ok(())
}

pub(super) fn declare_fun(
    ctx: &mut ExecutionContext,
    name: &str,
    arg_sorts: &[Sort],
    return_sort: &Sort,
) -> Result<(), ExecuteError> {
    // NOT the full `is_reserved_symbol` here: the declaration-activated
    // collection predicates (`set.subset`, `map.dom`, …) are `declare-fun`-able
    // BY DESIGN — declaring one at its native collection signature is the
    // documented route that activates ay's native set/map/multiset solvers, and
    // `Context::declare_fun` special-cases them ahead of its reserved check.
    // Rejecting them here would break every default `Set::subset_of`/`Map::dom`
    // encoding. What stays rejected is what `Context::declare_fun` really
    // refuses: the internal namespace and the structurally-matched builtin
    // theory-operator names.
    if ay_frontend::is_reserved_op_name(name) {
        return Err(ExecuteError::ConstraintExecution(format!(
            "declare_fun: symbol name '{name}' is a reserved ay builtin \
             theory-operator name and cannot be declared as an uninterpreted function"
        )));
    }
    reject_internal_namespace(name, "declare_fun")?;
    let domain = arg_sorts
        .iter()
        .map(translate_sort)
        .collect::<Result<Vec<_>, _>>()?;
    let range = translate_sort(return_sort)?;
    let mut session = ctx.session();
    let _ = session
        .try_declare_or_get_fun(name, &domain, range)
        .map_err(|error| ExecuteError::ConstraintExecution(format!("declare_fun: {error}")))?;
    Ok(())
}

pub(super) fn define_fun(
    ctx: &mut ExecutionContext,
    name: &str,
    params: &[(String, Sort)],
    return_sort: &Sort,
    body: &Expr,
) -> Result<(), ExecuteError> {
    let mut param_names = Vec::with_capacity(params.len());
    let mut param_terms = Vec::with_capacity(params.len());
    let mut bound_scope = BTreeMap::new();

    reject_reserved_symbol(name, "define_fun")?;
    for (param_name, param_sort) in params {
        let api_sort = translate_sort(param_sort)?;
        // `fresh_var` panics when the prefix would enter a reserved namespace;
        // its fallible twin reports the same condition as a recoverable error.
        let term = ctx
            .solver
            .try_fresh_var(param_name, api_sort)
            .map_err(|error| {
                ExecuteError::ConstraintExecution(format!("define_fun parameter: {error}"))
            })?;
        bound_scope.insert(param_name.clone(), term);
        param_names.push(param_name.clone());
        param_terms.push(term);
    }

    ctx.bound_var_scopes.push(bound_scope);
    let body_result = translate_expr(ctx, body);
    ctx.bound_var_scopes.pop();
    let body_term = body_result?;

    let range = translate_sort(return_sort)?;
    let param_refs: Vec<(&str, Term)> = param_names
        .iter()
        .zip(param_terms.iter())
        .map(|(param_name, &term)| (param_name.as_str(), term))
        .collect();
    let mut session = ctx.session();
    uf::try_define(&mut session, name, &param_refs, range, body_term)
        .map_err(|error| ExecuteError::ConstraintExecution(format!("define_fun: {error}")))?;
    Ok(())
}

pub(super) fn declare_var(
    ctx: &mut ExecutionContext,
    name: &str,
    sort: &Sort,
) -> Result<(), ExecuteError> {
    reject_reserved_symbol(name, "declare_var")?;
    let api_sort = translate_sort(sort)?;
    let mut session = ctx.session();
    let _ = session
        .try_get_or_declare(name.to_string(), name, api_sort)
        .map_err(|error| ExecuteError::ConstraintExecution(format!("declare_var: {error}")))?;
    Ok(())
}

pub(super) fn maybe_translate_expr(
    ctx: &mut ExecutionContext,
    expr: &Expr,
) -> Option<Result<Term, ExecuteError>> {
    let result = match expr.value() {
        ExprValue::Not(inner) => {
            translate_unary(ctx, inner, |session, term| ops::bool_not(session, term))
        }
        ExprValue::And(args) => translate_nary(ctx, args, |session, terms| {
            ops::bool_nary(session, NaryBoolOp::And, terms)
        }),
        ExprValue::Or(args) => translate_nary(ctx, args, |session, terms| {
            ops::bool_nary(session, NaryBoolOp::Or, terms)
        }),
        ExprValue::Xor(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            ops::xor(session, left, right)
        }),
        ExprValue::Implies(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            ops::implies(session, left, right)
        }),
        ExprValue::Ite {
            cond,
            then_expr,
            else_expr,
        } => translate_ternary(
            ctx,
            cond,
            then_expr,
            else_expr,
            |session, one, two, three| ops::ite(session, one, two, three),
        ),
        ExprValue::Eq(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            ops::compare(session, Comparison::Eq, left, right)
        }),
        ExprValue::Distinct(args) => translate_distinct(ctx, args),
        ExprValue::IntAdd(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            arith::add(session, left, right)
        }),
        ExprValue::IntSub(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            arith::sub(session, left, right)
        }),
        ExprValue::IntMul(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            arith::mul(session, left, right)
        }),
        ExprValue::IntDiv(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            arith::int_div(session, left, right)
        }),
        ExprValue::IntMod(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            arith::modulo(session, left, right)
        }),
        ExprValue::IntNeg(inner) => {
            translate_unary(ctx, inner, |session, term| arith::neg(session, term))
        }
        ExprValue::IntLt(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            ops::compare(session, Comparison::Lt, left, right)
        }),
        ExprValue::IntLe(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            ops::compare(session, Comparison::Le, left, right)
        }),
        ExprValue::IntGt(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            ops::compare(session, Comparison::Gt, left, right)
        }),
        ExprValue::IntGe(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            ops::compare(session, Comparison::Ge, left, right)
        }),
        ExprValue::BvAdd(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            bv::add(session, left, right)
        }),
        ExprValue::BvSub(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            bv::sub(session, left, right)
        }),
        ExprValue::BvMul(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            bv::binop(session, bv::BinOp::Mul, left, right)
        }),
        ExprValue::BvULt(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            bv::cmp(session, bv::Cmp::ULt, left, right)
        }),
        ExprValue::BvSLt(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            bv::cmp(session, bv::Cmp::SLt, left, right)
        }),
        ExprValue::Select { array, index } => {
            translate_binary(ctx, array, index, |session, arr, idx| {
                array::select(session, arr, idx)
            })
        }
        ExprValue::Store {
            array,
            index,
            value,
        } => translate_ternary(ctx, array, index, value, |session, arr, idx, value| {
            array::store(session, arr, idx, value)
        }),
        ExprValue::ConstArray { index_sort, value } => {
            let idx_sort = match translate_sort(index_sort) {
                Ok(sort) => sort,
                Err(error) => return Some(Err(error)),
            };
            translate_unary(ctx, value, |session, term| {
                array::const_array(session, idx_sort, term)
            })
        }
        ExprValue::BvUDiv(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            bv::binop(session, bv::BinOp::UDiv, left, right)
        }),
        ExprValue::BvSDiv(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            bv::binop(session, bv::BinOp::SDiv, left, right)
        }),
        ExprValue::BvURem(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            bv::binop(session, bv::BinOp::URem, left, right)
        }),
        ExprValue::BvSRem(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            bv::binop(session, bv::BinOp::SRem, left, right)
        }),
        ExprValue::BvNeg(a) => translate_unary(ctx, a, |session, term| {
            bv::unary(session, bv::UnaryOp::Neg, term)
        }),
        ExprValue::BvNot(a) => translate_unary(ctx, a, |session, term| bv::not(session, term)),
        ExprValue::BvAnd(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            bv::and(session, left, right)
        }),
        ExprValue::BvOr(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            bv::or(session, left, right)
        }),
        ExprValue::BvXor(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            bv::binop(session, bv::BinOp::Xor, left, right)
        }),
        ExprValue::BvShl(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            bv::binop(session, bv::BinOp::Shl, left, right)
        }),
        ExprValue::BvLShr(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            bv::binop(session, bv::BinOp::LShr, left, right)
        }),
        ExprValue::BvAShr(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            bv::binop(session, bv::BinOp::AShr, left, right)
        }),
        ExprValue::BvULe(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            bv::cmp(session, bv::Cmp::ULe, left, right)
        }),
        ExprValue::BvUGt(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            bv::cmp(session, bv::Cmp::UGt, left, right)
        }),
        ExprValue::BvUGe(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            bv::cmp(session, bv::Cmp::UGe, left, right)
        }),
        ExprValue::BvSLe(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            bv::cmp(session, bv::Cmp::SLe, left, right)
        }),
        ExprValue::BvSGt(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            bv::cmp(session, bv::Cmp::SGt, left, right)
        }),
        ExprValue::BvSGe(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            bv::cmp(session, bv::Cmp::SGe, left, right)
        }),
        ExprValue::BvZeroExtend { expr, extra_bits } => {
            translate_unary(ctx, expr, |session, term| {
                bv::zext(session, *extra_bits, term)
            })
        }
        ExprValue::BvSignExtend { expr, extra_bits } => {
            translate_unary(ctx, expr, |session, term| {
                bv::sext(session, *extra_bits, term)
            })
        }
        ExprValue::BvExtract { expr, high, low } => translate_unary(ctx, expr, |session, term| {
            bv::extract(session, *high, *low, term)
        }),
        ExprValue::BvConcat(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            bv::concat(session, left, right)
        }),
        ExprValue::BvAddNoOverflowUnsigned(a, b) => {
            translate_binary(ctx, a, b, |session, left, right| {
                bv::add_no_overflow(session, left, right, false)
            })
        }
        ExprValue::BvAddNoOverflowSigned(a, b) => {
            translate_signed_bv_predicate(ctx, a, b, |session, left, right| {
                let no_ovfl = bv::add_no_overflow(session, left, right, true);
                let no_udfl = bv::add_no_underflow(session, left, right);
                ops::bool_nary(session, NaryBoolOp::And, &[no_ovfl, no_udfl])
            })
        }
        ExprValue::BvSubNoUnderflowUnsigned(a, b) => {
            translate_binary(ctx, a, b, |session, left, right| {
                bv::sub_no_underflow(session, left, right, false)
            })
        }
        ExprValue::BvSubNoOverflowSigned(a, b) => {
            translate_signed_bv_predicate(ctx, a, b, |session, left, right| {
                let no_ovfl = bv::sub_no_overflow(session, left, right);
                let no_udfl = bv::sub_no_underflow(session, left, right, true);
                ops::bool_nary(session, NaryBoolOp::And, &[no_ovfl, no_udfl])
            })
        }
        ExprValue::BvMulNoOverflowUnsigned(a, b) => {
            translate_binary(ctx, a, b, |session, left, right| {
                bv::mul_no_overflow(session, left, right, false)
            })
        }
        ExprValue::BvMulNoOverflowSigned(a, b) => {
            translate_signed_bv_predicate(ctx, a, b, |session, left, right| {
                let no_ovfl = bv::mul_no_overflow(session, left, right, true);
                let no_udfl = bv::mul_no_underflow(session, left, right);
                ops::bool_nary(session, NaryBoolOp::And, &[no_ovfl, no_udfl])
            })
        }
        ExprValue::BvNegNoOverflow(a) => {
            translate_unary(ctx, a, |session, term| bv::neg_no_overflow(session, term))
        }
        ExprValue::BvSdivNoOverflow(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            bv::sdiv_no_overflow(session, left, right)
        }),
        ExprValue::StrConcat(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            string::concat(session, left, right)
        }),
        ExprValue::StrLen(s) => translate_unary(ctx, s, |session, term| string::len(session, term)),
        ExprValue::StrAt(s, idx) => translate_binary(ctx, s, idx, |session, string_term, index| {
            string::at(session, string_term, index)
        }),
        ExprValue::StrSubstr(s, offset, len) => {
            translate_ternary(ctx, s, offset, len, |session, string_term, start, count| {
                string::substr(session, string_term, start, count)
            })
        }
        ExprValue::StrContains(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            string::predicate(session, StrPredicate::Contains, left, right)
        }),
        ExprValue::StrPrefixOf(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            string::predicate(session, StrPredicate::PrefixOf, left, right)
        }),
        ExprValue::StrSuffixOf(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            string::predicate(session, StrPredicate::SuffixOf, left, right)
        }),
        ExprValue::StrIndexOf(s, t, start) => {
            translate_ternary(ctx, s, t, start, |session, string_term, needle, from| {
                string::indexof(session, string_term, needle, from)
            })
        }
        ExprValue::StrReplace(s, from, to) => translate_ternary(
            ctx,
            s,
            from,
            to,
            |session, string_term, needle, replacement| {
                string::replace(session, string_term, needle, replacement)
            },
        ),
        ExprValue::StrReplaceAll(s, from, to) => translate_ternary(
            ctx,
            s,
            from,
            to,
            |session, string_term, needle, replacement| {
                string::replace_all(session, string_term, needle, replacement)
            },
        ),
        ExprValue::StrToInt(s) => {
            translate_unary(ctx, s, |session, term| string::to_int(session, term))
        }
        ExprValue::StrFromInt(n) => {
            translate_unary(ctx, n, |session, term| string::from_int(session, term))
        }
        ExprValue::StrToRe(s) => {
            translate_unary(ctx, s, |session, term| string::to_re(session, term))
        }
        ExprValue::StrInRe(s, re) => translate_binary(ctx, s, re, |session, string_term, regex| {
            string::in_re(session, string_term, regex)
        }),
        ExprValue::ReStar(re) => {
            translate_unary(ctx, re, |session, term| string::re_star(session, term))
        }
        ExprValue::RePlus(re) => {
            translate_unary(ctx, re, |session, term| string::re_plus(session, term))
        }
        ExprValue::ReUnion(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            string::re_union(session, left, right)
        }),
        ExprValue::ReConcat(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            string::re_concat(session, left, right)
        }),
        ExprValue::SeqEmpty(element_sort) => {
            let element_sort = match translate_sort(element_sort) {
                Ok(sort) => sort,
                Err(error) => return Some(Err(error)),
            };
            translate_with_session(ctx, |session| seq::empty(session, element_sort))
        }
        ExprValue::SeqUnit(elem) => {
            translate_unary(ctx, elem, |session, term| seq::unit(session, term))
        }
        ExprValue::SeqConcat(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            seq::concat(session, left, right)
        }),
        ExprValue::SeqLen(s) => translate_unary(ctx, s, |session, term| seq::len(session, term)),
        ExprValue::SeqNth(s, idx) => translate_binary(ctx, s, idx, |session, sequence, index| {
            seq::nth(session, sequence, index)
        }),
        ExprValue::SeqExtract(s, offset, len) => {
            translate_ternary(ctx, s, offset, len, |session, sequence, start, count| {
                seq::extract(session, sequence, start, count)
            })
        }
        ExprValue::SeqContains(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            seq::predicate(session, SeqPredicate::Contains, left, right)
        }),
        ExprValue::SeqPrefixOf(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            seq::predicate(session, SeqPredicate::PrefixOf, left, right)
        }),
        ExprValue::SeqSuffixOf(a, b) => translate_binary(ctx, a, b, |session, left, right| {
            seq::predicate(session, SeqPredicate::SuffixOf, left, right)
        }),
        ExprValue::SeqIndexOf(s, t, start) => {
            translate_ternary(ctx, s, t, start, |session, sequence, needle, from| {
                seq::indexof(session, sequence, needle, from)
            })
        }
        ExprValue::SeqReplace(s, from, to) => translate_ternary(
            ctx,
            s,
            from,
            to,
            |session, sequence, needle, replacement| {
                seq::replace(session, sequence, needle, replacement)
            },
        ),
        ExprValue::FuncApp { name, args } => {
            let func = match ctx.lookup_func(name) {
                Some(func) => func,
                None => {
                    return Some(Err(ExecuteError::ExprTranslation(format!(
                        "undeclared function '{name}' in direct execution"
                    ))));
                }
            };
            let translated_args = match translate_terms(ctx, args) {
                Ok(args) => args,
                Err(error) => return Some(Err(error)),
            };
            let term = {
                let mut session = ctx.session();
                uf::apply(&mut session, &func, &translated_args)
            };
            Ok(term)
        }
        _ => return None,
    };

    Some(result)
}

fn translate_unary(
    ctx: &mut ExecutionContext,
    expr: &Expr,
    build: impl FnOnce(&mut Session<'_>, Term) -> Term,
) -> Result<Term, ExecuteError> {
    let term = translate_expr(ctx, expr)?;
    translate_with_session(ctx, |session| build(session, term))
}

fn translate_binary(
    ctx: &mut ExecutionContext,
    left: &Expr,
    right: &Expr,
    build: impl FnOnce(&mut Session<'_>, Term, Term) -> Term,
) -> Result<Term, ExecuteError> {
    let lhs = translate_expr(ctx, left)?;
    let rhs = translate_expr(ctx, right)?;
    translate_with_session(ctx, |session| build(session, lhs, rhs))
}

fn translate_ternary(
    ctx: &mut ExecutionContext,
    first: &Expr,
    second: &Expr,
    third: &Expr,
    build: impl FnOnce(&mut Session<'_>, Term, Term, Term) -> Term,
) -> Result<Term, ExecuteError> {
    let one = translate_expr(ctx, first)?;
    let two = translate_expr(ctx, second)?;
    let three = translate_expr(ctx, third)?;
    translate_with_session(ctx, |session| build(session, one, two, three))
}

fn translate_nary(
    ctx: &mut ExecutionContext,
    exprs: &[Expr],
    build: impl FnOnce(&mut Session<'_>, &[Term]) -> Term,
) -> Result<Term, ExecuteError> {
    let terms = translate_terms(ctx, exprs)?;
    translate_with_session(ctx, |session| build(session, &terms))
}

fn translate_distinct(ctx: &mut ExecutionContext, exprs: &[Expr]) -> Result<Term, ExecuteError> {
    if exprs.len() < 2 {
        return Ok(ctx.solver.bool_const(true));
    }
    translate_nary(ctx, exprs, |session, terms| ops::distinct(session, terms))
}

fn translate_signed_bv_predicate(
    ctx: &mut ExecutionContext,
    left: &Expr,
    right: &Expr,
    build: impl FnOnce(&mut Session<'_>, Term, Term) -> Term,
) -> Result<Term, ExecuteError> {
    translate_binary(ctx, left, right, build)
}

fn translate_terms(ctx: &mut ExecutionContext, exprs: &[Expr]) -> Result<Vec<Term>, ExecuteError> {
    exprs.iter().map(|expr| translate_expr(ctx, expr)).collect()
}

fn translate_with_session(
    ctx: &mut ExecutionContext,
    build: impl FnOnce(&mut Session<'_>) -> Term,
) -> Result<Term, ExecuteError> {
    match panic::catch_unwind(AssertUnwindSafe(|| {
        let mut session = ctx.session();
        build(&mut session)
    })) {
        Ok(term) => Ok(term),
        Err(payload) => handle_bridge_builder_panic(payload),
    }
}

fn handle_bridge_builder_panic(payload: Box<dyn Any + Send>) -> Result<Term, ExecuteError> {
    let reason = ay_core::panic_payload_to_string(&*payload);
    if reason.starts_with("ay-translate ") || reason.contains(": ay-translate ") {
        Err(ExecuteError::ExprTranslation(reason))
    } else {
        panic::resume_unwind(payload)
    }
}
