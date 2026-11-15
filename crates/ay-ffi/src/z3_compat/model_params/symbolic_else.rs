// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Function interpretations whose body is a term over the parameters.
//!
//! A quantified definition `forall y. f(y) = y + 1` is satisfied by no finite
//! table: the engine's validated model interprets `f` as `(+ x0 1)`, and z3
//! publishes `f = [else -> 1 + Var(0)]`. The literal-table reader
//! ([`super::parse_func_interps`]) cannot carry such a body, so the API either
//! dropped `f` (measured: `sat` with the bound `y` listed instead, under which
//! the assertion is false) or, once that was refused, answered `unknown`. This
//! reader carries the body as the interpretation's `else` over private
//! parameter variables (argument `i`), for the arithmetic and Boolean body
//! shapes the engine prints; any other body stays unrepresented and the check
//! is refused as before. The private variables are never declared constants of
//! the context: the reader runs inside `Z3_solver_check`, and a declaration
//! there leaked into later models and fixed the de Bruijn variable's sort for
//! the whole context. Only `Z3_func_interp_get_else` shows the body over the
//! de Bruijn variables `__db{i}` (the `Z3_mk_bound` convention).

use ay_dpll::api::{ModelValue, Solver, Term};
use ay_frontend::SExpr;
use num_bigint::BigInt;

use super::{parse_sort_sexpr, FuncInterp};

/// Interpretations for every function `define-fun` of `model_text` that
/// `known` (the literal tables) does not carry and whose body converts.
pub(crate) fn symbolic_func_interps(
    solver: &mut Solver,
    model_text: &str,
    known: &[FuncInterp],
) -> Vec<FuncInterp> {
    let Ok(root) = ay_frontend::sexp::parse_sexp(model_text) else {
        return Vec::new();
    };
    let SExpr::List(items) = &root else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for item in items {
        let SExpr::List(parts) = item else { continue };
        let [SExpr::Symbol(kw), SExpr::Symbol(name), SExpr::List(params), result, body] =
            parts.as_slice()
        else {
            continue;
        };
        if kw != "define-fun"
            || params.is_empty()
            || known
                .iter()
                .any(|fi| fi.name == *name && fi.param_sorts.len() == params.len())
        {
            continue;
        }
        let Some(result_sort) = parse_sort_sexpr(result) else {
            continue;
        };
        let mut bound: Vec<(String, Term)> = Vec::with_capacity(params.len());
        let mut param_sorts = Vec::with_capacity(params.len());
        let mut parsed = true;
        for (i, param) in params.iter().enumerate() {
            let SExpr::List(pair) = param else {
                parsed = false;
                break;
            };
            let [SExpr::Symbol(param_name), param_sort] = pair.as_slice() else {
                parsed = false;
                break;
            };
            let Some(sort) = parse_sort_sexpr(param_sort) else {
                parsed = false;
                break;
            };
            // A PRIVATE parameter variable: never a declared constant of the
            // context. Declaring the de Bruijn `__db{i}` here (inside
            // `Z3_solver_check`) leaked it into every later model and fixed
            // its sort for the whole context, so a later `Z3_mk_bound` or
            // symbolic else at another sort panicked in `declare_const`.
            let Ok(var) = solver.try_fresh_var(&private_param_prefix(i), sort.clone()) else {
                parsed = false;
                break;
            };
            bound.push((param_name.clone(), var));
            param_sorts.push(sort);
        }
        if !parsed {
            continue;
        }
        let Some(term) = body_term(solver, body, &bound) else {
            continue;
        };
        if solver.term_sort(term) != result_sort {
            continue;
        }
        out.push(FuncInterp {
            name: name.clone(),
            param_sorts,
            result_sort,
            rows: Vec::new(),
            else_value: ModelValue::Unknown,
            else_term: Some((bound.into_iter().map(|(_, var)| var).collect(), term)),
        });
    }
    out
}

/// The name prefix of the private variable standing for parameter `i` of a
/// symbolic else (`try_fresh_var` appends `_<id>`).
pub(crate) fn private_param_prefix(i: usize) -> String {
    format!("!ay.z3-else-param{i}")
}

/// The body of `interp`'s symbolic `else` over the de Bruijn bound variables
/// `__db{i}` (the `Z3_mk_bound` convention z3 uses for
/// `Z3_func_interp_get_else`: `[else -> Var(0) + 1]`). The variables are
/// created only now, when the caller asks for the body, exactly as
/// `Z3_mk_bound` creates them (one variable per index and sort, so an index
/// already used at another sort is no conflict). Should a variable not be
/// declarable, the body over the private parameters is returned instead
/// (never a panic, never a re-sorted binder).
pub(crate) fn else_body_over_bound_vars(solver: &mut Solver, interp: &FuncInterp) -> Option<Term> {
    let (params, body) = interp.else_term.as_ref()?;
    let mut bound = Vec::with_capacity(params.len());
    for (i, sort) in interp.param_sorts.iter().enumerate() {
        match solver.try_de_bruijn_var(i, sort.clone()) {
            Ok(var) => bound.push(var),
            Err(_) => return Some(*body),
        }
    }
    Some(solver.substitute(*body, params, &bound))
}

/// The term an engine-printed body denotes, for the shapes listed in the
/// module docs; `None` for anything else.
fn body_term(solver: &mut Solver, body: &SExpr, bound: &[(String, Term)]) -> Option<Term> {
    match body {
        SExpr::True => Some(solver.bool_const(true)),
        SExpr::False => Some(solver.bool_const(false)),
        SExpr::Numeral(text) => Some(solver.int_const_bigint(&text.parse::<BigInt>().ok()?)),
        SExpr::Decimal(text) => {
            let (int_part, frac_part) = text.split_once('.')?;
            let numer = format!("{int_part}{frac_part}").parse::<BigInt>().ok()?;
            let denom = BigInt::from(10u32).pow(u32::try_from(frac_part.len()).ok()?);
            solver.try_rational_const_bigint(&numer, &denom).ok()
        }
        SExpr::Symbol(name) => bound
            .iter()
            .find(|(param, _)| param == name)
            .map(|&(_, var)| var),
        SExpr::List(items) => {
            let (SExpr::Symbol(op), operands) = items.split_first()? else {
                return None;
            };
            let args = operands
                .iter()
                .map(|operand| body_term(solver, operand, bound))
                .collect::<Option<Vec<Term>>>()?;
            apply(solver, op, &args)
        }
        _ => None,
    }
}

/// `op` applied to `args`, through the solver's sort-checked builders.
fn apply(solver: &mut Solver, op: &str, args: &[Term]) -> Option<Term> {
    let built = match (op, args) {
        ("-", [a]) => solver.try_neg(*a),
        ("-", [first, rest @ ..]) if !rest.is_empty() => {
            let mut acc = *first;
            for &next in rest {
                acc = solver.try_sub(acc, next).ok()?;
            }
            Ok(acc)
        }
        ("+", [_, _, ..]) => solver.try_add_many(args),
        ("*", [_, _, ..]) => solver.try_mul_many(args),
        ("/", [a, b]) => solver.try_div(*a, *b),
        ("div", [a, b]) => solver.try_int_div(*a, *b),
        ("mod", [a, b]) => solver.try_modulo(*a, *b),
        ("ite", [c, t, e]) => solver.try_ite(*c, *t, *e),
        ("=", [a, b]) => solver.try_eq(*a, *b),
        ("<", [a, b]) => solver.try_lt(*a, *b),
        ("<=", [a, b]) => solver.try_le(*a, *b),
        (">", [a, b]) => solver.try_gt(*a, *b),
        (">=", [a, b]) => solver.try_ge(*a, *b),
        ("and", [_, _, ..]) => solver.try_and_many(args),
        ("or", [_, _, ..]) => solver.try_or_many(args),
        ("not", [a]) => solver.try_not(*a),
        ("=>", [a, b]) => solver.try_implies(*a, *b),
        _ => return None,
    };
    built.ok()
}

/// The value of `interp`'s symbolic `else` at `args`: the body with each
/// parameter replaced by its argument, simplified.
pub(crate) fn instantiate_else(
    solver: &mut Solver,
    interp: &FuncInterp,
    args: &[Term],
) -> Option<Term> {
    let (params, body) = interp.else_term.as_ref()?;
    if params.len() != args.len() {
        return None;
    }
    let substituted = solver.substitute(*body, params, args);
    Some(solver.simplify(substituted))
}
