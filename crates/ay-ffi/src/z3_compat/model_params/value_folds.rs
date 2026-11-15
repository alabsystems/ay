// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model evaluation through binders, and the value folds z3's model
//! evaluator applies that the term simplifier does not.
//!
//! `Z3_model_eval` used to refuse every term with a quantifier (capture
//! safety), and left `bv2nat`, `int2bv` and `^` over values unevaluated. The
//! publication backstop of `Z3_solver_check` reads the model the same way, so
//! a model that falsified a quantified assumption (`forall q. pr(5)` under
//! `pr = false`) or that left a function out was published. Here:
//!
//! * [`scoped_leaves`] separates the free constants of a term from the
//!   variables its binders bind, by name and scope. A constant that also
//!   occurs bound (a caller constant bound by `Z3_mk_forall_const` and used
//!   free elsewhere) cannot be substituted by term identity without capture,
//!   so such a term is still refused.
//! * [`fold_values`] folds `bv2nat`/`bv2int`, `int2bv` and `^` over literal
//!   arguments, a datatype selector or tester over a constructor
//!   application, `seq.len` over a sequence value, and a quantifier whose body is a literal or does not
//!   mention its variables.

use std::collections::{HashMap, HashSet};

use ay_dpll::api::{Solver, Sort, Term, TermKind};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};

/// The constants of a term, and its bound-variable occurrences.
pub(crate) struct ScopedLeaves {
    /// Constant leaves outside every binder of the same name.
    pub(crate) free: Vec<Term>,
    /// Variable occurrences some enclosing binder binds.
    pub(crate) bound: HashSet<Term>,
}

/// The leaves of `root` by scope. `None` for a `let` (its names are not
/// exposed) or when one term occurs both free and bound.
pub(crate) fn scoped_leaves(solver: &Solver, root: Term) -> Option<ScopedLeaves> {
    // Scopes are interned: scope 0 is empty, each binder opens its parent's
    // names plus its own.
    let mut scopes: Vec<Vec<String>> = vec![Vec::new()];
    let mut seen: HashSet<(Term, usize)> = HashSet::new();
    let mut stack = vec![(root, 0usize)];
    let mut free = Vec::new();
    let mut free_set = HashSet::new();
    let mut bound = HashSet::new();
    while let Some((term, scope)) = stack.pop() {
        if !seen.insert((term, scope)) {
            continue;
        }
        match solver.term_kind(term) {
            TermKind::Var { name } => {
                if scopes[scope].contains(&name) {
                    bound.insert(term);
                } else if free_set.insert(term) {
                    free.push(term);
                }
            }
            TermKind::Const => {}
            TermKind::Forall | TermKind::Exists => {
                let mut names = scopes[scope].clone();
                names.extend(
                    solver
                        .quantifier_bound_vars(term)?
                        .into_iter()
                        .map(|(n, _)| n),
                );
                scopes.push(names);
                let inner = scopes.len() - 1;
                stack.extend(solver.term_children(term).into_iter().map(|c| (c, inner)));
            }
            // A lambda (`lambda-array`) binds its variable, as a quantifier
            // does: substituting a model value for it built `(lambda-array 0
            // 1)`, which is no term at all.
            TermKind::App { name, num_args: 2 } if name == "lambda-array" => {
                let children = solver.term_children(term);
                let TermKind::Var { name: var } = solver.term_kind(children[0]) else {
                    return None;
                };
                let mut names = scopes[scope].clone();
                names.push(var);
                scopes.push(names);
                stack.push((children[1], scopes.len() - 1));
            }
            TermKind::App { .. } | TermKind::Not | TermKind::Ite => {
                stack.extend(solver.term_children(term).into_iter().map(|c| (c, scope)));
            }
            _ => return None,
        }
    }
    if free.iter().any(|leaf| bound.contains(leaf)) {
        return None;
    }
    Some(ScopedLeaves { free, bound })
}

/// The nullary applications of `root` (`f` of a `Z3_mk_func_decl` of arity
/// 0), with their names.
pub(crate) fn nullary_applications(solver: &Solver, root: Term) -> Vec<(Term, String)> {
    let mut seen = HashSet::new();
    let mut stack = vec![root];
    let mut out = Vec::new();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermKind::App { name, num_args: 0 } = solver.term_kind(term) {
            out.push((term, name));
        }
        stack.extend(solver.term_children(term));
    }
    out
}

/// Whether `term` mentions one of `vars`.
pub(crate) fn mentions_any(solver: &Solver, term: Term, vars: &HashSet<Term>) -> bool {
    if vars.is_empty() {
        return false;
    }
    let mut seen = HashSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if vars.contains(&t) {
            return true;
        }
        stack.extend(solver.term_children(t));
    }
    false
}

fn int_literal(solver: &Solver, term: Term) -> Option<BigInt> {
    if !solver.is_numeral(term) || solver.term_sort(term) != Sort::Int {
        return None;
    }
    solver.numeral_string(term)?.parse().ok()
}

fn rational_literal(solver: &Solver, term: Term) -> Option<BigRational> {
    if !solver.is_numeral(term) {
        return None;
    }
    match solver.term_sort(term) {
        Sort::Int => Some(BigRational::from_integer(int_literal(solver, term)?)),
        Sort::Real => {
            let text = solver.numeral_string(term)?;
            let (numer, denom) = text.split_once('/').unwrap_or((&text, "1"));
            let numer: BigInt = numer.parse().ok()?;
            let denom: BigInt = denom.parse().ok()?;
            (!denom.is_zero()).then(|| BigRational::new(numer, denom))
        }
        _ => None,
    }
}

fn bv_literal(solver: &Solver, term: Term) -> Option<BigInt> {
    if !solver.is_numeral(term) || !matches!(solver.term_sort(term), Sort::BitVec(_)) {
        return None;
    }
    solver.numeral_string(term)?.parse().ok()
}

fn rational_term(solver: &mut Solver, value: &BigRational, sort: &Sort) -> Term {
    if *sort == Sort::Int && value.is_integer() {
        solver.int_const_bigint(&value.to_integer())
    } else {
        solver.rational_const_bigint(value.numer(), value.denom())
    }
}

/// `base ^ exponent` over literals, where z3 defines it: an integer exponent,
/// and a non-zero base unless the exponent is positive.
fn power_value(base: &BigRational, exponent: &BigRational) -> Option<BigRational> {
    if !exponent.is_integer() {
        return None;
    }
    let k = exponent.to_integer();
    if base.is_zero() && !k.is_positive() {
        return None;
    }
    let magnitude = k.abs().to_u32().filter(|&m| m <= 4096)?;
    let mut value = BigRational::one();
    for _ in 0..magnitude {
        value *= base;
    }
    Some(if k.is_negative() {
        value.recip()
    } else {
        value
    })
}

/// The width `n` of an `(_ int2bv n)` operator name.
fn int2bv_width(name: &str) -> Option<u32> {
    name.strip_prefix("(_ int2bv ")?
        .strip_suffix(')')?
        .trim()
        .parse()
        .ok()
}

/// One bottom-up pass of the folds listed in the module docs.
pub(crate) fn fold_values(solver: &mut Solver, root: Term) -> Term {
    let mut memo: HashMap<Term, Term> = HashMap::new();
    fold_rec(solver, root, &mut memo, 0)
}

fn fold_rec(solver: &mut Solver, term: Term, memo: &mut HashMap<Term, Term>, depth: usize) -> Term {
    if let Some(&done) = memo.get(&term) {
        return done;
    }
    if depth > 2000 {
        return term;
    }
    let kind = solver.term_kind(term);
    if matches!(kind, TermKind::Var { .. } | TermKind::Const) {
        return term;
    }
    let children = solver.term_children(term);
    let folded: Vec<Term> = children
        .iter()
        .map(|&child| fold_rec(solver, child, memo, depth + 1))
        .collect();
    let rebuilt = if folded == children {
        term
    } else {
        solver.update_term(term, &folded).unwrap_or(term)
    };
    let result = match kind {
        TermKind::App { name, num_args: 1 } if name == "bv2nat" || name == "bv2int" => {
            match bv_literal(solver, folded[0]) {
                Some(value) => solver.int_const_bigint(&value),
                None => rebuilt,
            }
        }
        TermKind::App { name, num_args: 1 } if int2bv_width(&name).is_some() => {
            match (int2bv_width(&name), int_literal(solver, folded[0])) {
                (Some(width), Some(value)) => {
                    let modulus = BigInt::one() << width;
                    let wrapped = ((value % &modulus) + &modulus) % &modulus;
                    solver.bv_const_bigint(&wrapped, width)
                }
                _ => rebuilt,
            }
        }
        TermKind::App { name, num_args: 1 } if name == "seq.len" => {
            match sequence_length(solver, folded[0], 0) {
                Some(length) => solver.int_const_bigint(&BigInt::from(length)),
                None => rebuilt,
            }
        }
        TermKind::App { name, num_args: 1 } => {
            datatype_access(solver, &name, folded[0]).unwrap_or(rebuilt)
        }
        TermKind::App { name, num_args: 2 } if name == "^" => {
            let sort = solver.term_sort(term);
            match (
                rational_literal(solver, folded[0]),
                rational_literal(solver, folded[1]),
            ) {
                (Some(base), Some(exponent)) => match power_value(&base, &exponent) {
                    Some(value) if sort == Sort::Real || value.is_integer() => {
                        rational_term(solver, &value, &sort)
                    }
                    _ => rebuilt,
                },
                _ => rebuilt,
            }
        }
        TermKind::Forall | TermKind::Exists => {
            let body = folded[0];
            match solver.bool_value(body) {
                // Every sort is non-empty, so a quantifier over a literal body
                // is that literal.
                Some(value) => solver.bool_const(value),
                None => {
                    let names: HashSet<String> = solver
                        .quantifier_bound_vars(term)
                        .unwrap_or_default()
                        .into_iter()
                        .map(|(name, _)| name)
                        .collect();
                    if mentions_named_var(solver, body, &names) {
                        rebuilt
                    } else {
                        body
                    }
                }
            }
        }
        _ => rebuilt,
    };
    memo.insert(term, result);
    result
}

/// The length of a sequence value built from `seq.empty`, `seq.unit` and
/// `seq.++` (`seq.len(seq.unit 0)` is `1`); `None` for anything else.
fn sequence_length(solver: &Solver, term: Term, depth: usize) -> Option<usize> {
    if depth > 256 {
        return None;
    }
    match solver.term_kind(term) {
        TermKind::App { name, num_args: 0 } if name == "seq.empty" => Some(0),
        TermKind::App { name, num_args: 1 } if name == "seq.unit" => Some(1),
        TermKind::App { name, .. } if name == "seq.++" => {
            let mut total = 0usize;
            for part in solver.term_children(term) {
                total = total.checked_add(sequence_length(solver, part, depth + 1)?)?;
            }
            Some(total)
        }
        _ => None,
    }
}

/// A selector or tester applied to a constructor value: `hd(cons(3, nil))`
/// is `3` and `is-nil(cons(3, nil))` is `false`, as z3's evaluator reduces
/// them. `None` for anything else, including a selector of another
/// constructor (`hd(nil)`, which only model completion could interpret).
fn datatype_access(solver: &mut Solver, name: &str, arg: Term) -> Option<Term> {
    let (ctor, fields) = match solver.term_kind(arg) {
        TermKind::App { name: ctor, .. } => (ctor, solver.term_children(arg)),
        TermKind::Var { name: ctor } => (ctor, Vec::new()),
        _ => return None,
    };
    let (datatype, selectors) = solver.constructor_selector_names(&ctor)?;
    if selectors.len() != fields.len() {
        return None;
    }
    if let Some(tested) = name.strip_prefix("is-") {
        // Only a tester of a constructor of the same datatype.
        let (tested_datatype, _) = solver.constructor_selector_names(tested)?;
        if tested_datatype != datatype {
            return None;
        }
        return Some(solver.bool_const(tested == ctor));
    }
    let index = selectors.iter().position(|selector| selector == name)?;
    Some(fields[index])
}

/// Whether `term` has a variable leaf named in `names` (a binder's variables;
/// an inner binder of the same name only shadows, so this over-approximates,
/// which only keeps a quantifier).
fn mentions_named_var(solver: &Solver, term: Term, names: &HashSet<String>) -> bool {
    let mut seen = HashSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if let TermKind::Var { name } = solver.term_kind(t) {
            if names.contains(&name) {
                return true;
            }
        }
        stack.extend(solver.term_children(t));
    }
    false
}
