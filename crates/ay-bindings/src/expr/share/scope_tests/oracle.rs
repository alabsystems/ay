// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

//! Independent Boolean semantics over the public SMT parser, not Expr builders
//! or the sharing planner. Every operand is evaluated, including unused ITE
//! arms, so an unbound symbol cannot hide behind Boolean short-circuiting.

use ay_frontend::{Command, Constant, Sort, Term};
use std::collections::HashMap;

#[derive(Clone, Copy)]
enum Quantifier {
    Universal,
    Existential,
}

pub(super) fn assertion(text: &str) -> Term {
    let commands = ay_frontend::parse(&format!("(assert {text})")).unwrap();
    let [Command::Assert(term)] = commands.as_slice() else {
        panic!("one assertion")
    };
    term.clone()
}

pub(super) fn evaluate(term: &Term, values: &[(&str, bool)]) -> Option<bool> {
    let env = values
        .iter()
        .map(|(name, value)| ((*name).to_owned(), *value))
        .collect();
    eval(term, &env)
}

fn eval(term: &Term, env: &HashMap<String, bool>) -> Option<bool> {
    match term {
        Term::Const(Constant::True) => Some(true),
        Term::Const(Constant::False) => Some(false),
        Term::Symbol(name) => env.get(name).copied(),
        Term::App(name, args) => {
            let args = args
                .iter()
                .map(|arg| eval(arg, env))
                .collect::<Option<Vec<_>>>()?;
            match (name.as_str(), args.as_slice()) {
                ("not", [value]) => Some(!value),
                ("and", values) => Some(values.iter().all(|v| *v)),
                ("or", values) => Some(values.iter().any(|v| *v)),
                ("xor", [a, b]) => Some(a ^ b),
                ("=", [a, b]) => Some(a == b),
                ("=>", [a, b]) => Some(!a || *b),
                ("ite", [condition, yes, no]) => Some(if *condition { *yes } else { *no }),
                _ => None,
            }
        }
        Term::Let(bindings, body) => {
            // SMT-LIB let bindings are simultaneous, not sequential.
            let values = bindings
                .iter()
                .map(|(name, value)| Some((name.clone(), eval(value, env)?)))
                .collect::<Option<Vec<_>>>()?;
            let mut nested = env.clone();
            nested.extend(values);
            eval(body, &nested)
        }
        Term::Forall(vars, body) => quantified(vars, body, env, Quantifier::Universal),
        Term::Exists(vars, body) => quantified(vars, body, env, Quantifier::Existential),
        Term::Annotated(body, _) => eval(body, env),
        _ => None,
    }
}

fn quantified(
    vars: &[(String, Sort)],
    body: &Term,
    env: &HashMap<String, bool>,
    quantifier: Quantifier,
) -> Option<bool> {
    let Some(((name, sort), rest)) = vars.split_first() else {
        return eval(body, env);
    };
    if !matches!(sort, Sort::Simple(name) if name == "Bool") {
        return None;
    }
    let mut nested = env.clone();
    nested.insert(name.clone(), false);
    let low = quantified(rest, body, &nested, quantifier)?;
    nested.insert(name.clone(), true);
    let high = quantified(rest, body, &nested, quantifier)?;
    Some(match quantifier {
        Quantifier::Universal => low && high,
        Quantifier::Existential => low || high,
    })
}
