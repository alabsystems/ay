// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Independent tiny SMT interpreter for exhaustive Bool/BV2 lexical tests.
//! It consumes emitted text, not the source AST or renderer's variable maps.
//! `SExpr` erases symbol quoting, so this is not an independent lexical
//! validator. Raw indexed syntax is checked separately on renderer output.

use ay_frontend::sexp::{parse_sexps, SExpr};
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Value {
    Bool(bool),
    Bv(u64),
}

type Env = BTreeMap<String, Value>;

fn symbol(expr: &SExpr) -> &str {
    let SExpr::Symbol(value) = expr else {
        panic!("symbol required");
    };
    value
}

fn list(expr: &SExpr) -> &[SExpr] {
    let SExpr::List(values) = expr else {
        panic!("list required");
    };
    values
}

fn domain(sort: &SExpr) -> Vec<Value> {
    if matches!(sort, SExpr::Symbol(name) if name == "Bool") {
        return vec![Value::Bool(false), Value::Bool(true)];
    }
    // Display quotes reserved symbol names, including `_`; it is not the
    // original SMT syntax. Authenticate the exact indexed-sort tree instead.
    assert!(matches!(list(sort),
        [SExpr::Symbol(marker), SExpr::Symbol(name), SExpr::Numeral(width)]
            if marker == "_" && name == "BitVec" && width == "2"
    ));
    (0..4).map(Value::Bv).collect()
}

fn truth(value: Value) -> bool {
    let Value::Bool(value) = value else {
        panic!("Boolean required");
    };
    value
}

fn evaluate(expr: &SExpr, env: &Env) -> Value {
    match expr {
        SExpr::True => return Value::Bool(true),
        SExpr::False => return Value::Bool(false),
        SExpr::Symbol(name) => return env.get(name).expect("every free name declared").clone(),
        _ => {}
    }
    let values = list(expr);
    let op = symbol(&values[0]);
    let args = &values[1..];
    match op {
        "_" => {
            assert_eq!(args[1].to_string(), "2");
            Value::Bv(
                symbol(&args[0])
                    .strip_prefix("bv")
                    .unwrap()
                    .parse()
                    .unwrap(),
            )
        }
        "let" => {
            let mut next = env.clone();
            // SMT lets are simultaneous: every right side sees the old env.
            for binding in list(&args[0]) {
                let binding = list(binding);
                next.insert(symbol(&binding[0]).to_owned(), evaluate(&binding[1], env));
            }
            evaluate(&args[1], &next)
        }
        "forall" => Value::Bool(forall(list(&args[0]), &args[1], env)),
        "=" => Value::Bool(evaluate(&args[0], env) == evaluate(&args[1], env)),
        "distinct" => Value::Bool(evaluate(&args[0], env) != evaluate(&args[1], env)),
        "not" => Value::Bool(!truth(evaluate(&args[0], env))),
        "and" => Value::Bool(args.iter().all(|arg| truth(evaluate(arg, env)))),
        "=>" => Value::Bool(!truth(evaluate(&args[0], env)) || truth(evaluate(&args[1], env))),
        "bvadd" => {
            let (Value::Bv(a), Value::Bv(b)) = (evaluate(&args[0], env), evaluate(&args[1], env))
            else {
                panic!("BV arguments");
            };
            Value::Bv((a + b) % 4)
        }
        _ => panic!("unsupported oracle operation {op}"),
    }
}

fn forall(bindings: &[SExpr], body: &SExpr, env: &Env) -> bool {
    let Some((binding, rest)) = bindings.split_first() else {
        return truth(evaluate(body, env));
    };
    let binding = list(binding);
    domain(&binding[1]).into_iter().all(|value| {
        let mut next = env.clone();
        next.insert(symbol(&binding[0]).to_owned(), value);
        forall(rest, body, &next)
    })
}

pub(super) fn models(script: &str) -> Vec<Vec<u64>> {
    let commands = parse_sexps(script).unwrap();
    let mut declarations = Vec::new();
    let mut assertions = Vec::new();
    for command in &commands {
        let command = list(command);
        match symbol(&command[0]) {
            "declare-const" => declarations.push((symbol(&command[1]), domain(&command[2]))),
            "assert" => assertions.push(&command[1]),
            "set-logic" | "check-sat" => {}
            other => panic!("unsupported oracle command {other}"),
        }
    }
    let count = declarations
        .iter()
        .map(|(_, values)| values.len())
        .product::<usize>();
    assert!(count <= 256);
    let mut models = Vec::new();
    for ordinal in 0..count {
        let mut remaining = ordinal;
        let mut env = Env::new();
        let mut row = Vec::new();
        for (name, values) in &declarations {
            let value = &values[remaining % values.len()];
            remaining /= values.len();
            row.push(match value {
                Value::Bool(value) => u64::from(*value),
                Value::Bv(value) => *value,
            });
            assert!(env.insert((*name).to_owned(), value.clone()).is_none());
        }
        if assertions
            .iter()
            .all(|assertion| truth(evaluate(assertion, &env)))
        {
            models.push(row);
        }
    }
    models
}
