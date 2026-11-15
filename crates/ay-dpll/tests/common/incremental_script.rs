// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Replay an incremental (push/pop) SMT-LIB script on one executor and check
//! every verdict against something the executor's incremental lane did not
//! compute.
//!
//! A verdict-only pin cannot tell a correct `sat` from one whose model is
//! wrong or a correct `unsat` from a stale one, and a debug assertion inside
//! the solver vanishes under `--release`. So, independently of the lane under
//! test:
//!
//! * after every `sat`, the values of all declared constants are read with
//!   `get-value` and every assertion live at that check-sat is evaluated on
//!   them with exact rational arithmetic;
//! * after every `unsat`, the assertions live at that check-sat are solved
//!   again on a fresh, non-incremental `Executor` (no persistent SAT solver,
//!   no scopes), which must answer `unsat` too.
//!
//! Supported fragment: Bool/Int/Real constants, numerals, decimals, `+ - * /`,
//! `< <= > >= = distinct`, `not and or => xor ite`.

use ay_dpll::Executor;
use ay_frontend::parse;
use ay_frontend::sexp::{parse_sexps, SExpr};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq)]
enum Value {
    Bool(bool),
    Num(BigRational),
}

type Env = HashMap<String, Value>;

fn eval(expr: &SExpr, env: &Env) -> Value {
    match expr {
        SExpr::True => Value::Bool(true),
        SExpr::False => Value::Bool(false),
        SExpr::Numeral(n) => Value::Num(BigRational::from_integer(
            n.parse::<BigInt>()
                .unwrap_or_else(|e| panic!("numeral {n}: {e}")),
        )),
        SExpr::Decimal(d) => Value::Num(decimal(d)),
        SExpr::Symbol(s) if s == "true" => Value::Bool(true),
        SExpr::Symbol(s) if s == "false" => Value::Bool(false),
        SExpr::Symbol(s) => match negative_literal(s) {
            Some(n) => Value::Num(n),
            None => env
                .get(s)
                .cloned()
                .unwrap_or_else(|| panic!("no model value for `{s}`")),
        },
        SExpr::List(items) => {
            let (head, args) = items
                .split_first()
                .unwrap_or_else(|| panic!("empty application"));
            let op = head
                .as_symbol()
                .unwrap_or_else(|| panic!("unsupported head {head}"));
            let vals: Vec<Value> = args.iter().map(|a| eval(a, env)).collect();
            apply(op, &vals)
        }
        other => panic!("unsupported term {other}"),
    }
}

/// `-3` and `-3.5` lex as symbols, and the model printer emits negative
/// values that way.
fn negative_literal(symbol: &str) -> Option<BigRational> {
    let digits = symbol.strip_prefix('-')?;
    let numeric = !digits.is_empty()
        && digits.chars().all(|c| c.is_ascii_digit() || c == '.')
        && digits.chars().filter(|&c| c == '.').count() <= 1;
    numeric.then(|| -decimal(digits))
}

fn decimal(text: &str) -> BigRational {
    let (int_part, frac_part) = text.split_once('.').unwrap_or((text, ""));
    let digits: BigInt = format!("{int_part}{frac_part}")
        .parse()
        .unwrap_or_else(|e| panic!("decimal {text}: {e}"));
    let scale = BigInt::from(10u32).pow(u32::try_from(frac_part.len()).expect("short decimal"));
    BigRational::new(digits, scale)
}

fn num(v: &Value) -> &BigRational {
    match v {
        Value::Num(n) => n,
        Value::Bool(_) => panic!("expected a number, got {v:?}"),
    }
}

fn boolean(v: &Value) -> bool {
    match v {
        Value::Bool(b) => *b,
        Value::Num(_) => panic!("expected a Boolean, got {v:?}"),
    }
}

fn chain(vals: &[Value], rel: impl Fn(&BigRational, &BigRational) -> bool) -> Value {
    Value::Bool(vals.windows(2).all(|w| rel(num(&w[0]), num(&w[1]))))
}

fn apply(op: &str, vals: &[Value]) -> Value {
    match op {
        "+" => Value::Num(vals.iter().fold(BigRational::zero(), |acc, v| acc + num(v))),
        "*" => Value::Num(vals.iter().fold(BigRational::one(), |acc, v| acc * num(v))),
        "-" if vals.len() == 1 => Value::Num(-num(&vals[0]).clone()),
        "-" => Value::Num(
            vals[1..]
                .iter()
                .fold(num(&vals[0]).clone(), |acc, v| acc - num(v)),
        ),
        "/" => {
            let d = num(&vals[1]);
            assert!(!d.is_zero(), "division by zero in an asserted term");
            Value::Num(num(&vals[0]) / d)
        }
        "<" => chain(vals, |a, b| a < b),
        "<=" => chain(vals, |a, b| a <= b),
        ">" => chain(vals, |a, b| a > b),
        ">=" => chain(vals, |a, b| a >= b),
        "=" => Value::Bool(vals.windows(2).all(|w| w[0] == w[1])),
        "distinct" => {
            Value::Bool((0..vals.len()).all(|i| (i + 1..vals.len()).all(|j| vals[i] != vals[j])))
        }
        "not" => Value::Bool(!boolean(&vals[0])),
        "and" => Value::Bool(vals.iter().all(boolean)),
        "or" => Value::Bool(vals.iter().any(boolean)),
        "=>" => Value::Bool(!boolean(&vals[0]) || boolean(&vals[1])),
        "xor" => Value::Bool(boolean(&vals[0]) != boolean(&vals[1])),
        "ite" => {
            if boolean(&vals[0]) {
                vals[1].clone()
            } else {
                vals[2].clone()
            }
        }
        other => panic!("unsupported operator `{other}`"),
    }
}

/// Parse a `get-value` answer `((name value) ...)` into a model.
fn parse_model(answer: &str) -> Env {
    let parsed = parse_sexps(answer).unwrap_or_else(|e| panic!("get-value answer {answer}: {e}"));
    let bindings = parsed
        .first()
        .and_then(SExpr::as_list)
        .unwrap_or_else(|| panic!("get-value answer is not a list: {answer}"));
    bindings
        .iter()
        .map(|binding| {
            let pair = binding
                .as_list()
                .unwrap_or_else(|| panic!("binding {binding} in {answer}"));
            let name = pair[0].as_symbol().expect("bound symbol").to_owned();
            (name, eval(&pair[1], &Env::new()))
        })
        .collect()
}

/// Run `smt` on a fresh default executor and return its single verdict.
fn fresh_verdict(smt: &str) -> String {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"));
    let mut exec = Executor::new();
    let mut verdict = None;
    for command in &commands {
        let answer = exec
            .execute_authored(command)
            .unwrap_or_else(|err| panic!("execution failed: {err}\nSMT2:\n{smt}"));
        if let Some(line) = answer.map(|a| a.trim().to_owned()) {
            if matches!(line.as_str(), "sat" | "unsat" | "unknown") {
                verdict = Some(line);
            }
        }
    }
    verdict.unwrap_or_else(|| panic!("no verdict printed\nSMT2:\n{smt}"))
}

/// The number of `push` / `pop` levels a command names (default 1).
fn scope_count(items: &[SExpr]) -> usize {
    items
        .get(1)
        .and_then(SExpr::as_numeral)
        .map_or(1, |n| n.parse::<usize>().expect("push/pop count"))
}

/// Execute `smt` on one executor, configured by `configure`, and return the
/// check-sat verdicts in order, checking every `sat` against its model and
/// every `unsat` against a fresh non-incremental solve (see the module docs).
pub(crate) fn run_checking_models(smt: &str, configure: impl FnOnce(&mut Executor)) -> Vec<String> {
    let texts = parse_sexps(smt).unwrap_or_else(|err| panic!("sexp parse failed: {err}\n{smt}"));
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"));
    assert_eq!(
        texts.len(),
        commands.len(),
        "one command per top-level s-expression"
    );

    let mut exec = Executor::new();
    configure(&mut exec);
    let produce_models = parse("(set-option :produce-models true)").expect("option parses");
    exec.execute_authored(&produce_models[0])
        .expect("enable model production");

    // `set-logic` and the declarations, replayed verbatim for the fresh run.
    let mut preamble: Vec<String> = Vec::new();
    let mut declared: Vec<String> = Vec::new();
    let mut frames: Vec<Vec<SExpr>> = vec![Vec::new()];
    let mut verdicts = Vec::new();
    for (text, command) in texts.iter().zip(&commands) {
        let items = text.as_list().unwrap_or_default();
        match items.first().and_then(SExpr::as_symbol) {
            Some("set-logic") => preamble.push(text.to_string()),
            Some("declare-const") => {
                declared.push(items[1].as_symbol().expect("name").to_owned());
                preamble.push(text.to_string());
            }
            Some("declare-fun") if items[2].as_list().is_some_and(<[SExpr]>::is_empty) => {
                declared.push(items[1].as_symbol().expect("name").to_owned());
                preamble.push(text.to_string());
            }
            Some("assert") => frames
                .last_mut()
                .expect("a live frame")
                .push(items[1].clone()),
            Some("push") => {
                for _ in 0..scope_count(items) {
                    frames.push(Vec::new());
                }
            }
            Some("pop") => {
                for _ in 0..scope_count(items) {
                    frames.pop();
                }
                assert!(!frames.is_empty(), "script pops below the base frame");
            }
            _ => {}
        }

        let answer = exec
            .execute_authored(command)
            .unwrap_or_else(|err| panic!("execution failed: {err}\nSMT2:\n{smt}"));
        let Some(line) = answer.map(|a| a.trim().to_owned()) else {
            continue;
        };
        if !matches!(line.as_str(), "sat" | "unsat" | "unknown") {
            continue;
        }
        let live = frames.iter().flatten();
        if line == "sat" && !declared.is_empty() {
            let query = format!("(get-value ({}))", declared.join(" "));
            let query = parse(&query).expect("get-value parses");
            let values = exec
                .execute_authored(&query[0])
                .unwrap_or_else(|err| panic!("get-value failed: {err}\nSMT2:\n{smt}"))
                .unwrap_or_else(|| panic!("get-value printed nothing\nSMT2:\n{smt}"));
            let model = parse_model(&values);
            for assertion in live {
                assert_eq!(
                    eval(assertion, &model),
                    Value::Bool(true),
                    "check-sat #{} answered sat with a model violating {assertion}\n\
                     model: {values}\nSMT2:\n{smt}",
                    verdicts.len(),
                );
            }
        } else if line == "unsat" {
            let mut flat = preamble.clone();
            flat.extend(live.map(|assertion| format!("(assert {assertion})")));
            flat.push("(check-sat)".to_owned());
            let flat = flat.join("\n");
            assert_eq!(
                fresh_verdict(&flat),
                "unsat",
                "check-sat #{} answered unsat but a fresh non-incremental solve of its live \
                 assertions did not:\n{flat}\nSMT2:\n{smt}",
                verdicts.len(),
            );
        }
        verdicts.push(line);
    }
    verdicts
}

/// The scripts of `repros/empty-clause-scope-2026-09-23/corpus/` whose file
/// name starts with `prefix`, sorted by name, as `(file name, contents)`.
///
/// A missing or empty corpus is a failure, not a skip: a test that checked
/// nothing must not read as green.
pub(crate) fn empty_clause_scope_corpus(prefix: &str) -> Vec<(String, String)> {
    let dir = super::workspace_path("repros/empty-clause-scope-2026-09-23/corpus");
    let mut scripts: Vec<(String, String)> = std::fs::read_dir(&dir)
        .unwrap_or_else(|err| panic!("corpus {} must be present: {err}", dir.display()))
        .map(|entry| entry.expect("readable corpus entry").path())
        .filter(|path| {
            path.extension()
                .is_some_and(|ext| ext.eq_ignore_ascii_case("smt2"))
                && path
                    .file_name()
                    .and_then(|name| name.to_str())
                    .is_some_and(|name| name.starts_with(prefix))
        })
        .map(|path| {
            let name = path
                .file_name()
                .and_then(|name| name.to_str())
                .expect("utf-8 file name")
                .to_owned();
            let smt = std::fs::read_to_string(&path)
                .unwrap_or_else(|err| panic!("read {}: {err}", path.display()));
            (name, smt)
        })
        .collect();
    scripts.sort();
    assert!(
        !scripts.is_empty(),
        "no `{prefix}*.smt2` script in {}",
        dir.display()
    );
    scripts
}
