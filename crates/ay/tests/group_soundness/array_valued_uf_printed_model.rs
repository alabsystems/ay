// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The model the CLI prints for an array-valued uninterpreted function
//! satisfies the assertions (2026-09-23 hunt M2; 2026-09-24 verifier).
//!
//! M2: main printed `g = ((as const (Array Int Int)) 0)` with `i2 = 1`,
//! `i1 = 1`, `a1 = (store K0 1 0)`, so assertion 2 reads `(g 2)[1] = 0 >
//! a1[1] = 0`, false, while its independent model gate said `confirmed-sat`:
//! the gate evaluated `(g (+ i2 1))` from a per-application pin the printed
//! `g` contradicts. The in-process group pin
//! (`m2_array_valued_uf_model_is_checked_as_printed`) passed with the gate fix
//! reverted because the in-process executor never reaches that model; the CLI
//! does. These tests run the CLI binary, in both postures, and check what it
//! PRINTS:
//!
//! * the M2 witness: a `sat` must come with a `(get-model)` under which every
//!   assertion evaluates to true. The check does not ask AY: it parses the
//!   printed `define-fun`s and evaluates the assertions with a self-contained
//!   evaluator for exactly this fragment (Int arithmetic comparisons, `+`,
//!   const/store/select arrays over Int, `ite`, and applications of printed
//!   functions);
//! * the verifier's `m2u_27`, UNSAT by congruence (`i2 = 1` makes
//!   `(g (+ i2 1))` the application `(g 2)`, asserted to be `(const 1)`, so
//!   assertion 2 reads `1 > 3`; z3 5.1.0 `unsat`): main printed `sat` with
//!   `confirmed-sat` in both postures. Never `sat`.

use ntest::timeout;
use std::collections::BTreeMap;
use std::process::Command;
use std::time::Duration;

use crate::spawn::OutputTimeout;

const TIMEOUT: Duration = Duration::from_mins(2);

const M2: &str = "\
(set-logic QF_AUFLIA)
(declare-fun g (Int) (Array Int Int))
(declare-fun f ((Array Int Int)) Int)
(declare-fun a1 () (Array Int Int))
(declare-fun i1 () Int)
(declare-fun i2 () Int)
(assert (<= 0 i2))
(assert (> (select (g (+ i2 1)) i1) (select a1 i1)))
(assert (not (= (f (g 2)) i1)))
(check-sat)
(get-model)
";

const M2U_27: &str = "\
(set-logic QF_AUFLIA)
(declare-fun g (Int) (Array Int Int))
(declare-fun f ((Array Int Int)) Int)
(declare-fun a1 () (Array Int Int))
(declare-fun i1 () Int)
(declare-fun i2 () Int)
(assert (and (<= 1 i2) (<= i2 1)))
(assert (> (select (g (+ i2 1)) i1) (select a1 i1)))
(assert (= (g 2) ((as const (Array Int Int)) 1)))
(assert (= (select a1 i1) 3))
(assert (not (= (f (g 2)) i1)))
(check-sat)
(get-model)
";

const POSTURES: [&[&str]; 2] = [&[], &["--z3-mode"]];

fn run_cli(args: &[&str], script: &str) -> String {
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(args)
        .args(["-T:30", "--quiet-soundness-gate"])
        .output_timeout_with_stdin(script.as_bytes(), TIMEOUT)
        .expect("run ay");
    String::from_utf8_lossy(&output.stdout).to_string()
}

/// A parsed s-expression.
#[derive(Debug, Clone, PartialEq)]
enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

fn tokenize(text: &str) -> Vec<String> {
    text.replace('(', " ( ")
        .replace(')', " ) ")
        .split_whitespace()
        .map(str::to_string)
        .collect()
}

fn parse_all(text: &str) -> Vec<Sexp> {
    fn parse(tokens: &[String], at: &mut usize) -> Sexp {
        let token = &tokens[*at];
        *at += 1;
        if token != "(" {
            return Sexp::Atom(token.clone());
        }
        let mut items = Vec::new();
        while tokens[*at] != ")" {
            items.push(parse(tokens, at));
        }
        *at += 1;
        Sexp::List(items)
    }
    let tokens = tokenize(text);
    let mut at = 0;
    let mut out = Vec::new();
    while at < tokens.len() {
        out.push(parse(&tokens, &mut at));
    }
    out
}

/// A value of the fragment: an integer, a Boolean, or an Int->Int array as
/// its default and normalized exception table (an entry equal to the
/// default is dropped, so two arrays are equal iff their values are equal:
/// the index sort is infinite).
#[derive(Debug, Clone, PartialEq, Eq)]
enum Value {
    Int(i64),
    Bool(bool),
    Array(i64, BTreeMap<i64, i64>),
}

/// A printed function: parameter names and body.
struct Definition {
    params: Vec<String>,
    body: Sexp,
}

fn definitions(model: &Sexp) -> BTreeMap<String, Definition> {
    let Sexp::List(items) = model else {
        panic!("model is not a list: {model:?}")
    };
    let mut defs = BTreeMap::new();
    for item in items {
        let Sexp::List(parts) = item else { continue };
        if parts.first() != Some(&Sexp::Atom("define-fun".to_string())) {
            continue;
        }
        let (Sexp::Atom(name), Sexp::List(params)) = (&parts[1], &parts[2]) else {
            panic!("unexpected define-fun shape: {item:?}")
        };
        let params = params
            .iter()
            .map(|p| match p {
                Sexp::List(pair) => match &pair[0] {
                    Sexp::Atom(n) => n.clone(),
                    other => panic!("parameter name {other:?}"),
                },
                other => panic!("parameter {other:?}"),
            })
            .collect();
        defs.insert(
            name.clone(),
            Definition {
                params,
                body: parts[4].clone(),
            },
        );
    }
    defs
}

fn int(v: &Value) -> i64 {
    match v {
        Value::Int(n) => *n,
        other => panic!("expected Int, got {other:?}"),
    }
}

fn boolean(v: &Value) -> bool {
    match v {
        Value::Bool(b) => *b,
        other => panic!("expected Bool, got {other:?}"),
    }
}

fn normalized(default: i64, table: BTreeMap<i64, i64>) -> Value {
    Value::Array(
        default,
        table.into_iter().filter(|(_, v)| *v != default).collect(),
    )
}

fn eval(term: &Sexp, defs: &BTreeMap<String, Definition>, env: &BTreeMap<String, Value>) -> Value {
    match term {
        Sexp::Atom(a) if a == "true" => Value::Bool(true),
        Sexp::Atom(a) if a == "false" => Value::Bool(false),
        Sexp::Atom(a) => {
            if let Ok(n) = a.parse::<i64>() {
                return Value::Int(n);
            }
            if let Some(v) = env.get(a) {
                return v.clone();
            }
            let def = defs
                .get(a)
                .unwrap_or_else(|| panic!("the printed model does not define `{a}`"));
            assert!(def.params.is_empty(), "`{a}` used as a constant");
            eval(&def.body, defs, &BTreeMap::new())
        }
        Sexp::List(items) => {
            // ((as const (Array Int Int)) v)
            if let Sexp::List(head) = &items[0] {
                assert_eq!(head[0], Sexp::Atom("as".to_string()), "head {head:?}");
                assert_eq!(head[1], Sexp::Atom("const".to_string()), "head {head:?}");
                return normalized(int(&eval(&items[1], defs, env)), BTreeMap::new());
            }
            let Sexp::Atom(op) = &items[0] else {
                unreachable!()
            };
            let args: Vec<Value> = items[1..].iter().map(|t| eval(t, defs, env)).collect();
            match op.as_str() {
                "-" if args.len() == 1 => Value::Int(-int(&args[0])),
                "-" => Value::Int(int(&args[0]) - args[1..].iter().map(int).sum::<i64>()),
                "+" => Value::Int(args.iter().map(int).sum()),
                "<" => Value::Bool(int(&args[0]) < int(&args[1])),
                "<=" => Value::Bool(int(&args[0]) <= int(&args[1])),
                ">" => Value::Bool(int(&args[0]) > int(&args[1])),
                ">=" => Value::Bool(int(&args[0]) >= int(&args[1])),
                "=" => Value::Bool(args[0] == args[1]),
                "not" => Value::Bool(!boolean(&args[0])),
                "and" => Value::Bool(args.iter().all(boolean)),
                "or" => Value::Bool(args.iter().any(boolean)),
                "ite" => {
                    if boolean(&args[0]) {
                        args[1].clone()
                    } else {
                        args[2].clone()
                    }
                }
                "select" => {
                    let Value::Array(default, table) = &args[0] else {
                        panic!("select from {:?}", args[0])
                    };
                    Value::Int(*table.get(&int(&args[1])).unwrap_or(default))
                }
                "store" => {
                    let Value::Array(default, mut table) = args[0].clone() else {
                        panic!("store into {:?}", args[0])
                    };
                    table.insert(int(&args[1]), int(&args[2]));
                    normalized(default, table)
                }
                name => {
                    let def = defs
                        .get(name)
                        .unwrap_or_else(|| panic!("the printed model does not define `{name}`"));
                    assert_eq!(def.params.len(), args.len(), "arity of `{name}`");
                    let local: BTreeMap<String, Value> =
                        def.params.iter().cloned().zip(args).collect();
                    eval(&def.body, defs, &local)
                }
            }
        }
    }
}

/// The assertions of `script`.
fn assertions(script: &str) -> Vec<Sexp> {
    parse_all(script)
        .into_iter()
        .filter_map(|cmd| match cmd {
            Sexp::List(items) if items.first() == Some(&Sexp::Atom("assert".to_string())) => {
                Some(items[1].clone())
            }
            _ => None,
        })
        .collect()
}

/// `(verdict, printed model)` of one CLI run.
fn verdict_and_model(stdout: &str) -> (String, Option<Sexp>) {
    let verdict = stdout
        .lines()
        .map(str::trim)
        .find(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .unwrap_or("")
        .to_string();
    // The model is the balanced s-expression that opens right before the
    // first `(define-fun`.
    let model = stdout
        .find("(define-fun")
        .and_then(|at| stdout[..at].rfind('('))
        .map(|start| {
            let mut depth = 0usize;
            let mut end = stdout.len();
            for (offset, c) in stdout[start..].char_indices() {
                match c {
                    '(' => depth += 1,
                    ')' => {
                        depth -= 1;
                        if depth == 0 {
                            end = start + offset + 1;
                            break;
                        }
                    }
                    _ => {}
                }
            }
            parse_all(&stdout[start..end])
                .into_iter()
                .next()
                .expect("model")
        });
    (verdict, model)
}

#[test]
#[timeout(300_000)]
fn m2_printed_model_satisfies_every_assertion() {
    for args in POSTURES {
        let stdout = run_cli(args, M2);
        let (verdict, model) = verdict_and_model(&stdout);
        assert!(
            verdict == "sat" || verdict == "unknown",
            "{args:?}: z3 5.1.0 answers sat: {stdout}"
        );
        if verdict != "sat" {
            continue;
        }
        let model = model.unwrap_or_else(|| panic!("{args:?}: sat without a model: {stdout}"));
        let defs = definitions(&model);
        for assertion in assertions(M2) {
            assert!(
                boolean(&eval(&assertion, &defs, &BTreeMap::new())),
                "{args:?}: the printed model falsifies {assertion:?}:\n{stdout}"
            );
        }
    }
}

#[test]
#[timeout(300_000)]
fn m2u_27_congruent_array_valued_applications_never_sat_on_the_cli() {
    for args in POSTURES {
        let stdout = run_cli(args, M2U_27);
        let (verdict, _) = verdict_and_model(&stdout);
        assert!(
            verdict == "unsat" || verdict == "unknown",
            "{args:?}: m2u_27 is unsat (z3 5.1.0); AY printed:\n{stdout}"
        );
    }
}

#[test]
fn evaluator_refutes_the_model_main_printed_for_m2() {
    // Main f399eca07a's M2 model (the verifier's CLI run): assertion 2 is
    // false under it, so the check above would have failed on main.
    let printed = "(model
      (define-fun g ((x!0 Int)) (Array Int Int) ((as const (Array Int Int)) 0))
      (define-fun f ((x!0 (Array Int Int))) Int 0)
      (define-fun a1 () (Array Int Int) (store ((as const (Array Int Int)) 0) 1 0))
      (define-fun i1 () Int 1)
      (define-fun i2 () Int 1))";
    let model = parse_all(printed).into_iter().next().expect("model");
    let defs = definitions(&model);
    let results: Vec<bool> = assertions(M2)
        .iter()
        .map(|a| boolean(&eval(a, &defs, &BTreeMap::new())))
        .collect();
    assert_eq!(results, vec![true, false, true]);
}
