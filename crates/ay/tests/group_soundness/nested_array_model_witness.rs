// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A published `sat` over nested arrays prints a model that satisfies the
//! assertions.
//!
//! `r3_rank4_qf_ax__nested_arrays__array_index__array_index_elem___false_UNSAT`
//! is satisfiable. Measured on the round-4 head and again on its merge with
//! origin/main: `(get-model)` printed `n1` and `n2` as the same bare
//! `((as const (Array Index (Array Index Elem))) ((as const (Array Index Elem))
//! (as @Elem!0 Elem)))`, which falsifies assertion 2 `(not (= n2 n1))` and
//! assertion 3, while AY's own `(get-value ((select n1 i1)))` returned a
//! `store`. The model gate had confirmed the INTERNAL interpretation; the
//! printed witness dropped every cell whose value is itself an array, because
//! that value's text carries `@` atoms.
//!
//! The check below does not trust the printer's own evaluator: it parses the
//! printed `(define-fun ...)` values and evaluates every assertion of the
//! problem under them with a self-contained evaluator for exactly this
//! fragment (uninterpreted-sort atoms, `const`/`store`/`select` arrays,
//! `=`/`not`/`and`), in which two arrays are equal exactly when their
//! normalized `store` tables are (the index sort is uninterpreted and every
//! differing default is witnessed by an index outside both tables). An
//! earlier version handed the substituted model back to AY, which answered
//! `unknown` on the re-check itself: a checker that can abstain is no check.

use ntest::timeout;
use std::collections::BTreeMap;
use std::path::PathBuf;
use std::process::Command;
use std::time::Duration;

use crate::spawn::OutputTimeout;

const TIMEOUT: Duration = Duration::from_mins(2);

const PROBLEM: &str = "benchmarks/smt/regression/soundness_fuzz_round3/r3_rank4_qf_ax__nested_arrays__array_index__array_index_elem___false_UNSAT.smt2";

fn run_stdin(args: &[&str], script: &str) -> (String, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(args)
        .output_timeout_with_stdin(script.as_bytes(), TIMEOUT)
        .expect("run ay");
    (
        String::from_utf8_lossy(&output.stdout).to_string(),
        String::from_utf8_lossy(&output.stderr).to_string(),
    )
}

/// `(define-fun NAME () SORT VALUE)` blocks of a printed model, by name.
fn model_definitions(model: &str) -> BTreeMap<String, String> {
    let mut definitions = BTreeMap::new();
    let mut rest = model;
    while let Some(start) = rest.find("(define-fun ") {
        let text = &rest[start..];
        let mut depth = 0usize;
        let mut end = text.len();
        for (offset, c) in text.char_indices() {
            match c {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        end = offset + 1;
                        break;
                    }
                }
                _ => {}
            }
        }
        let block = &text[..end];
        let name = block["(define-fun ".len()..]
            .split_whitespace()
            .next()
            .expect("define-fun name")
            .to_string();
        definitions.insert(name, block.to_string());
        rest = &text[end..];
    }
    definitions
}

/// A parsed s-expression.
#[derive(Debug, Clone)]
enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

fn parse_sexp(text: &str) -> Sexp {
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
    let tokens: Vec<String> = text
        .replace('(', " ( ")
        .replace(')', " ) ")
        .split_whitespace()
        .map(str::to_string)
        .collect();
    parse(&tokens, &mut 0)
}

/// A model value of the fragment.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Value {
    Bool(bool),
    /// An uninterpreted-sort element, by its model name.
    Element(String),
    /// An array: its default and its normalized exception table.
    Array(Box<Value>, BTreeMap<Value, Value>),
}

fn store(array: Value, index: Value, element: Value) -> Value {
    let Value::Array(default, mut table) = array else {
        panic!("store into a non-array")
    };
    if element == *default {
        table.remove(&index);
    } else {
        table.insert(index, element);
    }
    Value::Array(default, table)
}

fn eval(term: &Sexp, model: &BTreeMap<String, Sexp>) -> Value {
    match term {
        Sexp::Atom(name) if name == "true" => Value::Bool(true),
        Sexp::Atom(name) if name == "false" => Value::Bool(false),
        Sexp::Atom(name) => eval(
            model
                .get(name)
                .unwrap_or_else(|| panic!("the model does not define {name}")),
            model,
        ),
        Sexp::List(items) => match items.as_slice() {
            // `(as @S!k S)`: an element of an uninterpreted sort.
            [Sexp::Atom(head), Sexp::Atom(atom), _] if head == "as" => Value::Element(atom.clone()),
            // `((as const (Array I E)) v)`
            [Sexp::List(head), value]
                if matches!(head.first(), Some(Sexp::Atom(a)) if a == "as")
                    && matches!(head.get(1), Some(Sexp::Atom(c)) if c == "const") =>
            {
                Value::Array(Box::new(eval(value, model)), BTreeMap::new())
            }
            [Sexp::Atom(op), args @ ..] => {
                let values: Vec<Value> = args.iter().map(|a| eval(a, model)).collect();
                match (op.as_str(), values.as_slice()) {
                    ("not", [Value::Bool(b)]) => Value::Bool(!b),
                    ("and", _) => Value::Bool(values.iter().all(|v| *v == Value::Bool(true))),
                    ("=", [a, b]) => Value::Bool(a == b),
                    ("distinct", _) => Value::Bool(
                        (0..values.len())
                            .all(|i| (i + 1..values.len()).all(|j| values[i] != values[j])),
                    ),
                    ("store", [a, i, e]) => store(a.clone(), i.clone(), e.clone()),
                    ("select", [Value::Array(default, table), i]) => {
                        table.get(i).cloned().unwrap_or_else(|| (**default).clone())
                    }
                    _ => panic!("unsupported term {term:?}"),
                }
            }
            _ => panic!("unsupported term {term:?}"),
        },
    }
}

#[test]
#[timeout(300_000)]
fn a_nested_array_sat_prints_a_model_that_satisfies_every_assertion() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(PROBLEM);
    let problem =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let (stdout, stderr) = run_stdin(&["--stdin"], &format!("{problem}\n(get-model)\n"));
    assert!(
        stdout.lines().next() == Some("sat"),
        "the problem is satisfiable and AY decides it: {stdout}\n{stderr}"
    );
    let definitions = model_definitions(&stdout);
    for name in ["c", "n1", "n2", "i0", "i1", "i2", "e2"] {
        assert!(
            definitions.contains_key(name),
            "the model must define {name}: {stdout}"
        );
    }
    let value = |name: &str| {
        let block = &definitions[name];
        let sort_end = block.find(')').expect("empty parameter list") + 1;
        block[sort_end..].to_string()
    };
    assert_ne!(
        value("n1"),
        value("n2"),
        "assertion 2 is (not (= n2 n1)); the printed model must tell them apart: {stdout}"
    );

    // Evaluate every assertion under the printed model.
    let model: BTreeMap<String, Sexp> = definitions
        .iter()
        .map(|(name, block)| {
            let Sexp::List(items) = parse_sexp(block) else {
                panic!("define-fun is a list: {block}")
            };
            (name.clone(), items[4].clone())
        })
        .collect();
    let mut checked = 0;
    for line in problem.lines().map(str::trim) {
        if let Some(assertion) = line
            .strip_prefix("(assert ")
            .and_then(|a| a.strip_suffix(')'))
        {
            assert_eq!(
                eval(&parse_sexp(assertion), &model),
                Value::Bool(true),
                "the printed model falsifies {assertion}:\n{stdout}"
            );
            checked += 1;
        }
    }
    assert_eq!(checked, 3, "all three assertions were evaluated");
}
