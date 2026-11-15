// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Tiny independent BV2/Bool interpreter for original and canonical text.
//! It does not reuse decoder typing, numeric conversion or operator helpers.

use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Value {
    Bool(bool),
    Bv(u8),
}

fn eval(expr: &SExpr, env: &mut Vec<(String, Value)>) -> Value {
    match expr {
        SExpr::True => Value::Bool(true),
        SExpr::False => Value::Bool(false),
        SExpr::Binary(text) => {
            Value::Bv(u8::from_str_radix(text.strip_prefix("#b").unwrap_or(text), 2).unwrap())
        }
        SExpr::Symbol(name) => env.iter().rev().find(|(key, _)| key == name).unwrap().1,
        SExpr::List(items) => match items.as_slice() {
            [head, value, width] if head.is_symbol("_") => {
                assert_eq!(width.as_numeral(), Some("2"));
                Value::Bv(
                    value
                        .as_symbol()
                        .unwrap()
                        .strip_prefix("bv")
                        .unwrap()
                        .parse()
                        .unwrap(),
                )
            }
            [head, test, left, right] if head.is_symbol("ite") => {
                let Value::Bool(test) = eval(test, env) else {
                    panic!("test")
                };
                eval(if test { left } else { right }, env)
            }
            [head, left, right] if head.is_symbol("=") => {
                Value::Bool(eval(left, env) == eval(right, env))
            }
            [head, left, right] if head.is_symbol("and") => {
                let Value::Bool(left) = eval(left, env) else {
                    panic!("and")
                };
                let Value::Bool(right) = eval(right, env) else {
                    panic!("and")
                };
                Value::Bool(left && right)
            }
            [head, value] if head.is_symbol("not") => {
                let Value::Bool(value) = eval(value, env) else {
                    panic!("not")
                };
                Value::Bool(!value)
            }
            [head, bindings, body] if head.is_symbol("let") => {
                let old = env.len();
                let mut values = Vec::new();
                for binding in bindings.as_list().unwrap() {
                    let [name, value] = binding.as_list().unwrap() else {
                        panic!("binding")
                    };
                    values.push((name.as_symbol().unwrap().to_owned(), eval(value, env)));
                }
                env.extend(values);
                let result = eval(body, env);
                env.truncate(old);
                result
            }
            _ => panic!("independent fragment {expr:?}"),
        },
        _ => panic!("independent fragment {expr:?}"),
    }
}

fn evaluate(definition: &str, values: &[Value]) -> Value {
    let sexp = ay_frontend::sexp::parse_sexp(definition).unwrap();
    let [head, _, params, _, body] = sexp.as_list().unwrap() else {
        panic!("definition")
    };
    assert!(head.is_symbol("define-fun"));
    let params = params.as_list().unwrap();
    assert_eq!(params.len(), values.len());
    let mut env = params
        .iter()
        .zip(values)
        .map(|(param, value)| {
            let [name, _] = param.as_list().unwrap() else {
                panic!("parameter")
            };
            (name.as_symbol().unwrap().to_owned(), *value)
        })
        .collect();
    eval(body, &mut env)
}

#[test]
fn parallel_lets_and_shadowed_parameters_preserve_all_bv2_bool_assignments() {
    let body = "(let ((saved x) (x y)) (let ((y x) (same (= x saved))) (ite (and flag (not same)) saved y)))";
    let params = "(x (_ BitVec 2)) (y (_ BitVec 2)) (flag Bool)";
    let original = format!("(define-fun f ({params}) (_ BitVec 2) {body})");
    let model = one(body, params, &[bv(2), bv(2), Sort::Bool], 2).unwrap();
    for x in 0..4 {
        for y in 0..4 {
            for flag in [false, true] {
                let values = [Value::Bv(x), Value::Bv(y), Value::Bool(flag)];
                let expected = Value::Bv(if flag && y != x { x } else { y });
                assert_eq!(evaluate(&original, &values), expected);
                assert_eq!(evaluate(model.definition_smtlib(), &values), expected);
            }
        }
    }
}

#[test]
fn total_ite_order_and_projection_keep_unlisted_argument_points() {
    let body = "(ite (= x (_ bv1 2)) (_ bv2 2) (ite (= x (_ bv1 2)) (_ bv3 2) y))";
    let params = "(x (_ BitVec 2)) (y (_ BitVec 2))";
    let original = format!("(define-fun f ({params}) (_ BitVec 2) {body})");
    let model = one(body, params, &[bv(2), bv(2)], 2).unwrap();
    let projection = one("y", params, &[bv(2), bv(2)], 2).unwrap();
    for x in 0..4 {
        for y in 0..4 {
            let values = [Value::Bv(x), Value::Bv(y)];
            let expected = Value::Bv(if x == 1 { 2 } else { y });
            assert_eq!(evaluate(&original, &values), expected);
            assert_eq!(evaluate(model.definition_smtlib(), &values), expected);
            assert_eq!(
                evaluate(projection.definition_smtlib(), &values),
                Value::Bv(y)
            );
        }
    }
}
