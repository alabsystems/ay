// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_flatzinc_parser::ast::{Annotation, Expr};

#[test]
fn test_parse_int_search() {
    let ann = Annotation::Call(
        "int_search".into(),
        vec![
            Expr::ArrayLit(vec![Expr::Ident("x".into()), Expr::Ident("y".into())]),
            Expr::Ident("first_fail".into()),
            Expr::Ident("indomain_min".into()),
            Expr::Ident("complete".into()),
        ],
    );
    let result = parse_one(&ann).unwrap();
    match result {
        SearchAnnotation::IntSearch {
            vars,
            var_choice,
            val_choice,
            strategy,
        } => {
            assert_eq!(vars, vec!["x", "y"]);
            assert_eq!(var_choice, VarChoice::FirstFail);
            assert_eq!(val_choice, ValChoice::IndomainMin);
            assert_eq!(strategy, SearchStrategy::Complete);
        }
        _ => panic!("expected IntSearch"),
    }
}

#[test]
fn test_parse_bool_search() {
    let ann = Annotation::Call(
        "bool_search".into(),
        vec![
            Expr::ArrayLit(vec![Expr::Ident("b".into())]),
            Expr::Ident("input_order".into()),
            Expr::Ident("indomain_max".into()),
            Expr::Ident("complete".into()),
        ],
    );
    let result = parse_one(&ann).unwrap();
    match result {
        SearchAnnotation::BoolSearch {
            vars,
            var_choice,
            val_choice,
            ..
        } => {
            assert_eq!(vars, vec!["b"]);
            assert_eq!(var_choice, VarChoice::InputOrder);
            assert_eq!(val_choice, ValChoice::IndomainMax);
        }
        _ => panic!("expected BoolSearch"),
    }
}

#[test]
fn test_parse_seq_search() {
    let ann = Annotation::Call(
        "seq_search".into(),
        vec![Expr::ArrayLit(vec![
            Expr::Annotation(Box::new(Annotation::Call(
                "int_search".into(),
                vec![
                    Expr::ArrayLit(vec![Expr::Ident("x".into())]),
                    Expr::Ident("first_fail".into()),
                    Expr::Ident("indomain_min".into()),
                    Expr::Ident("complete".into()),
                ],
            ))),
            Expr::Annotation(Box::new(Annotation::Call(
                "bool_search".into(),
                vec![
                    Expr::ArrayLit(vec![Expr::Ident("b".into())]),
                    Expr::Ident("input_order".into()),
                    Expr::Ident("indomain_max".into()),
                    Expr::Ident("complete".into()),
                ],
            ))),
        ])],
    );
    let result = parse_one(&ann).unwrap();
    match result {
        SearchAnnotation::SeqSearch(inner) => {
            assert_eq!(inner.len(), 2);
        }
        _ => panic!("expected SeqSearch"),
    }
}

#[test]
fn test_flatten_search_vars() {
    let anns = vec![
        SearchAnnotation::IntSearch {
            vars: vec!["x".into(), "y".into()],
            var_choice: VarChoice::FirstFail,
            val_choice: ValChoice::IndomainMin,
            strategy: SearchStrategy::Complete,
        },
        SearchAnnotation::BoolSearch {
            vars: vec!["b".into()],
            var_choice: VarChoice::InputOrder,
            val_choice: ValChoice::IndomainMax,
            strategy: SearchStrategy::Complete,
        },
    ];
    let flat = flatten_search_vars(&anns);
    assert_eq!(
        flat,
        vec![("x".into(), false), ("y".into(), false), ("b".into(), true),]
    );
}

#[test]
fn test_parse_unknown_heuristics() {
    let ann = Annotation::Call(
        "int_search".into(),
        vec![
            Expr::ArrayLit(vec![Expr::Ident("x".into())]),
            Expr::Ident("custom_heuristic".into()),
            Expr::Ident("custom_value".into()),
            Expr::Ident("custom_strategy".into()),
        ],
    );
    let result = parse_one(&ann).unwrap();
    match result {
        SearchAnnotation::IntSearch {
            var_choice,
            val_choice,
            strategy,
            ..
        } => {
            assert_eq!(var_choice, VarChoice::Unknown);
            assert_eq!(val_choice, ValChoice::Unknown);
            assert_eq!(strategy, SearchStrategy::Unknown);
        }
        _ => panic!("expected IntSearch"),
    }
}

#[test]
fn test_non_search_annotation_ignored() {
    let anns = vec![
        Annotation::Atom("output_var".into()),
        Annotation::Call("domain".into(), vec![]),
    ];
    let result = parse_search_annotations(&anns);
    assert!(result.is_empty());
}
