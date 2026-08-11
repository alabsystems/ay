// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ast::*;

#[test]
fn test_parse_par_bool() {
    let input = "bool: b = true;\nsolve satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse");
    assert_eq!(model.parameters.len(), 1);
    assert_eq!(model.parameters[0].id, "b");
    assert_eq!(model.parameters[0].ty, FznType::Bool);
    assert_eq!(model.parameters[0].value, Expr::Bool(true));
}

#[test]
fn test_parse_par_int() {
    let input = "int: n = 42;\nsolve satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse");
    assert_eq!(model.parameters[0].id, "n");
    assert_eq!(model.parameters[0].ty, FznType::Int);
    assert_eq!(model.parameters[0].value, Expr::Int(42));
}

#[test]
fn test_parse_par_int_range() {
    let input = "1..10: x = 5;\nsolve satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse");
    assert_eq!(model.parameters[0].ty, FznType::IntRange(1, 10));
}

#[test]
fn test_parse_par_array() {
    let input = "array [1..3] of int: a = [1, 2, 3];\nsolve satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse");
    assert_eq!(model.parameters[0].id, "a");
    match &model.parameters[0].value {
        Expr::ArrayLit(v) => assert_eq!(v.len(), 3),
        other => panic!("expected array literal, got {other:?}"),
    }
}

#[test]
fn test_parse_par_set_literal() {
    let input = "set of int: s = {1, 3, 5};\nsolve satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse");
    assert_eq!(model.parameters[0].ty, FznType::SetOfInt);
    match &model.parameters[0].value {
        Expr::SetLit(v) => assert_eq!(v.len(), 3),
        other => panic!("expected set literal, got {other:?}"),
    }
}

#[test]
fn test_parse_var_bool() {
    let input = "var bool: x;\nsolve satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse");
    assert_eq!(model.variables.len(), 1);
    assert_eq!(model.variables[0].id, "x");
    assert_eq!(model.variables[0].ty, FznType::Bool);
    assert!(model.variables[0].value.is_none());
}

#[test]
fn test_parse_var_int_range() {
    let input = "var 1..10: x;\nsolve satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse");
    assert_eq!(model.variables[0].ty, FznType::IntRange(1, 10));
}

#[test]
fn test_parse_var_with_assignment() {
    let input = "var bool: x = true;\nsolve satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse");
    assert_eq!(model.variables[0].value, Some(Expr::Bool(true)));
}

#[test]
fn test_parse_var_set_of_int_range() {
    let input = "var set of 1..5: s;\nsolve satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse");
    assert_eq!(model.variables[0].ty, FznType::SetOfIntRange(1, 5));
}

#[test]
fn test_parse_var_array() {
    let input = "array [1..3] of var 1..10: xs = [x1, x2, x3];\nsolve satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse");
    assert_eq!(model.variables[0].id, "xs");
}

#[test]
fn test_parse_constraint_basic() {
    let input = "var bool: x;\nconstraint int_eq(x, 5);\nsolve satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse");
    assert_eq!(model.constraints.len(), 1);
    assert_eq!(model.constraints[0].id, "int_eq");
    assert_eq!(model.constraints[0].args.len(), 2);
}

#[test]
fn test_parse_constraint_with_annotation() {
    let input = "var bool: x;\nconstraint bool_eq(x, true) :: domain;\nsolve satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse");
    assert_eq!(model.constraints[0].annotations.len(), 1);
    match &model.constraints[0].annotations[0] {
        Annotation::Atom(s) => assert_eq!(s, "domain"),
        other => panic!("expected atom annotation, got {other:?}"),
    }
}

#[test]
fn test_parse_constraint_array_arg() {
    let input = "var 1..3: x;\nconstraint int_lin_eq([1, 2], [x, x], 5);\nsolve satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse");
    assert_eq!(model.constraints[0].args.len(), 3);
}

#[test]
fn test_parse_solve_satisfy() {
    let input = "solve satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse");
    assert_eq!(model.solve.kind, SolveKind::Satisfy);
    assert!(model.solve.annotations.is_empty());
}

#[test]
fn test_parse_solve_minimize() {
    let input = "var int: obj;\nsolve minimize obj;\n";
    let model = parse_flatzinc(input).expect("should parse");
    match &model.solve.kind {
        SolveKind::Minimize(Expr::Ident(s)) => assert_eq!(s, "obj"),
        other => panic!("expected minimize, got {other:?}"),
    }
}

#[test]
fn test_parse_solve_maximize() {
    let input = "var int: obj;\nsolve maximize obj;\n";
    let model = parse_flatzinc(input).expect("should parse");
    match &model.solve.kind {
        SolveKind::Maximize(Expr::Ident(s)) => assert_eq!(s, "obj"),
        other => panic!("expected maximize, got {other:?}"),
    }
}

#[test]
fn test_parse_solve_with_search_annotation() {
    let input =
        "var 1..3: x;\nsolve :: int_search([x], first_fail, indomain_min, complete) satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse");
    assert_eq!(model.solve.annotations.len(), 1);
    match &model.solve.annotations[0] {
        Annotation::Call(name, args) => {
            assert_eq!(name, "int_search");
            assert_eq!(args.len(), 4);
        }
        other => panic!("expected call annotation, got {other:?}"),
    }
}

#[test]
fn test_parse_predicate_decl() {
    let input = "predicate my_pred(var int: x, int: y);\nsolve satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse");
    assert_eq!(model.predicates.len(), 1);
    assert_eq!(model.predicates[0].id, "my_pred");
    assert_eq!(model.predicates[0].params.len(), 2);
}

#[test]
fn test_parse_comments_ignored() {
    let input = "% This is a comment\nbool: b = true;\n% Another\nsolve satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse");
    assert_eq!(model.parameters.len(), 1);
}

#[test]
fn test_parse_negative_int() {
    let input = "int: n = -42;\nsolve satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse");
    assert_eq!(model.parameters[0].value, Expr::Int(-42));
}

#[test]
fn test_parse_empty_set() {
    let input = "set of int: s = {};\nsolve satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse");
    assert_eq!(model.parameters[0].value, Expr::EmptySet);
}

#[test]
fn test_parse_float_literal() {
    let input = "float: f = 1.5;\nsolve satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse");
    match model.parameters[0].value {
        Expr::Float(v) => assert!((v - 1.5).abs() < 1e-10),
        ref other => panic!("expected float, got {other:?}"),
    }
}

#[test]
fn parses_exponent_only_float_literals() {
    let input = "float: large = 3e8;\nfloat: small = -2E-3;\nsolve satisfy;\n";
    let model = parse_flatzinc(input).expect("exponent-only floats are valid FlatZinc");

    assert!(matches!(model.parameters[0].value, Expr::Float(v) if v == 300_000_000.0));
    assert!(matches!(model.parameters[1].value, Expr::Float(v) if (v + 0.002).abs() < 1e-12));
}

#[test]
fn rejects_float_literals_that_overflow_to_infinity() {
    for literal in ["1e9999", "-1E9999", "1.0e9999"] {
        let input = format!("float: overflow = {literal};\nsolve satisfy;\n");
        let error = parse_flatzinc(&input)
            .expect_err("finite-looking float overflow must not enter the model as infinity");
        assert!(
            matches!(error, ParseError::InvalidFloat { .. }),
            "unexpected error for {literal}: {error}"
        );
    }
}

#[test]
fn parses_prefixed_integer_literals() {
    let input =
        "int: hex = 0x7f;\nint: oct = 0o17;\nint: min = -0x8000000000000000;\nsolve satisfy;\n";
    let model = parse_flatzinc(input).expect("prefixed integers are valid FlatZinc");

    assert_eq!(model.parameters[0].value, Expr::Int(127));
    assert_eq!(model.parameters[1].value, Expr::Int(15));
    assert_eq!(model.parameters[2].value, Expr::Int(i64::MIN));
}

#[test]
fn rejects_out_of_range_prefixed_integer() {
    let error = parse_flatzinc("int: overflow = 0x8000000000000000;\nsolve satisfy;\n")
        .expect_err("positive value above i64::MAX must be rejected");

    assert!(matches!(error, ParseError::InvalidInt { .. }));
}

#[test]
fn test_parse_string_literal() {
    let input = r#"int: n = 1;
solve satisfy;
"#;
    let model = parse_flatzinc(input).expect("should parse");
    assert_eq!(model.parameters.len(), 1);
}

#[test]
fn string_literals_preserve_unicode() {
    let input = "constraint label(\"Grüße 世界\");\nsolve satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse Unicode string");
    assert_eq!(
        model.constraints[0].args[0],
        Expr::Str("Grüße 世界".to_string())
    );
}

#[test]
fn unknown_unicode_escape_is_preserved_without_mojibake() {
    let input = "constraint label(\"\\\\é\");\nsolve satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse escaped Unicode string");
    assert_eq!(model.constraints[0].args[0], Expr::Str("\\é".to_string()));
}

#[test]
fn unicode_string_does_not_shift_following_error_column() {
    let mut lexer = lexer::Lexer::new("\"é\" @");
    let string = lexer.next_token().expect("string token");
    assert!(matches!(string.token, lexer::Token::StringLit(_)));

    let error = lexer.next_token().expect_err("@ is not a FlatZinc token");
    assert!(matches!(
        error,
        ParseError::UnexpectedToken {
            line: 1,
            col: 5,
            ..
        }
    ));
}

#[test]
fn rejects_raw_newline_in_string_literal() {
    let error = parse_flatzinc("constraint label(\"first\nsecond\");\nsolve satisfy;\n")
        .expect_err("FlatZinc strings cannot contain raw newlines");

    assert!(matches!(error, ParseError::UnexpectedToken { line: 1, .. }));
}

#[test]
fn malformed_predicate_parameter_is_not_silently_skipped() {
    let error = parse_flatzinc("predicate p(int x);\nsolve satisfy;\n")
        .expect_err("missing ':' must be rejected at the parameter");
    assert!(matches!(error, ParseError::UnexpectedToken { .. }));
    assert!(error.to_string().contains("Colon"), "{error}");
}

#[test]
fn test_parse_var_int_set_type() {
    let input = "var {1, 3, 5}: x;\nsolve satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse");
    assert_eq!(model.variables[0].ty, FznType::IntSet(vec![1, 3, 5]));
}

#[test]
fn test_parse_output_annotation() {
    let input = "var 1..5: x :: output_var;\nsolve satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse");
    assert_eq!(model.variables[0].annotations.len(), 1);
    match &model.variables[0].annotations[0] {
        Annotation::Atom(s) => assert_eq!(s, "output_var"),
        other => panic!("expected output_var annotation, got {other:?}"),
    }
}

#[test]
fn test_parse_multiple_annotations() {
    let input = "var 1..5: x :: output_var :: is_defined_var;\nsolve satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse");
    assert_eq!(model.variables[0].annotations.len(), 2);
}

#[test]
fn test_parse_complete_small_model() {
    let input = "\
        % Small N-Queens FlatZinc\n\
        int: n = 4;\n\
        array [1..4] of var 1..4: q;\n\
        constraint int_ne(q[1], q[2]);\n\
        constraint int_ne(q[1], q[3]);\n\
        constraint int_ne(q[2], q[3]);\n\
        solve :: int_search(q, first_fail, indomain_min, complete) satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse");
    assert_eq!(model.parameters.len(), 1);
    assert_eq!(model.variables.len(), 1);
    assert_eq!(model.constraints.len(), 3);
    assert_eq!(model.solve.kind, SolveKind::Satisfy);
    assert_eq!(model.solve.annotations.len(), 1);
}

#[test]
fn test_parse_array_access_in_constraint() {
    let input = "array [1..3] of var 1..3: x;\n\
                  constraint int_ne(x[1], x[2]);\n\
                  solve satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse");
    match &model.constraints[0].args[0] {
        Expr::ArrayAccess(name, idx) => {
            assert_eq!(name, "x");
            assert_eq!(**idx, Expr::Int(1));
        }
        other => panic!("expected array access, got {other:?}"),
    }
}

#[test]
fn test_missing_solve_item_error() {
    let input = "int: n = 1;\n";
    let err = parse_flatzinc(input).unwrap_err();
    assert!(matches!(err, ParseError::MissingSolveItem));
}

#[test]
fn test_duplicate_solve_error() {
    let input = "solve satisfy;\nsolve satisfy;\n";
    let err = parse_flatzinc(input).unwrap_err();
    assert!(matches!(err, ParseError::DuplicateSolveItem { .. }));
}

#[test]
fn test_lexer_tokens() {
    let input = "var 1..10: x;";
    let mut lexer = lexer::Lexer::new(input);
    let tokens = lexer.tokenize_all().expect("should tokenize");
    let kinds: Vec<_> = tokens.iter().map(|t| &t.token).collect();
    assert!(matches!(kinds[0], lexer::Token::Var));
    assert!(matches!(kinds[1], lexer::Token::IntLit(1)));
    assert!(matches!(kinds[2], lexer::Token::DotDot));
    assert!(matches!(kinds[3], lexer::Token::IntLit(10)));
    assert!(matches!(kinds[4], lexer::Token::Colon));
    assert!(matches!(kinds[5], lexer::Token::Ident(_)));
    assert!(matches!(kinds[6], lexer::Token::Semicolon));
}

#[test]
fn test_parse_bool_search_annotation() {
    let input = "var bool: b;\n\
                  solve :: bool_search([b], input_order, indomain_max, complete) satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse");
    match &model.solve.annotations[0] {
        Annotation::Call(name, args) => {
            assert_eq!(name, "bool_search");
            assert_eq!(args.len(), 4);
        }
        other => panic!("expected bool_search, got {other:?}"),
    }
}

#[test]
fn test_parse_reified_constraint() {
    let input = "var bool: b;\nvar 1..5: x;\nvar 1..5: y;\n\
                  constraint int_eq_reif(x, y, b);\nsolve satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse");
    assert_eq!(model.constraints[0].id, "int_eq_reif");
    assert_eq!(model.constraints[0].args.len(), 3);
}

#[test]
fn test_parse_par_with_annotation() {
    let input = "int: n :: output_var = 10;\nsolve satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse");
    assert_eq!(model.parameters[0].annotations.len(), 1);
}

#[test]
fn test_parse_seq_search_annotation() {
    // seq_search([int_search(xs, ...), int_search(ys, ...)]) requires
    // parse_ann_expr to handle array literals containing annotation calls.
    let input = "var 1..3: x;\nvar 1..3: y;\n\
                  solve :: seq_search([int_search([x], first_fail, indomain_min, complete), \
                  int_search([y], first_fail, indomain_min, complete)]) satisfy;\n";
    let model = parse_flatzinc(input).expect("should parse seq_search");
    assert_eq!(model.solve.annotations.len(), 1);
    match &model.solve.annotations[0] {
        Annotation::Call(name, args) => {
            assert_eq!(name, "seq_search");
            assert_eq!(args.len(), 1); // one array argument
            match &args[0] {
                Expr::ArrayLit(elems) => {
                    assert_eq!(elems.len(), 2); // two int_search calls
                    for elem in elems {
                        match elem {
                            Expr::Annotation(ann) => match ann.as_ref() {
                                Annotation::Call(n, a) => {
                                    assert_eq!(n, "int_search");
                                    assert_eq!(a.len(), 4);
                                }
                                other => panic!("expected int_search call, got {other:?}"),
                            },
                            other => panic!("expected annotation, got {other:?}"),
                        }
                    }
                }
                other => panic!("expected array literal, got {other:?}"),
            }
        }
        other => panic!("expected seq_search call, got {other:?}"),
    }
}
