// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model extraction tests - get-model, get-value, validate-model

use crate::Executor;
use ay_frontend::parse;
use ay_frontend::sexp::{parse_sexp, SExpr};

#[test]
fn test_get_model_bool() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert a)
        (assert (not b))
        (check-sat)
        (get-model)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    // Model should contain definitions for a and b
    let model = &outputs[1];
    assert!(model.starts_with("(model"));
    assert!(model.contains("define-fun a () Bool"));
    assert!(model.contains("define-fun b () Bool"));
}

#[test]
fn test_get_model_before_check_sat() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (get-model)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert!(outputs[0].contains("error"));
}

#[test]
fn test_get_model_after_unsat() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        (assert (not a))
        (check-sat)
        (get-model)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    assert!(outputs[1].contains("error"));
}

#[test]
fn test_get_model_empty_assertions() {
    let input = r#"
        (set-logic QF_UF)
        (check-sat)
        (get-model)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    // Empty model is valid for no assertions
    assert!(outputs[1].contains("model"));
}

#[test]
fn test_get_model_requires_produce_models() {
    let input = r#"
        (set-option :produce-models false)
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        (check-sat)
        (get-model)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    assert!(outputs[1].contains("error"), "Output: {}", outputs[1]);
    assert!(
        outputs[1].contains("model generation is not enabled"),
        "Output: {}",
        outputs[1]
    );
}

#[test]
fn test_get_model_with_uninterpreted_sort() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const x U)
        (check-sat)
        (get-model)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    // For a trivially SAT case with no Boolean constraints, we may get
    // an empty model or one with placeholder values
    assert!(model.contains("model"), "Model output: {model}");
}

#[test]
fn test_get_value_bool() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert a)
        (assert (not b))
        (check-sat)
        (get-value (a b))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    // Get-value should output pairs like ((a true) (b false))
    let values = &outputs[1];
    assert!(values.starts_with('('), "Values: {values}");
    assert!(values.contains('a'), "Values: {values}");
    assert!(values.contains('b'), "Values: {values}");
}

#[test]
fn test_get_value_before_check_sat() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (get-value (a))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert!(outputs[0].contains("error"), "Output: {}", outputs[0]);
}

#[test]
fn test_get_value_requires_produce_models() {
    let input = r#"
        (set-option :produce-models false)
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        (check-sat)
        (get-value (a))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    assert!(outputs[1].contains("error"), "Output: {}", outputs[1]);
    assert!(
        outputs[1].contains("model generation is not enabled"),
        "Output: {}",
        outputs[1]
    );
}

#[test]
fn test_get_value_after_unsat() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        (assert (not a))
        (check-sat)
        (get-value (a))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    assert!(outputs[1].contains("error"), "Output: {}", outputs[1]);
}

#[test]
fn test_get_value_expression() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert a)
        (assert b)
        (check-sat)
        (get-value ((and a b)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    // Get-value for (and a b) should work
    let values = &outputs[1];
    assert!(values.starts_with('('), "Values: {values}");
    assert!(values.contains("and"), "Values: {values}");
}

#[test]
fn test_get_value_multiple_terms() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const x Bool)
        (declare-const y Bool)
        (declare-const z Bool)
        (assert x)
        (assert (not y))
        (check-sat)
        (get-value (x y z))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    let values = &outputs[1];
    // Should have all three variables
    assert!(values.contains('x'), "Values: {values}");
    assert!(values.contains('y'), "Values: {values}");
    assert!(values.contains('z'), "Values: {values}");
}

#[test]
fn test_get_value_string_literals_escape_and_round_trip() {
    // SMT-LIB 2.6 string escaping: `""` is the only quote escape and a backslash
    // is a LITERAL character (only `\u…` are escapes). So `say ""hi""` is
    // `say "hi"`, `path\\to\\file` keeps BOTH backslashes of each `\\`, and
    // `hello\nworld` is a literal backslash+`n` (not a newline). Decoding `\\`
    // to a single `\` was a wrong-verdict soundness bug (see ay-core 204a245f).
    let input = r#"
        (set-logic ALL)
        (declare-const a Bool)
        (assert a)
        (check-sat)
        (get-value ("say ""hi""" "path\\to\\file" "hello\nworld"))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");

    let sexp = parse_sexp(&outputs[1]).unwrap();
    let SExpr::List(ref pairs) = sexp else {
        panic!("Expected get-value output list, got: {sexp:?}");
    };
    assert_eq!(pairs.len(), 3);

    for pair in pairs {
        let SExpr::List(items) = pair else {
            panic!("Expected get-value pair list, got: {pair:?}");
        };
        assert_eq!(items.len(), 2, "Pair: {items:?}");
        assert!(matches!(&items[0], SExpr::String(_)), "Pair: {items:?}");
        assert!(matches!(&items[1], SExpr::String(_)), "Pair: {items:?}");
    }

    let value0 = match &pairs[0] {
        SExpr::List(items) => match &items[1] {
            SExpr::String(s) => s.as_str(),
            other => panic!("Expected string value, got: {other:?}"),
        },
        other => panic!("Expected pair list, got: {other:?}"),
    };
    assert_eq!(value0, r#"say "hi""#);

    let value1 = match &pairs[1] {
        SExpr::List(items) => match &items[1] {
            SExpr::String(s) => s.as_str(),
            other => panic!("Expected string value, got: {other:?}"),
        },
        other => panic!("Expected pair list, got: {other:?}"),
    };
    assert_eq!(value1, r"path\\to\\file");

    let value2 = match &pairs[2] {
        SExpr::List(items) => match &items[1] {
            SExpr::String(s) => s.as_str(),
            other => panic!("Expected string value, got: {other:?}"),
        },
        other => panic!("Expected pair list, got: {other:?}"),
    };
    assert_eq!(value2, r"hello\nworld");
}

#[test]
fn test_get_model_uninterpreted_constants() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (assert (distinct a b))
        (check-sat)
        (get-model)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    // Model should include definitions for a and b with different values
    assert!(model.contains("define-fun a"), "Model: {model}");
    assert!(model.contains("define-fun b"), "Model: {model}");
    // Values should be element identifiers like @U!0
    assert!(model.contains("@U!"), "Model: {model}");
}

#[test]
fn test_get_model_quotes_uninterpreted_sort_elements_with_colons() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort |foo::bar| 0)
        (declare-const a |foo::bar|)
        (assert (= a a))
        (check-sat)
        (get-model)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    if model.contains("define-fun") {
        assert!(model.contains("|foo::bar|"), "Model: {model}");
        assert!(
            model.contains("|@foo::bar!"),
            "Expected quoted element identifier, Model: {model}"
        );
    }

    // Ensure the output round-trips through our lexer/parser.
    let sexp = parse_sexp(model).unwrap();
    assert!(matches!(sexp, SExpr::List(_)), "Model sexp: {sexp:?}");
}

/// Full SMT-LIB round-trip test for get-model output (#1280).
///
/// Verifies that the define-fun commands inside model output can be
/// re-parsed as valid SMT-LIB, not just as S-expressions.
#[test]
fn test_get_model_define_fun_smt_lib_round_trip() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort |foo::bar| 0)
        (declare-const a |foo::bar|)
        (declare-const b |foo::bar|)
        (assert (= a b))
        (check-sat)
        (get-model)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];

    // Extract define-fun commands from the model output.
    // Model format: "(model\n  (define-fun ...)\n  (define-fun ...)\n)\n"
    // We extract each define-fun as a standalone SMT-LIB command.
    let define_funs: Vec<&str> = model
        .lines()
        .filter(|line| line.trim().starts_with("(define-fun"))
        .collect();

    assert!(
        !define_funs.is_empty(),
        "Model should contain define-fun commands. Model: {model}"
    );

    // Build SMT-LIB input with declarations and define-funs
    let smt_lib_input = format!(
        "(set-logic QF_UF)\n(declare-sort |foo::bar| 0)\n{}",
        define_funs.join("\n")
    );

    let reparsed = parse(&smt_lib_input);
    assert!(
        reparsed.is_ok(),
        "Model define-fun should parse as SMT-LIB. Input:\n{}\nError: {:?}",
        smt_lib_input,
        reparsed.err()
    );

    let reparsed_commands = reparsed.unwrap();
    // Should have at least set-logic + declare-sort + the define-fun commands
    assert!(
        reparsed_commands.len() >= 3,
        "Expected at least 3 commands (set-logic + declare-sort + define-fun), got {}",
        reparsed_commands.len()
    );
}

#[test]
fn test_get_model_uninterpreted_function() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-fun f (U) U)
        (assert (= (f a) b))
        (check-sat)
        (get-model)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    // Model should include a function definition for f
    assert!(model.contains("define-fun f"), "Model: {model}");
    // Function should have a parameter of sort U
    assert!(model.contains("(x0 U)"), "Model: {model}");
}

#[test]
fn test_get_model_equal_constants_same_value() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (assert (= a b))
        (check-sat)
        (get-model)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    // Model should have a and b with the same value since they're equal
    assert!(model.contains("define-fun a"), "Model: {model}");
    assert!(model.contains("define-fun b"), "Model: {model}");
    // Both should have the same element (e.g., @U!0)
    // Extract values to verify they're the same
    let lines: Vec<&str> = model.lines().collect();
    let mut values = Vec::new();
    for line in lines {
        if line.contains("define-fun a") || line.contains("define-fun b") {
            // Extract the value (last token before closing paren)
            if let Some(val) = line.split_whitespace().last() {
                let val = val.trim_end_matches(')');
                values.push(val.to_string());
            }
        }
    }
    assert_eq!(
        values.len(),
        2,
        "Expected 2 values, got {}: {:?}",
        values.len(),
        values
    );
    assert_eq!(
        values[0], values[1],
        "a and b should have same value: {values:?}"
    );
}

#[test]
fn test_get_model_function_congruence() {
    // When a = b, f(a) and f(b) should have the same value
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-fun f (U) U)
        (assert (= a b))
        (check-sat)
        (get-model)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    // Model should be valid
    assert!(model.contains("(model"), "Model: {model}");
}

// ========== Model Validation Tests ==========

#[test]
fn test_validate_model_simple_bool() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert a)
        (assert (not b))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap();

    // Model validation should succeed
    let result = exec.validate_model();
    assert!(result.is_ok(), "Model validation failed: {result:?}");
}

#[test]
fn test_validate_model_with_and() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert (and a b))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap();

    let result = exec.validate_model();
    assert!(result.is_ok(), "Model validation failed: {result:?}");
}

#[test]
fn test_validate_model_with_or() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert (or a b))
        (assert (not a))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap();

    let result = exec.validate_model();
    assert!(result.is_ok(), "Model validation failed: {result:?}");
}

#[test]
fn test_validate_model_accepts_quantified_assertions() {
    // Quantified assertions evaluate to Unknown. With the lenient
    // validation policy, Unknown is accepted (only BV comparison
    // predicates are rejected).
    let input = r#"
        (set-logic QF_LIA)
        (assert (forall ((x Int)) (=> (> x 0) (>= x 1))))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");
    assert_eq!(outputs, vec!["sat"]);

    let result = exec.validate_model();
    assert!(
        result.is_ok(),
        "validate_model should accept quantified assertions as Unknown, got: {result:?}"
    );
}

#[test]
fn test_validate_model_euf_equality() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (assert (= a b))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap();

    let result = exec.validate_model();
    assert!(result.is_ok(), "Model validation failed: {result:?}");
}

#[test]
fn test_validate_model_euf_distinct() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (assert (distinct a b c))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap();

    let result = exec.validate_model();
    assert!(result.is_ok(), "Model validation failed: {result:?}");
}

#[test]
fn test_validate_model_requires_sat() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        (assert (not a))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap();

    // Validation should fail because result is UNSAT
    let result = exec.validate_model();
    assert!(result.is_err(), "Should fail for UNSAT");
}

#[test]
fn test_validate_model_no_check_sat() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap();

    // Validation should fail because no check-sat was run
    let result = exec.validate_model();
    assert!(result.is_err(), "Should fail without check-sat");
}

// ========== Composite Term Evaluation Tests ==========

#[test]
fn test_get_value_composite_and_true() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert a)
        (assert b)
        (check-sat)
        (get-value ((and a b)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    // (and a b) should evaluate to true
    assert!(
        outputs[1].contains("true"),
        "Expected true in output: {}",
        outputs[1]
    );
}

#[test]
fn test_get_value_composite_and_false() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert a)
        (assert (not b))
        (check-sat)
        (get-value ((and a b)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    // (and a b) should evaluate to false since b is false
    assert!(
        outputs[1].contains("false"),
        "Expected false in output: {}",
        outputs[1]
    );
}

#[test]
fn test_get_value_composite_or() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert (not a))
        (assert b)
        (check-sat)
        (get-value ((or a b)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    // (or a b) should evaluate to true since b is true
    assert!(
        outputs[1].contains("true"),
        "Expected true in output: {}",
        outputs[1]
    );
}

#[test]
fn test_get_value_composite_not() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        (check-sat)
        (get-value ((not a)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    // (not a) should evaluate to false since a is true
    assert!(
        outputs[1].contains("false"),
        "Expected false in output: {}",
        outputs[1]
    );
}

#[test]
fn test_get_value_composite_equality() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (assert (= a b))
        (check-sat)
        (get-value ((= a b)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    // (= a b) should evaluate to true
    assert!(
        outputs[1].contains("true"),
        "Expected true in output: {}",
        outputs[1]
    );
}

#[test]
fn test_get_value_nested_composite() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (declare-const c Bool)
        (assert a)
        (assert b)
        (assert (not c))
        (check-sat)
        (get-value ((and (or a b) (not c))))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    // (and (or a b) (not c)) = (and true true) = true
    assert!(
        outputs[1].contains("true"),
        "Expected true in output: {}",
        outputs[1]
    );
}

// ========== Predicate Table Tests ==========

#[test]
fn test_get_model_predicate_function() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-fun p (U) Bool)
        (assert (p a))
        (assert (not (p b)))
        (check-sat)
        (get-model)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    // Model should include a function definition for predicate p
    assert!(
        model.contains("define-fun p"),
        "Model should contain p: {model}"
    );
    // Should have Bool as return type
    assert!(
        model.contains("Bool"),
        "Model should have Bool return type: {model}"
    );
}

#[test]
fn test_validate_model_with_predicate() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-fun p (U) Bool)
        (assert (p a))
        (assert (not (p b)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap();

    // Model validation should succeed
    let result = exec.validate_model();
    assert!(result.is_ok(), "Model validation failed: {result:?}");
}

// ========== If-Then-Else Evaluation Tests ==========

#[test]
fn test_get_value_ite_true_condition() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const c Bool)
        (declare-const x Bool)
        (declare-const y Bool)
        (assert c)
        (assert x)
        (assert (not y))
        (check-sat)
        (get-value ((ite c x y)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    // (ite c x y) with c=true should return x=true
    assert!(
        outputs[1].contains("true"),
        "Expected true (then branch) in output: {}",
        outputs[1]
    );
}

#[test]
fn test_get_value_ite_false_condition() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const c Bool)
        (declare-const x Bool)
        (declare-const y Bool)
        (assert (not c))
        (assert x)
        (assert (not y))
        (check-sat)
        (get-value ((ite c x y)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    // (ite c x y) with c=false should return y=false
    assert!(
        outputs[1].contains("false"),
        "Expected false (else branch) in output: {}",
        outputs[1]
    );
}

#[test]
fn test_get_value_nested_ite() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (declare-const x Bool)
        (declare-const y Bool)
        (declare-const z Bool)
        (assert a)
        (assert (not b))
        (assert x)
        (assert (not y))
        (assert z)
        (check-sat)
        (get-value ((ite a (ite b y x) z)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    // a=true, so we take (ite b y x)
    // b=false, so we take x=true
    assert!(
        outputs[1].contains("true"),
        "Expected true in output: {}",
        outputs[1]
    );
}

#[test]
fn test_validate_model_with_ite() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const c Bool)
        (declare-const x Bool)
        (declare-const y Bool)
        (assert c)
        (assert (ite c x (not x)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap();

    let result = exec.validate_model();
    assert!(result.is_ok(), "Model validation failed: {result:?}");
}

#[test]
fn test_get_value_ite_with_euf_elements() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const c Bool)
        (declare-const x U)
        (declare-const y U)
        (assert c)
        (assert (distinct x y))
        (check-sat)
        (get-value ((ite c x y)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    // (ite c x y) with c=true should return x's element value
    let values = &outputs[1];
    assert!(values.contains("ite"), "Values: {values}");
    assert!(
        values.contains("@U!"),
        "Expected element value in output: {values}"
    );
}

// ========== Implication Evaluation Tests ==========

#[test]
fn test_get_value_implication_true_antecedent() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert a)
        (assert b)
        (check-sat)
        (get-value ((=> a b)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    // (=> a b) with a=true, b=true should be true
    assert!(
        outputs[1].contains("true"),
        "Expected true in output: {}",
        outputs[1]
    );
}

#[test]
fn test_get_value_implication_false_antecedent() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert (not a))
        (assert (not b))
        (check-sat)
        (get-value ((=> a b)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    // (=> a b) with a=false should be true regardless of b
    assert!(
        outputs[1].contains("true"),
        "Expected true (vacuous truth) in output: {}",
        outputs[1]
    );
}

#[test]
fn test_get_value_implication_false_result() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert a)
        (assert (not b))
        (check-sat)
        (get-value ((=> a b)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    // (=> a b) with a=true, b=false should be false
    assert!(
        outputs[1].contains("false"),
        "Expected false in output: {}",
        outputs[1]
    );
}

#[test]
fn test_validate_model_with_implication() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert (=> a b))
        (assert a)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap();

    let result = exec.validate_model();
    assert!(result.is_ok(), "Model validation failed: {result:?}");
}

#[test]
fn test_get_value_nested_implication() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (declare-const c Bool)
        (assert a)
        (assert b)
        (assert c)
        (check-sat)
        (get-value ((=> (=> a b) c)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    // (=> (=> a b) c) = (=> true true) = true
    assert!(
        outputs[1].contains("true"),
        "Expected true in output: {}",
        outputs[1]
    );
}

// ========== XOR Evaluation Tests ==========
// XOR is desugared during elaboration to (or (and a (not b)) (and (not a) b))
// These tests verify the desugaring works correctly with model evaluation

#[test]
fn test_get_value_xor_true() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert a)
        (assert (not b))
        (check-sat)
        (get-value ((xor a b)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    // xor(true, false) = true
    assert!(
        outputs[1].contains("true"),
        "Expected true in output: {}",
        outputs[1]
    );
}

#[test]
fn test_get_value_xor_false_same_values() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert a)
        (assert b)
        (check-sat)
        (get-value ((xor a b)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    // xor(true, true) = false
    assert!(
        outputs[1].contains("false"),
        "Expected false in output: {}",
        outputs[1]
    );
}

#[test]
fn test_validate_model_with_xor() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert (xor a b))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap();

    let result = exec.validate_model();
    assert!(result.is_ok(), "Model validation failed: {result:?}");
}

/// Test that LIA model is properly extracted in check-sat-assuming path (#1160)
///
/// This test verifies the fix for the bug where solve_with_assumptions_for_theory
/// was not extracting the LIA model, causing model validation to fail because
/// integer variables defaulted to 0.
#[test]
fn test_validate_model_lia_check_sat_assuming_issue_1160() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (> x 0))
        (assert (< x 10))
        (check-sat-assuming ())
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // First verify we got SAT
    assert_eq!(outputs.last().unwrap(), "sat", "Expected SAT result");

    // This should pass - the LIA model must have x > 0
    // Before the fix, x would default to 0, making (> x 0) = (< 0 0) = false
    let result = exec.validate_model();
    assert!(
        result.is_ok(),
        "LIA model validation failed in check-sat-assuming path: {result:?}"
    );
}

// ========== Boolean Equality Tests ==========

#[test]
fn test_get_value_bool_equality_true() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert a)
        (assert b)
        (check-sat)
        (get-value ((= a b)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    // (= true true) = true
    assert!(
        outputs[1].contains("true"),
        "Expected true in output: {}",
        outputs[1]
    );
}

#[test]
fn test_get_value_bool_equality_false() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert a)
        (assert (not b))
        (check-sat)
        (get-value ((= a b)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    // (= true false) = false
    assert!(
        outputs[1].contains("false"),
        "Expected false in output: {}",
        outputs[1]
    );
}

#[test]
fn test_get_value_bitvector() {
    // Test that get-value returns actual bitvector values from the model
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x2A))
        (check-sat)
        (get-value (x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    // x should be #x2a (42)
    assert!(
        outputs[1].to_lowercase().contains("#x2a"),
        "Expected #x2a in output: {}",
        outputs[1]
    );
}

#[test]
fn test_get_value_bitvector_computed() {
    // Test get-value with a bitvector variable constrained by arithmetic
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= x #x10))
        (assert (= y (bvadd x #x05)))
        (check-sat)
        (get-value (y))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    // y should be #x15 (16 + 5 = 21)
    assert!(
        outputs[1].to_lowercase().contains("#x15"),
        "Expected #x15 in output: {}",
        outputs[1]
    );
}

#[test]
fn test_get_value_bitvector_concat() {
    // Regression (#1790): get-value should respect concat constraints.
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 16))
        (declare-const a (_ BitVec 8))
        (declare-const b (_ BitVec 8))
        (assert (= x (concat a b)))
        (assert (= a #xAB))
        (assert (= b #xCD))
        (check-sat)
        (get-value (x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    assert!(
        outputs[1].to_lowercase().contains("#xabcd"),
        "Expected #xabcd in output: {}",
        outputs[1]
    );
}

#[test]
fn test_get_value_integer() {
    // Test that get-value returns actual integer values from the model
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= x 42))
        (check-sat)
        (get-value (x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    // x should be 42
    assert!(
        outputs[1].contains("42"),
        "Expected 42 in output: {}",
        outputs[1]
    );
}

#[test]
fn test_get_value_real() {
    // Test that get-value returns actual real values from the model
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (= x 3.5))
        (check-sat)
        (get-value (x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    // z3-exact user-facing Real spelling (#real-fmt).
    assert_eq!(outputs[1], "((x (/ 7.0 2.0)))");
}

// ========== Array + Arithmetic Model Validation Tests ==========

/// Regression test for #3836: evaluate_select() skipped the array model
/// entirely in AUFLIA/AUFLRA (whenever lia_model or lra_model was present).
/// This test asserts select(store(a, 0, 42), 0) = 42 in QF_AUFLIA, which
/// requires evaluate_select to walk the store layer with integer indices.
#[test]
fn test_validate_model_array_with_lia() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const x Int)
        (assert (= x (select (store a 0 42) 0)))
        (assert (= x 42))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");
    assert_eq!(outputs, vec!["sat"]);

    let result = exec.validate_model();
    assert!(
        result.is_ok(),
        "AUFLIA array model validation should succeed: {result:?}"
    );
}

#[test]
fn test_validate_model_degrades_false_auflia_array_assertion_to_unknown() {
    // Regression for #4275 / #4304: contradictory array assertions must NOT
    // be silently skipped. The model evaluator may lack the full array model,
    // so false array results return ModelValidationError::Incomplete (which
    // finalize_sat_model_validation converts to SolveResult::Unknown).
    //
    // The contradictory assertion is added via ctx.process_command (not
    // exec.execute) to preserve the cached SAT model. execute() correctly
    // invalidates stale query state per SMT-LIB (#4516), but validate_model
    // is an internal API that needs the model to evaluate assertions.
    let sat_input = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (assert (= i 7))
        (assert (= (select a i) 42))
        (check-sat)
    "#;
    let contra_input = "(assert (= (select a i) 41))";

    let sat_cmds = parse(sat_input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&sat_cmds)
        .expect("invariant: execute succeeds");
    assert_eq!(outputs, vec!["sat"]);

    // Add contradictory assertion directly to context (bypasses invalidation).
    let contra_cmds = parse(contra_input).expect("invariant: valid assert");
    exec.ctx
        .process_command(&contra_cmds[0])
        .expect("invariant: assert elaborates");

    let err = exec
        .validate_model()
        .expect_err("Contradictory AUFLIA array assertion must be rejected");
    assert!(
        err.is_incomplete(),
        "Expected Incomplete error for degradable array assertion, got: {err}"
    );
    // After #5542 (Bool defaults to Unknown) and #5499 (equality evaluator
    // no longer falls back to SAT model for Int-sort operands), the evaluator
    // may return Unknown instead of false for contradictory array assertions.
    // Both "false" and "Unknown" are acceptable.
    assert!(
        err.contains("array assertion evaluates to"),
        "Expected array-specific diagnostic, got: {err}"
    );
}

#[test]
fn test_validate_model_degrades_false_auflra_array_assertion_to_unknown() {
    // Regression for #4275 / #4304: contradictory array assertions must NOT
    // be silently skipped. False array results degrade to Incomplete
    // (finalize_sat_model_validation -> Unknown).
    //
    // Contradictory assertion added via ctx.process_command to preserve the
    // cached SAT model (execute() invalidates per SMT-LIB, #4516).
    let sat_input = r#"
        (set-logic QF_AUFLRA)
        (declare-const a (Array Int Real))
        (declare-const i Int)
        (declare-const x Real)
        (assert (= (select a i) x))
        (assert (>= x 1.5))
        (assert (<= x 2.5))
        (check-sat)
    "#;
    let contra_input = "(assert (= (select a i) 3.5))";

    let sat_cmds = parse(sat_input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&sat_cmds)
        .expect("invariant: execute succeeds");
    assert_eq!(outputs, vec!["sat"]);

    let contra_cmds = parse(contra_input).expect("invariant: valid assert");
    exec.ctx
        .process_command(&contra_cmds[0])
        .expect("invariant: assert elaborates");

    let err = exec
        .validate_model()
        .expect_err("Contradictory AUFLRA array assertion must be rejected");
    assert!(
        err.is_incomplete(),
        "Expected Incomplete error for degradable array assertion, got: {err}"
    );
    // After #5542 / #5499 — see AUFLIA test comment above.
    assert!(
        err.contains("array assertion evaluates to"),
        "Expected array-specific diagnostic, got: {err}"
    );
}

/// Regression test for #3903 Wave 2: deep store chains must be fully
/// traversed by evaluate_select without a depth-cap truncation.
/// Uses 20 layers (parser recursion limits prevent very deep nesting);
/// the unit test in model.rs covers 150 layers directly via term API.
#[test]
fn test_validate_model_deep_store_chain_no_depth_cap() {
    let mut stores = String::from("a");
    for i in 0..20u32 {
        let val = if i == 0 { 42 } else { 0 };
        stores = format!("(store {stores} {i} {val})");
    }
    let input = format!(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const x Int)
        (assert (= x (select {stores} 0)))
        (assert (= x 42))
        (check-sat)
    "#
    );

    let commands = parse(&input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");
    assert_eq!(outputs, vec!["sat"]);

    let result = exec.validate_model();
    assert!(
        result.is_ok(),
        "Deep store chain (20 layers) model validation must pass: {result:?}"
    );
}

// ========== Array Model Validation Behavioral Tests (#4275) ==========

/// Behavioral test: non-array false assertion produces a `Violated` error
/// (NOT `Incomplete`), so finalize_sat_model_validation will NOT degrade
/// it to Unknown.
#[test]
fn test_validate_model_non_array_false_assertion_is_hard_error() {
    // Solve a simple LIA problem, then add a contradictory assertion.
    // Contradictory assertion added via ctx.process_command to preserve the
    // cached SAT model (execute() invalidates per SMT-LIB, #4516).
    let sat_input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= x 42))
        (check-sat)
    "#;
    let contra_input = "(assert (= x 41))";

    let sat_cmds = parse(sat_input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&sat_cmds)
        .expect("invariant: execute succeeds");
    assert_eq!(outputs, vec!["sat"]);

    let contra_cmds = parse(contra_input).expect("invariant: valid assert");
    exec.ctx
        .process_command(&contra_cmds[0])
        .expect("invariant: assert elaborates");

    let err = exec
        .validate_model()
        .expect_err("Contradictory non-array assertion must be rejected");
    assert!(
        err.is_violated(),
        "Non-array false assertion must be a Violated error, got: {err}"
    );
    assert!(
        err.contains("violated"),
        "Detail must mention 'violated', got: {err}"
    );
}

/// Behavioral regression: QF_AUFLIA store/select SAT formula must return `sat`.
///
/// This was the original #6731 regression host. The test was weakened in
/// `d417ea2fe` to accept `unknown` alongside `sat`. The weakening masks the
/// root cause: inner `finalize_sat_model_validation()` running against
/// temporary preprocessed assertions instead of the original formula.
///
/// Restored to a strict `sat` gate by #6731 Packet 1.
#[test]
fn test_validate_model_array_store_select_sat_passes() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (declare-const i Int)
        (assert (= (store a i 42) b))
        (assert (= (select b i) 42))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");
    let result = outputs.first().expect("expected one check-sat output");
    assert_eq!(
        result, "sat",
        "#6731 regression: QF_AUFLIA store/select must return sat, got {outputs:?}"
    );
    let validation = exec.validate_model();
    assert!(
        validation.is_ok(),
        "Array store/select model validation must pass: {validation:?}"
    );
    assert!(
        exec.get_reason_unknown().is_none(),
        "#6731 regression: strict AUFLIA SAT must not retain reason-unknown: {:?}",
        exec.get_reason_unknown()
    );
}

/// Behavioral test: contradictory array assertion added after SAT causes
/// validate_model to return a typed `Incomplete` error (not `Violated`).
/// finalize_sat_model_validation degrades `Incomplete` to Unknown.
#[test]
fn test_validate_model_array_false_error_message_is_degradable() {
    // This verifies the typed Incomplete contract that
    // finalize_sat_model_validation relies on.
    // Contradictory assertion added via ctx.process_command to preserve the
    // cached SAT model (execute() invalidates per SMT-LIB, #4516).
    let sat_input = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (assert (= i 5))
        (assert (= (select a i) 100))
        (check-sat)
    "#;
    let contra_input = "(assert (= (select a i) 200))";

    let sat_cmds = parse(sat_input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&sat_cmds)
        .expect("invariant: execute succeeds");
    assert_eq!(outputs, vec!["sat"]);

    let contra_cmds = parse(contra_input).expect("invariant: valid assert");
    exec.ctx
        .process_command(&contra_cmds[0])
        .expect("invariant: assert elaborates");

    let err = exec
        .validate_model()
        .expect_err("Contradictory array assertion must be rejected");

    // Verify the error is Incomplete (finalize_sat_model_validation
    // degrades Incomplete to Unknown, not a hard error).
    assert!(
        err.is_incomplete(),
        "Array false assertion must produce Incomplete error, got: {err}"
    );

    // After #5542 / #5499 — evaluator may return Unknown or false
    // for contradictory array assertions.
    assert!(
        err.contains("array assertion evaluates to"),
        "Error must mention array evaluation diagnostic, got: {err}"
    );
}

/// Behavioral test: validate_model distinguishes array vs non-array
/// false assertions in mixed AUFLIA formulas. The array assertion
/// produces a degradable error; non-array assertions would produce
/// a hard error.
#[test]
fn test_validate_model_mixed_auflia_array_assertion_degrades() {
    // Mix arithmetic and array assertions. The SAT model satisfies the
    // arithmetic constraints; the array contradiction triggers degradation.
    // Contradictory assertion added via ctx.process_command to preserve the
    // cached SAT model (execute() invalidates per SMT-LIB, #4516).
    let sat_input = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const x Int)
        (declare-const y Int)
        (assert (= x 10))
        (assert (= y 20))
        (assert (= (+ x y) 30))
        (assert (= (select a x) y))
        (check-sat)
    "#;
    let contra_input = "(assert (= (select a x) 99))";

    let sat_cmds = parse(sat_input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&sat_cmds)
        .expect("invariant: execute succeeds");
    assert_eq!(outputs, vec!["sat"]);

    let contra_cmds = parse(contra_input).expect("invariant: valid assert");
    exec.ctx
        .process_command(&contra_cmds[0])
        .expect("invariant: assert elaborates");

    let err = exec
        .validate_model()
        .expect_err("Contradictory array assertion in mixed formula must be rejected");
    assert!(
        err.is_incomplete(),
        "Mixed AUFLIA: array false assertion must be Incomplete, got: {err}"
    );
}

// ========== UF-Array Equality Propagation Tests (#7435) ==========

/// Regression test for #7435: when a UF function returns an Array-sorted term
/// that is EUF-equal to a const-array, the Array model builder must propagate
/// the const-array interpretation to the UF application term. Without this,
/// select(f(x), i) evaluates to Unknown and model validation degrades SAT to
/// Unknown.
#[test]
fn test_validate_model_uf_array_equality_to_const_array() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-fun f (Int) (Array Int Int))
        (declare-const x Int)
        (assert (= (f x) ((as const (Array Int Int)) 0)))
        (assert (= (select (f x) 5) 0))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");
    assert_eq!(
        outputs,
        vec!["sat"],
        "#7435: UF-Array equality to const-array must be SAT"
    );

    let result = exec.validate_model();
    assert!(
        result.is_ok(),
        "#7435: model validation must pass when UF array equals const-array: {result:?}"
    );
}

// ========== Validation Stats Tests ==========

#[test]
fn test_validation_stats_counts_quantifier_and_uf_skips() {
    // Formula with two evaluable assertions (pure Bool + UF predicate) and
    // one quantified assertion (skipped by quantifier gate).
    // UF assertions are now evaluated and fail-closed (#4686), not skipped.
    //
    // NOTE: The solver returns Unknown for this formula because quantifier
    // E-matching correctly detects incompleteness (#7979). The test checks
    // the output and, if SAT, validates the model stats.
    let input = r#"
        (set-logic AUFLIA)
        (declare-const a Bool)
        (declare-fun p (Int) Bool)
        (assert a)
        (assert (p 0))
        (assert (forall ((x Int)) (=> (> x 0) (p x))))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    // With quantifier incompleteness detection (#7979), the solver correctly
    // returns Unknown rather than SAT when quantified assertions cannot be
    // verified. Both SAT and Unknown are acceptable — SAT is not unsound
    // (the ground assertions do hold), but Unknown is more conservative.
    assert!(
        outputs == vec!["sat"] || outputs == vec!["unknown"],
        "expected sat or unknown for quantified formula, got: {outputs:?}"
    );

    if outputs == vec!["sat"] {
        let stats = exec
            .validate_model()
            .expect("invariant: validation should succeed when SAT");
        assert_eq!(stats.total, 3, "3 assertions in formula");
        assert_eq!(stats.checked, 2, "Bool + UF assertions checked");
        assert_eq!(stats.skipped_quantifier, 1, "quantified assertion skipped");
        assert_eq!(stats.skipped_datatype, 0);
        assert_eq!(stats.skipped_internal, 0);
    }
}

// ========== #7979: All-quantifier assertions must not return SAT ==========

#[test]
fn test_all_quantifier_assertions_degrade_to_unknown_7979() {
    // When ALL assertions are quantified, the model validation pipeline
    // skips all of them (checked==0, skipped_quantifier==total). Prior to
    // the #7979 fix, this returned SAT because skipped_quantifier was not
    // included in the no_verification_evidence guard. The fix ensures
    // degradation to Unknown when no assertion produced verification evidence
    // due to quantifier skipping.
    let input = r#"
        (set-logic UFLIA)
        (declare-fun P (Int) Bool)
        (assert (forall ((x Int)) (P x)))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    // Must NOT return SAT — the quantified assertion was never verified.
    // Unknown is the correct conservative result.
    assert!(
        outputs == vec!["unknown"] || outputs == vec!["unsat"],
        "BUG #7979: all-quantifier formula must not return sat, got: {outputs:?}"
    );
}

// ========== UF Function Model Resolution Tests (#5452) ==========

#[test]
fn test_get_model_uf_int_returning_function_resolves_value() {
    // #5452: UF functions returning Int should show concrete values, not @?N.
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun x () Int)
        (assert (= (f x) 42))
        (assert (>= x 0))
        (check-sat)
        (get-model)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    assert!(
        model.contains("define-fun f"),
        "Model should contain f: {model}"
    );
    // The function body must not contain @? placeholders.
    assert!(
        !model.contains("@?"),
        "Model should not contain @? placeholders: {model}"
    );
    // The function should resolve to 42 (the asserted value).
    assert!(
        model.contains("42"),
        "Model should contain concrete value 42: {model}"
    );
}

#[test]
fn test_get_model_uf_real_returning_function_resolves_value() {
    // #5452: UF functions returning Real should show concrete values.
    let input = r#"
        (set-logic QF_UFLRA)
        (declare-fun g (Real) Real)
        (declare-fun y () Real)
        (assert (= (g y) (/ 157 50)))
        (assert (>= y 0.0))
        (check-sat)
        (get-model)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    assert!(
        model.contains("define-fun g"),
        "Model should contain g: {model}"
    );
    assert!(
        !model.contains("@?"),
        "Model should not contain @? placeholders: {model}"
    );
}

// ========== DT Model Resolution Tests (#5450) ==========

#[test]
fn test_get_model_dt_constructor_concrete_int_arg() {
    // #5450: DT constructors with Int-typed arguments should show concrete values.
    let input = r#"
        (set-logic QF_DT)
        (declare-datatypes ((Pair 0)) (((mkpair (fst Int) (snd Int)))))
        (declare-const p Pair)
        (assert (= (fst p) 10))
        (assert (= (snd p) 20))
        (check-sat)
        (get-model)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    assert!(
        model.contains("define-fun p"),
        "Model should contain p: {model}"
    );
    // Should not contain internal @Sort!N names.
    assert!(
        !model.contains("@Pair!"),
        "Model should not contain @Pair! internal names: {model}"
    );
    // Should contain the concrete value 10.
    assert!(
        model.contains("10"),
        "Model should contain value 10: {model}"
    );
}

// ========== Check-Sat-Assuming Tests ==========

// ========== z3-exact user-facing Real value output (#real-fmt) ==========
//
// The stdout boundary (get-value / get-model / get-objectives / resolved
// function tables) prints Real values in the z3-exact spelling — `5.0`,
// `(- 5.0)`, `(/ 7.0 2.0)`, `(- (/ 7.0 2.0))` — while Int output and every
// internal comparison-key producer (`eval_value_to_model_atom`,
// `format_eval_value`, `format_rational`, euf `term_values`) keep the legacy
// spelling. Every Real expectation below was byte-confirmed against
// z3 4.15.4 on the same script.

#[test]
fn test_real_int_mixed_get_value_z3_exact() {
    let input = r#"
        (set-logic QF_LIRA)
        (declare-const r Real)
        (declare-const s Real)
        (declare-const n Real)
        (declare-const m Real)
        (declare-const i Int)
        (declare-const j Int)
        (assert (= r 5.0))
        (assert (= s (/ 7 2)))
        (assert (= n (- 5.0)))
        (assert (= m (- (/ 7 2))))
        (assert (= i 5))
        (assert (= j (- 5)))
        (check-sat)
        (get-value (r s n m i j))
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(outputs[0], "sat");
    // Real pairs are z3-byte-exact. Int stays on the legacy path untouched
    // (positive `5` matches z3; the bare `-5` is the pre-existing Int
    // get-value spelling, deliberately NOT changed here — flagged follow-up).
    assert_eq!(
        outputs[1],
        "((r 5.0) (s (/ 7.0 2.0)) (n (- 5.0)) (m (- (/ 7.0 2.0))) (i 5) (j -5))"
    );
}

#[test]
fn test_real_int_mixed_get_model_z3_exact() {
    let input = r#"
        (set-logic QF_LIRA)
        (declare-const r Real)
        (declare-const s Real)
        (declare-const n Real)
        (declare-const m Real)
        (declare-const i Int)
        (declare-const j Int)
        (assert (= r 5.0))
        (assert (= s (/ 7 2)))
        (assert (= n (- 5.0)))
        (assert (= m (- (/ 7 2))))
        (assert (= i 5))
        (assert (= j (- 5)))
        (check-sat)
        (get-model)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    // Value atoms byte-identical to z3's (modulo the `(model` wrapper and
    // line layout, which are cosmetic).
    assert!(model.contains("(define-fun r () Real 5.0)"), "{model}");
    assert!(
        model.contains("(define-fun s () Real (/ 7.0 2.0))"),
        "{model}"
    );
    assert!(model.contains("(define-fun n () Real (- 5.0))"), "{model}");
    assert!(
        model.contains("(define-fun m () Real (- (/ 7.0 2.0)))"),
        "{model}"
    );
    // Int define-funs byte-identical to the pre-change output (and to z3).
    assert!(model.contains("(define-fun i () Int 5)"), "{model}");
    assert!(model.contains("(define-fun j () Int (- 5))"), "{model}");
    // No legacy fraction spelling anywhere in the printed model.
    assert!(!model.contains("(/ 7 2)"), "{model}");
    assert!(!model.contains("(/ -7 2)"), "{model}");
}

#[test]
fn test_real_int_objectives_z3_exact() {
    let input = r#"
        (declare-const x Real)
        (declare-const i Int)
        (assert (>= x (/ 7 2)))
        (assert (>= i 4))
        (minimize x)
        (minimize i)
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(outputs[0], "sat");
    // Fractional Real objective is z3-byte-exact; Int objective unchanged
    // (`(i 4)`, matches z3).
    assert!(outputs[1].contains("(x (/ 7.0 2.0))"), "{}", outputs[1]);
    assert!(outputs[1].contains("(i 4)"), "{}", outputs[1]);
}

#[test]
fn test_real_integer_valued_objective_prints_real_literal() {
    // Box mode exercises `format_objective_rational` (the recorded box
    // optimum), lex/single mode the evaluate-then-format path; both must
    // print an integer-valued Real objective as a Real literal `2.0`.
    // NOTE: z3 4.15.4 prints a bare `2` for an integer-valued Real objective
    // in `(get-objectives)` (its own Real-objective spelling is
    // inconsistent: fractions print `(/ 7.0 2.0)`); AY deliberately keeps
    // the value a valid Real literal (#real-fmt).
    let input = r#"
        (set-option :opt.priority box)
        (declare-const x Real)
        (declare-const y Real)
        (assert (>= x (/ 7 2)))
        (assert (>= y 2.0))
        (minimize x)
        (minimize y)
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(outputs[0], "sat");
    assert!(outputs[1].contains("(x (/ 7.0 2.0))"), "{}", outputs[1]);
    assert!(outputs[1].contains("(y 2.0)"), "{}", outputs[1]);
}

#[test]
fn test_real_uf_table_atoms_z3_exact() {
    // Function-table entries route through `resolve_placeholder` /
    // `resolve_table_value`; every Real atom in the printed define-fun must
    // use the z3-exact spelling, and a get-value read at a listed point must
    // match the table byte-for-byte.
    let input = r#"
        (set-logic QF_UFLRA)
        (declare-fun f (Real) Real)
        (declare-const a Real)
        (assert (= a (/ 1 2)))
        (assert (= (f a) (/ 7 2)))
        (assert (= (f 2.0) (- (/ 9 4))))
        (check-sat)
        (get-model)
        (get-value ((f 2.0)))
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    assert!(
        model.contains("(define-fun a () Real (/ 1.0 2.0))"),
        "{model}"
    );
    assert!(model.contains("(/ 7.0 2.0)"), "{model}");
    assert!(model.contains("(- (/ 9.0 4.0))"), "{model}");
    // No legacy spellings (`(/ 7 2)`, `(/ -9 4)`) survive in the table.
    assert!(!model.contains("(/ 7 2)"), "{model}");
    assert!(!model.contains("(/ -9 4)"), "{model}");
    assert_eq!(outputs[2], "(((f 2.0) (- (/ 9.0 4.0))))");
}

#[test]
fn test_real_uf_unlisted_point_matches_printed_else_branch() {
    // A read at an argument point the table does not list must answer the
    // printed define-fun's ELSE branch byte-for-byte.
    let input = r#"
        (set-logic QF_UFLRA)
        (declare-fun f (Real) Real)
        (assert (= (f (/ 1 2)) (/ 7 2)))
        (assert (= (f 2.0) (- (/ 9 4))))
        (check-sat)
        (get-model)
        (get-value ((f 99.0)))
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    // The else branch is the LAST resolved table entry; extract it from the
    // get-value answer and confirm the printed table ends with it.
    let value = outputs[2]
        .strip_prefix("(((f 99.0) ")
        .and_then(|s| s.strip_suffix("))"))
        .unwrap_or_else(|| panic!("unexpected get-value shape: {}", outputs[2]));
    assert!(
        model.contains(value),
        "else-branch value {value} must appear in the printed table: {model}"
    );
    // And it is in the new spelling (a Real table over these constraints
    // has only z3-exact atoms).
    assert!(
        value == "(/ 7.0 2.0)" || value == "(- (/ 9.0 4.0))",
        "unexpected else value: {value}"
    );
}

#[test]
fn test_real_printed_values_round_trip_to_sat_and_pin_unsat_on_distinct() {
    // Round-trip: re-asserting AY's own printed get-value pairs on top of the
    // original constraints stays sat...
    let round_trip = r#"
        (set-logic QF_LRA)
        (declare-const r Real)
        (declare-const s Real)
        (declare-const n Real)
        (declare-const m Real)
        (assert (= r 5.0))
        (assert (= s (/ 7 2)))
        (assert (= n (- 5.0)))
        (assert (= m (- (/ 7 2))))
        (assert (= r 5.0))
        (assert (= s (/ 7.0 2.0)))
        (assert (= n (- 5.0)))
        (assert (= m (- (/ 7.0 2.0))))
        (check-sat)
    "#;
    let commands = parse(round_trip).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");
    assert_eq!(outputs, vec!["sat"]);

    // ...and the printed value is THE value, not merely parseable: requiring
    // the variable to differ from it is unsat.
    let wrong = r#"
        (set-logic QF_LRA)
        (declare-const s Real)
        (assert (= s (/ 7 2)))
        (assert (distinct s (/ 7.0 2.0)))
        (check-sat)
    "#;
    let commands = parse(wrong).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");
    assert_eq!(outputs, vec!["unsat"]);
}
