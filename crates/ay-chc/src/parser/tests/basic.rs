// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_parse_simple_chc() {
    let input = r#"
            (set-logic HORN)
            (declare-rel Inv (Int))
            (declare-var x Int)
        "#;

    let problem = ChcParser::parse(input).expect("test should succeed");
    assert_eq!(problem.predicates().len(), 1);
}

#[test]
fn test_parse_sort() {
    let mut parser = ChcParser::new();
    parser.input = "Int".to_string();
    parser.pos = 0;
    let sort = parser.parse_sort().expect("test should succeed");
    assert_eq!(sort, ChcSort::Int);

    parser.input = "Bool".to_string();
    parser.pos = 0;
    let sort = parser.parse_sort().expect("test should succeed");
    assert_eq!(sort, ChcSort::Bool);

    parser.input = "(_ BitVec 32)".to_string();
    parser.pos = 0;
    let sort = parser.parse_sort().expect("test should succeed");
    assert_eq!(sort, ChcSort::BitVec(32));
}

#[test]
fn test_parse_expr_literal() {
    let mut parser = ChcParser::new();

    parser.input = "42".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("test should succeed");
    assert_eq!(expr, ChcExpr::int(42));

    parser.input = "-10".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("test should succeed");
    assert_eq!(expr, ChcExpr::int(-10));

    parser.input = "true".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("test should succeed");
    assert_eq!(expr, ChcExpr::Bool(true));
}

#[test]
fn test_parse_expr_arithmetic() {
    let mut parser = ChcParser::new();
    parser.variables.insert("x".to_string(), ChcSort::Int);

    parser.input = "(+ x 1)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("test should succeed");
    // Just check it parses without error
    assert!(matches!(expr, ChcExpr::Op(ChcOp::Add, _)));

    parser.input = "(- x 5)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("test should succeed");
    assert!(matches!(expr, ChcExpr::Op(ChcOp::Sub, _)));
}

#[test]
fn test_parse_expr_comparison() {
    let mut parser = ChcParser::new();
    parser.variables.insert("x".to_string(), ChcSort::Int);

    parser.input = "(< x 10)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("test should succeed");
    assert!(matches!(expr, ChcExpr::Op(ChcOp::Lt, _)));

    parser.input = "(= x 0)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("test should succeed");
    assert!(matches!(expr, ChcExpr::Op(ChcOp::Eq, _)));
}

#[test]
fn test_parse_expr_boolean() {
    let mut parser = ChcParser::new();
    parser.variables.insert("a".to_string(), ChcSort::Bool);
    parser.variables.insert("b".to_string(), ChcSort::Bool);

    parser.input = "(and a b)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("test should succeed");
    assert!(matches!(expr, ChcExpr::Op(ChcOp::And, _)));

    parser.input = "(or a b)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("test should succeed");
    assert!(matches!(expr, ChcExpr::Op(ChcOp::Or, _)));

    parser.input = "(not a)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("test should succeed");
    assert!(matches!(expr, ChcExpr::Op(ChcOp::Not, _)));
}

#[test]
fn test_parse_expr_implication() {
    let mut parser = ChcParser::new();
    parser.variables.insert("x".to_string(), ChcSort::Int);

    parser.input = "(=> (= x 0) (< x 10))".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("test should succeed");
    assert!(matches!(expr, ChcExpr::Op(ChcOp::Implies, _)));
}

#[test]
fn test_parse_let_expr() {
    let mut parser = ChcParser::new();

    parser.input = "(let ((x 5)) (+ x 1))".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("test should succeed");
    // After substitution, should be (+ 5 1)
    assert!(matches!(expr, ChcExpr::Op(ChcOp::Add, _)));
}

#[test]
fn test_parse_forall_expr() {
    let mut parser = ChcParser::new();

    parser.input = "(forall ((x Int)) (>= x 0))".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("test should succeed");
    // Forall is stripped for CHC, just returns body
    assert!(matches!(expr, ChcExpr::Op(ChcOp::Ge, _)));
}

/// The MODEL_CHECKER_CONSUMER singleton array initializer has an exact quantifier-free form
/// by array extensionality. It must not take the general body-forall
/// over-approximation (which used to make AY answer `sat` where Z3 answered
/// `unsat`).
#[test]
fn body_position_singleton_forall_is_eliminated_exactly() {
    let input = r#"
        (set-logic HORN)
        (declare-var a (Array (_ BitVec 64) (_ BitVec 64)))
        (declare-var b (Array (_ BitVec 64) (_ BitVec 64)))
        (declare-rel P ((Array (_ BitVec 64) (_ BitVec 64))))
        (declare-rel bad ())
        (rule (=> (forall ((i (_ BitVec 64))) (= (select b i) #x0000000000000007)) (P b)))
        (rule (=> (and (P a) (not (= (select a #x0000000000000005) #x0000000000000007))) bad))
        (query bad)
    "#;
    let problem = ChcParser::parse(input).expect("body-forall must still parse");
    assert!(
        !problem.has_stripped_body_forall(),
        "the exact singleton array equivalence must not arm the downgrade"
    );
    let constraint = problem.clauses()[0]
        .body
        .constraint
        .as_ref()
        .expect("the initializer rule has an array equality constraint");
    let ChcExpr::Op(ChcOp::Eq, arguments) = constraint else {
        panic!("expected rewritten array equality, got {constraint:?}");
    };
    assert!(
        arguments
            .iter()
            .any(|argument| matches!(argument.as_ref(), ChcExpr::ConstArray(_, _))),
        "forall-select initializer must become equality with a const array"
    );
}

#[test]
fn negative_singleton_forall_accepts_reversed_equality_and_capture_rename() {
    let mut parser = ChcParser::new();
    parser.polarity = -1;
    parser.variables.insert(
        "a".to_string(),
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    // Force the quantifier binder through the parser's capture-renaming path.
    parser.variables.insert("i".to_string(), ChcSort::Int);
    parser.clause_binder_names.insert("i".to_string());
    parser.input = "(forall ((i Int)) (= 7 (select a i)))".to_string();

    let rewritten = parser
        .parse_expr()
        .expect("exact reversed form should parse");
    assert!(!parser.problem.has_stripped_body_forall());
    let ChcExpr::Op(ChcOp::Eq, arguments) = &rewritten else {
        panic!("expected array equality after exact elimination");
    };
    assert!(matches!(
        arguments[1].as_ref(),
        ChcExpr::ConstArray(ChcSort::Int, value)
            if matches!(value.as_ref(), ChcExpr::Int(7))
    ));
}

#[test]
fn singleton_forall_elimination_is_negative_polarity_only() {
    for polarity in [0, 1] {
        let mut parser = ChcParser::new();
        parser.polarity = polarity;
        parser.variables.insert(
            "a".to_string(),
            ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
        );
        parser.input = "(forall ((i Int)) (= (select a i) 7))".to_string();

        let body = parser.parse_expr().expect("forall should parse");
        let ChcExpr::Op(ChcOp::Eq, arguments) = &body else {
            panic!("expected the original equality");
        };
        assert!(matches!(
            arguments[0].as_ref(),
            ChcExpr::Op(ChcOp::Select, _)
        ));
        assert!(
            polarity > 0 || parser.problem.has_stripped_body_forall(),
            "mixed polarity must retain the conservative downgrade"
        );
        assert!(
            polarity <= 0 || !parser.problem.has_stripped_body_forall(),
            "positive forall stripping is already exact and must not be flagged"
        );
    }
}

#[test]
fn negative_singleton_forall_near_misses_remain_fail_closed() {
    let cases = [
        // The value depends on the binder.
        "(forall ((i Int)) (= (select a i) i))",
        // The select index is not exactly the binder.
        "(forall ((i Int)) (= (select a (+ i 0)) 7))",
        // The selected array expression depends on the binder.
        "(forall ((i Int)) (= (select (store a i 7) i) 7))",
        // The exact equivalence is intentionally singleton-binder only.
        "(forall ((i Int) (j Int)) (= (select a i) 7))",
    ];

    for input in cases {
        let mut parser = ChcParser::new();
        parser.polarity = -1;
        parser.variables.insert(
            "a".to_string(),
            ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
        );
        parser.input = input.to_string();

        let body = parser.parse_expr().expect("near miss should still parse");
        assert!(
            parser.problem.has_stripped_body_forall(),
            "near miss must preserve the Unsafe-to-Unknown downgrade: {input}"
        );
        let ChcExpr::Op(ChcOp::Eq, arguments) = &body else {
            panic!("near miss must retain its equality body: {input}");
        };
        assert!(
            arguments
                .iter()
                .all(|argument| !matches!(argument.as_ref(), ChcExpr::ConstArray(_, _))),
            "near miss must not synthesize a const array: {input}"
        );
    }
}

#[test]
fn singleton_forall_elimination_checks_key_and_value_sorts_exactly() {
    let binder = ChcVar::new("i", ChcSort::Int);
    let index = ChcExpr::var(binder.clone());
    let wrong_key_array = ChcExpr::var(ChcVar::new(
        "wrong-key",
        ChcSort::Array(Box::new(ChcSort::Bool), Box::new(ChcSort::Int)),
    ));
    let wrong_key_body = ChcExpr::eq(
        ChcExpr::select(wrong_key_array, index.clone()),
        ChcExpr::Int(7),
    );
    assert!(
        ChcParser::eliminate_singleton_forall_const_array(
            &wrong_key_body,
            &binder.name,
            &binder.sort,
        )
        .is_none(),
        "a binder whose sort differs from the array key cannot be eliminated"
    );

    let int_array = ChcExpr::var(ChcVar::new(
        "wrong-value",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    ));
    let wrong_value_body = ChcExpr::eq(ChcExpr::select(int_array, index), ChcExpr::Bool(true));
    assert!(
        ChcParser::eliminate_singleton_forall_const_array(
            &wrong_value_body,
            &binder.name,
            &binder.sort,
        )
        .is_none(),
        "a value whose sort differs from the array element cannot be eliminated"
    );
}

#[test]
fn singleton_forall_binder_scan_charges_flat_fanout_before_scheduling() {
    fn const_array_with_flat_value(child_count: usize) -> ChcExpr {
        ChcExpr::ConstArray(
            ChcSort::Int,
            std::sync::Arc::new(ChcExpr::Op(
                ChcOp::And,
                (0..child_count)
                    .map(|_| std::sync::Arc::new(ChcExpr::Bool(true)))
                    .collect(),
            )),
        )
    }

    let binder = ChcVar::new("i", ChcSort::Int);
    let limit = super::super::expr::MAX_SINGLETON_FORALL_INSPECTION_NODES;
    assert!(ChcParser::expr_is_binder_free(
        &const_array_with_flat_value(limit - 2),
        &binder.name,
    ));
    assert!(
        !ChcParser::expr_is_binder_free(&const_array_with_flat_value(limit - 1), &binder.name,),
        "cap+1 must fail before extending the work stack with flat children"
    );
}

#[test]
fn singleton_forall_sort_depth_and_node_caps_are_exact() {
    fn nested_key_sort(array_depth: usize) -> ChcSort {
        let mut sort = ChcSort::Int;
        for _ in 0..array_depth {
            sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(sort));
        }
        sort
    }

    fn candidate(key_sort: ChcSort) -> (ChcVar, ChcExpr) {
        let binder = ChcVar::new("i", key_sort.clone());
        let array = ChcExpr::var(ChcVar::new(
            "a",
            ChcSort::Array(Box::new(key_sort), Box::new(ChcSort::Int)),
        ));
        let body = ChcExpr::eq(
            ChcExpr::select(array, ChcExpr::var(binder.clone())),
            ChcExpr::Int(7),
        );
        (binder, body)
    }

    // At depth 63, the binder sort contributes 127 nodes and the outer
    // array sort contributes 129: exactly the shared 256-node cap, with the
    // deepest child at the exact depth-64 boundary.
    let (at_binder, at_body) = candidate(nested_key_sort(63));
    assert!(ChcParser::eliminate_singleton_forall_const_array(
        &at_body,
        &at_binder.name,
        &at_binder.sort,
    )
    .is_some());

    let (over_binder, over_body) = candidate(nested_key_sort(64));
    assert!(ChcParser::eliminate_singleton_forall_const_array(
        &over_body,
        &over_binder.name,
        &over_binder.sort,
    )
    .is_none());
}

#[test]
fn singleton_forall_sort_name_byte_cap_is_exact() {
    fn candidate(sort_name_bytes: usize) -> (ChcVar, ChcExpr) {
        let key_sort = ChcSort::Uninterpreted("K".repeat(sort_name_bytes));
        let binder = ChcVar::new("i", key_sort.clone());
        let array = ChcExpr::var(ChcVar::new(
            "a",
            ChcSort::Array(Box::new(key_sort), Box::new(ChcSort::Int)),
        ));
        let body = ChcExpr::eq(
            ChcExpr::select(array, ChcExpr::var(binder.clone())),
            ChcExpr::Int(7),
        );
        (binder, body)
    }

    // The key-sort name is visited once through the binder and once through
    // the array sort, so half the byte cap is the exact admitted boundary.
    let at_name_bytes = super::super::expr::MAX_SINGLETON_FORALL_SORT_NAME_BYTES / 2;
    let (at_binder, at_body) = candidate(at_name_bytes);
    assert!(ChcParser::eliminate_singleton_forall_const_array(
        &at_body,
        &at_binder.name,
        &at_binder.sort,
    )
    .is_some());

    let (over_binder, over_body) = candidate(at_name_bytes + 1);
    assert!(ChcParser::eliminate_singleton_forall_const_array(
        &over_body,
        &over_binder.name,
        &over_binder.sort,
    )
    .is_none());
}

#[test]
fn singleton_forall_binder_name_copy_cap_is_exact() {
    fn parse_with_binder_name(name: &str) -> ChcProblem {
        ChcParser::parse(&format!(
            "(set-logic HORN)\n\
             (declare-var a (Array Int Int))\n\
             (declare-fun P () Bool)\n\
             (assert (=> (forall (({name} Int)) (= (select a {name}) 7)) P))\n\
             (assert (=> P false))\n\
             (check-sat)"
        ))
        .expect("bounded-name singleton forall should parse")
    }

    let at_name = "i".repeat(super::super::expr::MAX_SINGLETON_FORALL_BINDER_NAME_BYTES);
    assert!(!parse_with_binder_name(&at_name).has_stripped_body_forall());

    let over_name = "i".repeat(super::super::expr::MAX_SINGLETON_FORALL_BINDER_NAME_BYTES + 1);
    assert!(parse_with_binder_name(&over_name).has_stripped_body_forall());
}

/// A `forall` at POSITIVE polarity is the legitimate implicit-universal
/// wrapper; stripping it is equivalence-preserving and must NOT flag.
#[test]
fn positive_position_forall_is_not_flagged() {
    let input = r#"
        (set-logic HORN)
        (declare-var x Int)
        (declare-rel Inv (Int))
        (rule (=> (= x 0) (Inv x)))
        (query (and (Inv x) (< x 0)))
    "#;
    let problem = ChcParser::parse(input).expect("plain rule must parse");
    assert!(
        !problem.has_stripped_body_forall(),
        "no body-position forall here, so nothing may be flagged"
    );
}

/// An `exists` in a HEAD would be STRENGTHENED to `forall` by stripping,
/// making facts derivable that the input never entailed -- a false-proof
/// route. No verdict downgrade can repair that, so it must be rejected.
#[test]
fn head_position_exists_is_rejected() {
    let input = r#"
        (set-logic HORN)
        (declare-rel Q ((_ BitVec 8)))
        (rule (=> true (exists ((y (_ BitVec 8))) (Q y))))
    "#;
    let err = ChcParser::parse(input).expect_err("head-exists must be rejected, not mis-parsed");
    let msg = format!("{err}");
    assert!(
        msg.contains("exists") && msg.contains("STRENGTHENED"),
        "error should explain the strengthening risk, got: {msg}"
    );
}

#[test]
fn test_parse_chc_with_rule() {
    let input = r#"
            (set-logic HORN)
            (declare-rel Inv (Int))
            (declare-var x Int)
            (rule (=> (= x 0) (Inv x)))
        "#;

    let problem = ChcParser::parse(input).expect("test should succeed");
    assert_eq!(problem.predicates().len(), 1);
    // Rule should be added
    assert!(!problem.clauses().is_empty());
}

#[test]
fn test_parse_comments() {
    let input = r#"
            ; This is a comment
            (set-logic HORN) ; inline comment
            (declare-rel Inv (Int)) ; another comment
        "#;

    let problem = ChcParser::parse(input).expect("test should succeed");
    assert_eq!(problem.predicates().len(), 1);
}

// --- Quantifier variable capture (the development design notes) ---
//
// Stripping a binder hoists it into the flat clause scope. Two binders in ONE
// clause sharing a name used to become one variable, collapsing two independent
// quantifications — a wrong-answer bug whose verdict depended on the binder's
// NAME. Renaming is applied ONLY to binder-vs-binder collisions; shadowing a
// file-scoped `declare-var` is the ordinary idiom and must stay untouched.

#[test]
fn sibling_binders_sharing_a_name_do_not_collapse() {
    let problem = ChcParser::parse(
        "(set-logic HORN)\
         (declare-fun P (Int) Bool)\
         (declare-fun R (Int) Bool)\
         (assert (forall ((u Int)) (=> (= u 0) (P u))))\
         (assert (forall ((u Int)) (=> (= u 1) (R u))))\
         (assert (=> (and (exists ((y Int)) (P y)) (exists ((y Int)) (R y))) false))\
         (check-sat)",
    )
    .expect("parses");
    // The two `y` binders must denote DIFFERENT variables. Before the fix both
    // resolved to a single `y` and the clause was satisfiable (wrong).
    let last = problem.clauses().last().expect("a clause");
    let text = format!("{last:?}");
    assert!(
        text.contains("ay!cap!"),
        "second sibling binder must be renamed; got {text}"
    );
}

#[test]
fn binder_shadowing_a_declare_var_renames_the_binder() {
    // A binder shadowing a file-scoped `declare-var` DOES capture whenever the
    // clause also uses the outer name outside the binder:
    //
    //   (rule (=> (and (exists ((y Int)) (P y)) (= y 7)) (Q y)))
    //
    // where `y` in `(= y 7)` / `(Q y)` is the declare-var. AY answered unsat
    // where z3 and the truth say sat (fp_single_shadow.smt2).
    //
    // Renaming the BINDER is sound whether or not the outer name is used again:
    // the declare-var binding is left completely intact and the binder simply
    // gets a private name. That is the opposite of the earlier attempt, which
    // removed names from scope and cost five regressions.
    let problem = ChcParser::parse(
        "(set-logic HORN)\
         (declare-var x Int)\
         (declare-fun P (Int) Bool)\
         (assert (forall ((x Int)) (=> (= x 0) (P x))))\
         (check-sat)",
    )
    .expect("parses");
    let text = format!("{:?}", problem.clauses());
    assert!(
        text.contains("ay!cap!"),
        "declare-var shadowing must rename the binder: {text}"
    );
}

#[test]
fn the_same_binder_name_in_separate_clauses_is_not_capture() {
    // Binder scopes are per-clause; `u` in clause after clause is ordinary.
    let problem = ChcParser::parse(
        "(set-logic HORN)\
         (declare-fun P (Int) Bool)\
         (declare-fun R (Int) Bool)\
         (assert (forall ((u Int)) (=> (= u 0) (P u))))\
         (assert (forall ((u Int)) (=> (= u 1) (R u))))\
         (check-sat)",
    )
    .expect("parses");
    let text = format!("{:?}", problem.clauses());
    assert!(
        !text.contains("ay!cap!"),
        "cross-clause reuse must not rename: {text}"
    );
}
