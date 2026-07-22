// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_elaborate_assert_soft_records_soft_constraint() {
    let input = r#"
            (declare-const a Bool)
            (declare-const b Bool)
            (assert (or a b))
            (assert-soft (not a) :weight 3)
            (assert-soft (not b))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    // The hard `(or a b)` is the only hard assertion; softs go to soft_constraints.
    assert_eq!(
        ctx.assertions.len(),
        1,
        "soft constraints are not hard asserts"
    );
    let softs = ctx.soft_constraints();
    assert_eq!(softs.len(), 2);
    assert_eq!(softs[0].weight, 3);
    assert_eq!(softs[1].weight, 1, "default weight is 1");
}

#[test]
fn test_elaborate_assert_soft_rejects_non_bool() {
    let input = r#"
            (declare-const x Int)
            (assert-soft x :weight 1)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let mut err = None;
    for cmd in &commands {
        if let Err(e) = ctx.process_command(cmd) {
            err = Some(e);
        }
    }
    assert!(
        matches!(err, Some(ElaborateError::SortMismatch { .. })),
        "assert-soft on Int term must be a sort mismatch, got {err:?}"
    );
}

#[test]
fn test_elaborate_assert_soft_scoped_by_push_pop() {
    let input = r#"
            (declare-const a Bool)
            (assert-soft a :weight 1)
            (push 1)
            (assert-soft (not a) :weight 2)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.soft_constraints().len(), 2);
    assert!(ctx.pop(), "pop should succeed");
    assert_eq!(
        ctx.soft_constraints().len(),
        1,
        "pop must drop the scoped soft constraint"
    );
}

#[test]
fn test_elaborate_simple() {
    let input = r#"
            (declare-const x Int)
            (declare-const y Int)
            (assert (= x y))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn boolean_connectives_require_smtlib_arity_and_bool_operands() {
    for input in [
        "(assert (and true))",
        "(assert (or true))",
        "(assert (=> true))",
        "(assert (implies true))",
        "(assert (xor true))",
    ] {
        let commands = parse(input).expect("malformed-arity term still parses");
        let mut ctx = Context::new();
        let error = commands
            .iter()
            .try_for_each(|command| ctx.process_command(command).map(|_| ()))
            .expect_err("binary Boolean connective must reject fewer than two operands");
        assert!(
            matches!(error, ElaborateError::InvalidConstant(_)),
            "expected arity error for `{input}`, got {error:?}"
        );
    }

    for input in [
        "(assert (and true 1))",
        "(assert (or 0 false))",
        "(assert (=> true 0))",
        "(assert (implies 0 true))",
        "(assert (xor true 0))",
    ] {
        let commands = parse(input).expect("wrong-sort term still parses");
        let mut ctx = Context::new();
        let error = commands
            .iter()
            .try_for_each(|command| ctx.process_command(command).map(|_| ()))
            .expect_err("Boolean connective must reject a non-Bool operand");
        assert!(
            matches!(error, ElaborateError::SortMismatch { .. }),
            "expected Bool sort error for `{input}`, got {error:?}"
        );
    }
}

#[test]
fn test_elaborate_forall_preserves_termdata_and_binds_var() {
    let input = r#"
            (assert (forall ((x Int)) (> x 0)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
    let assertion = ctx.assertions[0];
    let (vars, body) = match ctx.terms.get(assertion) {
        TermData::Forall(vars, body, _) => (vars, *body),
        other => panic!("Expected TermData::Forall, got {other:?}"),
    };

    assert_eq!(vars.len(), 1);
    let binder_name = vars[0].0.clone();

    let mut names_in_body = Vec::new();
    collect_var_names(&ctx.terms, body, &mut names_in_body);
    assert!(
        names_in_body.contains(&binder_name),
        "Binder {binder_name} not found in body vars: {names_in_body:?}"
    );
}

#[test]
fn test_elaborate_exists_preserves_termdata_and_binds_var() {
    let input = r#"
            (assert (exists ((x Int)) (> x 0)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
    let assertion = ctx.assertions[0];
    let (vars, body) = match ctx.terms.get(assertion) {
        TermData::Exists(vars, body, _) => (vars, *body),
        other => panic!("Expected TermData::Exists, got {other:?}"),
    };

    assert_eq!(vars.len(), 1);
    let binder_name = vars[0].0.clone();

    let mut names_in_body = Vec::new();
    collect_var_names(&ctx.terms, body, &mut names_in_body);
    assert!(
        names_in_body.contains(&binder_name),
        "Binder {binder_name} not found in body vars: {names_in_body:?}"
    );
}

#[test]
fn test_elaborate_nested_quantifiers_preserves_structure() {
    let input = r#"
            (assert (forall ((x Int)) (exists ((y Int)) (= (+ x y) 0))))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
    let assertion = ctx.assertions[0];
    let (outer_vars, outer_body) = match ctx.terms.get(assertion) {
        TermData::Forall(vars, body, _) => (vars, *body),
        other => panic!("Expected TermData::Forall, got {other:?}"),
    };
    assert_eq!(outer_vars.len(), 1);

    match ctx.terms.get(outer_body) {
        TermData::Exists(inner_vars, _, _) => assert_eq!(inner_vars.len(), 1),
        other => panic!("Expected nested TermData::Exists, got {other:?}"),
    }
}

#[test]
fn test_elaborate_forall_with_user_triggers_from_pattern_annotation() {
    let input = r#"
            (declare-fun P (Int) Bool)
            (declare-fun Q (Int) Bool)
            (assert (forall ((x Int))
              (! (=> (P x) (Q x))
                 :pattern ((P x)) )))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
    let assertion = ctx.assertions[0];
    let (vars, triggers) = match ctx.terms.get(assertion) {
        TermData::Forall(vars, _body, triggers) => (vars, triggers),
        other => panic!("Expected TermData::Forall, got {other:?}"),
    };

    assert_eq!(vars.len(), 1);
    assert_eq!(triggers.len(), 1);
    assert_eq!(triggers[0].len(), 1);

    let trigger_term = triggers[0][0];
    let TermData::App(Symbol::Named(sym), args) = ctx.terms.get(trigger_term) else {
        panic!(
            "Expected trigger term to be App, got {:?}",
            ctx.terms.get(trigger_term)
        );
    };
    assert_eq!(sym, "P");
    assert_eq!(args.len(), 1);

    let TermData::Var(var_name, _) = ctx.terms.get(args[0]) else {
        panic!(
            "Expected trigger arg to be bound Var, got {:?}",
            ctx.terms.get(args[0])
        );
    };
    assert_eq!(var_name, &vars[0].0);
}

#[test]
fn test_elaborate_bool_ops() {
    let input = r#"
            (declare-const a Bool)
            (declare-const b Bool)
            (assert (and a b))
            (assert (or a (not b)))
            (assert (=> a b))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 3);
}

#[test]
fn test_elaborate_let() {
    let input = r#"
            (declare-const x Int)
            (assert (let ((y x)) (= y x)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    // let (y = x) in (= y x) should simplify to (= x x) = true
    assert_eq!(ctx.assertions.len(), 1);
    assert!(ctx.terms.is_true(ctx.assertions[0]));
}

#[test]
fn test_elaborate_define_fun() {
    let input = r#"
            (define-fun double ((x Int)) Int (+ x x))
            (declare-const a Int)
            (assert (= (double a) (+ a a)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_define_fun_nullary() {
    let input = r#"
            (declare-sort U 0)
            (declare-fun a () U)
            (declare-fun b () U)
            (define-fun my_eq () Bool (= a b))
            (assert my_eq)
            (assert (not (= a b)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 2);
}

#[test]
fn test_push_pop() {
    let input = r#"
            (declare-const x Int)
            (push 1)
            (declare-const y Int)
            (assert (= x y))
            (pop 1)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 0);
    assert!(ctx.symbols.contains_key("x"));
    assert!(!ctx.symbols.contains_key("y"));
}

#[test]
fn test_global_declarations_keep_const_after_pop() {
    let input = r#"
            (set-option :global-declarations true)
            (push 1)
            (declare-const x Int)
            (pop 1)
            (assert (= x 0))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert!(ctx.symbols.contains_key("x"));
    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_global_decls_alias_updates_global_declarations_option() {
    let input = r#"
            (set-option :global-decls true)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(
        ctx.get_option(":global-declarations"),
        Some(&OptionValue::Bool(true))
    );
    assert_eq!(
        ctx.get_option(":global-decls"),
        Some(&OptionValue::Bool(true))
    );
}

#[test]
fn test_global_declarations_option_changes_apply_to_future_declarations() {
    let input = r#"
            (push 1)
            (set-option :global-decls true)
            (declare-const x Int)
            (set-option :global-declarations false)
            (declare-const y Int)
            (pop 1)
            (assert (= x 0))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert!(ctx.symbols.contains_key("x"));
    assert!(!ctx.symbols.contains_key("y"));
    assert_eq!(
        ctx.get_option(":global-declarations"),
        Some(&OptionValue::Bool(false))
    );
    assert_eq!(
        ctx.get_option(":global-decls"),
        Some(&OptionValue::Bool(false))
    );
    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_redeclare_after_pop_gets_fresh_term_id_6813() {
    let input = r#"
            (push 1)
            (declare-const x Int)
            (pop 1)
            (push 1)
            (declare-const x Int)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let mut first_x = None;

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
        if first_x.is_none() {
            first_x = ctx.symbols.get("x").and_then(|info| info.term);
        }
    }

    let second_x = ctx
        .symbols
        .get("x")
        .and_then(|info| info.term)
        .expect("x should be declared in the second scope");
    let first_x = first_x.expect("x should be declared in the first scope");

    assert_ne!(
        first_x, second_x,
        "redeclaring x after pop must allocate a fresh internal term id"
    );
}

#[test]
fn test_reserved_symbol_const_rejected() {
    let input = r#"
            (declare-const __ay_internal Int)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let result = ctx.process_command(&commands[0]);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        matches!(err, ElaborateError::ReservedSymbol(_)),
        "Expected ReservedSymbol error, got: {err:?}"
    );
}

#[test]
fn test_reserved_symbol_fun_rejected() {
    let input = r#"
            (declare-fun __ay_myfunc (Int) Bool)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let result = ctx.process_command(&commands[0]);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        ElaborateError::ReservedSymbol(_)
    ));
}

#[test]
fn test_reserved_symbol_define_fun_rejected() {
    let input = r#"
            (define-fun __ay_helper ((x Int)) Int (+ x 1))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let result = ctx.process_command(&commands[0]);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        ElaborateError::ReservedSymbol(_)
    ));
}

#[test]
fn test_reserved_symbol_datatype_rejected() {
    let input = r#"
            (declare-datatype __ay_MyDT ((ctor)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let result = ctx.process_command(&commands[0]);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        ElaborateError::ReservedSymbol(_)
    ));
}

#[test]
fn test_reserved_symbol_constructor_rejected() {
    let input = r#"
            (declare-datatype MyDT ((__ay_badctor)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let result = ctx.process_command(&commands[0]);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        ElaborateError::ReservedSymbol(_)
    ));
}

#[test]
fn test_reserved_symbol_selector_rejected() {
    let input = r#"
            (declare-datatype MyDT ((ctor (__ay_badsel Int))))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let result = ctx.process_command(&commands[0]);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        ElaborateError::ReservedSymbol(_)
    ));
}

/// Soundness: a builtin theory-operator name that AY matches STRUCTURALLY on
/// `App(Named(name), ..)` (array `const-array`/`select`/`store`, a BV op, a set
/// op, …) must be rejected at declaration. Otherwise the user-symbol
/// elaboration path builds the very `App(Named(name), ..)` shape the theory
/// then conflates with the builtin op — for arrays that is a *wrong-UNSAT*
/// (a false claim "proved"), the cardinal soundness failure.
#[test]
fn test_reserved_theory_op_names_rejected() {
    for (form, name) in [
        (
            "(declare-fun const-array (Bool) (Array Int Bool))",
            "const-array",
        ),
        ("(declare-fun select ((Array Int Int) Int) Int)", "select"),
        (
            "(declare-fun store ((Array Int Int) Int Int) (Array Int Int))",
            "store",
        ),
        ("(declare-fun default ((Array Int Int)) Int)", "default"),
        (
            "(declare-fun bvadd ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))",
            "bvadd",
        ),
        (
            "(declare-fun set.union ((Array Int Bool) (Array Int Bool)) (Array Int Bool))",
            "set.union",
        ),
        // FP classification predicates: forging fp.isZero/fp.isNaN/fp.isInfinite
        // was a CONFIRMED wrong-UNSAT (e.g. `(not (fp.isZero (_ +zero 8 24)))`
        // answered unsat, the forged symbol conflated with the builtin).
        (
            "(declare-fun fp.isZero ((_ FloatingPoint 8 24)) Bool)",
            "fp.isZero",
        ),
        (
            "(declare-fun fp.isNaN ((_ FloatingPoint 8 24)) Bool)",
            "fp.isNaN",
        ),
        (
            "(declare-fun fp.isInfinite ((_ FloatingPoint 8 24)) Bool)",
            "fp.isInfinite",
        ),
        (
            "(declare-fun fp.isNormal ((_ FloatingPoint 8 24)) Bool)",
            "fp.isNormal",
        ),
        (
            "(declare-fun fp.isSubnormal ((_ FloatingPoint 8 24)) Bool)",
            "fp.isSubnormal",
        ),
        // Multiset pointwise/higher-order ops: same conflation surface
        // (fail-closed `unknown` downstream today, sealed uniformly here).
        (
            "(declare-fun multiset.union ((Array Int Int) (Array Int Int)) (Array Int Int))",
            "multiset.union",
        ),
        (
            "(declare-fun multiset.sum ((Array Int Int)) Int)",
            "multiset.sum",
        ),
        (
            "(declare-const const-array (Array Int Bool))",
            "const-array (declare-const)",
        ),
        (
            "(define-fun select ((a (Array Int Int)) (i Int)) Int 0)",
            "select (define-fun)",
        ),
    ] {
        let commands = parse(form).unwrap();
        let mut ctx = Context::new();
        let result = ctx.process_command(&commands[0]);
        assert!(
            matches!(result, Err(ElaborateError::ReservedSymbol(_))),
            "expected ReservedSymbol rejecting forged builtin op `{name}` via `{form}`, got: {result:?}"
        );
    }
}

/// The confirmed cardinal wrong-UNSAT repro: forging `const-array` as a user
/// function used to let AY treat `(const-array false)` as the all-false builtin
/// array and "prove" a satisfiable query UNSAT. It must now be REJECTED at
/// elaboration (never reach the solver as a false UNSAT).
#[test]
fn test_forged_const_array_impl_repro_rejected() {
    let input = r#"
            (declare-fun const-array (Bool) (Array Int Bool))
            (declare-const V (Array Int Bool))
            (declare-const len Int)
            (assert (= V (const-array false)))
            (assert (= len (ite (select V 0) 0 1)))
            (assert (= len 0))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let mut saw_reserved = false;
    for cmd in &commands {
        if let Err(ElaborateError::ReservedSymbol(_)) = ctx.process_command(cmd) {
            saw_reserved = true;
            break;
        }
    }
    assert!(
        saw_reserved,
        "forged const-array declaration must be rejected as ReservedSymbol"
    );
}

/// The SMT-LIB Core connectives and arithmetic operators are NOT reserved: AY's
/// higher-order `(_ map f)` feature legitimately `declare-fun`s them as map
/// targets (`((_ map not) s)` = set complement over `(Array _ Bool)`). Reserving
/// them would reject legitimate input, so they must stay declarable.
#[test]
fn test_core_connectives_not_reserved_for_map() {
    let input = r#"
            (declare-fun not (Bool) Bool)
            (declare-fun and (Bool Bool) Bool)
            (declare-fun or (Bool Bool) Bool)
            (declare-const s (Array Int Bool))
            (declare-const i Int)
            (assert (select ((_ map not) s) i))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd)
            .expect("core connective declarations must be accepted (map targets)");
    }
    assert!(ctx.symbols.contains_key("not"));
    assert!(ctx.symbols.contains_key("and"));
    assert!(ctx.symbols.contains_key("or"));
}

/// Qualified-(as)-path names (elaborate/qualified.rs, matched BEFORE the
/// declared-symbol fallback) are reserved: forging each via declare-fun +
/// `(as <name> <sort>)` was a confirmed wrong-UNSAT on clean HEAD
/// (rc_setempty_as.smt2 / rc_msempty_as.smt2 / rc_mapempty_as.smt2 — e.g. a
/// declared `set.empty` used under `(as set.empty (Array Int Bool))` was
/// treated as the builtin constant-false array).
#[test]
fn test_forged_qualified_as_path_names_rejected() {
    for decl in [
        "(declare-fun set.empty () (Array Int Bool))",
        "(declare-fun multiset.empty () (Array Int Int))",
        "(declare-fun map.empty () (Array Int Int))",
        "(declare-const set.empty (Array Int Bool))",
        "(define-fun map.empty () Int 0)",
        "(declare-fun seq.empty () (Seq Int))",
    ] {
        let commands = parse(decl).unwrap();
        let mut ctx = Context::new();
        let result = ctx.process_command(&commands[0]);
        assert!(
            matches!(result, Err(ElaborateError::ReservedSymbol(_))),
            "expected ReservedSymbol rejection for `{decl}`, got: {result:?}"
        );
    }
}

/// `const` is handled by SHADOWING, not reservation: real-world QF_UF
/// benchmarks legitimately declare it (the CLEARSY B-method fixtures declare
/// `(declare-fun |const| (U U) U)`), so the declaration must stay accepted —
/// and once declared, `(as const <sort>)` must resolve to the USER symbol (a
/// plain uninterpreted application), not the builtin constant array (the
/// rc_const_as wrong-UNSAT conflation).
#[test]
fn test_declared_const_shadows_builtin_constant_array() {
    // Declaration accepted (CLEARSY pattern).
    let input = r#"
            (declare-fun const (Int) (Array Int Int))
            (assert (= (select ((as const (Array Int Int)) 7) 3) 7))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd)
            .expect("declared `const` must stay accepted and usable under (as ...)");
    }
    assert!(ctx.symbols.contains_key("const"));
    // The elaborated assertion must contain the USER's `const` application —
    // NOT a folded builtin constant array (whose select would already have
    // reduced to the constant 7, collapsing the equality to `true`).
    use ay_core::term::TermData;
    let assertion = *ctx.assertions.last().expect("assertion recorded");
    assert!(
        !matches!(ctx.terms.get(assertion), TermData::Const(_)),
        "(as const ...) over a DECLARED `const` must stay an uninterpreted \
         application, not fold to the builtin constant array"
    );
    // Without a declaration, the builtin constant array still folds:
    // select(const-array(7), 3) = 7 elaborates to a trivially-true equality.
    let builtin_input = r#"
            (assert (= (select ((as const (Array Int Int)) 7) 3) 7))
        "#;
    let commands = parse(builtin_input).unwrap();
    let mut ctx2 = Context::new();
    for cmd in &commands {
        ctx2.process_command(cmd)
            .expect("builtin (as const ...) must keep elaborating when undeclared");
    }
}

/// The builtin `(as …)` USE path is unaffected by reserving the qualified
/// names: the dedicated match arms in `elaborate_qualified_app` fire before
/// any symbol lookup and never require a declaration.
#[test]
fn test_legit_qualified_as_builtin_uses_still_work() {
    let input = r#"
            (declare-const s (Set Int))
            (declare-const m (Multiset Int))
            (declare-const mp (Map Int Int))
            (assert (= s (as set.empty (Set Int))))
            (assert (= m (as multiset.empty (Multiset Int))))
            (assert (= mp (as map.empty (Map Int Int))))
            (assert (= (select ((as const (Array Int Int)) 7) 3) 7))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd)
            .expect("builtin (as ...) uses must keep elaborating");
    }
    assert_eq!(ctx.assertions.len(), 4);
}

#[test]
fn test_is_reserved_op_name_classification() {
    use crate::elaborate::{is_excluded_declarable_op_name, is_reserved_op_name};
    // Structurally-matched theory ops: reserved.
    for op in [
        "const-array",
        "select",
        "store",
        "default",
        "as-array",
        "bvadd",
        "concat",
        "int2bv",
        "bv2nat",
        "set.union",
        "map.get",
        "seq.len",
        "str.len",
        "re.union",
        "fp.add",
        "multiset.count",
        // Qualified-(as)-path names (elaborate/qualified.rs).
        "set.empty",
        "multiset.empty",
        "map.empty",
        "seq.empty",
        // FP classification predicates (fp.isZero/isNaN/isInfinite were
        // confirmed wrong-UNSAT forgeries before being reserved).
        "fp.isNaN",
        "fp.isInfinite",
        "fp.isZero",
        "fp.isNormal",
        "fp.isSubnormal",
        // Multiset pointwise/higher-order ops.
        "multiset.union",
        "multiset.inter",
        "multiset.diff",
        "multiset.map",
        "multiset.filter",
        "multiset.fold",
        "multiset.comprehension",
        "multiset.sum",
    ] {
        assert!(is_reserved_op_name(op), "`{op}` should be reserved");
    }
    // Core/arith (map-target-eligible) and ordinary names: NOT reserved.
    for ok in [
        "and",
        "or",
        "not",
        "xor",
        "=",
        "distinct",
        "ite",
        "+",
        "-",
        "*",
        "div",
        "mod",
        "abs",
        "min",
        "max",
        "to_real",
        "union",
        "member",
        "subset",
        "count",
        "map",
        "foo",
        "my_select",
        "Option",
        // `const` is declared-shadowed, not reserved (CLEARSY declares it).
        "const",
        // Declaration-activated collection ops: deductive-checks's encoder
        // declares these via try_declare_fun to activate the native
        // collection solvers — they must stay declarable.
        "set.subset",
        "map.dom",
        "map.subset",
        "multiset.subset",
    ] {
        assert!(!is_reserved_op_name(ok), "`{ok}` should NOT be reserved");
    }
    // The explicit exclusion table matches the helper, and no name is in both
    // tables.
    for &(op, reason) in EXCLUDED_DECLARABLE_OP_NAMES {
        assert!(is_excluded_declarable_op_name(op));
        assert!(
            !is_reserved_op_name(op),
            "`{op}` ({reason}) is in BOTH the reserved and excluded tables"
        );
    }
    assert!(!is_excluded_declarable_op_name("select"));
    assert!(!is_excluded_declarable_op_name("foo"));
}

/// BLOCKER-2 regression (deductive-checks compatibility): the declaration-activated
/// collection predicates must remain user-declarable. deductive-checks-core declares
/// exactly these four names via the ay-dpll programmatic API
/// (`try_declare_fun`) — which funnels through this same
/// `Context::declare_fun`/`is_reserved_symbol` choke point — as the documented
/// activation route for the native set/map/multiset solvers:
///   - `set.subset`       (encoder/collection_set.rs)
///   - `map.dom`          (encoder/collection_map.rs)
///   - `map.subset`       (encoder/collection_map.rs)
///   - `multiset.subset`  (encoder/ir_encoder/multiset.rs)
/// Reserving them hard-fails those default (no-fallback) encodings on the
/// first collection proof. Misuse of the declared name fails CLOSED (probed:
/// mismatched Int-sorted declarations answer unknown/sat, never a bogus
/// unsat).
#[test]
fn test_declaration_activated_collection_ops_declarable() {
    let input = r#"
            (declare-fun set.subset ((Array Int Bool) (Array Int Bool)) Bool)
            (declare-fun map.dom ((Array Int Int)) (Array Int Bool))
            (declare-fun map.subset ((Array Int Int) (Array Int Int)) Bool)
            (declare-fun multiset.subset ((Array Int Int) (Array Int Int)) Bool)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd)
            .expect("declaration-activated collection op must stay declarable");
    }
    for name in ["set.subset", "map.dom", "map.subset", "multiset.subset"] {
        assert!(ctx.symbols.contains_key(name), "`{name}` not declared");
    }
}

/// The declaration-activated names are declarable ONLY via `declare-fun` at
/// the native collection signature (the activation contract). Every other
/// declaration form must be rejected fail-closed: a mismatched signature
/// previously reached the native subset rule — `(declare-fun set.subset (Int
/// Int) Bool)` + `(assert (not (set.subset 0 0)))` answered a definitive
/// `unsat` via ground-identity reflexivity on the forged symbol.
#[test]
fn test_declaration_activated_wrong_signature_rejected() {
    // Wrong signatures via declare-fun: rejected by the signature gate.
    for (form, name) in [
        (
            "(declare-fun set.subset (Int Int) Bool)",
            "set.subset over Int",
        ),
        (
            "(declare-fun map.subset (Int Int) Bool)",
            "map.subset over Int",
        ),
        (
            "(declare-fun multiset.subset (Int Int) Bool)",
            "multiset.subset over Int",
        ),
        ("(declare-fun map.dom (Int) Int)", "map.dom over Int"),
        (
            "(declare-fun set.subset ((Array Int Bool)) Bool)",
            "set.subset arity 1",
        ),
        (
            "(declare-fun set.subset ((Array Int Bool) (Array Int Bool)) Int)",
            "set.subset non-Bool result",
        ),
        (
            "(declare-fun map.dom ((Array Int Int)) Int)",
            "map.dom non-array result",
        ),
        // Mixed-index carriers: previously ACCEPTED by the gate and then
        // PANICKED in ay-core (`mk_select index sort mismatch`) when the
        // native subset rule instantiated a shared element variable across
        // both carriers — a user-triggerable crash, now rejected fail-closed.
        (
            "(declare-fun set.subset ((Array Int Bool) (Array Bool Bool)) Bool)",
            "set.subset mixed index sorts",
        ),
        (
            "(declare-fun multiset.subset ((Array Int Int) (Array Bool Int)) Bool)",
            "multiset.subset mixed index sorts",
        ),
        (
            "(declare-fun map.dom ((Array Int Int)) (Array Bool Bool))",
            "map.dom result indexed by non-key sort",
        ),
    ] {
        let commands = parse(form).unwrap();
        let mut ctx = Context::new();
        let result = ctx.process_command(&commands[0]);
        assert!(
            matches!(result, Err(ElaborateError::Unsupported(_))),
            "expected signature-gate rejection for {name} via `{form}`, got: {result:?}"
        );
    }
    // Non-declare-fun forms: rejected as reserved outright.
    for (form, name) in [
        (
            "(declare-const set.subset Bool)",
            "declare-const set.subset",
        ),
        (
            "(declare-const map.dom (Array Int Bool))",
            "declare-const map.dom",
        ),
        (
            "(define-fun map.subset ((a (Array Int Int)) (b (Array Int Int))) Bool true)",
            "define-fun map.subset",
        ),
        (
            "(declare-datatype D ((multiset.subset (f Int))))",
            "datatype ctor multiset.subset",
        ),
    ] {
        let commands = parse(form).unwrap();
        let mut ctx = Context::new();
        let result = ctx.process_command(&commands[0]);
        assert!(
            matches!(result, Err(ElaborateError::ReservedSymbol(_))),
            "expected ReservedSymbol rejection for {name} via `{form}`, got: {result:?}"
        );
    }
}

/// DRIFT-PROOF: mechanically re-extract every operator name the elaborators
/// match structurally (string-literal match arms and `== "…"` comparisons in
/// `src/elaborate/app/*.rs`, `src/elaborate/indexed.rs`,
/// `src/elaborate/qualified.rs`, and `src/elaborate/term.rs`) and assert each
/// one is classified in exactly one of [`RESERVED_OP_NAMES`] or
/// [`EXCLUDED_DECLARABLE_OP_NAMES`]. A future match-arm addition whose name is
/// in neither table fails here, so the reserved set cannot silently drift from
/// the true structural-match vocabulary (that drift is exactly how the
/// fp.isZero/fp.isNaN/fp.isInfinite wrong-UNSAT forgeries slipped past the
/// first hand-curated table, and how the qualified-(as)-path names
/// set.empty/multiset.empty/map.empty/const — matched in `qualified.rs`, a
/// file the first drift test did not scan — stayed forgeable wrong-UNSATs
/// after the app-arm vocabulary was sealed).
///
/// Scan scope: every `src/elaborate/*.rs` file that matches TERM-LEVEL
/// operator/identifier names. Deliberately excluded from the scan:
/// `sorts.rs` (matches SORT names — a separate namespace; declaring a
/// function named `Set`/`Array` is legitimate and cannot conflate with sort
/// elaboration), `commands.rs` (matches option keywords), and
/// `declarations.rs`/`datatypes.rs`/`commands.rs` symbol handling (no
/// structural op-name matching; datatype member names are USER-defined
/// vocabulary gated dynamically by the `DatatypeMemberCollision` /
/// `SortRedeclaration` checks, not by these static tables).
#[test]
fn test_reserved_op_table_covers_all_elaborator_match_arms() {
    use crate::elaborate::{
        is_excluded_declarable_op_name, is_reserved_op_name, EXCLUDED_DECLARABLE_OP_NAMES,
    };
    use std::path::{Path, PathBuf};

    /// Extract the string literals of a match-arm pattern line: a line that
    /// (after trimming and an optional leading `|`) consists ONLY of one or
    /// more `"…"` literals separated by `|`, terminated by `=>`, an `if …`
    /// match-arm guard (e.g. the declared-symbol guard on the `"const"` arm
    /// in `qualified.rs`), a trailing `|`, or end-of-line (multi-line arm
    /// continuation). Everything else — error-message strings, function-call
    /// arguments, `.to_string()` receivers — is rejected by the terminator
    /// check.
    fn extract_arm_string_literals(line: &str) -> Vec<String> {
        let trimmed = line.trim();
        let mut rest = trimmed.strip_prefix('|').map_or(trimmed, str::trim_start);
        if !rest.starts_with('"') {
            return Vec::new();
        }
        let mut lits = Vec::new();
        loop {
            let Some(end) = rest[1..].find('"') else {
                return Vec::new();
            };
            lits.push(rest[1..=end].to_string());
            rest = rest[end + 2..].trim_start();
            if let Some(after_pipe) = rest.strip_prefix('|') {
                rest = after_pipe.trim_start();
                if rest.is_empty() {
                    break; // arm continues on the next line
                }
                if !rest.starts_with('"') {
                    return Vec::new();
                }
                continue;
            }
            break;
        }
        if rest.is_empty() || rest.starts_with("=>") || rest.starts_with("if ") {
            lits
        } else {
            Vec::new()
        }
    }

    /// Extract the right-hand literals of `== "…"` comparisons (e.g.
    /// `sym.name() == "const-array"`, `parts[0] == "map"`).
    fn extract_eq_string_literals(line: &str) -> Vec<String> {
        let mut lits = Vec::new();
        let mut rest = line;
        while let Some(pos) = rest.find("== \"") {
            let after = &rest[pos + 4..];
            let Some(end) = after.find('"') else { break };
            lits.push(after[..end].to_string());
            rest = &after[end + 1..];
        }
        lits
    }

    /// Filter: operator names are short single tokens; format/error strings
    /// contain whitespace, braces, parens, colons or quotes and are dropped.
    fn looks_like_op_name(name: &str) -> bool {
        !name.is_empty()
            && name.len() <= 40
            && !name
                .chars()
                .any(|c| c.is_whitespace() || "{}():'\\\"".contains(c))
    }

    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let app_dir = manifest.join("src/elaborate/app");
    let mut files: Vec<PathBuf> = std::fs::read_dir(&app_dir)
        .expect("read src/elaborate/app")
        .map(|entry| entry.expect("dir entry").path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "rs"))
        .collect();
    files.push(manifest.join("src/elaborate/indexed.rs"));
    files.push(manifest.join("src/elaborate/qualified.rs"));
    files.push(manifest.join("src/elaborate/term.rs"));
    files.sort();

    let mut extracted = std::collections::BTreeSet::new();
    for file in &files {
        let source = std::fs::read_to_string(file)
            .unwrap_or_else(|e| panic!("read {}: {e}", file.display()));
        for line in source.lines() {
            for lit in extract_arm_string_literals(line)
                .into_iter()
                .chain(extract_eq_string_literals(line))
            {
                if looks_like_op_name(&lit) {
                    extracted.insert(lit);
                }
            }
        }
    }

    // Extraction sanity: it must SEE the known vocabulary (guards against the
    // extractor itself rotting into a vacuous pass).
    assert!(
        extracted.len() >= 150,
        "extraction looks broken: only {} names extracted",
        extracted.len()
    );
    for must_see in [
        "select",
        "store",
        "bvadd",
        "fp.isNaN",
        "fp.isZero",
        "multiset.union",
        "set.subset",
        "map.dom",
        "const-array",
        "seq.len",
        "str.len",
        "map",
        // qualified.rs vocabulary (the recheck-found blind spot)
        "set.empty",
        "multiset.empty",
        "map.empty",
        "const",
        // term.rs vocabulary (rounding modes, FP special literals)
        "roundNearestTiesToEven",
        "NaN",
    ] {
        assert!(
            extracted.contains(must_see),
            "extraction failed to find known op `{must_see}` — extractor broken?"
        );
    }

    let unclassified: Vec<&String> = extracted
        .iter()
        .filter(|name| !is_reserved_op_name(name) && !is_excluded_declarable_op_name(name))
        .collect();
    assert!(
        unclassified.is_empty(),
        "elaborator-matched op names in NEITHER RESERVED_OP_NAMES nor \
         EXCLUDED_DECLARABLE_OP_NAMES (classify each: reserve it, or add it to \
         the excluded table with a documented reason): {unclassified:?}"
    );

    // And the tables must stay disjoint.
    for &(op, _) in EXCLUDED_DECLARABLE_OP_NAMES {
        assert!(
            !is_reserved_op_name(op),
            "`{op}` appears in BOTH the reserved and excluded tables"
        );
    }
}

#[test]
fn test_normal_symbol_accepted() {
    // Symbols not starting with __ay_ should be accepted
    let input = r#"
            (declare-const _ay_almost Int)
            (declare-fun normal_func (Int) Bool)
            (declare-datatype MyList ((nil) (cons (head Int) (tail MyList))))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    // All should succeed
    assert!(ctx.symbols.contains_key("_ay_almost"));
    assert!(ctx.symbols.contains_key("normal_func"));
    assert!(ctx.symbols.contains_key("nil"));
    assert!(ctx.symbols.contains_key("cons"));
}

#[test]
fn test_is_reserved_symbol() {
    assert!(is_reserved_symbol("__ay_test"));
    assert!(is_reserved_symbol("__ay_dt_depth_List"));
    assert!(is_reserved_symbol("__ay_"));
    assert!(!is_reserved_symbol("_ay_test"));
    assert!(!is_reserved_symbol("__z3_test"));
    assert!(!is_reserved_symbol("normal"));
}

/// Regression test for #2992: undeclared functions in application position
/// must produce an error, not silently create an App with default Sort::Bool.
#[test]
fn test_undeclared_function_application_rejected() {
    let input = r#"
            (declare-const s Int)
            (assert (= (__field_value s) 42))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    let mut found_error = false;
    for cmd in &commands {
        if let Err(e) = ctx.process_command(cmd) {
            assert!(
                matches!(e, ElaborateError::UndefinedSymbol(ref name) if name == "__field_value"),
                "Expected UndefinedSymbol for __field_value, got: {e:?}"
            );
            found_error = true;
        }
    }
    assert!(
        found_error,
        "Expected UndefinedSymbol error for undeclared function application"
    );
}

/// Declared functions in application position should still work.
#[test]
fn test_declared_function_application_accepted() {
    let input = r#"
            (declare-fun __field_value (Int) Int)
            (declare-const s Int)
            (assert (= (__field_value s) 42))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

/// #8621: define-fun definitions inside a pushed scope must be removed on pop.
#[test]
fn test_define_fun_removed_on_pop() {
    let input = r#"
            (declare-const a Int)
            (push 1)
            (define-fun f ((x Int)) Int (+ x 1))
            (assert (= (f a) (+ a 1)))
            (pop 1)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    // After pop, fun_defs should not contain "f"
    assert!(
        !ctx.fun_defs.contains_key("f"),
        "fun_defs should not contain 'f' after pop"
    );
    // Symbol table entry for "f" should also be removed on pop
    assert!(
        !ctx.symbols.contains_key("f"),
        "symbols should not contain 'f' after pop"
    );
    // a should still be present since it was declared before push
    assert!(ctx.symbols.contains_key("a"));
    assert_eq!(ctx.assertions.len(), 0);
}

/// #8621: define-fun-rec definitions inside a pushed scope must be removed on pop.
#[test]
fn test_define_fun_rec_removed_on_pop() {
    let input = r#"
            (declare-const a Int)
            (push 1)
            (define-fun-rec g ((x Int)) Int (ite (= x 0) 0 (+ 1 (g (- x 1)))))
            (pop 1)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert!(
        !ctx.fun_defs.contains_key("g"),
        "fun_defs should not contain 'g' after pop"
    );
    // Symbol table entry for "g" should also be removed on pop
    assert!(
        !ctx.symbols.contains_key("g"),
        "symbols should not contain 'g' after pop"
    );
    assert!(ctx.symbols.contains_key("a"));
}

/// #8621: global define-fun (no push) should persist.
#[test]
fn test_define_fun_persists_without_scope() {
    let input = r#"
            (define-fun double ((x Int)) Int (+ x x))
            (declare-const a Int)
            (assert (= (double a) (+ a a)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    // Without push/pop, the definition should remain
    assert!(
        ctx.fun_defs.contains_key("double"),
        "fun_defs should contain 'double' at global scope"
    );
    assert_eq!(ctx.assertions.len(), 1);
}

/// #8622: define-fun-rec with unbounded recursion must error, not stack overflow.
#[test]
fn test_define_fun_rec_depth_limit() {
    // Define a recursive function that always recurses (no base case reachable
    // during elaboration expansion)
    let input = r#"
            (define-fun-rec diverge ((x Int)) Int (diverge x))
            (declare-const a Int)
            (assert (= (diverge a) 0))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    let mut found_depth_error = false;
    for cmd in &commands {
        if let Err(e) = ctx.process_command(cmd) {
            assert!(
                matches!(e, ElaborateError::RecursionDepthExceeded(_)),
                "Expected RecursionDepthExceeded error, got: {e:?}"
            );
            found_depth_error = true;
            break;
        }
    }
    assert!(
        found_depth_error,
        "Expected RecursionDepthExceeded error for unbounded recursive function"
    );
}

/// Unknown indexed identifiers must also be rejected, not silently accepted.
#[test]
fn test_unknown_indexed_identifier_rejected() {
    let input = r#"
            (declare-const x (_ BitVec 8))
            (assert (= ((_ unknown_bv_op 4) x) x))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    let mut found_error = false;
    for cmd in &commands {
        if let Err(e) = ctx.process_command(cmd) {
            assert!(
                format!("{e:?}").contains("unknown indexed identifier"),
                "Expected 'unknown indexed identifier' error, got: {e:?}"
            );
            found_error = true;
        }
    }
    assert!(found_error, "Expected error for unknown indexed identifier");
}
