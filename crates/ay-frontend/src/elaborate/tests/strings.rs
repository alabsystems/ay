// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_elaborate_string_builtins() {
    let input = r#"
            (declare-const x String)
            (declare-const y String)
            (declare-const i Int)
            (assert (= (str.++ x y) x))
            (assert (= (str.len x) i))
            (assert (= (str.at x i) y))
            (assert (= (str.substr x i i) y))
            (assert (str.contains x y))
            (assert (str.prefixof x y))
            (assert (str.suffixof x y))
            (assert (= (str.indexof x y i) i))
            (assert (= (str.replace x y x) x))
            (assert (= (str.replace_all x y x) x))
            (assert (= (str.to_int x) i))
            (assert (= (str.to.int x) i))
            (assert (= (str.from_int i) x))
            (assert (= (int.to.str i) x))
            (assert (str.< x y))
            (assert (str.<= x y))
            (assert (str.is_digit x))
            (assert (= (str.to_code x) i))
            (assert (= (str.from_code i) x))
            (assert (= (str.replace_re x (str.to_re "a") y) x))
            (assert (= (str.replace_re_all x (str.to_re "a") y) x))
            (assert (= (str.to_lower x) y))
            (assert (= (str.to_upper x) y))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 23);
}

#[test]
fn str_at_lowers_to_substr_length_one() {
    // SMT-LIB defines `(str.at s i)` == `(str.substr s i 1)`. AY lowers it at
    // elaboration so symbolic str.at routes through the (more complete) substr
    // theory instead of the opaque `str.at` atom that returned `unknown`.
    use ay_core::{Constant, Symbol};
    let input = r#"
            (declare-const s String)
            (declare-const i Int)
            (assert (= (str.at s i) "a"))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
    // The equality's LHS must now be a 3-arg `str.substr` whose length is the
    // integer literal 1 (never a bare `str.at` application).
    let TermData::App(_, eq_args) = ctx.terms.get(ctx.assertions[0]) else {
        panic!("expected an equality application");
    };
    let lhs = eq_args[0];
    let TermData::App(Symbol::Named(op), sub_args) = ctx.terms.get(lhs) else {
        panic!("str.at LHS must elaborate to an application, got {lhs:?}");
    };
    assert_eq!(op, "str.substr", "str.at must lower to str.substr");
    assert_eq!(sub_args.len(), 3, "str.substr(s, i, 1) has three args");
    let len_arg = sub_args[2];
    assert!(
        matches!(ctx.terms.get(len_arg), TermData::Const(Constant::Int(n)) if *n == num_bigint::BigInt::from(1)),
        "the length argument must be the literal 1"
    );
}

#[test]
fn test_elaborate_str_replace_all_constant_fold() {
    let input = r#"
            (assert (= (str.replace_all "aaba" "a" "c") "ccbc"))
            (assert (= (str.replace_all "aaba" "a" "c") "wrong"))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 2);
    assert!(ctx.terms.is_true(ctx.assertions[0]));
    assert!(ctx.terms.is_false(ctx.assertions[1]));
}

#[test]
fn test_elaborate_str_is_digit_sort_mismatch() {
    let input = r#"
            (declare-const n Int)
            (assert (str.is_digit n))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    ctx.process_command(&commands[0]).unwrap();

    let err = ctx.process_command(&commands[1]).unwrap_err();
    assert!(
        matches!(err, ElaborateError::SortMismatch { .. }),
        "expected sort mismatch, got: {err:?}"
    );
}

#[test]
fn test_elaborate_str_is_digit_arity_mismatch() {
    let input = r#"
            (declare-const x String)
            (declare-const y String)
            (assert (str.is_digit x y))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    ctx.process_command(&commands[0]).unwrap();
    ctx.process_command(&commands[1]).unwrap();

    let err = ctx.process_command(&commands[2]).unwrap_err();
    assert!(
        matches!(err, ElaborateError::InvalidConstant(_)),
        "expected arity error, got: {err:?}"
    );
}

#[test]
fn test_elaborate_string_builtin_sort_mismatch() {
    let input = r#"
            (assert (= (str.len 0) 0))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    let err = ctx.process_command(&commands[0]).unwrap_err();
    assert!(
        matches!(err, ElaborateError::SortMismatch { .. }),
        "expected sort mismatch, got: {err:?}"
    );
}

#[test]
fn test_elaborate_regex_builtins() {
    let input = r#"
            (declare-const x String)
            (assert (str.in_re x (str.to_re "a")))
            (assert (str.in.re x (str.to.re "a")))
            (assert (str.in_re x (re.* (str.to_re "a"))))
            (assert (str.in_re x (re.+ (str.to_re "a"))))
            (assert (str.in_re x (re.opt (str.to_re "a"))))
            (assert (str.in_re x (re.comp (str.to_re "a"))))
            (assert (str.in_re x (re.++ (str.to_re "a") (str.to_re "b"))))
            (assert (str.in_re x (re.union (str.to_re "a") (str.to_re "b"))))
            (assert (str.in_re x (re.inter (str.to_re "a") (str.to_re "b"))))
            (assert (str.in_re x (re.diff (str.to_re "a") (str.to_re "b"))))
            (assert (str.in_re x (re.range "a" "z")))
            (assert (str.in_re x ((_ re.^  3) (str.to_re "a"))))
            (assert (str.in_re x ((_ re.loop 2 4) (str.to_re "a"))))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 13);
}

#[test]
fn indexed_regex_repetition_rejects_invalid_bounds_and_operand_sort() {
    // SMT-LIB 2.6: `((_ re.loop i n) e)` denotes `⋃_{k=i}^{n} L(e)^k`, so
    // `i > n` is an EMPTY index set — a well-formed term denoting the empty
    // language, NOT an invalid constant. It must ELABORATE (and fold to
    // `re.none`); rejecting it refused a conformant input
    // (#regex-loop-degenerate-bounds).
    {
        let input = "(assert (str.in_re \"x\" ((_ re.loop 3 2) (str.to_re \"a\"))))";
        let commands = parse(input).expect("degenerate re.loop parses");
        let mut ctx = Context::new();
        ctx.process_command(&commands[0])
            .expect("a degenerate re.loop bound is the EMPTY LANGUAGE, not an error");
    }
    // Operand-sort violations are still genuine elaboration errors.
    for input in [
        "(assert (str.in_re \"x\" ((_ re.loop 1 2) 7)))",
        "(assert (str.in_re \"x\" ((_ re.^ 2) 7)))",
    ] {
        let commands = parse(input).expect("invalid indexed regex still parses");
        let mut ctx = Context::new();
        let error = ctx
            .process_command(&commands[0])
            .expect_err("invalid indexed regex must fail elaboration");
        assert!(
            matches!(
                error,
                ElaborateError::InvalidConstant(_) | ElaborateError::SortMismatch { .. }
            ),
            "unexpected error for `{input}`: {error:?}"
        );
    }
}

#[test]
fn test_elaborate_str_in_re_sort_mismatch() {
    let input = r#"
            (declare-const x String)
            (assert (str.in_re x x))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    ctx.process_command(&commands[0]).unwrap();

    let err = ctx.process_command(&commands[1]).unwrap_err();
    assert!(
        matches!(err, ElaborateError::SortMismatch { .. }),
        "expected sort mismatch, got: {err:?}"
    );
}

#[test]
fn test_elaborate_str_suffixof_sort_mismatch() {
    let input = r#"
            (declare-const n Int)
            (assert (str.suffixof n "a"))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    ctx.process_command(&commands[0]).unwrap();

    let err = ctx.process_command(&commands[1]).unwrap_err();
    assert!(
        matches!(err, ElaborateError::SortMismatch { .. }),
        "expected sort mismatch, got: {err:?}"
    );
}

#[test]
fn test_elaborate_str_le_sort_mismatch() {
    let input = r#"
            (declare-const n Int)
            (declare-const x String)
            (assert (str.<= n x))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    ctx.process_command(&commands[0]).unwrap();
    ctx.process_command(&commands[1]).unwrap();

    let err = ctx.process_command(&commands[2]).unwrap_err();
    assert!(
        matches!(err, ElaborateError::SortMismatch { .. }),
        "expected sort mismatch, got: {err:?}"
    );
}
