// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn sequence_power_accepts_strings_sequences_and_symbolic_counts() {
    let input = r#"
        (declare-const n Int)
        (declare-const s String)
        (declare-const xs (Seq Int))
        (assert (= (seq.power s 3) (str.++ s s s)))
        (assert (= (seq.power xs n) xs))
    "#;
    let mut ctx = Context::new();
    for command in parse(input).unwrap() {
        ctx.process_command(&command).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 2);
}

#[test]
fn sequence_power_rejects_invalid_types_and_arity() {
    for expression in [
        "(seq.power 7 3)",
        "(seq.power \"a\" true)",
        "(seq.power \"a\")",
    ] {
        let mut ctx = Context::new();
        let input = format!("(assert (= {expression} \"a\"))");
        let commands = parse(&input).unwrap();
        assert!(ctx.process_command(&commands[0]).is_err());
    }
}

// --- Seq operation parser tests (#6030) ---

/// `RegLan` types regular expressions over strings only, so a regular
/// expression over a `(Seq Int)` is unsupported: `RegLan` would also accept
/// it beside a string regex, which z3 rejects.
#[test]
fn test_elaborate_seq_to_re_over_a_non_string_sequence_is_unsupported() {
    let input = r#"
            (declare-const s (Seq Int))
            (assert (= (seq.to_re s) (seq.to.re s)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    ctx.process_command(&commands[0]).unwrap();
    let err = ctx.process_command(&commands[1]).unwrap_err();
    assert!(matches!(err, ElaborateError::Unsupported(_)), "{err:?}");
}

#[test]
fn test_elaborate_seq_to_re_sort_mismatch() {
    let input = r#"
            (declare-const n Int)
            (assert (= (seq.to_re n) re.none))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    ctx.process_command(&commands[0]).unwrap();
    let err = ctx.process_command(&commands[1]).unwrap_err();
    assert!(
        matches!(err, ElaborateError::SortMismatch { .. }),
        "seq.to_re on Int arg should fail, got: {err:?}"
    );
}

#[test]
fn test_elaborate_seq_in_re_over_a_non_string_sequence_is_unsupported() {
    let input = r#"
            (declare-const s (Seq Int))
            (assert (seq.in.re s re.none))
            (assert (seq.in.re "a" (str.to_re "a")))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    ctx.process_command(&commands[0]).unwrap();
    let err = ctx.process_command(&commands[1]).unwrap_err();
    assert!(matches!(err, ElaborateError::Unsupported(_)), "{err:?}");
    ctx.process_command(&commands[2]).unwrap();
    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_seq_in_re_sort_mismatch() {
    let input = r#"
            (declare-const s (Seq Int))
            (assert (seq.in_re s s))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    ctx.process_command(&commands[0]).unwrap();
    let err = ctx.process_command(&commands[1]).unwrap_err();
    assert!(
        matches!(err, ElaborateError::SortMismatch { .. }),
        "seq.in_re with non-RegLan second arg should fail, got: {err:?}"
    );
}

#[test]
fn test_elaborate_seq_map() {
    let input = r#"
            (declare-const f (Array Int Int))
            (declare-const s (Seq Int))
            (assert (= (seq.len (seq.map f s)) (seq.len s)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
}

/// A fold's function is curried as nested arrays, accumulator then element,
/// giving the accumulator; an `(Array Int Int)` is not one.
#[test]
fn test_elaborate_seq_foldl_checks_its_function() {
    let input = r#"
            (declare-const f (Array Int Int))
            (declare-const g (Array Int (Array Int Int)))
            (declare-const init Int)
            (declare-const s (Seq Int))
            (assert (= (seq.foldl f init s) 0))
            (assert (= (seq.foldl g init s) 0))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands[..4] {
        ctx.process_command(cmd).unwrap();
    }
    let err = ctx.process_command(&commands[4]).unwrap_err();
    assert!(
        matches!(err, ElaborateError::SortMismatch { .. }),
        "{err:?}"
    );
    ctx.process_command(&commands[5]).unwrap();
    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_seq_mapi_rejects_binary_array_function() {
    let input = r#"
            (declare-const f (Array Int Int))
            (declare-const s (Seq Int))
            (assert (= (seq.len (seq.mapi f 0 s)) (seq.len s)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    ctx.process_command(&commands[0]).unwrap();
    ctx.process_command(&commands[1]).unwrap();
    let error = ctx.process_command(&commands[2]).unwrap_err();
    assert!(matches!(error, ElaborateError::SortMismatch { .. }));
}

#[test]
fn test_elaborate_seq_mapi_with_two_argument_lambda() {
    let input = r#"
            (declare-const s (Seq Int))
            (assert (=
                (seq.len (seq.mapi (lambda ((i Int) (x Int)) x) 0 s))
                (seq.len s)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
}

/// `seq.foldli`'s function takes the index first.
#[test]
fn test_elaborate_seq_foldli_checks_its_function() {
    let input = r#"
            (declare-const f (Array Int Int))
            (declare-const init Int)
            (declare-const s (Seq Int))
            (assert (= (seq.foldli f 0 init s) 0))
            (assert (= (seq.foldli (lambda ((i Int) (acc Int) (x Int)) (+ acc x i)) 0 init s) 0))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands[..3] {
        ctx.process_command(cmd).unwrap();
    }
    let err = ctx.process_command(&commands[3]).unwrap_err();
    assert!(
        matches!(err, ElaborateError::SortMismatch { .. }),
        "{err:?}"
    );
    ctx.process_command(&commands[4]).unwrap();
    assert_eq!(ctx.assertions.len(), 1);
}
