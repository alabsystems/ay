// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// --- Seq operation parser tests (#6030) ---

#[test]
fn test_elaborate_seq_to_re() {
    let input = r#"
            (declare-const s (Seq Int))
            (assert (= (seq.to_re s) (seq.to.re s)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_seq_to_re_sort_mismatch() {
    let input = r#"
            (declare-const n Int)
            (assert (= (seq.to_re n) (re.none)))
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
fn test_elaborate_seq_in_re() {
    let input = r#"
            (declare-const s (Seq Int))
            (assert (seq.in_re s (seq.to_re s)))
            (assert (seq.in.re s (seq.to.re s)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 2);
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

#[test]
fn test_elaborate_seq_foldl() {
    // AY Array only supports 2 type params: (Array Index Element).
    // Use (Array Int Int) as the function type for foldl.
    // The higher-order semantics aren't implemented — this tests parsing only.
    let input = r#"
            (declare-const f (Array Int Int))
            (declare-const init Int)
            (declare-const s (Seq Int))
            (assert (= (seq.foldl f init s) 0))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
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

#[test]
fn test_elaborate_seq_foldli() {
    let input = r#"
            (declare-const f (Array Int Int))
            (declare-const init Int)
            (declare-const s (Seq Int))
            (assert (= (seq.foldli f 0 init s) 0))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
}
