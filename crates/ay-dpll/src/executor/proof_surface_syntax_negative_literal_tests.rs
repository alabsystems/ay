// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The authored echo of the negative-literal shorthand: an unquoted `-N` is the
//! numeral (as z3 5.1.0 and pinned Carcara read it), a symbol spelled `-N` is
//! only ever the quoted `|-N|`.

use super::*;

/// An unquoted `-16` is parsed as the numeral and echoed bare, as pinned
/// Carcara reads it; a symbol named `-16` (only ever the quoted `|-16|`) keeps
/// its quotes, under a binder and beside the bare number alike.
#[test]
fn the_negative_literal_shorthand_is_echoed_bare_and_the_quoted_name_quoted() {
    let commands = ay_frontend::parse(
        "(declare-const |-16| Int)
         (declare-const x Int)
         (assert (<= |-16| -16))
         (assert (let ((|-1| x)) (> |-1| -1)))
         (assert (forall ((|-3| Int)) (> (+ |-3| x) -3)))",
    )
    .expect("fixture parses");
    let echoes: Vec<String> = commands
        .iter()
        .filter_map(|command| match command {
            ay_frontend::Command::Assert(term) => Some(format_authored_frontend_term(term)),
            _ => None,
        })
        .collect();
    assert_eq!(
        echoes,
        [
            "(<= |-16| -16)",
            "(let ((|-1| x)) (> |-1| -1))",
            "(forall ((|-3| Int)) (> (+ |-3| x) -3))",
        ]
    );
}

/// a10: `(= x -2)` with `x` Real. A bare Int numeral in a Real position is
/// echoed as the decimal `-2.0`, as `2` is echoed `2.0`; pinned Carcara reads
/// `-2` there as an Int and refused the document with a sort error.
#[test]
fn a_negative_numeral_in_a_real_position_is_echoed_as_a_decimal() {
    let mut ctx = Context::new();
    let commands = ay_frontend::parse(
        "(set-logic QF_LRA) (declare-const x Real) (assert (= x -2)) (assert (<= -3 x))",
    )
    .expect("fixture parses");
    let mut echoes = Vec::new();
    for command in &commands {
        ctx.process_command(command).expect("fixture elaborates");
        if let ay_frontend::Command::Assert(term) = command {
            let echo = realify_real_context_numerals(&mut ctx, term, false, &mut Vec::new());
            echoes.push(format_frontend_term(&echo));
        }
    }
    assert_eq!(echoes, ["(= x -2.0)", "(<= -3.0 x)"]);
}
