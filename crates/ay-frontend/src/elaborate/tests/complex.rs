// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn complex_ground_arithmetic_elaborates_to_exact_truths() {
    let input = r#"
        (set-logic ALL)
        (assert (= (* (complex.make 1 2) (complex.make 1 2)) (complex.make (- 3) 4)))
        (assert (= (/ (complex.make 1 2) (complex.make 3 (- 4)))
                   (complex.make (/ (- 1) 5) (/ 2 5))))
        (assert (= (+ 2 (complex.make 1 2) 3) (complex.make 6 2)))
        (assert (= (- (complex.make 1 2)) (complex.make (- 1) (- 2))))
        (assert (= (complex.real (complex.make 2 3)) 2))
        (assert (= (complex.imag (complex.make 2 3)) 3))
        (assert (= (complex.real 5) 5))
        (assert (= (complex.imag 5) 0))
        (assert (= (complex.make 1 0) 1))
        (assert (= (ite true 1 (complex.make 2 3)) (complex.make 1 0)))
    "#;
    let mut ctx = Context::new();
    for command in parse(input).unwrap() {
        ctx.process_command(&command).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 10);
    for &assertion in &ctx.assertions {
        assert_eq!(
            assertion,
            ctx.terms.true_term(),
            "{:?}",
            ctx.terms.get(assertion)
        );
    }
}

#[test]
fn complex_symbolic_components_and_nested_sorts_are_typed() {
    let input = r#"
        (declare-const z Complex)
        (declare-const a (Array Int Complex))
        (assert (= z (complex.make (complex.real z) (complex.imag z))))
        (assert (= (+ z 2) (select a 0)))
        (assert (= (complex.real (* z z)) 0))
    "#;
    let mut ctx = Context::new();
    for command in parse(input).unwrap() {
        ctx.process_command(&command).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 3);
    assert!(ctx
        .assertions
        .iter()
        .all(|&term| ctx.terms.sort(term) == &Sort::Bool));
}

#[test]
fn complex_invalid_operands_and_unavailable_logic_are_rejected() {
    for expression in [
        "(complex.make true 0)",
        "(complex.make 1)",
        "(complex.real true)",
        "(complex.imag (complex.make 1 2) 0)",
        "(+ true (complex.make 1 2))",
        "(< (complex.make 1 2) (complex.make 2 3))",
        "(^ (complex.make 1 2) 2)",
    ] {
        let mut ctx = Context::new();
        let input = format!("(assert (= {expression} 0))");
        assert!(
            ctx.process_command(&parse(&input).unwrap()[0]).is_err(),
            "{expression}"
        );
    }
    let mut ctx = Context::new();
    ctx.set_z3_mode(true);
    let commands = parse("(set-logic QF_LRA) (declare-const z Complex)").unwrap();
    ctx.process_command(&commands[0]).unwrap();
    assert!(ctx.process_command(&commands[1]).is_err());
}

#[test]
fn complex_coercions_respect_the_existing_option() {
    let mut ctx = Context::new();
    let commands = parse(
        r#"
        (set-option :int-real-coercions false)
        (assert (= (complex.make 1.0 2.0) (complex.make 1.0 2.0)))
        (assert (= (complex.make 1 2) (complex.make 1.0 2.0)))
        (assert (= (complex.real 1) 1))
    "#,
    )
    .unwrap();
    ctx.process_command(&commands[0]).unwrap();
    ctx.process_command(&commands[1]).unwrap();
    assert!(ctx.process_command(&commands[2]).is_err());
    assert!(ctx.process_command(&commands[3]).is_err());
}
