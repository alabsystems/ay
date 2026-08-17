// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `elaborate::tests::numerics` to preserve test FQNs.

/// `(^ x 2)` with a non-literal base must unfold to a product in the base's
/// sort (Real here). After unfolding, neither side of the resulting
/// comparison should contain a raw `^` application — it must have been
/// rewritten into `*`.
#[test]
fn test_elaborate_power_variable_base_small_exp() {
    let input = r#"
        (set-logic QF_NRA)
        (declare-const x Real)
        (assert (>= (^ x 2) 0.0))
    "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
    // The top-level assertion is a (possibly normalized) comparison. Walk
    // it to ensure no sub-term is a raw `^` application.
    fn contains_pow(terms: &TermStore, t: TermId) -> bool {
        match terms.get(t) {
            TermData::App(Symbol::Named(name), args) if name == "^" => true,
            TermData::App(_, args) => args.iter().any(|&a| contains_pow(terms, a)),
            TermData::Ite(c, th, el) => {
                contains_pow(terms, *c) || contains_pow(terms, *th) || contains_pow(terms, *el)
            }
            TermData::Not(inner) => contains_pow(terms, *inner),
            TermData::Let(bindings, body) => {
                bindings.iter().any(|(_, v)| contains_pow(terms, *v)) || contains_pow(terms, *body)
            }
            _ => false,
        }
    }
    assert!(
        !contains_pow(&ctx.terms, ctx.assertions[0]),
        "literal-integer exponent must be unfolded to *, not left as ^"
    );
}

/// A surviving symbolic or non-integral `^` must fail closed. Encoding it as
/// an uninterpreted function is unsound when constraints determine the
/// exponent later (for example, `y = 2`).
#[test]
fn test_elaborate_power_unsupported_exponents_are_rejected() {
    for input in [
        r#"
            (set-logic QF_NRA)
            (declare-const x Real)
            (declare-const y Real)
            (assert (= 1.0 (^ x y)))
        "#,
        r#"
            (set-logic QF_NRA)
            (declare-const x Real)
            (assert (= 1.0 (^ x 0.5)))
        "#,
    ] {
        let commands = parse(input).unwrap();
        let mut ctx = Context::new();
        let error = commands
            .iter()
            .find_map(|command| ctx.process_command(command).err())
            .expect("unsupported exponent must be rejected");
        assert!(
            matches!(&error, ElaborateError::Unsupported(message) if message.contains('^')),
            "unexpected rejection for {input}: {error}"
        );
    }
}
