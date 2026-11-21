// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{Budget, Executor};
use ay_core::kani_compat::DetHashMap;
use ay_core::{Sort, Symbol};
use num_bigint::BigInt;
use num_rational::BigRational;

#[test]
fn datatype_problem_repeated_override_is_priced_before_printing() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_var("shared-override", Sort::Int);
    let root = exec
        .ctx
        .terms
        .mk_app(Symbol::named("repeated-head"), vec![x; 64], Sort::Bool);
    let mut overrides = DetHashMap::default();
    overrides.insert(x, "x".repeat(128 * 1024));
    assert!(exec
        .datatype_transport_print_footprint(root, &overrides, &mut Budget::default())
        .is_none());
}

#[test]
fn datatype_problem_decimal_work_refuses_large_int_and_rational_before_display() {
    let mut exec = Executor::new();
    let huge = BigInt::from(1) << 100_000usize;
    let integer = exec.ctx.terms.mk_int(huge.clone());
    let rational = exec
        .ctx
        .terms
        .mk_rational(BigRational::new(huge, BigInt::from(3)));
    for root in [integer, rational] {
        assert!(exec
            .datatype_transport_print_footprint(
                root,
                &DetHashMap::default(),
                &mut Budget::default()
            )
            .is_none());
    }
}

#[test]
fn datatype_problem_tester_override_requires_exact_registered_domain() {
    let mut exec = Executor::new();
    exec.execute_all(
        &ay_frontend::parse("(declare-datatype ExactChoice ((exact-left) (exact-right)))")
            .expect("syntax"),
    )
    .expect("declaration");
    let wrong = exec.ctx.terms.mk_var("wrong-sort", Sort::Int);
    exec.ctx
        .terms
        .mk_app(Symbol::named("is-exact-left"), [wrong], Sort::Bool);
    assert!(exec.datatype_problem_spelling_overrides(None).is_none());
}

#[test]
fn datatype_problem_does_not_replace_opaque_authored_tester_spelling() {
    let mut exec = Executor::new();
    exec.execute_all(&ay_frontend::parse("(declare-datatype OpaqueChoice ((opaque-left) (opaque-right))) (declare-const c OpaqueChoice) (assert (is-opaque-left c))").expect("syntax")).expect("source");
    let root = exec.ctx.assertions[0];
    let mut source = DetHashMap::default();
    source.insert(root, "(is-opaque-left c)".to_owned());
    assert!(exec
        .datatype_problem_spelling_overrides(Some(&source))
        .is_none());
}

#[test]
fn datatype_problem_mutual_recursion_round_trips_as_datatype_metadata() {
    let mut exec = Executor::new();
    let source = "(declare-datatypes ((Even 0) (Odd 0))
        (((even-zero) (even-next (next-odd Odd)))
         ((odd-next (next-even Even)))))";
    exec.execute_all(&ay_frontend::parse(source).expect("syntax"))
        .expect("datatypes");
    let problem = exec
        .alethe_problem_smt2_for(&[], None)
        .expect("complete simultaneous datatype group");
    let mut decoded = Executor::new();
    decoded
        .execute_all(&ay_frontend::parse(&problem).expect("transport syntax"))
        .expect("transport semantics");
    for (constructor, field, range) in [
        ("even-next", "next-odd", "Odd"),
        ("odd-next", "next-even", "Even"),
    ] {
        let signature = decoded
            .ctx
            .constructor_selector_info(constructor)
            .expect("interpreted selector");
        assert_eq!(
            signature,
            &[(field.to_owned(), Sort::Uninterpreted(range.to_owned()))]
        );
    }
}
