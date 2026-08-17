// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Focused Z3 5.0.0 textual `FiniteSet` surface and ground-semantics tests.

use super::*;

fn elaborate(input: &str) -> Context {
    let commands = parse(input).expect("finite-set script parses");
    let mut context = Context::new();
    for command in &commands {
        context
            .process_command(command)
            .expect("finite-set command elaborates");
    }
    context
}

fn elaborate_strict(input: &str) -> Result<Context> {
    let commands = parse(input).expect("finite-set script parses");
    let mut context = Context::new();
    context.set_finite_set_typing_mode(FiniteSetTypingMode::Z3_5Strict);
    for command in &commands {
        context.process_command(command)?;
    }
    Ok(context)
}

fn contains_named_app(terms: &TermStore, root: TermId, needle: &str) -> bool {
    match terms.get(root) {
        TermData::App(Symbol::Named(name), args) => {
            name == needle
                || args
                    .iter()
                    .any(|&arg| contains_named_app(terms, arg, needle))
        }
        TermData::App(_, args) => args
            .iter()
            .any(|&arg| contains_named_app(terms, arg, needle)),
        TermData::Not(inner) => contains_named_app(terms, *inner, needle),
        TermData::Ite(condition, then_term, else_term) => {
            contains_named_app(terms, *condition, needle)
                || contains_named_app(terms, *then_term, needle)
                || contains_named_app(terms, *else_term, needle)
        }
        TermData::Let(bindings, body) => {
            bindings
                .iter()
                .any(|(_, value)| contains_named_app(terms, *value, needle))
                || contains_named_app(terms, *body, needle)
        }
        TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
            contains_named_app(terms, *body, needle)
                || triggers
                    .iter()
                    .flatten()
                    .any(|&trigger| contains_named_app(terms, trigger, needle))
        }
        _ => false,
    }
}

#[test]
fn z3_500_finite_set_sort_lowers_recursively_and_routes_set_theory() {
    let context = elaborate(
        r#"
        (declare-const s (FiniteSet Int))
        (declare-const nested (FiniteSet (FiniteSet Int)))
        (assert (= s (as set.empty (FiniteSet Int))))
        (assert (= nested (set.singleton s)))
        "#,
    );

    let set_sort = Sort::array(Sort::Int, Sort::Bool);
    assert_eq!(context.symbols["s"].sort, set_sort);
    assert_eq!(
        context.symbols["nested"].sort,
        Sort::array(set_sort, Sort::Bool)
    );
    assert!(context.uses_set());
}

#[test]
fn z3_500_ground_constructor_algebra_is_exact() {
    let context = elaborate(
        r#"
        (assert (set.in 1 (set.singleton 1)))
        (assert (not (set.in 2 (set.singleton 1))))
        (assert (set.in 1 (set.union (set.singleton 1) (set.singleton 2))))
        (assert (set.in 2 (set.union (set.singleton 1) (set.singleton 2))))
        (assert
          (= (set.intersect
               (set.union (set.singleton 1) (set.singleton 2))
               (set.singleton 1))
             (set.singleton 1)))
        (assert
          (= (set.difference
               (set.union (set.singleton 1) (set.singleton 2))
               (set.singleton 1))
             (set.singleton 2)))
        "#,
    );

    assert_eq!(context.assertions.len(), 6);
    assert!(
        context
            .assertions
            .iter()
            .all(|&assertion| context.terms.is_true(assertion)),
        "every ground Z3 5 finite-set constructor law should fold to true"
    );
}

#[test]
fn z3_500_array_plugin_legacy_set_aliases_share_exact_set_semantics() {
    let context = elaborate(
        r#"
        (define-fun empty () (Set Int) ((as const (Set Int)) false))
        (define-fun one () (Set Int) (store empty 1 true))
        (define-fun two () (Set Int) (store empty 2 true))
        (assert (select (union one two) 2))
        (assert (not (select (intersection one two) 1)))
        (assert (select (setminus (union one two) two) 1))
        (assert (not (select (complement one) 1)))
        (assert (subset one (union one two)))
        "#,
    );

    assert_eq!(context.assertions.len(), 5);
    assert!(
        context
            .assertions
            .iter()
            .all(|&assertion| context.terms.is_true(assertion)),
        "legacy array-plugin set operations must reduce through the canonical set implementation"
    );
    assert!(context.uses_set());
}

#[test]
fn z3_500_ground_legacy_subset_can_be_refuted_exactly() {
    let context = elaborate(
        r#"
        (define-fun empty () (Set Int) ((as const (Set Int)) false))
        (define-fun one () (Set Int) (store empty 1 true))
        (define-fun two () (Set Int) (store empty 2 true))
        (assert (not (subset one two)))
        "#,
    );

    assert_eq!(context.assertions.len(), 1);
    assert!(context.terms.is_true(context.assertions[0]));
}

#[test]
fn z3_500_symbolic_legacy_set_reads_use_exact_pointwise_semantics() {
    let context = elaborate(
        r#"
        (declare-const s (Set Int))
        (declare-const t (Set Int))
        (assert (= (select (union s t) 0)
                   (or (select s 0) (select t 0))))
        (assert (= (select (intersection s t) 0)
                   (and (select s 0) (select t 0))))
        (assert (= (select (setminus s t) 0)
                   (and (select s 0) (not (select t 0)))))
        (assert (= (select (complement s) 0)
                   (not (select s 0))))
        "#,
    );

    assert_eq!(context.assertions.len(), 4);
    assert!(context
        .assertions
        .iter()
        .all(|&assertion| context.terms.is_true(assertion)));
}

#[test]
fn z3_500_inclusive_literal_range_has_exact_empty_singleton_membership_and_size_shape() {
    let context = elaborate(
        r#"
        (assert (= (set.range 4 3) (as set.empty (FiniteSet Int))))
        (assert (= (set.range 3 3) (set.singleton 3)))
        (assert (set.in 3 (set.range 1 3)))
        (assert (not (set.in 4 (set.range 1 3))))
        (assert (= (set.size (set.range 1 3)) 3))
        "#,
    );

    assert!(
        context.assertions[..4]
            .iter()
            .all(|&assertion| context.terms.is_true(assertion)),
        "literal range constructor and membership laws should fold exactly"
    );
    assert!(
        contains_named_app(&context.terms, context.assertions[4], "set.card"),
        "Z3 set.size must route to the native exact-cardinality node"
    );
    assert!(
        !contains_named_app(&context.terms, context.assertions[4], "set.range"),
        "small literal range must be a covered store chain, not an opaque range"
    );
}

#[test]
fn z3_500_ground_map_and_filter_reuse_exact_array_semantics() {
    let context = elaborate(
        r#"
        (assert
          (set.in 2
            (set.map (lambda ((x Int)) (+ x 1)) (set.singleton 1))))
        (assert
          (set.in 2
            (set.filter
              (lambda ((x Int)) (> x 1))
              (set.union (set.singleton 1) (set.singleton 2)))))
        (assert
          (not
            (set.in 1
              (set.filter
                (lambda ((x Int)) (> x 1))
                (set.union (set.singleton 1) (set.singleton 2))))))
        "#,
    );

    assert!(
        context
            .assertions
            .iter()
            .all(|&assertion| context.terms.is_true(assertion)),
        "ground map/filter laws should beta-reduce and fold to true"
    );
}

#[test]
fn z3_500_symbolic_pointwise_ops_are_exact_and_image_ops_remain_fail_closed() {
    let context = elaborate(
        r#"
        (declare-const s (FiniteSet Int))
        (declare-const t (FiniteSet Int))
        (declare-const f (Array Int Int))
        (declare-const p (Array Int Bool))
        (declare-const lo Int)
        (declare-const hi Int)
        (assert (set.in 0 (set.union s t)))
        (assert (set.in 0 (set.intersect s t)))
        (assert (set.in 0 (set.difference s t)))
        (assert (set.in 0 (set.map f s)))
        (assert (set.in 0 (set.filter p s)))
        (assert (set.in 0 (set.range lo hi)))
        "#,
    );

    for (assertion, operator) in context.assertions[..3].iter().copied().zip([
        "set.union",
        "set.intersect",
        "set.difference",
    ]) {
        assert!(
            !contains_named_app(&context.terms, assertion, operator),
            "symbolic pointwise `{operator}` must lower to exact characteristic-array semantics"
        );
        assert!(
            contains_named_app(&context.terms, assertion, "select"),
            "symbolic pointwise `{operator}` must preserve reads of its source sets"
        );
    }

    for (assertion, operator) in
        context.assertions[3..]
            .iter()
            .copied()
            .zip(["set.map", "set.filter", "set.range"])
    {
        assert!(
            contains_named_app(&context.terms, assertion, operator),
            "symbolic `{operator}` must remain visible to the fail-closed set gate"
        );
    }
}

#[test]
fn z3_500_finite_set_arity_and_sort_errors_are_rejected() {
    for input in [
        "(declare-const s (FiniteSet Int Bool))",
        "(declare-const s (FiniteSet Int)) (assert (set.in true s))",
        "(declare-const s (FiniteSet Int)) (assert (= (set.union s) s))",
        "(declare-const s (FiniteSet Int)) (assert (= (set.intersect s) s))",
        "(declare-const s (FiniteSet Int)) (assert (= (set.difference s s s) s))",
        "(assert (= (set.size 1) 0))",
        "(declare-const s (FiniteSet Int)) (declare-const f (Array Bool Int)) \
         (assert (= (set.map f s) s))",
        "(declare-const s (FiniteSet Int)) (declare-const p (Array Int Int)) \
         (assert (= (set.filter p s) s))",
        "(assert (= (set.range 0.0 1.0) (as set.empty (FiniteSet Int))))",
    ] {
        let commands = parse(input).expect("ill-sorted finite-set script still parses");
        let mut context = Context::new();
        let result = commands
            .iter()
            .try_for_each(|command| context.process_command(command).map(|_| ()));
        assert!(
            result.is_err(),
            "expected elaboration rejection for: {input}"
        );
    }
}

#[test]
fn z3_500_finite_set_sort_and_operator_names_are_reserved() {
    for input in [
        "(declare-sort FiniteSet 0)",
        "(define-sort FiniteSet (T) (Array T Bool))",
        "(declare-datatype FiniteSet ((mk-finite-set)))",
    ] {
        let commands = parse(input).expect("reserved-sort probe parses");
        let mut context = Context::new();
        assert!(
            matches!(
                context.process_command(&commands[0]),
                Err(ElaborateError::ReservedSymbol(_))
            ),
            "builtin FiniteSet sort constructor must reject redeclaration: {input}"
        );
    }

    for operator in [
        "set.in",
        "set.size",
        "set.intersect",
        "set.difference",
        "set.map",
        "set.filter",
        "set.range",
    ] {
        assert!(
            is_reserved_op_name(operator),
            "Z3 5 finite-set builtin `{operator}` must be reserved"
        );
    }
}

#[test]
fn z3_500_strict_public_identity_rejects_array_conflation() {
    for input in [
        "(declare-const f (FiniteSet Int)) (declare-const a (Array Int Bool)) (assert (= f a))",
        "(declare-const f (FiniteSet Int)) (declare-const a (Set Int)) (assert (distinct f a))",
        "(declare-const f (FiniteSet Int)) (declare-const a (Array Int Bool)) \
         (declare-const c Bool) (assert (= (ite c f a) f))",
        "(declare-const f (FiniteSet Int)) (assert (select f 0))",
        "(declare-const f (FiniteSet Int)) (assert (= (store f 0 true) f))",
    ] {
        assert!(
            elaborate_strict(input).is_err(),
            "strict Z3 5 public typing must reject: {input}"
        );
    }
}

#[test]
fn z3_500_strict_nested_finite_sets_and_finite_set_array_indices_are_valid() {
    let context = elaborate_strict(
        r#"
        (declare-const s (FiniteSet Int))
        (declare-const ss (FiniteSet (FiniteSet Int)))
        (declare-const a (Array (FiniteSet Int) Int))
        (assert (= ss (set.singleton s)))
        (assert (= (select a s) (select a (as set.empty (FiniteSet Int)))))
        "#,
    )
    .expect("Z3 5 accepts nested FiniteSet identity and FiniteSet array indices");

    assert_eq!(context.assertions.len(), 2);
    assert_eq!(
        context.symbols["ss"].public_sort,
        PublicSort::FiniteSet(Box::new(PublicSort::FiniteSet(Box::new(PublicSort::Core(
            Sort::Int
        )))))
    );
}

#[test]
fn z3_500_strict_shared_set_operators_are_finite_set_only() {
    for input in [
        "(declare-const s (Set Int)) (assert (= s (set.singleton 1)))",
        "(declare-const s (Set Int)) (assert (= s (as set.empty (Set Int))))",
        "(declare-const s (Set Int)) (assert (= s (set.union s s)))",
        "(declare-const s (Set Int)) (assert (set.subset s s))",
        "(assert (= ((as const (FiniteSet Int)) false) (as set.empty (FiniteSet Int))))",
    ] {
        assert!(
            elaborate_strict(input).is_err(),
            "strict Z3 5 shared operator must reject legacy/array use: {input}"
        );
    }

    // AY's established non-Z3 textual extension remains available only in the
    // default compatibility mode.
    elaborate(
        r#"
        (declare-const s (Set Int))
        (assert (= s (set.singleton 1)))
        (assert (= s (as set.empty (Set Int))))
        "#,
    );
}

#[test]
fn z3_500_occurrence_metadata_survives_lowered_empty_carrier_collision() {
    let context = elaborate_strict(
        r#"
        (declare-const fs (FiniteSet Int))
        (declare-const a (Array Int Bool))
        (assert
          (and
            (= fs (as set.empty (FiniteSet Int)))
            (= a ((as const (Array Int Bool)) false))))
        "#,
    )
    .expect("mixed public carriers remain separately well-sorted");
    let root = context.assertion_finite_set_metadata()[0]
        .root
        .as_ref()
        .expect("FiniteSet assertion has occurrence metadata");
    let finite_empty = &root.arguments[0].arguments[1];
    let legacy_empty = &root.arguments[1].arguments[1];
    assert_eq!(finite_empty.finite_set_op, Some(FiniteSetOp::Empty));
    assert!(matches!(finite_empty.public_sort, PublicSort::FiniteSet(_)));
    assert!(matches!(legacy_empty.public_sort, PublicSort::Array(_, _)));
    assert_eq!(
        finite_empty.engine_term, legacy_empty.engine_term,
        "the regression must exercise an actual lowered TermId collision"
    );
}

#[test]
fn z3_500_public_identity_flows_through_aliases_and_declared_functions() {
    let context = elaborate_strict(
        r#"
        (define-sort FSInt () (FiniteSet Int))
        (declare-fun pass (FSInt) FSInt)
        (declare-const s FSInt)
        (assert (= (pass s) s))
        "#,
    )
    .expect("public FiniteSet identity survives aliases and declared applications");

    let signature = context
        .public_symbol_signatures()
        .into_iter()
        .find(|signature| signature.name == "pass")
        .expect("pass signature");
    assert!(matches!(
        signature.result,
        PublicSort::FiniteSet(ref element)
            if matches!(element.as_ref(), PublicSort::Core(Sort::Int))
    ));
    assert!(
        context.assertion_finite_set_metadata()[0]
            .finite_sets
            .has_arbitrary_value
    );
}

include!("finite_sets_z3_500/public_identity_and_metadata.rs");
