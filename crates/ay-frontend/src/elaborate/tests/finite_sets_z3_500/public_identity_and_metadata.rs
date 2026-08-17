// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `elaborate::tests::finite_sets_z3_500` to preserve test FQNs.

#[test]
fn z3_500_native_alias_can_upgrade_to_an_exact_public_signature() {
    let mut context = Context::new();
    context.set_finite_set_typing_mode(FiniteSetTypingMode::Z3_5Strict);
    let engine_finite_set = Sort::array(Sort::Int, Sort::Bool);
    context
        .register_native_function_alias(
            "native-pass".to_string(),
            "native-pass!0".to_string(),
            vec![engine_finite_set.clone()],
            engine_finite_set,
        )
        .expect("lowered native alias registers");
    let finite_set = PublicSort::FiniteSet(Box::new(PublicSort::Core(Sort::Int)));
    assert!(context
        .register_native_public_function_alias(
            "native-pass".to_string(),
            "native-pass!0".to_string(),
            vec![finite_set.clone()],
            finite_set.clone(),
        )
        .expect("same native identity upgrades to exact public sorts"));

    let commands = parse(
        "(assert (= (native-pass (as set.empty (FiniteSet Int))) \
                    (as set.empty (FiniteSet Int))))",
    )
    .expect("native alias assertion parses");
    context
        .process_command(&commands[0])
        .expect("upgraded native alias participates in strict public typing");
    let signature = context
        .public_symbol_signatures()
        .into_iter()
        .find(|signature| signature.name == "native-pass")
        .expect("native alias signature");
    assert_eq!(signature.arguments, vec![finite_set.clone()]);
    assert_eq!(signature.result, finite_set);
}

#[test]
fn z3_500_native_alias_rejects_public_only_overload_distinctions() {
    let mut context = Context::new();
    let finite_set = PublicSort::FiniteSet(Box::new(PublicSort::Core(Sort::Int)));
    context
        .register_native_public_function_alias(
            "native-predicate".to_string(),
            "native-predicate!finite".to_string(),
            vec![finite_set],
            PublicSort::Core(Sort::Bool),
        )
        .expect("first exact native alias registers");
    let legacy_set = PublicSort::Array(
        Box::new(PublicSort::Core(Sort::Int)),
        Box::new(PublicSort::Core(Sort::Bool)),
    );
    assert!(matches!(
        context.register_native_public_function_alias(
            "native-predicate".to_string(),
            "native-predicate!legacy".to_string(),
            vec![legacy_set],
            PublicSort::Core(Sort::Bool),
        ),
        Err(ElaborateError::UnrepresentableOverload(_))
    ));
}

#[test]
fn z3_500_indexed_array_functions_mark_arbitrary_finite_set_values() {
    let context = elaborate_strict(
        r#"
        (declare-fun f (Int) (FiniteSet Int))
        (declare-fun g (Int) (FiniteSet Int))
        (declare-const a (Array Int Int))
        (assert
          (= (select (_ as-array f) 0)
             (as set.empty (FiniteSet Int))))
        (assert
          (= (select ((_ map g) a) 0)
             (as set.empty (FiniteSet Int))))
        "#,
    )
    .expect("indexed array functions returning FiniteSet elaborate");

    for metadata in context.assertion_finite_set_metadata() {
        assert!(
            metadata.finite_sets.has_arbitrary_value,
            "as-array/map values returned by an arbitrary function require the SAT gate"
        );
    }
}

#[test]
fn z3_500_map_empty_finite_set_default_marks_arbitrary_value() {
    let context = elaborate_strict(
        r#"
        (assert
          (= (select (as map.empty (Map Int (FiniteSet Int))) 0)
             (as set.empty (FiniteSet Int))))
        "#,
    )
    .expect("map.empty with a FiniteSet value sort elaborates");

    let metadata = &context.assertion_finite_set_metadata()[0].finite_sets;
    assert!(metadata.uses_finite_set);
    assert!(
        metadata.has_arbitrary_value,
        "map.empty's observable fresh FiniteSet default requires the SAT gate"
    );
}

#[test]
fn z3_500_nested_set_operations_mark_finite_set_binders() {
    let context = elaborate_strict(
        r#"
        (declare-const ss (FiniteSet (FiniteSet Int)))
        (declare-const s (FiniteSet Int))
        (declare-const p (Array (FiniteSet Int) Bool))
        (declare-const domain-map (Array (FiniteSet Int) Int))
        (declare-const image-map (Array Int (FiniteSet Int)))
        (assert (set.subset ss ss))
        (assert (= (set.filter p ss) ss))
        (assert
          (= (set.map domain-map ss)
             (as set.empty (FiniteSet Int))))
        (assert
          (= (set.map image-map s)
             (as set.empty (FiniteSet (FiniteSet Int)))))
        "#,
    )
    .expect("nested FiniteSet subset/filter/map terms elaborate");

    for metadata in context.assertion_finite_set_metadata() {
        assert!(
            metadata.finite_sets.has_finite_set_binder,
            "a nested FiniteSet domain or image requires the binder-aware SAT gate"
        );
    }
}

#[test]
fn z3_500_strict_rejects_unrepresentable_finite_set_surfaces() {
    for input in [
        "(declare-datatype Box ((box (value (FiniteSet Int)))))",
        "(declare-const s (FiniteSet Int)) (assert (= (set.map s s) s))",
        "(declare-const s (FiniteSet Int)) (assert (= (set.filter s s) s))",
        "(declare-fun f ((FiniteSet Int)) Bool) \
         (declare-fun f ((Set Int)) Bool)",
        "(declare-const fs (FiniteSet Int)) (declare-const ls (Set Int)) \
         (assert (seq.contains (seq.unit fs) (seq.unit ls)))",
        "(declare-const fs (FiniteSet Int)) \
         (assert (= (seq.extract (seq.unit fs) true 1) (seq.unit fs)))",
        "(declare-const fs (FiniteSet Int)) (assert (= (seq.len fs) 0))",
        "(assert
           (= (as seq.empty (Seq (FiniteSet Int)))
              (as seq.empty (Seq (FiniteSet Int)))))",
    ] {
        assert!(
            elaborate_strict(input).is_err(),
            "unsupported FiniteSet surface must fail closed: {input}"
        );
    }
}

#[test]
fn z3_500_numeric_metadata_tracks_promotions_and_conversions() {
    let context = elaborate_strict(
        r#"
        (declare-const fs (FiniteSet Int))
        (assert (= (+ (set.size fs) 0.5) 0.5))
        (assert (= (to_real (set.size fs)) 0.5))
        (assert (= (to_int (+ (to_real (set.size fs)) 0.5)) (set.size fs)))
        (assert (= (ite true (set.size fs) 0.5) 0.5))
        "#,
    )
    .expect("numeric promotion around finite-set cardinality is well-sorted");

    for assertion in 0..4 {
        let root = context.assertion_finite_set_metadata()[assertion]
            .root
            .as_ref()
            .expect("finite-set arithmetic assertion metadata");
        assert_eq!(
            root.arguments[0].public_sort,
            if assertion == 2 {
                PublicSort::Core(Sort::Int)
            } else {
                PublicSort::Core(Sort::Real)
            },
            "numeric result public sort for assertion {assertion}"
        );
    }
}

#[test]
fn z3_500_quantifier_metadata_retains_public_binder_sorts() {
    let context = elaborate_strict(
        r#"
        (assert
          (forall ((fs (FiniteSet Int)) (nested (FiniteSet (FiniteSet Int))))
            true))
        "#,
    )
    .expect("binder-only finite-set quantifier elaborates");
    let root = context.assertion_finite_set_metadata()[0]
        .root
        .as_ref()
        .expect("quantifier metadata");

    assert_eq!(
        root.public_bound_sorts,
        vec![
            PublicSort::FiniteSet(Box::new(PublicSort::Core(Sort::Int))),
            PublicSort::FiniteSet(Box::new(PublicSort::FiniteSet(Box::new(PublicSort::Core(
                Sort::Int
            ))))),
        ]
    );
    assert!(
        context.assertion_finite_set_metadata()[0]
            .finite_sets
            .has_finite_set_binder
    );
}

#[test]
fn z3_500_strict_rejects_unretained_public_ast_expansions() {
    for input in [
        "(assert (= (let ((s (as set.empty (FiniteSet Int)))) s) \
                    (as set.empty (FiniteSet Int))))",
        "(assert (forall ((s (FiniteSet Int))) (= s s)))",
        "(assert (= (lambda ((s (FiniteSet Int))) s) \
                    (lambda ((s (FiniteSet Int))) s)))",
        "(define-fun e () (FiniteSet Int) (as set.empty (FiniteSet Int))) \
         (assert (= e e))",
        "(declare-datatypes ((Box 0)) (((mk (value Int))))) \
         (declare-const b Box) \
         (assert (match b (((mk x) (set.in x (set.singleton x))))))",
    ] {
        assert!(
            elaborate_strict(input).is_err(),
            "shape whose expanded body identity is unavailable must fail closed: {input}"
        );
    }
}

#[test]
fn z3_500_strict_rejects_unretained_finite_set_trigger_annotations() {
    for input in [
        "(assert
           (forall ((x Int))
             (! true :pattern ((set.in x (set.singleton x))))))",
        "(assert
           (forall ((s (FiniteSet Int)))
             (! true :pattern ((set.size s)))))",
        "(assert
           (forall ((s (FiniteSet Int)))
             (! true :no-pattern (set.size s))))",
    ] {
        assert!(
            elaborate_strict(input).is_err(),
            "FiniteSet trigger identity must fail closed until annotations are retained: {input}"
        );
    }
}

#[test]
fn z3_500_strict_preserves_ordinary_non_finite_set_annotations() {
    elaborate_strict(
        r#"
        (declare-fun p (Int) Bool)
        (assert (forall ((x Int)) (! (p x) :pattern ((p x)))))
        (assert (! true :named ordinary))
        "#,
    )
    .expect("ordinary pattern and named annotations remain available");
}

#[test]
fn z3_500_shared_constructor_occurrences_resolve_from_their_mode_and_use_site() {
    let strict =
        elaborate_strict("(declare-const fs (FiniteSet Int)) (assert (= fs (set.singleton 1)))")
            .expect("strict singleton is FiniteSet");
    let strict_singleton = &strict.assertion_finite_set_metadata()[0]
        .root
        .as_ref()
        .expect("strict metadata")
        .arguments[1];
    assert!(matches!(
        strict_singleton.public_sort,
        PublicSort::FiniteSet(_)
    ));

    let legacy = elaborate("(declare-const s (Set Int)) (assert (= s (set.singleton 1)))");
    let legacy_singleton = &legacy.assertion_finite_set_metadata()[0]
        .root
        .as_ref()
        .expect("legacy assertion still carries set occurrence metadata")
        .arguments[1];
    assert!(matches!(
        legacy_singleton.public_sort,
        PublicSort::Array(_, _)
    ));
}
