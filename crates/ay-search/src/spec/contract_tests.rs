// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included in `spec::tests`; every helper must remain directly test-only.

#[test]
fn search_spec_structural_parse_defers_semantic_validation_to_build() {
    let unsupported = SearchSpec::from_json(r#"{"version":2,"variables":[]}"#)
        .expect("version is a semantic, not structural, concern");
    assert!(matches!(
        unsupported.build(),
        Err(SearchError::UnsupportedVersion(2))
    ));

    let zero_timeout =
        SearchSpec::from_json(r#"{"version":1,"variables":[],"limits":{"timeout_ms":0}}"#)
            .expect("zero is structurally an unsigned integer");
    assert!(matches!(
        zero_timeout.build(),
        Err(SearchError::InvalidLimit {
            name: "timeout_ms",
            value: 0,
        })
    ));

    let zero_solutions =
        SearchSpec::from_json(r#"{"version":1,"variables":[],"limits":{"max_solutions":0}}"#)
            .expect("zero is structurally an unsigned integer");
    assert!(matches!(
        zero_solutions.build(),
        Err(SearchError::InvalidLimit {
            name: "max_solutions",
            value: 0,
        })
    ));
}

#[test]
fn search_spec_v1_rejects_unknown_and_mixed_variant_fields() {
    for document in [
        r#"{"version":1,"variables":[],"unknown":true}"#,
        r#"{"version":1,"variables":[{"name":"x","domain":{"min":0,"max":1},"unknown":true}]}"#,
        r#"{"version":1,"variables":[{"name":"x","domain":{"min":0,"max":1,"unknown":true}}]}"#,
        r#"{"version":1,"variables":[{"name":"x","domain":{"min":0,"max":1,"values":[0]}}]}"#,
        r#"{"version":1,"variables":[],"constraints":[{"table":{"variables":[],"tuples":[],"unknown":true}}]}"#,
        r#"{"version":1,"variables":[],"constraints":[{"element":{"index":"i","array":[],"result":"r","unknown":true}}]}"#,
        r#"{"version":1,"variables":[],"objective":{"sense":"minimize","expression":"0","unknown":true}}"#,
        r#"{"version":1,"variables":[],"limits":{"timeout_ms":1,"unknown":true}}"#,
    ] {
        assert!(
            matches!(SearchSpec::from_json(document), Err(SearchError::Json(_))),
            "accepted strict-v1 violation: {document}"
        );
    }
}

#[test]
fn search_spec_v1_defaults_and_full_wire_shapes_are_stable() {
    let minimal = SearchSpec::from_json(r#"{"version":1,"variables":[]}"#).unwrap();
    assert_eq!(
        serde_json::to_value(&minimal).unwrap(),
        serde_json::json!({"version": 1, "variables": []})
    );

    let full = SearchSpec {
        version: 1,
        name: Some("contract".to_owned()),
        variables: vec![
            VariableSpec {
                name: "index".to_owned(),
                domain: DomainSpec::Interval { min: 0, max: 1 },
                labels: BTreeMap::new(),
            },
            VariableSpec {
                name: "choice".to_owned(),
                domain: DomainSpec::Values { values: vec![2, 4] },
                labels: BTreeMap::from([(2, "two".to_owned())]),
            },
            VariableSpec {
                name: "result".to_owned(),
                domain: DomainSpec::Interval { min: 0, max: 4 },
                labels: BTreeMap::new(),
            },
        ],
        constraints: vec![
            ConstraintSpec::Expression {
                expression: "result >= 0".to_owned(),
            },
            ConstraintSpec::AllDifferent {
                all_different: vec!["index".to_owned(), "result".to_owned()],
            },
            ConstraintSpec::Table {
                table: TableSpec {
                    variables: vec!["index".to_owned(), "result".to_owned()],
                    tuples: vec![vec![0, 2], vec![1, 4]],
                },
            },
            ConstraintSpec::Element {
                element: ElementSpec {
                    index: "index".to_owned(),
                    array: vec!["choice".to_owned(), "result".to_owned()],
                    result: "result".to_owned(),
                },
            },
        ],
        objective: Some(ObjectiveSpec {
            sense: ObjectiveSense::Maximize,
            expression: "result".to_owned(),
        }),
        limits: Some(LimitsSpec {
            timeout_ms: Some(25),
            max_solutions: None,
        }),
    };
    let encoded = serde_json::to_value(&full).unwrap();
    assert_eq!(encoded["variables"][1]["labels"]["2"], "two");
    assert_eq!(encoded["objective"]["sense"], "maximize");
    assert!(encoded["limits"].get("max_solutions").is_none());
    let decoded: SearchSpec = serde_json::from_value(encoded).unwrap();
    decoded.build().expect("all version-1 wire shapes build");
}

#[test]
fn search_run_result_serialization_has_no_variant_wrapper() {
    assert_eq!(
        serde_json::to_value(SearchRunResult::Solve(SolveResult::Unsat)).unwrap(),
        serde_json::json!({"status": "unsat"})
    );
}
