// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included in `spec::tests` to preserve existing test FQNs.
#[test]
fn hostile_unary_chain_is_bounded_without_recursion() {
    // Regression: a recursive parse_unary crashed at ~42k frames on a long
    // minus chain reaching the parser through the public C ABI. Unary
    // parsing is iterative, and resource caps now reject hostile chains.
    let mut model = Model::new();
    model.int_var("x", Domain::interval(0, 3).unwrap()).unwrap();
    let at_token_limit = format!("{}x", "-".repeat(MAX_EXPRESSION_TOKENS - 1));
    parse_linear_expression(&at_token_limit, &model).expect("token limit is inclusive");

    let too_many_tokens = format!("{}x", "-".repeat(MAX_EXPRESSION_TOKENS));
    assert!(matches!(
        parse_linear_expression(&too_many_tokens, &model),
        Err(SearchError::ExpressionLimit {
            resource: "token count",
            ..
        })
    ));

    let too_many_bytes = format!("{}x", "+".repeat(MAX_EXPRESSION_BYTES));
    assert!(matches!(
        parse_linear_expression(&too_many_bytes, &model),
        Err(SearchError::ExpressionLimit {
            resource: "input byte length",
            ..
        })
    ));
}

#[test]
fn hostile_paren_nesting_fails_closed_at_the_depth_limit() {
    let mut model = Model::new();
    model.int_var("x", Domain::interval(0, 3).unwrap()).unwrap();
    // At the limit: parses.
    let ok = format!(
        "{}x{}",
        "(".repeat(MAX_EXPR_DEPTH),
        ")".repeat(MAX_EXPR_DEPTH)
    );
    parse_linear_expression(&ok, &model).expect("nesting at the limit parses");
    // One past the limit: clean error, not a crash.
    let too_deep = format!(
        "{}x{}",
        "(".repeat(MAX_EXPR_DEPTH + 1),
        ")".repeat(MAX_EXPR_DEPTH + 1)
    );
    assert!(matches!(
        parse_linear_expression(&too_deep, &model),
        Err(SearchError::ExpressionLimit {
            resource: "parenthesis nesting depth",
            ..
        })
    ));
    // And absurd depth from hostile input: still just an error.
    let hostile = format!("{}x{}", "(".repeat(500_000), ")".repeat(500_000));
    assert!(matches!(
        parse_linear_expression(&hostile, &model),
        Err(SearchError::ExpressionLimit { .. })
    ));
}

#[test]
fn parser_rejects_nonlinear_and_injection_syntax() {
    let mut model = Model::new();
    model.int_var("x", Domain::interval(0, 3).unwrap()).unwrap();
    model.int_var("y", Domain::interval(0, 3).unwrap()).unwrap();

    assert!(matches!(
        parse_linear_expression("x * y", &model),
        Err(SearchError::NonlinearExpression)
    ));
    assert!(matches!(
        parse_linear_expression("x); (check-sat)", &model),
        Err(SearchError::ExpressionParse { .. })
    ));
}

#[test]
fn parser_does_not_launder_overflow_through_multiply_and_cancellation() {
    let max = i128::MAX;
    let json = format!(
        r#"{{
          "version":1,
          "variables":[{{"name":"x","domain":{{"min":1,"max":1}}}}],
          "constraints":[
            {{"expression":"(({max} + 1) * x) - ({max} * x) - x == 0"}}
          ]
        }}"#
    );
    assert!(matches!(
        SearchSpec::from_json(&json).unwrap().build(),
        Err(SearchError::ExpressionOverflow)
    ));
}

#[test]
fn json_round_trip_and_safe_equation_solve() {
    let json = r#"{
      "version": 1,
      "variables": [
        {"name":"x","domain":{"min":0,"max":10}},
        {"name":"y","domain":{"values":[1,3,8]}}
      ],
      "constraints": [{"expression":"2*x + y == 9"}]
    }"#;
    let spec = SearchSpec::from_json(json).unwrap();
    let rendered = serde_json::to_string(&spec).unwrap();
    let problem = SearchSpec::from_json(&rendered).unwrap().build().unwrap();
    let SearchRunResult::Solve(SolveResult::Sat(solution)) = problem.run().unwrap() else {
        panic!("expected SAT");
    };
    assert_eq!(solution.value("x"), Some(3));
    assert_eq!(solution.value("y"), Some(3));
}

#[test]
fn objective_and_enumeration_limit_are_rejected_as_conflicting_modes() {
    let json = r#"{
      "version":1,
      "variables":[{"name":"x","domain":{"min":0,"max":1}}],
      "objective":{"sense":"maximize","expression":"x"},
      "limits":{"max_solutions":2}
    }"#;
    assert!(matches!(
        SearchSpec::from_json(json).unwrap().build(),
        Err(SearchError::ConflictingExecutionModes)
    ));
}

#[test]
fn search_spec_enumeration_has_solution_and_assignment_cell_caps() {
    let too_many_solutions = format!(
        r#"{{"version":1,"variables":[],"limits":{{"max_solutions":{}}}}}"#,
        MAX_SEARCH_SPEC_SOLUTIONS + 1
    );
    assert!(matches!(
        SearchSpec::from_json(&too_many_solutions).unwrap().build(),
        Err(SearchError::InvalidLimit {
            name: "max_solutions",
            ..
        })
    ));

    let variable_count = 101;
    let variables = (0..variable_count)
        .map(|index| format!(r#"{{"name":"x_{index}","domain":{{"min":0,"max":1}}}}"#))
        .collect::<Vec<_>>()
        .join(",");
    let max_solutions = MAX_SEARCH_SPEC_RESULT_CELLS / variable_count + 1;
    let too_many_cells = format!(
        r#"{{"version":1,"variables":[{variables}],"limits":{{"max_solutions":{max_solutions}}}}}"#
    );
    assert!(matches!(
        SearchSpec::from_json(&too_many_cells).unwrap().build(),
        Err(SearchError::EnumerationResultTooLarge { .. })
    ));
}

#[test]
fn search_spec_enumeration_caps_repeated_names_and_labels_in_json_output() {
    let long_name = format!("x{}", "a".repeat(1_700));
    let mut repeated_name_variables = vec![VariableSpec {
        name: long_name,
        domain: DomainSpec::Interval { min: 0, max: 1 },
        labels: BTreeMap::new(),
    }];
    repeated_name_variables.extend((1..14).map(|index| VariableSpec {
        name: format!("x_{index}"),
        domain: DomainSpec::Interval { min: 0, max: 1 },
        labels: BTreeMap::new(),
    }));
    let repeated_name = SearchSpec {
        version: 1,
        name: None,
        // 2^14 assignments ensure the requested 10,000-result cap is
        // reachable; the long name would really be repeated 10,000 times.
        variables: repeated_name_variables,
        constraints: Vec::new(),
        objective: None,
        limits: Some(LimitsSpec {
            timeout_ms: None,
            max_solutions: Some(MAX_SEARCH_SPEC_SOLUTIONS),
        }),
    };
    assert!(matches!(
        repeated_name.build(),
        Err(SearchError::EnumerationOutputTooLarge { .. })
    ));

    // One control byte is six bytes in compact JSON (`\u0001`). The
    // selected label is repeated in every retained solution just like the
    // assignment name, so escaped size—not source String length—must count.
    let long_escaped_label = "\u{1}".repeat(300);
    let mut escaped_label_variables = vec![VariableSpec {
        name: "route".to_owned(),
        domain: DomainSpec::Interval { min: 0, max: 1 },
        labels: BTreeMap::from([(0, long_escaped_label.clone()), (1, long_escaped_label)]),
    }];
    escaped_label_variables.extend((1..14).map(|index| VariableSpec {
        name: format!("route_{index}"),
        domain: DomainSpec::Interval { min: 0, max: 1 },
        labels: BTreeMap::new(),
    }));
    let escaped_label = SearchSpec {
        version: 1,
        name: None,
        variables: escaped_label_variables,
        constraints: Vec::new(),
        objective: None,
        limits: Some(LimitsSpec {
            timeout_ms: None,
            max_solutions: Some(MAX_SEARCH_SPEC_SOLUTIONS),
        }),
    };
    assert!(matches!(
        escaped_label.build(),
        Err(SearchError::EnumerationOutputTooLarge { .. })
    ));
}

#[test]
fn enumeration_json_estimate_bounds_the_actual_serializer() {
    let spec = SearchSpec {
        version: 1,
        name: None,
        variables: vec![
            VariableSpec {
                name: "x".to_owned(),
                domain: DomainSpec::Interval { min: 0, max: 1 },
                labels: BTreeMap::from([(0, "\u{1}\"\\é".to_owned())]),
            },
            VariableSpec {
                name: "y".to_owned(),
                domain: DomainSpec::Interval { min: 0, max: 1 },
                labels: BTreeMap::from([(1, "line\nbreak".to_owned())]),
            },
        ],
        constraints: Vec::new(),
        objective: None,
        limits: Some(LimitsSpec {
            timeout_ms: None,
            max_solutions: Some(4),
        }),
    };
    let estimate = enumeration_result_json_upper_bound(&spec.variables, 4);
    let result = spec.build().unwrap().run().unwrap();
    let actual = serde_json::to_vec(&result).unwrap().len() as u128;
    assert!(actual <= estimate, "actual={actual}, estimate={estimate}");
    assert!(estimate <= u128::from(MAX_SEARCH_SPEC_RESULT_BYTES));
}

#[test]
fn smt_size_preflight_matches_all_normalized_lowerings() {
    let spec = SearchSpec {
        version: 1,
        name: None,
        variables: vec![
            VariableSpec {
                name: "index".to_owned(),
                domain: DomainSpec::Interval { min: 0, max: 1 },
                labels: BTreeMap::new(),
            },
            VariableSpec {
                name: "first".to_owned(),
                domain: DomainSpec::Values {
                    values: vec![-2, 4],
                },
                labels: BTreeMap::new(),
            },
            VariableSpec {
                name: "second".to_owned(),
                domain: DomainSpec::Interval { min: -1, max: 5 },
                labels: BTreeMap::new(),
            },
            VariableSpec {
                name: "selected".to_owned(),
                domain: DomainSpec::Interval { min: -2, max: 5 },
                labels: BTreeMap::new(),
            },
        ],
        constraints: vec![
            ConstraintSpec::Expression {
                expression: "2*first - second != -3".to_owned(),
            },
            ConstraintSpec::Expression {
                expression: "1 == 2".to_owned(),
            },
            ConstraintSpec::AllDifferent {
                all_different: vec!["first".to_owned(), "second".to_owned()],
            },
            ConstraintSpec::Table {
                table: TableSpec {
                    variables: vec!["first".to_owned(), "second".to_owned()],
                    tuples: vec![vec![-2, -1], vec![4, 5]],
                },
            },
            ConstraintSpec::Element {
                element: ElementSpec {
                    index: "index".to_owned(),
                    array: vec!["first".to_owned(), "second".to_owned()],
                    result: "selected".to_owned(),
                },
            },
        ],
        objective: Some(ObjectiveSpec {
            sense: ObjectiveSense::Maximize,
            expression: "selected + 2".to_owned(),
        }),
        limits: None,
    };
    let problem = spec.build().unwrap();
    let mut estimated = problem.model.smt2_size_upper_bound();
    let (_, objective) = problem.objective.as_ref().unwrap();
    estimated += problem
        .model
        .expression_smt_size_upper_bound(objective)
        .unwrap()
        + "maximize".len() as u128
        + 4;
    let rendered = problem.to_smt2().unwrap();
    assert_eq!(rendered.len() as u128, estimated);
}

#[test]
fn search_spec_smt_compile_rejects_table_name_amplification() {
    let variable_count = 100;
    let variables = (0..variable_count)
        .map(|index| VariableSpec {
            name: format!("x_{index}_{}", "a".repeat(2_000)),
            domain: DomainSpec::Interval { min: 0, max: 1 },
            labels: BTreeMap::new(),
        })
        .collect::<Vec<_>>();
    let variable_names = variables
        .iter()
        .map(|variable| variable.name.clone())
        .collect();
    let spec = SearchSpec {
        version: 1,
        name: None,
        variables,
        constraints: vec![ConstraintSpec::Table {
            table: TableSpec {
                variables: variable_names,
                // Compact JSON (100,000 small integers) would render each
                // 2,000-byte name once per cell, amplifying past 16 MiB.
                tuples: vec![vec![0; variable_count]; 1_000],
            },
        }],
        objective: None,
        limits: None,
    };
    assert!(matches!(
        spec.to_smt2(),
        Err(SearchError::SmtOutputTooLarge {
            estimated_bytes,
            limit: MAX_SEARCH_SPEC_SMT_BYTES,
        }) if estimated_bytes > u128::from(MAX_SEARCH_SPEC_SMT_BYTES)
    ));
}
