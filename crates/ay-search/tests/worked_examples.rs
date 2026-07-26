// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::BTreeSet;

use ay_search::{
    Domain, EnumerationResult, LinearExpr, Model, OptimizationResult, SearchError, SearchRunResult,
    SearchSpec, SolveResult, MAX_BACKEND_WORK, MAX_CP_SAFE_MAGNITUDE, MAX_ENCODED_DOMAIN_SPAN,
    MAX_TOTAL_ENCODED_VALUES,
};

#[test]
fn solves_a_four_by_four_sudoku() {
    let mut model = Model::new();
    let mut cells = Vec::new();
    for row in 0..4 {
        for column in 0..4 {
            cells.push(
                model
                    .int_var(
                        format!("cell_{row}_{column}"),
                        Domain::interval(1, 4).unwrap(),
                    )
                    .unwrap(),
            );
        }
    }

    for row in 0..4 {
        model.all_different(&cells[row * 4..row * 4 + 4]).unwrap();
    }
    for column in 0..4 {
        let variables = (0..4)
            .map(|row| cells[row * 4 + column])
            .collect::<Vec<_>>();
        model.all_different(&variables).unwrap();
    }
    for box_row in 0..2 {
        for box_column in 0..2 {
            let mut variables = Vec::new();
            for row in 0..2 {
                for column in 0..2 {
                    variables.push(cells[(box_row * 2 + row) * 4 + box_column * 2 + column]);
                }
            }
            model.all_different(&variables).unwrap();
        }
    }

    // A compact puzzle with a unique completion.
    for (index, value) in [
        (0, 1),
        (3, 4),
        (5, 4),
        (6, 1),
        (9, 1),
        (10, 4),
        (12, 4),
        (15, 1),
    ] {
        model.eq(cells[index], value).unwrap();
    }

    let SolveResult::Sat(solution) = model.solve().unwrap() else {
        panic!("Sudoku should be satisfiable");
    };
    for row in 0..4 {
        let values = (0..4)
            .map(|column| solution.int_value(cells[row * 4 + column]).unwrap())
            .collect::<BTreeSet<_>>();
        assert_eq!(values, BTreeSet::from([1, 2, 3, 4]));
    }
}

#[test]
fn minesweeper_neighborhood_equations_infer_safe_and_mined_cells() {
    let mut model = Model::new();
    let left = model.bool_var("left").unwrap();
    let center = model.bool_var("center").unwrap();
    let right = model.bool_var("right").unwrap();

    // Two adjacent revealed clues. A hand-written search would branch; the
    // equations immediately imply left=0 and center=right=1.
    model.eq(left + center, 1).unwrap();
    model.eq(center + right, 2).unwrap();

    let SolveResult::Sat(solution) = model.solve().unwrap() else {
        panic!("neighborhood should be consistent");
    };
    assert!(!solution.bool_value(left).unwrap());
    assert!(solution.bool_value(center).unwrap());
    assert!(solution.bool_value(right).unwrap());
}

#[test]
fn optimizes_an_llm_token_route_and_proves_the_incumbent() {
    let mut model = Model::new();
    let local = model.bool_var("local").unwrap();
    let fast_gpu = model.bool_var("fast_gpu").unwrap();
    let frontier_api = model.bool_var("frontier_api").unwrap();

    model.eq(local + fast_gpu + frontier_api, 1).unwrap();
    // Quality scores are 70, 90, and 98. This request requires at least 90.
    model
        .ge(70 * local + 90 * fast_gpu + 98 * frontier_api, 90)
        .unwrap();
    // Per-million-token costs are 2, 5, and 9.
    let cost = 2 * local + 5 * fast_gpu + 9 * frontier_api;

    let OptimizationResult::Optimal { solution, value } = model.minimize(cost).unwrap() else {
        panic!("router should have a proven optimum");
    };
    assert_eq!(value, 5);
    assert!(!solution.bool_value(local).unwrap());
    assert!(solution.bool_value(fast_gpu).unwrap());
    assert!(!solution.bool_value(frontier_api).unwrap());
}

#[test]
fn table_element_and_enumeration_have_exact_semantics() {
    let mut model = Model::new();
    let index = model
        .int_var("index", Domain::interval(0, 1).unwrap())
        .unwrap();
    let first = model
        .int_var("first", Domain::values([10, 20]).unwrap())
        .unwrap();
    let second = model
        .int_var("second", Domain::values([10, 20]).unwrap())
        .unwrap();
    let selected = model
        .int_var("selected", Domain::values([10, 20]).unwrap())
        .unwrap();
    model
        .table(&[first, second], &[vec![10, 20], vec![20, 10]])
        .unwrap();
    model.element(index, &[first, second], selected).unwrap();
    model.eq(selected, 10).unwrap();

    let EnumerationResult::Capped(prefix) = model.enumerate_up_to(1).unwrap() else {
        panic!("a one-solution cap should be reported explicitly");
    };
    assert_eq!(prefix.len(), 1);

    let EnumerationResult::Complete(solutions) = model.enumerate_all().unwrap() else {
        panic!("small model should enumerate completely");
    };
    assert_eq!(solutions.len(), 2);
    for solution in solutions {
        let position = solution.int_value(index).unwrap() as usize;
        let values = [
            solution.int_value(first).unwrap(),
            solution.int_value(second).unwrap(),
        ];
        assert_eq!(values[position], 10);
    }
}

#[test]
fn json_labels_results_and_smt_lowering_are_portable() {
    let json = r#"{
      "version":1,
      "name":"router",
      "variables":[
        {"name":"route","domain":{"values":[0,1]},"labels":{"0":"local","1":"gpu"}}
      ],
      "constraints":[{"expression":"route == 1"}],
      "objective":{"sense":"minimize","expression":"3*route + 2"}
    }"#;
    let spec = SearchSpec::from_json(json).unwrap();
    let smt = spec.to_smt2().unwrap();
    assert!(smt.contains("(assert (or (= |route| 0) (= |route| 1)))"));
    assert!(smt.contains("(assert (= |route| 1))"));
    assert!(smt.contains("(minimize (+ (* 3 |route|) 2))"));

    let result = spec.build().unwrap().run().unwrap();
    let SearchRunResult::Optimization(OptimizationResult::Optimal { .. }) = &result else {
        panic!("expected optimal route");
    };
    let output = serde_json::to_value(result).unwrap();
    assert_eq!(output["status"], "optimal");
    assert_eq!(output["assignments"]["route"], 1);
    assert_eq!(output["labels"]["route"], "gpu");
    assert_eq!(output["objective"], 5);
}

#[test]
fn untrusted_dense_and_sparse_wide_domains_are_rejected_before_cp_allocation() {
    let too_wide_max = i64::try_from(MAX_ENCODED_DOMAIN_SPAN).unwrap();
    assert!(matches!(
        Domain::interval(0, too_wide_max),
        Err(SearchError::DomainTooLarge { .. })
    ));
    assert!(matches!(
        Domain::values([0, too_wide_max]),
        Err(SearchError::DomainTooLarge { .. })
    ));

    let json = format!(
        r#"{{"version":1,"variables":[{{"name":"x","domain":{{"min":0,"max":{too_wide_max}}}}}]}}"#
    );
    assert!(matches!(
        SearchSpec::from_json(&json).unwrap().build(),
        Err(SearchError::DomainTooLarge { .. })
    ));
}

#[test]
fn risky_empty_tables_and_out_of_range_element_indices_are_typed_errors() {
    let mut table_model = Model::new();
    let x = table_model
        .int_var("x", Domain::interval(0, 1).unwrap())
        .unwrap();
    assert!(matches!(
        table_model.table(&[x], &[]),
        Err(SearchError::EmptyTableTuples)
    ));

    let mut element_model = Model::new();
    let index = element_model
        .int_var("index", Domain::interval(-1, 0).unwrap())
        .unwrap();
    let item = element_model
        .int_var("item", Domain::interval(0, 1).unwrap())
        .unwrap();
    let result = element_model
        .int_var("result", Domain::interval(0, 1).unwrap())
        .unwrap();
    assert!(matches!(
        element_model.element(index, &[item], result),
        Err(SearchError::InvalidElementIndexDomain { .. })
    ));
}

#[test]
fn smt_lowering_quotes_even_builtin_names() {
    let mut model = Model::new();
    let and = model
        .int_var("and", Domain::interval(0, 1).unwrap())
        .unwrap();
    model.eq(and, 1).unwrap();
    let smt = model.to_smt2().unwrap();
    assert!(smt.contains("(declare-const |and| Int)"));
    assert!(smt.contains("(assert (= |and| 1))"));
}

#[test]
fn objective_auxiliary_domains_obey_the_same_allocation_guard() {
    let mut model = Model::new();
    let x = model
        .int_var(
            "x",
            Domain::interval(0, i64::try_from(MAX_ENCODED_DOMAIN_SPAN - 1).unwrap()).unwrap(),
        )
        .unwrap();
    assert!(matches!(
        model.minimize(2 * x),
        Err(SearchError::DomainTooLarge { .. })
    ));
}

#[test]
fn aggregate_order_encoding_size_is_capped() {
    let mut model = Model::new();
    let domain = Domain::interval(0, i64::try_from(MAX_ENCODED_DOMAIN_SPAN - 1).unwrap()).unwrap();
    let encoded_width = MAX_ENCODED_DOMAIN_SPAN + 1;
    let variables_that_fit = MAX_TOTAL_ENCODED_VALUES / encoded_width;
    for index in 0..variables_that_fit {
        model.int_var(format!("x_{index}"), domain.clone()).unwrap();
    }
    assert!(matches!(
        model.int_var("one_too_many", domain),
        Err(SearchError::ModelTooLarge { .. })
    ));
}

#[test]
fn i64_extrema_and_unsafe_linear_arithmetic_fail_before_cp_lowering() {
    for extreme in [i64::MIN, i64::MAX] {
        assert!(matches!(
            Domain::interval(extreme, extreme),
            Err(SearchError::NumericEnvelopeExceeded { .. })
        ));
        assert!(matches!(
            Domain::values([extreme]),
            Err(SearchError::NumericEnvelopeExceeded { .. })
        ));
    }

    let mut model = Model::new();
    let x = model.bool_var("x").unwrap();
    assert!(matches!(
        model.ne(i64::MAX * x, 0),
        Err(SearchError::NumericEnvelopeExceeded { .. })
    ));
    assert!(matches!(
        model.eq(i64::MIN * x, 0),
        Err(SearchError::NumericEnvelopeExceeded { .. })
    ));
    assert!(matches!(
        model.le(x, i64::MAX),
        Err(SearchError::NumericEnvelopeExceeded { .. })
    ));
    assert!(matches!(
        model.ge(x, i64::MIN),
        Err(SearchError::NumericEnvelopeExceeded { .. })
    ));
    assert!(matches!(
        model.ne(x, i64::MAX),
        Err(SearchError::NumericEnvelopeExceeded { .. })
    ));
    assert!(matches!(
        model.eq(x, i64::MIN),
        Err(SearchError::NumericEnvelopeExceeded { .. })
    ));
    assert!(matches!(
        model.minimize(i64::MAX * x),
        Err(SearchError::NumericEnvelopeExceeded { .. })
    ));
    assert!(matches!(
        model.maximize(LinearExpr::from(x) + i64::MAX),
        Err(SearchError::NumericEnvelopeExceeded { .. })
    ));

    let mut aggregate = Model::new();
    let large = aggregate
        .int_var(
            "large",
            Domain::interval(MAX_CP_SAFE_MAGNITUDE, MAX_CP_SAFE_MAGNITUDE).unwrap(),
        )
        .unwrap();
    assert!(matches!(
        aggregate.eq(2 * large, 0),
        Err(SearchError::NumericEnvelopeExceeded { .. })
    ));
}

#[test]
fn numeric_envelope_boundaries_cover_ne_all_different_and_objectives() {
    for value in [-MAX_CP_SAFE_MAGNITUDE, MAX_CP_SAFE_MAGNITUDE] {
        let mut disequality = Model::new();
        let x = disequality
            .int_var("x", Domain::interval(value, value).unwrap())
            .unwrap();
        disequality.ne(x, value).unwrap();
        assert!(matches!(disequality.solve().unwrap(), SolveResult::Unsat));

        let mut objective = Model::new();
        let x = objective
            .int_var("x", Domain::interval(value, value).unwrap())
            .unwrap();
        let result = if value < 0 {
            objective.maximize(x).unwrap()
        } else {
            objective.minimize(x).unwrap()
        };
        assert!(matches!(
            result,
            OptimizationResult::Optimal {
                value: actual,
                ..
            } if actual == value
        ));
    }

    for lower in [-MAX_CP_SAFE_MAGNITUDE, MAX_CP_SAFE_MAGNITUDE - 2] {
        let mut model = Model::new();
        let domain = Domain::interval(lower, lower + 2).unwrap();
        let variables = (0..3)
            .map(|index| model.int_var(format!("x_{index}"), domain.clone()).unwrap())
            .collect::<Vec<_>>();
        model.all_different(&variables).unwrap();
        assert!(matches!(model.solve().unwrap(), SolveResult::Sat(_)));
    }
}

#[test]
fn backend_work_budget_rejects_hidden_constraint_expansions() {
    assert_eq!(MAX_BACKEND_WORK, 1_000_000);

    // Fifteen wide variables fit under the aggregate encoding-value cap, but
    // AY CP would eagerly lower their pairwise disequalities to millions of
    // clauses before a timeout can apply.
    let mut all_different = Model::new();
    let wide = Domain::interval(0, 65_534).unwrap();
    let variables = (0..15)
        .map(|index| {
            all_different
                .int_var(format!("wide_{index}"), wide.clone())
                .unwrap()
        })
        .collect::<Vec<_>>();
    assert!(matches!(
        all_different.all_different(&variables),
        Err(SearchError::BackendWorkLimit { .. })
    ));

    // Linear and table propagators can each build one O(n)-sized explanation
    // for O(n) variables; cap that quadratic shape before compilation.
    let mut linear = Model::new();
    let linear_vars = (0..1_001)
        .map(|index| linear.bool_var(format!("b_{index}")).unwrap())
        .collect::<Vec<_>>();
    let expression = linear_vars
        .iter()
        .copied()
        .fold(LinearExpr::zero(), |sum, variable| sum + variable);
    assert!(matches!(
        linear.eq(expression.clone(), 0),
        Err(SearchError::BackendWorkLimit { .. })
    ));
    assert!(matches!(
        linear.minimize(expression),
        Err(SearchError::BackendWorkLimit { .. })
    ));

    let mut table = Model::new();
    let table_vars = (0..1_001)
        .map(|index| table.bool_var(format!("t_{index}")).unwrap().as_int())
        .collect::<Vec<_>>();
    assert!(matches!(
        table.table(&table_vars, &[vec![0; table_vars.len()]]),
        Err(SearchError::BackendWorkLimit { .. })
    ));

    let mut repeated = Model::new();
    let repeated_vars = (0..100)
        .map(|index| repeated.bool_var(format!("r_{index}")).unwrap())
        .collect::<Vec<_>>();
    let repeated_sum = repeated_vars
        .iter()
        .copied()
        .fold(LinearExpr::zero(), |sum, variable| sum + variable);
    // One 100-term equality is charged 2 * 100^2 units. Fifty fit exactly;
    // the next repeated constraint must fail without reaching the backend.
    for _ in 0..50 {
        repeated.eq(repeated_sum.clone(), 0).unwrap();
    }
    assert!(matches!(
        repeated.eq(repeated_sum, 0),
        Err(SearchError::BackendWorkLimit { .. })
    ));
}
