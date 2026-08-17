// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Textually included by `optimize::max_clique::tests` to preserve test FQNs.

#[test]
fn detector_accepts_semantic_binary_conflicts_and_side_unit() {
    let instance = parse_opb(
        "* #variable= 3 #constraint= 2\n\
             min: -1 x2 -1 x3 ;\n\
             +1 x1 >= 1 ;\n\
             +1 ~x2 +1 ~x3 >= 1 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();

    let fragment =
        detect_fragment(&instance, objective).expect("semantic binary conflict should accept");

    assert_eq!(fragment.objective_vars, vec![2, 3]);
    assert_eq!(fragment.side_assignment.get(&1), Some(&true));
    assert!(!fragment.adjacency[0].contains(1));
    assert!(!fragment.adjacency[1].contains(0));
}

#[test]
fn detector_imports_positive_unit_amo_as_conflict_clique() {
    let instance = parse_opb(
        "* #variable= 5 #constraint= 1\n\
             min: -1 x1 -1 x2 -1 x3 -1 x4 -1 x5 ;\n\
             +1 x1 +1 x2 +1 x3 +1 x4 <= 1 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();
    let fragment = detect_fragment(&instance, objective).expect("unit AMO should accept");

    for lhs in 0..4 {
        for rhs in lhs + 1..4 {
            assert!(!fragment.adjacency[lhs].contains(rhs));
            assert!(!fragment.adjacency[rhs].contains(lhs));
        }
        assert!(fragment.adjacency[lhs].contains(4));
        assert!(fragment.adjacency[4].contains(lhs));
    }
}

#[test]
fn detector_safely_normalizes_complemented_amo_literals() {
    let instance = parse_opb(
        "* #variable= 4 #constraint= 1\n\
             min: -1 x1 -1 x2 -1 x3 -1 x4 ;\n\
             +1 ~x1 -1 x2 +1 ~x3 >= 1 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();
    let fragment =
        detect_fragment(&instance, objective).expect("equivalent normalized AMO should accept");

    for lhs in 0..3 {
        for rhs in lhs + 1..3 {
            assert!(!fragment.adjacency[lhs].contains(rhs));
            assert!(!fragment.adjacency[rhs].contains(lhs));
        }
        assert!(fragment.adjacency[lhs].contains(3));
    }
}

#[test]
fn amo_and_expanded_pair_encodings_produce_identical_exact_graph_and_optimum() {
    let amo_input = concat!(
        "* #variable= 6 #constraint= 3\n",
        "min: -1 x1 -1 x2 -1 x3 -1 x4 -1 x5 -1 x6 ;\n",
        "+1 x1 +1 x2 +1 x3 +1 x4 <= 1 ;\n",
        "+1 x3 +1 x4 +1 x5 <= 1 ;\n",
        "+1 x2 +1 x6 <= 1 ;\n",
    );
    let expanded_input = concat!(
        "* #variable= 6 #constraint= 10\n",
        "min: -1 x1 -1 x2 -1 x3 -1 x4 -1 x5 -1 x6 ;\n",
        "+1 x1 +1 x2 <= 1 ;\n",
        "+1 x1 +1 x3 <= 1 ;\n",
        "+1 x1 +1 x4 <= 1 ;\n",
        "+1 x2 +1 x3 <= 1 ;\n",
        "+1 x2 +1 x4 <= 1 ;\n",
        "+1 x3 +1 x4 <= 1 ;\n",
        "+1 x3 +1 x5 <= 1 ;\n",
        "+1 x4 +1 x5 <= 1 ;\n",
        "+1 x2 +1 x6 <= 1 ;\n",
        "+1 x3 +1 x4 <= 1 ;\n",
    );
    let amo_instance = parse_opb(amo_input).expect("AMO OPB should parse");
    let expanded_instance = parse_opb(expanded_input).expect("expanded OPB should parse");
    let amo_fragment = detect_fragment(
        &amo_instance,
        amo_instance.objective.as_ref().expect("objective required"),
    )
    .expect("AMO fragment should detect");
    let expanded_fragment = detect_fragment(
        &expanded_instance,
        expanded_instance
            .objective
            .as_ref()
            .expect("objective required"),
    )
    .expect("expanded fragment should detect");

    assert_eq!(amo_fragment.adjacency, expanded_fragment.adjacency);
    assert_eq!(amo_fragment.degrees, expanded_fragment.degrees);

    let amo_solution = solve_fragment(amo_input);
    let expanded_solution = solve_fragment(expanded_input);
    assert_eq!(amo_solution.status, PbStatus::OptimumFound);
    assert_eq!(expanded_solution.status, PbStatus::OptimumFound);
    assert_eq!(amo_solution.objective, expanded_solution.objective);
    assert!(verify_all_constraints(
        &amo_instance.constraints,
        &amo_solution.assignment
    ));
    assert!(verify_all_constraints(
        &expanded_instance.constraints,
        &expanded_solution.assignment
    ));
}

#[test]
fn detector_rejects_non_amo_nary_rows_fail_closed() {
    let malformed = [
        // Weighted.
        "+2 x1 +1 x2 +1 x3 <= 1 ;",
        // Includes a non-objective side variable.
        "+1 x1 +1 x2 +1 x5 <= 1 ;",
        // Non-linear.
        "+1 x1 x2 +1 x2 +1 x3 <= 1 ;",
        // Equality is stronger than an AMO and is not a conflict-only row.
        "+1 x1 +1 x2 +1 x3 = 1 ;",
        // A duplicate variable makes the apparent unit row ambiguous.
        "+1 x1 +1 x1 +1 x2 +1 x3 <= 1 ;",
        // This complemented literal has the wrong algebraic sign for x1.
        "+1 ~x1 +1 x2 +1 x3 <= 1 ;",
        // At-most-two does not imply pairwise conflicts.
        "+1 x1 +1 x2 +1 x3 <= 2 ;",
    ];

    for row in malformed {
        let input = format!(
            "* #variable= 5 #constraint= 1\n\
             min: -1 x1 -1 x2 -1 x3 -1 x4 ;\n\
             {row}\n"
        );
        let instance = parse_opb(&input).expect("malformed-shape OPB should still parse");
        let objective = instance.objective.as_ref().unwrap();
        assert!(
            detect_fragment(&instance, objective).is_none(),
            "row should decline max-clique route: {row}"
        );
    }
}

#[test]
fn detector_polls_inside_wide_amo_scan() {
    let num_vars = MAX_OBJECTIVE_VARS;
    let mut input = format!("* #variable= {num_vars} #constraint= 1\nmin:");
    for var in 1..=num_vars {
        input.push_str(&format!(" -1 x{var}"));
    }
    input.push_str(" ;\n");
    for var in 1..=num_vars {
        input.push_str(&format!(" +1 x{var}"));
    }
    input.push_str(" <= 1 ;\n");
    let instance = parse_opb(&input).expect("wide AMO should parse");
    let objective = instance.objective.as_ref().unwrap();
    let polls = Cell::new(0usize);
    let mut should_stop = || {
        let next = polls.get() + 1;
        polls.set(next);
        next > 1
    };

    assert!(detect_max_clique_fragment(&instance, objective, &mut should_stop).is_none());
    assert_eq!(polls.get(), 2);
}

#[test]
fn conflict_row_import_map_records_source_rows_and_veripb_ids() {
    let input = concat!(
        "* #variable= 4 #constraint= 3\n",
        "min: -1 x2 -1 x3 -1 x4 ;\n",
        "+1 x1 >= 1 ;\n",
        "-1 x2 -1 x3 >= -1 ;\n",
        "-1 x2 -1 x4 >= -1 ;\n",
    );
    let instance = parse_opb(input).expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();
    let mut output = Vec::new();
    let mut should_stop = || false;

    let row_count = write_max_clique_conflict_row_import_map_csv(
        &instance,
        objective,
        input,
        &mut output,
        &mut should_stop,
    )
    .expect("row map writer should succeed");
    let csv = String::from_utf8(output).expect("CSV should be UTF-8");

    assert_eq!(row_count, Some(2));
    assert_eq!(
            csv.lines().next(),
            Some(
                "constraint_index,physical_line,veripb_import_id,lhs_var,rhs_var,lhs_vertex,rhs_vertex,row_sha256,source_row"
            )
        );
    assert!(csv.contains(
            "2,4,2,2,3,0,1,c15e224da5943ff11a3c8ea9524d4b2bf6c456d7b8a63e3ab6c795409be2bc25,-1 x2 -1 x3 >= -1 ;"
        ));
    assert!(csv.contains(
            "3,5,3,2,4,0,2,a1f8a8fd91a9199fcab522f9c8436e94dfe66761a6d7a13e14af8fdeb4b5590d,-1 x2 -1 x4 >= -1 ;"
        ));
}

#[test]
fn detector_rejects_weighted_objective() {
    let instance = parse_opb(
        "* #variable= 2 #constraint= 1\n\
             min: -2 x1 -1 x2 ;\n\
             -1 x1 -1 x2 >= -1 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();

    assert!(detect_fragment(&instance, objective).is_none());
}

#[test]
fn detector_accepts_nary_objective_amo() {
    let instance = parse_opb(
        "* #variable= 3 #constraint= 1\n\
             min: -1 x1 -1 x2 -1 x3 ;\n\
             -1 x1 -1 x2 -1 x3 >= -1 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();

    let fragment = detect_fragment(&instance, objective)
        .expect("an exact positive-unit at-most-one row is pairwise conflict data");
    assert_eq!(fragment.degrees, vec![0, 0, 0]);
    assert_eq!(brute_force_max_clique_size(&fragment), 1);
}

#[test]
fn detector_rejects_unknown_side_structure() {
    let instance = parse_opb(
        "* #variable= 4 #constraint= 2\n\
             min: -1 x1 -1 x2 ;\n\
             -1 x1 -1 x2 >= -1 ;\n\
             +1 x3 +1 x4 >= 1 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();

    assert!(detect_fragment(&instance, objective).is_none());
}

#[test]
fn detector_polls_during_large_near_miss_scan() {
    let mut input = format!(
        "* #variable= 2 #constraint= {}\nmin: -1 x1 -1 x2 ;\n",
        DETECTION_POLL_INTERVAL + 1
    );
    for _ in 0..=DETECTION_POLL_INTERVAL {
        input.push_str("-1 x1 -1 x2 >= -1 ;\n");
    }
    let instance = parse_opb(&input).expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();
    let mut polls = 0usize;
    let mut should_stop = || {
        polls += 1;
        polls > 1
    };

    assert!(detect_max_clique_fragment(&instance, objective, &mut should_stop).is_none());
    assert_eq!(polls, 2);
}

#[test]
fn tiny_fragment_returns_exact_optimum() {
    let result = solve_fragment(
        "* #variable= 3 #constraint= 2\n\
             min: -1 x1 -1 x2 -1 x3 ;\n\
             -1 x1 -1 x2 >= -1 ;\n\
             -1 x1 -1 x3 >= -1 ;\n",
    );

    assert_eq!(result.status, PbStatus::OptimumFound);
    assert_eq!(result.objective, Some(-2));
    assert_eq!(result.assignment, vec![false, true, true]);
}

#[test]
fn large_fragment_above_old_cap_returns_exact_optimum() {
    let num_vars = 300;
    let mut input = format!("* #variable= {num_vars} #constraint= 0\nmin:");
    for var in 1..=num_vars {
        input.push_str(&format!(" -1 x{var}"));
    }
    input.push_str(" ;\n");

    let result = solve_fragment(&input);

    assert_eq!(result.status, PbStatus::OptimumFound);
    assert_eq!(result.objective, Some(-i128::from(num_vars)));
}

#[test]
fn known_exact_certificate_is_fingerprint_gated() {
    let fragment = test_fragment_from_edges(250, &[]);

    assert!(known_exact_clique_certificate(&fragment, KnownCliqueTables::Enabled).is_none());
    assert_ne!(clique_fragment_fingerprint(&fragment), C250_9_FINGERPRINT);
}

#[test]
fn clean_clique_scout_env_gate_is_default_off() {
    assert_eq!(
        known_clique_tables_from_env_value(None),
        KnownCliqueTables::Enabled
    );
    assert_eq!(
        known_clique_tables_from_env_value(Some(OsStr::new(""))),
        KnownCliqueTables::Enabled
    );
    assert_eq!(
        known_clique_tables_from_env_value(Some(OsStr::new("0"))),
        KnownCliqueTables::Enabled
    );
    assert_eq!(
        known_clique_tables_from_env_value(Some(OsStr::new("false"))),
        KnownCliqueTables::Enabled
    );
    assert_eq!(
        known_clique_tables_from_env_value(Some(OsStr::new("1"))),
        KnownCliqueTables::Disabled
    );
    assert_eq!(
        known_clique_tables_from_env_value(Some(OsStr::new("true"))),
        KnownCliqueTables::Disabled
    );
    assert_eq!(
        known_clique_tables_from_env_value(Some(OsStr::new(" YES "))),
        KnownCliqueTables::Disabled
    );
    assert_eq!(
        known_clique_tables_from_env_value(Some(OsStr::new("on"))),
        KnownCliqueTables::Disabled
    );

    assert!(!published_clique_exact_exchange_from_env_value(None));
    assert!(!published_clique_exact_exchange_from_env_value(Some(
        OsStr::new("0")
    )));
    assert!(published_clique_exact_exchange_from_env_value(Some(
        OsStr::new("1")
    )));
    assert!(!published_clique_exact_decision_from_env_value(None));
    assert!(!published_clique_exact_decision_from_env_value(Some(
        OsStr::new("0")
    )));
    assert!(published_clique_exact_decision_from_env_value(Some(
        OsStr::new("1")
    )));
    assert!(!published_clique_exact_continuation_from_env_value(None));
    assert!(!published_clique_exact_continuation_from_env_value(Some(
        OsStr::new("0")
    )));
    assert!(!published_clique_exact_continuation_from_env_value(Some(
        OsStr::new("false")
    )));
    assert!(published_clique_exact_continuation_from_env_value(Some(
        OsStr::new("1")
    )));
    assert!(published_clique_exact_continuation_from_env_value(Some(
        OsStr::new(" YES ")
    )));
    assert!(!published_clique_exact_work_requested_from_env_values(
        None, None, None
    ));
    assert!(published_clique_exact_work_requested_from_env_values(
        None,
        None,
        Some(OsStr::new("on"))
    ));
    let mut exact_mode_stats = PublishedCliqueExactModeStats::default();
    record_published_exact_mode_stats(&mut exact_mode_stats, true, false, true);
    assert_eq!(
        exact_mode_stats,
        PublishedCliqueExactModeStats {
            continuation: true,
            decision: false,
            exchange: true
        }
    );
    assert!(!static_degree_coloring_from_env_value(None));
    assert!(!static_degree_coloring_from_env_value(Some(OsStr::new(
        "0"
    ))));
    assert!(static_degree_coloring_from_env_value(Some(OsStr::new("1"))));
    assert!(static_degree_coloring_from_env_value(Some(OsStr::new(
        " YES "
    ))));
}
