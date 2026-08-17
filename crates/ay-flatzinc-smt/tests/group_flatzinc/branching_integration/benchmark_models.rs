// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `branching_integration` to preserve test FQNs.

/// Verify branching on MiniZinc Challenge 2024: neighbours/neightbours-new-2.
///
/// This is an optimization (maximize) problem with `int_search([...], largest,
/// indomain_max, complete)`. Uses 8 integer variables with domains 1..3 or
/// 1..4, plus ~200 boolean reification variables, and constraints:
/// int_lin_le, int_lin_le_reif, int_eq_reif, int_le_reif, array_bool_and,
/// bool_clause, int_lin_eq.
///
/// We verify:
/// 1. Translation succeeds (all constraint types supported)
/// 2. Branching solver runs without error
/// 3. At least one solution is found (feasible problem)
/// 4. Objective value is in the valid range [8, 40]
///
/// Part of #273 (MiniZinc entry).
#[test]
fn branching_benchmark_neighbours_new_2() {
    let fzn_path = benchmark_cp_path("neighbours/neightbours-new-2.fzn");
    if !fzn_path.exists() {
        eprintln!("benchmark not found: {}; skipping", fzn_path.display());
        return;
    }

    let fzn = std::fs::read_to_string(&fzn_path).expect("failed to read benchmark");
    let result = translate_fzn(&fzn);

    // Translation must produce non-empty SMT-LIB
    assert!(
        !result.smtlib.is_empty(),
        "translation produced empty SMT-LIB for neighbours-new-2"
    );

    // Must have search annotations (int_search with largest/indomain_max)
    assert!(
        !result.search_annotations.is_empty(),
        "neighbours-new-2 must have search annotations"
    );

    // Must be an optimization problem (maximize)
    assert!(
        result.objective.is_some(),
        "neighbours-new-2 must be an optimization problem"
    );

    let config = SolverConfig {
        timeout_ms: Some(60_000), // 60s for a real benchmark
        all_solutions: false,
        global_deadline: None,
    };
    let mut output = Vec::new();
    let solutions = solve_branching(&result, &config, &mut output).expect("solve failed");

    let output_str = String::from_utf8(output).expect("valid utf8");

    // Must find at least one solution (this is a feasible problem)
    assert!(
        solutions >= 1,
        "neighbours-new-2 should be feasible, found 0 solutions. Output: {output_str}"
    );

    // Output must contain solution separator
    assert!(
        output_str.contains("----------"),
        "output must contain solution separator"
    );

    // Verify objective value is in valid range [8, 40]
    // The output variable is named "objective"
    for line in output_str.lines() {
        if line.starts_with("objective = ") {
            let val: i64 = line
                .trim_start_matches("objective = ")
                .trim_end_matches(';')
                .parse()
                .expect("objective must be an integer");
            assert!(
                (8..=40).contains(&val),
                "objective must be in [8, 40], got {val}"
            );
        }
    }
}

/// Verify translation of MiniZinc Challenge 2024: monitor-placement-1id.
///
/// This is an optimization (minimize) problem with `bool_search([...],
/// input_order, indomain_min, complete)`. All decision variables are boolean
/// (11 bools), with constraints: array_bool_and, bool_clause, bool2int,
/// int_lin_eq. The objective is derived from a sum of bool2int values.
///
/// We verify translation succeeds (all constraint types and bool_search
/// annotation parsing). Branching solve is NOT tested here because
/// the 1428-line benchmark causes stack overflow at the default 2MB thread
/// stack (recursive constraint encoding), and at larger stacks the
/// branching search is too slow for CI (bool_search over 11 vars = up to
/// 2^11 ay invocations).
///
/// Finding: The stack overflow indicates the translation recursion depth
/// is O(n_constraints), which is a scaling limitation for benchmarks with
/// >1000 constraints. Filed as @WORKER handoff.
///
/// Part of #273 (MiniZinc entry).
#[test]
fn branching_benchmark_monitor_placement_translates() {
    let fzn_path = benchmark_cp_path("monitor-placement-1id/hop_counting_based_zoo_Forthnet.fzn");
    if !fzn_path.exists() {
        eprintln!("benchmark not found: {}; skipping", fzn_path.display());
        return;
    }

    let fzn = std::fs::read_to_string(&fzn_path).expect("failed to read benchmark");

    // Run translation in a thread with an explicit 8MB stack to avoid
    // the default 2MB stack overflow on this 1428-constraint benchmark.
    let result = std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(move || {
            let model = ay_flatzinc_parser::parse_flatzinc(&fzn).expect("parse failed");
            translate(&model).expect("translate failed")
        })
        .expect("spawn thread")
        .join()
        .expect("translate thread panicked");

    // Translation must produce non-empty SMT-LIB
    assert!(
        !result.smtlib.is_empty(),
        "translation produced empty SMT-LIB for monitor-placement"
    );

    // Must have search annotations (bool_search)
    assert!(
        !result.search_annotations.is_empty(),
        "monitor-placement must have search annotations"
    );

    // Must be an optimization problem (minimize)
    assert!(
        result.objective.is_some(),
        "monitor-placement must be an optimization problem"
    );

    // Verify SMT-LIB contains expected constraint patterns
    assert!(
        result.smtlib.contains("(assert"),
        "SMT-LIB must contain assertions"
    );
}
