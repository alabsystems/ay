// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

fn render<F>(f: F) -> String
where
    F: FnOnce(&mut PbOutputWriter<Vec<u8>>) -> io::Result<()>,
{
    let mut writer = PbOutputWriter::new(Vec::new());
    f(&mut writer).expect("write should succeed");
    String::from_utf8(writer.into_inner()).expect("output should be utf-8")
}

#[test]
fn test_status_display_matches_competition_strings() {
    assert_eq!(PbStatus::Satisfiable.to_string(), "SATISFIABLE");
    assert_eq!(PbStatus::Unsatisfiable.to_string(), "UNSATISFIABLE");
    assert_eq!(PbStatus::OptimumFound.to_string(), "OPTIMUM FOUND");
    assert_eq!(PbStatus::Unknown.to_string(), "UNKNOWN");
    assert_eq!(PbStatus::Unsupported.to_string(), "UNSUPPORTED");
}

#[test]
fn test_write_comment_prefixes_each_line() {
    let out = render(|writer| writer.write_comment("first\nsecond\n"));
    assert_eq!(out, "c first\nc second\n");
}

#[test]
fn test_write_status() {
    let out = render(|writer| writer.write_status(PbStatus::Unsatisfiable));
    assert_eq!(out, "s UNSATISFIABLE\n");
}

#[test]
fn test_write_objective() {
    let out = render(|writer| writer.write_objective(-42));
    assert_eq!(out, "o -42\n");
}

#[test]
fn test_write_solution_outputs_all_variables() {
    let out = render(|writer| writer.write_solution(&[true, false, true]));
    assert_eq!(out, "v x1 -x2 x3\n");
}

#[test]
fn test_write_solution_wraps_at_80_columns() {
    let assignment = vec![true; 24];
    let out = render(|writer| writer.write_solution(&assignment));
    let lines: Vec<&str> = out.lines().collect();
    let flattened: Vec<&str> = lines
        .iter()
        .flat_map(|line| line.split_whitespace().skip(1))
        .collect();

    assert!(lines.len() > 1);
    assert!(lines.iter().all(|line| line.starts_with('v')));
    assert!(lines.iter().all(|line| line.len() <= 80));
    assert_eq!(
        flattened.join(" "),
        "x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24"
    );
}

#[test]
fn test_write_full_result_orders_objective_status_and_solution() {
    let solution = PbSolution {
        status: PbStatus::OptimumFound,
        assignment: vec![true, false],
        objective: Some(7),
    };
    let out = render(|writer| writer.write_full_result(&solution));
    assert_eq!(out, "o 7\ns OPTIMUM FOUND\nv x1 -x2\n");
}

#[test]
fn test_write_full_result_exact_keeps_positive_i64_overflow_objective() {
    let objective = i128::from(i64::MAX) + 1;
    let solution = PbExactSolution {
        status: PbStatus::OptimumFound,
        assignment: vec![true, true],
        objective: Some(objective),
    };
    let out = render(|writer| writer.write_full_result_exact(&solution));
    assert_eq!(out, format!("o {objective}\ns OPTIMUM FOUND\nv x1 x2\n"));
}

#[test]
fn test_write_full_result_exact_keeps_negative_i64_overflow_objective() {
    let objective = i128::from(i64::MIN) - 1;
    let solution = PbExactSolution {
        status: PbStatus::OptimumFound,
        assignment: vec![true, true],
        objective: Some(objective),
    };
    let out = render(|writer| writer.write_full_result_exact(&solution));
    assert_eq!(out, format!("o {objective}\ns OPTIMUM FOUND\nv x1 x2\n"));
}

#[test]
fn test_write_full_result_upgrades_unknown_with_partial_solution_to_sat() {
    let solution = PbSolution {
        status: PbStatus::Unknown,
        assignment: vec![false, true],
        objective: Some(11),
    };
    let out = render(|writer| writer.write_full_result(&solution));
    assert_eq!(out, "o 11\ns SATISFIABLE\nv -x1 x2\n");
}

#[test]
fn test_write_full_result_skips_empty_unknown_assignment() {
    let solution = PbSolution {
        status: PbStatus::Unknown,
        assignment: Vec::new(),
        objective: None,
    };
    let out = render(|writer| writer.write_full_result(&solution));
    assert_eq!(out, "s UNKNOWN\n");
}

#[test]
fn test_write_full_result_exact_unknown_with_objective_only_drops_final_o_line() {
    let solution = PbExactSolution {
        status: PbStatus::Unknown,
        assignment: Vec::new(),
        objective: Some(i128::from(i64::MAX) + 1),
    };
    let out = render(|writer| writer.write_full_result_exact(&solution));
    assert_eq!(out, "s UNKNOWN\n");
}

#[test]
fn test_write_full_result_unknown_with_objective_only_drops_final_o_line() {
    let solution = PbSolution {
        status: PbStatus::Unknown,
        assignment: Vec::new(),
        objective: Some(13),
    };
    let out = render(|writer| writer.write_full_result(&solution));
    assert_eq!(out, "s UNKNOWN\n");
}

#[test]
fn test_write_solution_empty_assignment_zero_variables() {
    let out = render(|writer| writer.write_solution(&[]));
    assert_eq!(out, "v \n");
}

#[test]
fn test_write_full_result_satisfiable_zero_variables() {
    // 0-variable SAT instance: should emit s SATISFIABLE and a `v ` line.
    let solution = PbSolution {
        status: PbStatus::Satisfiable,
        assignment: Vec::new(),
        objective: None,
    };
    let out = render(|writer| writer.write_full_result(&solution));
    assert_eq!(out, "s SATISFIABLE\nv \n");
}

#[test]
fn test_write_full_result_optimum_zero_variables() {
    let solution = PbSolution {
        status: PbStatus::OptimumFound,
        assignment: Vec::new(),
        objective: Some(0),
    };
    let out = render(|writer| writer.write_full_result(&solution));
    assert_eq!(out, "o 0\ns OPTIMUM FOUND\nv \n");
}

#[test]
fn test_write_full_result_unsatisfiable_no_v_line() {
    let solution = PbSolution {
        status: PbStatus::Unsatisfiable,
        assignment: Vec::new(),
        objective: None,
    };
    let out = render(|writer| writer.write_full_result(&solution));
    assert_eq!(out, "s UNSATISFIABLE\n");
}

#[test]
fn test_write_full_result_unsatisfiable_suppresses_stale_witness_and_objective() {
    let solution = PbSolution {
        status: PbStatus::Unsatisfiable,
        assignment: vec![true, false],
        objective: Some(17),
    };
    let out = render(|writer| writer.write_full_result(&solution));
    assert_eq!(out, "s UNSATISFIABLE\n");
}

#[test]
fn test_write_full_result_unsupported_suppresses_stale_witness_and_objective() {
    let solution = PbSolution {
        status: PbStatus::Unsupported,
        assignment: vec![false, true],
        objective: Some(23),
    };
    let out = render(|writer| writer.write_full_result(&solution));
    assert_eq!(out, "s UNSUPPORTED\n");
}

#[test]
fn test_write_solution_single_variable() {
    let out = render(|writer| writer.write_solution(&[true]));
    assert_eq!(out, "v x1\n");

    let out = render(|writer| writer.write_solution(&[false]));
    assert_eq!(out, "v -x1\n");
}

#[test]
fn test_write_objective_large_values() {
    let out = render(|writer| writer.write_objective(i128::MAX));
    assert_eq!(out, format!("o {}\n", i128::MAX));

    let out = render(|writer| writer.write_objective(i128::MIN));
    assert_eq!(out, format!("o {}\n", i128::MIN));
}

#[test]
fn test_write_objective_exact_beyond_i64() {
    let positive = i128::from(i64::MAX) + 1;
    let out = render(|writer| writer.write_objective_exact(positive));
    assert_eq!(out, format!("o {positive}\n"));

    let negative = i128::from(i64::MIN) - 1;
    let out = render(|writer| writer.write_objective_exact(negative));
    assert_eq!(out, format!("o {negative}\n"));
}

#[test]
fn test_write_full_result_unknown_with_partial_objective_and_assignment_becomes_sat() {
    // SIGTERM during optimization: best-known solution with UNKNOWN status.
    let solution = PbSolution {
        status: PbStatus::Unknown,
        assignment: vec![true, false, true],
        objective: Some(42),
    };
    let out = render(|writer| writer.write_full_result(&solution));
    assert_eq!(out, "o 42\ns SATISFIABLE\nv x1 -x2 x3\n");
}

#[test]
fn test_normalized_for_competition_upgrades_unknown_with_witness() {
    let solution = PbSolution {
        status: PbStatus::Unknown,
        assignment: vec![true, false],
        objective: Some(5),
    };

    assert_eq!(
        solution.normalized_for_competition(),
        PbSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![true, false],
            objective: Some(5),
        }
    );
}

#[test]
fn test_normalized_for_competition_strips_objective_only_unknown() {
    let solution = PbSolution {
        status: PbStatus::Unknown,
        assignment: Vec::new(),
        objective: Some(5),
    };

    assert_eq!(
        solution.normalized_for_competition(),
        PbSolution {
            status: PbStatus::Unknown,
            assignment: Vec::new(),
            objective: None,
        }
    );
}

#[test]
fn test_normalized_for_competition_strips_non_witness_status_payloads() {
    let solution = PbSolution {
        status: PbStatus::Unsupported,
        assignment: vec![true],
        objective: Some(5),
    };

    assert_eq!(
        solution.normalized_for_competition(),
        PbSolution {
            status: PbStatus::Unsupported,
            assignment: Vec::new(),
            objective: None,
        }
    );
}

#[test]
fn test_exact_solution_from_legacy_solution_preserves_competition_normalization() {
    let solution = PbSolution {
        status: PbStatus::Unknown,
        assignment: vec![true],
        objective: Some(5),
    };

    assert_eq!(
        PbExactSolution::from(&solution).normalized_for_competition(),
        PbExactSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![true],
            objective: Some(5),
        }
    );
}

#[test]
fn test_write_status_unsupported() {
    let out = render(|writer| writer.write_status(PbStatus::Unsupported));
    assert_eq!(out, "s UNSUPPORTED\n");
}

#[test]
fn test_write_comment_empty() {
    let out = render(|writer| writer.write_comment(""));
    assert_eq!(out, "c\n");
}
