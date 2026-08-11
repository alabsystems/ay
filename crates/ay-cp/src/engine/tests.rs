// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::domain::Domain;
use crate::encoder::OrderEncodingCapacityError;

#[cfg(debug_assertions)]
#[path = "tests_validate.rs"]
mod tests_validate;

#[path = "tests_cumulative.rs"]
mod tests_cumulative;

/// Helper: create a singleton-domain (constant) integer variable.
fn const_var(engine: &mut CpSatEngine, val: i64) -> IntVarId {
    engine.new_int_var(Domain::singleton(val), None)
}

/// Helper: create an array of singleton-domain (constant) integer variables.
fn const_vars(engine: &mut CpSatEngine, vals: &[i64]) -> Vec<IntVarId> {
    vals.iter().map(|&v| const_var(engine, v)).collect()
}

#[test]
fn test_engine_creation() {
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::new(1, 10), Some("x"));
    let y = engine.new_int_var(Domain::new(1, 10), Some("y"));
    assert_ne!(x, y);
}

#[test]
fn test_sparse_domain_registration_preserves_membership() {
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::from_values(&[1, 3, 5]), Some("x"));

    assert_eq!(engine.var_bounds(x), (1, 5));
    assert_eq!(engine.trail.lb(x), 1);
    assert_eq!(engine.trail.ub(x), 5);
    assert!(engine.trail.contains(x, 1));
    assert!(!engine.trail.contains(x, 2));
    assert!(engine.trail.contains(x, 3));
    assert!(!engine.trail.contains(x, 4));
    assert!(engine.trail.contains(x, 5));
}

#[test]
fn test_sparse_domain_root_holes_excluded() {
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::from_values(&[1, 3, 5]), Some("x"));
    assert_eq!(
        engine.encoder.num_literals(),
        0,
        "sparse holes must not allocate SAT literals before capacity preflight"
    );

    engine.add_constraint(Constraint::LinearGe {
        coeffs: vec![1],
        vars: vec![x],
        rhs: 2,
    });
    engine.add_constraint(Constraint::LinearLe {
        coeffs: vec![1],
        vars: vec![x],
        rhs: 4,
    });

    match engine.solve() {
        CpSolveResult::Sat(assignment) => {
            let x_val = assignment
                .iter()
                .find(|(var, _)| *var == x)
                .map(|(_, value)| *value)
                .expect("x must be assigned");
            assert_eq!(
                x_val, 3,
                "sparse-domain hole values must remain unreachable"
            );
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_alldiff_trivial_sat() {
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::new(1, 3), Some("x"));
    let y = engine.new_int_var(Domain::new(1, 3), Some("y"));
    let z = engine.new_int_var(Domain::new(1, 3), Some("z"));

    engine.add_constraint(Constraint::AllDifferent(vec![x, y, z]));

    match engine.solve() {
        CpSolveResult::Sat(assignment) => {
            let vals: Vec<i64> = assignment.iter().map(|(_, v)| *v).collect();
            let mut sorted = vals.clone();
            sorted.sort_unstable();
            sorted.dedup();
            assert_eq!(sorted.len(), 3, "all values must be distinct: {vals:?}");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_alldiff_unsat() {
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::new(1, 3), Some("x"));
    let y = engine.new_int_var(Domain::new(1, 3), Some("y"));
    let z = engine.new_int_var(Domain::new(1, 3), Some("z"));
    let w = engine.new_int_var(Domain::new(1, 3), Some("w"));

    engine.add_constraint(Constraint::AllDifferent(vec![x, y, z, w]));

    match engine.solve() {
        CpSolveResult::Unsat => {}
        other => panic!("expected UNSAT, got {other:?}"),
    }
}

#[test]
fn test_precompile_enrolls_ac_for_wide_sparse_alldiff_domains() {
    let mut engine = CpSatEngine::new();
    let a = engine.new_int_var(Domain::from_values(&[1, 200]), Some("a"));
    let b = engine.new_int_var(Domain::from_values(&[1, 200]), Some("b"));
    let c = engine.new_int_var(Domain::from_values(&[1, 2, 200]), Some("c"));
    let d = engine.new_int_var(Domain::from_values(&[2, 201]), Some("d"));

    engine.add_constraint(Constraint::AllDifferent(vec![a, b, c, d]));
    engine.pre_compile();

    assert!(
        engine
            .propagators
            .iter()
            .any(|prop| prop.name() == "alldifferent_bounds"),
        "bounds propagator should still be installed"
    );
    assert!(
        engine
            .propagators
            .iter()
            .any(|prop| prop.name() == "alldifferent_ac"),
        "AC propagator should use sparse cardinality, not interval span"
    );
}

#[test]
fn test_pre_compile_is_idempotent_for_order_encoding() {
    let mut engine = CpSatEngine::new();
    let _x = engine.new_int_var(Domain::new(0, 20), Some("x"));
    let _y = engine.new_int_var(Domain::new(0, 20), Some("y"));

    engine.pre_compile();
    let sat_vars_before = engine.sat.total_num_vars();
    let propagators_before = engine.propagators.len();

    engine.pre_compile();

    assert_eq!(
        engine.sat.total_num_vars(),
        sat_vars_before,
        "pre_compile must not recreate order-encoding SAT variables",
    );
    assert_eq!(
        engine.propagators.len(),
        propagators_before,
        "pre_compile must not duplicate propagators when no new constraints were added",
    );
}

#[test]
fn test_linear_le_sat() {
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::new(0, 10), Some("x"));
    let y = engine.new_int_var(Domain::new(0, 10), Some("y"));

    engine.add_constraint(Constraint::LinearLe {
        coeffs: vec![1, 1],
        vars: vec![x, y],
        rhs: 5,
    });

    match engine.solve() {
        CpSolveResult::Sat(assignment) => {
            let x_val = assignment.iter().find(|(v, _)| *v == x).unwrap().1;
            let y_val = assignment.iter().find(|(v, _)| *v == y).unwrap().1;
            assert!(
                x_val + y_val <= 5,
                "constraint violated: {x_val} + {y_val} > 5"
            );
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_linear_le_unsat() {
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::new(5, 10), Some("x"));
    let y = engine.new_int_var(Domain::new(5, 10), Some("y"));

    engine.add_constraint(Constraint::LinearLe {
        coeffs: vec![1, 1],
        vars: vec![x, y],
        rhs: 8,
    });

    match engine.solve() {
        CpSolveResult::Unsat => {}
        other => panic!("expected UNSAT, got {other:?}"),
    }
}

/// Set up an n-queens problem and encode diagonal constraints directly.
fn setup_nqueens(n: usize) -> CpSatEngine {
    let mut engine = CpSatEngine::new();
    let queens: Vec<IntVarId> = (0..n)
        .map(|i| engine.new_int_var(Domain::new(0, n as i64 - 1), Some(&format!("q{i}"))))
        .collect();
    engine.add_constraint(Constraint::AllDifferent(queens.clone()));
    encode_diagonal_constraints(&mut engine, &queens, n);
    engine
}

/// Encode diagonal constraints for n-queens: forbid q[i]=v ∧ q[j]=v±(j-i) for all pairs.
pub(super) fn encode_diagonal_constraints(engine: &mut CpSatEngine, queens: &[IntVarId], n: usize) {
    for i in 0..n {
        for j in (i + 1)..n {
            let diff = (j - i) as i64;
            for v in 0..n as i64 {
                for &target in &[v + diff, v - diff] {
                    if target >= 0 && target < n as i64 {
                        add_neq_clause(engine, queens[i], v, queens[j], target);
                    }
                }
            }
        }
    }
}

/// Add clause forbidding q_a = val_a ∧ q_b = val_b.
pub(super) fn add_neq_clause(
    engine: &mut CpSatEngine,
    qa: IntVarId,
    va: i64,
    qb: IntVarId,
    vb: i64,
) {
    let a_ge = engine.encoder.get_or_create_ge(&mut engine.sat, qa, va);
    let a_ge1 = engine.encoder.get_or_create_ge(&mut engine.sat, qa, va + 1);
    let b_ge = engine.encoder.get_or_create_ge(&mut engine.sat, qb, vb);
    let b_ge1 = engine.encoder.get_or_create_ge(&mut engine.sat, qb, vb + 1);
    engine
        .sat
        .add_clause(vec![a_ge.negated(), a_ge1, b_ge.negated(), b_ge1]);
}

/// Verify an n-queens solution: all-different columns, no diagonal conflicts.
fn verify_nqueens_solution(assignment: &[(IntVarId, i64)], n: usize) {
    assert_eq!(assignment.len(), n);
    let vals: Vec<i64> = assignment.iter().map(|(_, v)| *v).collect();

    let mut cols = vals.clone();
    cols.sort_unstable();
    cols.dedup();
    assert_eq!(cols.len(), n, "columns not all-different: {vals:?}");

    for i in 0..n {
        for j in (i + 1)..n {
            let col_diff = (vals[j] - vals[i]).unsigned_abs();
            let row_diff = (j - i) as u64;
            assert_ne!(
                col_diff, row_diff,
                "diagonal conflict: q[{i}]={}, q[{j}]={}",
                vals[i], vals[j]
            );
        }
    }
}

#[test]
fn test_4queens_sat() {
    let mut engine = setup_nqueens(4);
    match engine.solve() {
        CpSolveResult::Sat(assignment) => verify_nqueens_solution(&assignment, 4),
        other => panic!("4-queens should be SAT, got {other:?}"),
    }
}

#[test]
fn test_8queens_sat() {
    let mut engine = setup_nqueens(8);
    match engine.solve() {
        CpSolveResult::Sat(assignment) => verify_nqueens_solution(&assignment, 8),
        other => panic!("8-queens should be SAT, got {other:?}"),
    }
}

#[test]
fn test_20queens_sat() {
    let mut engine = setup_nqueens(20);
    match engine.solve() {
        CpSolveResult::Sat(assignment) => verify_nqueens_solution(&assignment, 20),
        other => panic!("20-queens should be SAT, got {other:?}"),
    }
}

/// Golomb ruler of order 6: find 6 marks on a ruler [0..17]
/// such that all C(6,2)=15 pairwise differences are distinct.
/// Optimal length is 17 (marks: {0, 1, 4, 10, 12, 17}).
#[test]
fn test_golomb6_sat() {
    let n = 6;
    let max_len = 17;
    let mut engine = CpSatEngine::new();

    // Create mark variables: m[0]=0 (fixed), m[1..5] ∈ [1..max_len]
    let marks: Vec<IntVarId> = (0..n)
        .map(|i| {
            if i == 0 {
                engine.new_int_var(Domain::new(0, 0), Some("m0"))
            } else {
                engine.new_int_var(Domain::new(1, max_len), Some(&format!("m{i}")))
            }
        })
        .collect();

    // Ordering: m[i] < m[i+1] → m[i+1] - m[i] >= 1
    for i in 0..(n - 1) {
        engine.add_constraint(Constraint::LinearGe {
            coeffs: vec![-1, 1],
            vars: vec![marks[i], marks[i + 1]],
            rhs: 1,
        });
    }

    // Create difference variables: d[k] = m[j] - m[i] for all i < j
    let mut diffs = Vec::new();
    for i in 0..n {
        for j in (i + 1)..n {
            let d = engine.new_int_var(Domain::new(1, max_len), Some(&format!("d{i}{j}")));
            // d = m[j] - m[i] → m[j] - m[i] - d = 0
            engine.add_constraint(Constraint::LinearEq {
                coeffs: vec![-1, 1, -1],
                vars: vec![marks[i], marks[j], d],
                rhs: 0,
            });
            diffs.push(d);
        }
    }

    // All differences must be distinct
    engine.add_constraint(Constraint::AllDifferent(diffs.clone()));

    match engine.solve() {
        CpSolveResult::Sat(assignment) => {
            let mark_vals: Vec<i64> = marks
                .iter()
                .map(|m| assignment.iter().find(|(v, _)| v == m).unwrap().1)
                .collect();

            // Verify ordering
            for i in 0..(n - 1) {
                assert!(
                    mark_vals[i] < mark_vals[i + 1],
                    "marks not ordered: {mark_vals:?}"
                );
            }

            // Verify all differences distinct
            let mut diffs_computed = Vec::new();
            for i in 0..n {
                for j in (i + 1)..n {
                    diffs_computed.push(mark_vals[j] - mark_vals[i]);
                }
            }
            let mut sorted = diffs_computed.clone();
            sorted.sort_unstable();
            sorted.dedup();
            assert_eq!(
                sorted.len(),
                diffs_computed.len(),
                "differences not all distinct: marks={mark_vals:?}, diffs={diffs_computed:?}"
            );
        }
        other => panic!("golomb-6 should be SAT, got {other:?}"),
    }
}

#[test]
fn test_linear_eq() {
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::new(0, 10), Some("x"));
    let y = engine.new_int_var(Domain::new(0, 10), Some("y"));

    engine.add_constraint(Constraint::LinearEq {
        coeffs: vec![1, 1],
        vars: vec![x, y],
        rhs: 7,
    });

    match engine.solve() {
        CpSolveResult::Sat(assignment) => {
            let x_val = assignment.iter().find(|(v, _)| *v == x).unwrap().1;
            let y_val = assignment.iter().find(|(v, _)| *v == y).unwrap().1;
            assert_eq!(
                x_val + y_val,
                7,
                "constraint violated: {x_val} + {y_val} != 7"
            );
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_combined_alldiff_and_linear() {
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::new(1, 5), Some("x"));
    let y = engine.new_int_var(Domain::new(1, 5), Some("y"));
    let z = engine.new_int_var(Domain::new(1, 5), Some("z"));

    engine.add_constraint(Constraint::AllDifferent(vec![x, y, z]));
    engine.add_constraint(Constraint::LinearLe {
        coeffs: vec![1, 1, 1],
        vars: vec![x, y, z],
        rhs: 9,
    });

    match engine.solve() {
        CpSolveResult::Sat(assignment) => {
            let vals: Vec<i64> = assignment.iter().map(|(_, v)| *v).collect();
            let mut sorted = vals.clone();
            sorted.sort_unstable();
            sorted.dedup();
            assert_eq!(sorted.len(), 3, "all values must be distinct: {vals:?}");
            let sum: i64 = vals.iter().sum();
            assert!(sum <= 9, "sum constraint violated: {sum} > 9");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// ============= Table constraint integration tests =============

#[test]
fn test_table_sat() {
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::new(1, 5), Some("x"));
    let y = engine.new_int_var(Domain::new(1, 5), Some("y"));

    // (x, y) must be one of: (1,3), (2,4), (3,5)
    engine.add_constraint(Constraint::Table {
        vars: vec![x, y],
        tuples: vec![vec![1, 3], vec![2, 4], vec![3, 5]],
    });

    match engine.solve() {
        CpSolveResult::Sat(assignment) => {
            let x_val = assignment.iter().find(|(v, _)| *v == x).unwrap().1;
            let y_val = assignment.iter().find(|(v, _)| *v == y).unwrap().1;
            let valid = [(1, 3), (2, 4), (3, 5)];
            assert!(
                valid.contains(&(x_val, y_val)),
                "assignment ({x_val}, {y_val}) not in allowed tuples"
            );
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_table_unsat() {
    let mut engine = CpSatEngine::new();
    // x ∈ [4, 5] — but tuples only have x values 1,2,3
    let x = engine.new_int_var(Domain::new(4, 5), Some("x"));
    let y = engine.new_int_var(Domain::new(1, 5), Some("y"));

    engine.add_constraint(Constraint::Table {
        vars: vec![x, y],
        tuples: vec![vec![1, 3], vec![2, 4], vec![3, 5]],
    });

    match engine.solve() {
        CpSolveResult::Unsat => {}
        other => panic!("expected UNSAT, got {other:?}"),
    }
}

#[test]
fn test_table_with_alldiff() {
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::new(1, 3), Some("x"));
    let y = engine.new_int_var(Domain::new(1, 3), Some("y"));
    let z = engine.new_int_var(Domain::new(1, 3), Some("z"));

    // Table constrains (x, y) to specific pairs
    engine.add_constraint(Constraint::Table {
        vars: vec![x, y],
        tuples: vec![vec![1, 2], vec![2, 3], vec![3, 1]],
    });
    // z must differ from both x and y
    engine.add_constraint(Constraint::AllDifferent(vec![x, y, z]));

    match engine.solve() {
        CpSolveResult::Sat(assignment) => {
            let x_val = assignment.iter().find(|(v, _)| *v == x).unwrap().1;
            let y_val = assignment.iter().find(|(v, _)| *v == y).unwrap().1;
            let z_val = assignment.iter().find(|(v, _)| *v == z).unwrap().1;
            let valid_pairs = [(1, 2), (2, 3), (3, 1)];
            assert!(
                valid_pairs.contains(&(x_val, y_val)),
                "table constraint violated: ({x_val}, {y_val})"
            );
            assert_ne!(x_val, z_val, "alldiff violated: x={x_val}, z={z_val}");
            assert_ne!(y_val, z_val, "alldiff violated: y={y_val}, z={z_val}");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

/// Regression test for #6591: table propagator must respect sparse-domain holes.
///
/// x ∈ {1, 3} (sparse: 2 is absent)
/// y ∈ {1, 2, 3}
/// Table: {(1,1), (2,2), (3,3)}
///
/// Since x cannot be 2, the only supported tuples are (1,1) and (3,3).
/// The solver must not assign (x=2, y=2) — that would require x=2 which
/// is absent from the sparse domain. The solution must be from {(1,1), (3,3)}.
#[test]
fn test_table_sparse_domain_excludes_hole_values() {
    let mut engine = CpSatEngine::new();
    // x ∈ {1, 3}: interval [1,3] but 2 is absent
    let x = engine.new_int_var(Domain::from_values(&[1, 3]), Some("x"));
    // y ∈ {1, 2, 3}: dense
    let y = engine.new_int_var(Domain::new(1, 3), Some("y"));

    engine.add_constraint(Constraint::Table {
        vars: vec![x, y],
        tuples: vec![vec![1, 1], vec![2, 2], vec![3, 3]],
    });

    match engine.solve() {
        CpSolveResult::Sat(assignment) => {
            let x_val = assignment.iter().find(|(v, _)| *v == x).unwrap().1;
            let y_val = assignment.iter().find(|(v, _)| *v == y).unwrap().1;
            assert!(
                (x_val == 1 && y_val == 1) || (x_val == 3 && y_val == 3),
                "table with sparse domain: assignment ({x_val}, {y_val}) should be \
                 (1,1) or (3,3), not (2,2) — x=2 is absent from the domain"
            );
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

/// Regression test for #6591: table + AllDifferent with sparse domains.
///
/// Combines the sparse-domain table fix with AllDifferent to verify that
/// interior holes are respected when both propagators interact.
#[test]
fn test_table_sparse_domain_with_alldiff() {
    let mut engine = CpSatEngine::new();
    // x ∈ {1, 3}, y ∈ {1, 3}, z ∈ {1, 2, 3}
    let x = engine.new_int_var(Domain::from_values(&[1, 3]), Some("x"));
    let y = engine.new_int_var(Domain::from_values(&[1, 3]), Some("y"));
    let z = engine.new_int_var(Domain::new(1, 3), Some("z"));

    // Table constrains (x, y): only (1,3) and (3,1) allowed
    engine.add_constraint(Constraint::Table {
        vars: vec![x, y],
        tuples: vec![vec![1, 3], vec![3, 1]],
    });
    // z must differ from x and y
    engine.add_constraint(Constraint::AllDifferent(vec![x, y, z]));

    match engine.solve() {
        CpSolveResult::Sat(assignment) => {
            let x_val = assignment.iter().find(|(v, _)| *v == x).unwrap().1;
            let y_val = assignment.iter().find(|(v, _)| *v == y).unwrap().1;
            let z_val = assignment.iter().find(|(v, _)| *v == z).unwrap().1;
            let valid_pairs = [(1, 3), (3, 1)];
            assert!(
                valid_pairs.contains(&(x_val, y_val)),
                "table violated: ({x_val}, {y_val})"
            );
            assert_ne!(x_val, z_val, "alldiff violated: x=z={x_val}");
            assert_ne!(y_val, z_val, "alldiff violated: y=z={y_val}");
            // z must be 2 since x and y are {1,3} or {3,1}
            assert_eq!(z_val, 2, "z must be 2 (only value not in {{1,3}})");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// ============= Element constraint integration tests =============

#[test]
fn test_element_sat_fixed_index() {
    let mut engine = CpSatEngine::new();
    let index = engine.new_int_var(Domain::new(1, 1), Some("index")); // fixed to 1
    let a0 = engine.new_int_var(Domain::new(10, 10), Some("a0")); // fixed 10
    let a1 = engine.new_int_var(Domain::new(20, 20), Some("a1")); // fixed 20
    let a2 = engine.new_int_var(Domain::new(30, 30), Some("a2")); // fixed 30
    let result = engine.new_int_var(Domain::new(0, 50), Some("result"));

    engine.add_constraint(Constraint::Element {
        index,
        array: vec![a0, a1, a2],
        result,
    });

    match engine.solve() {
        CpSolveResult::Sat(assignment) => {
            let result_val = assignment.iter().find(|(v, _)| *v == result).unwrap().1;
            assert_eq!(
                result_val, 20,
                "element constraint: result should be array[1] = 20, got {result_val}"
            );
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_element_sat_free_index() {
    let mut engine = CpSatEngine::new();
    let index = engine.new_int_var(Domain::new(0, 2), Some("index"));
    let a0 = engine.new_int_var(Domain::new(10, 10), Some("a0"));
    let a1 = engine.new_int_var(Domain::new(20, 20), Some("a1"));
    let a2 = engine.new_int_var(Domain::new(30, 30), Some("a2"));
    let result = engine.new_int_var(Domain::new(0, 50), Some("result"));

    engine.add_constraint(Constraint::Element {
        index,
        array: vec![a0, a1, a2],
        result,
    });

    match engine.solve() {
        CpSolveResult::Sat(assignment) => {
            let idx_val = assignment.iter().find(|(v, _)| *v == index).unwrap().1;
            let result_val = assignment.iter().find(|(v, _)| *v == result).unwrap().1;
            let expected = match idx_val {
                0 => 10,
                1 => 20,
                2 => 30,
                _ => panic!("invalid index {idx_val}"),
            };
            assert_eq!(
                result_val, expected,
                "element: result should be array[{idx_val}] = {expected}, got {result_val}"
            );
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_element_unsat() {
    let mut engine = CpSatEngine::new();
    let index = engine.new_int_var(Domain::new(0, 1), Some("index"));
    let a0 = engine.new_int_var(Domain::new(10, 10), Some("a0"));
    let a1 = engine.new_int_var(Domain::new(20, 20), Some("a1"));
    let result = engine.new_int_var(Domain::new(50, 60), Some("result")); // impossible

    engine.add_constraint(Constraint::Element {
        index,
        array: vec![a0, a1],
        result,
    });

    match engine.solve() {
        CpSolveResult::Unsat => {}
        other => panic!("expected UNSAT, got {other:?}"),
    }
}

#[test]
fn test_element_with_linear() {
    let mut engine = CpSatEngine::new();
    let index = engine.new_int_var(Domain::new(0, 2), Some("index"));
    let a0 = engine.new_int_var(Domain::new(1, 5), Some("a0"));
    let a1 = engine.new_int_var(Domain::new(1, 5), Some("a1"));
    let a2 = engine.new_int_var(Domain::new(1, 5), Some("a2"));
    let result = engine.new_int_var(Domain::new(1, 5), Some("result"));

    engine.add_constraint(Constraint::Element {
        index,
        array: vec![a0, a1, a2],
        result,
    });
    // result + index <= 4
    engine.add_constraint(Constraint::LinearLe {
        coeffs: vec![1, 1],
        vars: vec![result, index],
        rhs: 4,
    });

    match engine.solve() {
        CpSolveResult::Sat(assignment) => {
            let idx_val = assignment.iter().find(|(v, _)| *v == index).unwrap().1;
            let result_val = assignment.iter().find(|(v, _)| *v == result).unwrap().1;
            let arr_vals: Vec<i64> = [a0, a1, a2]
                .iter()
                .map(|v| assignment.iter().find(|(id, _)| id == v).unwrap().1)
                .collect();
            assert_eq!(
                result_val, arr_vals[idx_val as usize],
                "element violated: result={result_val} != array[{idx_val}]={}",
                arr_vals[idx_val as usize]
            );
            assert!(
                result_val + idx_val <= 4,
                "linear violated: {result_val} + {idx_val} > 4"
            );
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// ── Phase 2 gate tests: golomb-6 ──────────────────
// Note: test_20queens_sat already defined above (line 177).

/// Build a Golomb ruler model with `n` marks and max length `max_len`.
/// Returns (engine, mark_variable_ids).
fn setup_golomb(n: usize, max_len: i64) -> (CpSatEngine, Vec<IntVarId>) {
    let mut engine = CpSatEngine::new();

    // Mark variables: m[0] = 0, m[i] in [1..max_len]
    let mut marks = Vec::new();
    marks.push(engine.new_int_var(Domain::new(0, 0), Some("m0")));
    for i in 1..n {
        marks.push(engine.new_int_var(Domain::new(1, max_len), Some(&format!("m{i}"))));
    }

    // Marks strictly increasing: m[i+1] - m[i] >= 1
    for i in 0..(n - 1) {
        engine.add_constraint(Constraint::LinearGe {
            coeffs: vec![-1, 1],
            vars: vec![marks[i], marks[i + 1]],
            rhs: 1,
        });
    }

    // Difference variables d[i,j] = m[j] - m[i], all distinct
    let mut diffs = Vec::new();
    for i in 0..n {
        for j in (i + 1)..n {
            let d = engine.new_int_var(Domain::new(1, max_len), Some(&format!("d{i}_{j}")));
            engine.add_constraint(Constraint::LinearEq {
                coeffs: vec![1, -1, 1],
                vars: vec![d, marks[j], marks[i]],
                rhs: 0,
            });
            diffs.push(d);
        }
    }
    engine.add_constraint(Constraint::AllDifferent(diffs));
    (engine, marks)
}

/// Verify a Golomb ruler solution: marks increasing, all differences distinct.
fn verify_golomb_solution(assignment: &[(IntVarId, i64)], marks: &[IntVarId]) {
    let mark_vals: Vec<i64> = marks
        .iter()
        .map(|m| assignment.iter().find(|(v, _)| v == m).unwrap().1)
        .collect();
    let n = marks.len();
    for i in 0..(n - 1) {
        assert!(
            mark_vals[i] < mark_vals[i + 1],
            "marks not increasing: {mark_vals:?}"
        );
    }
    let mut all_diffs = Vec::new();
    for i in 0..n {
        for j in (i + 1)..n {
            all_diffs.push(mark_vals[j] - mark_vals[i]);
        }
    }
    let mut sorted = all_diffs.clone();
    sorted.sort_unstable();
    sorted.dedup();
    assert_eq!(
        sorted.len(),
        all_diffs.len(),
        "differences not all distinct: {all_diffs:?}"
    );
}

/// Golomb ruler order 6: test feasibility with relaxed max length 20 (optimal is 17).
#[test]
fn test_golomb_6_sat() {
    let (mut engine, marks) = setup_golomb(6, 20);
    match engine.solve() {
        CpSolveResult::Sat(assignment) => verify_golomb_solution(&assignment, &marks),
        other => panic!("golomb-6 should be SAT, got {other:?}"),
    }
}

// ── Search strategy integration tests ──────────────────────────

#[test]
fn test_search_strategy_first_fail_4queens() {
    use crate::search::SearchStrategy;
    let mut engine = setup_nqueens(4);
    engine.set_search_strategy(SearchStrategy::FirstFail);
    match engine.solve() {
        CpSolveResult::Sat(assignment) => verify_nqueens_solution(&assignment, 4),
        other => panic!("4-queens with first-fail should be SAT, got {other:?}"),
    }
}

#[test]
fn test_search_strategy_dom_wdeg_4queens() {
    use crate::search::SearchStrategy;
    let mut engine = setup_nqueens(4);
    engine.set_search_strategy(SearchStrategy::DomWDeg);
    match engine.solve() {
        CpSolveResult::Sat(assignment) => verify_nqueens_solution(&assignment, 4),
        other => panic!("4-queens with dom/wdeg should be SAT, got {other:?}"),
    }
}

#[test]
fn test_search_strategy_activity_4queens() {
    use crate::search::SearchStrategy;
    let mut engine = setup_nqueens(4);
    engine.set_search_strategy(SearchStrategy::Activity);
    match engine.solve() {
        CpSolveResult::Sat(assignment) => verify_nqueens_solution(&assignment, 4),
        other => panic!("4-queens with activity should be SAT, got {other:?}"),
    }
}

#[test]
fn test_search_strategy_dom_wdeg_8queens() {
    use crate::search::SearchStrategy;
    let mut engine = setup_nqueens(8);
    engine.set_search_strategy(SearchStrategy::DomWDeg);
    match engine.solve() {
        CpSolveResult::Sat(assignment) => verify_nqueens_solution(&assignment, 8),
        other => panic!("8-queens with dom/wdeg should be SAT, got {other:?}"),
    }
}

// ── Prover heuristic correctness tests (P1:447) ──────────────────

/// 3-queens is UNSAT — exercises backtracking and conflict-driven weight learning.
/// All three heuristics must agree on UNSAT.
#[test]
fn test_3queens_unsat_first_fail() {
    use crate::search::SearchStrategy;
    let mut engine = setup_nqueens(3);
    engine.set_search_strategy(SearchStrategy::FirstFail);
    match engine.solve() {
        CpSolveResult::Unsat => {}
        other => panic!("3-queens should be UNSAT, got {other:?}"),
    }
}

#[test]
fn test_3queens_unsat_dom_wdeg() {
    use crate::search::SearchStrategy;
    let mut engine = setup_nqueens(3);
    engine.set_search_strategy(SearchStrategy::DomWDeg);
    match engine.solve() {
        CpSolveResult::Unsat => {}
        other => panic!("3-queens should be UNSAT, got {other:?}"),
    }
}

#[test]
fn test_3queens_unsat_activity() {
    use crate::search::SearchStrategy;
    let mut engine = setup_nqueens(3);
    engine.set_search_strategy(SearchStrategy::Activity);
    match engine.solve() {
        CpSolveResult::Unsat => {}
        other => panic!("3-queens should be UNSAT, got {other:?}"),
    }
}

/// 12-queens with dom/wdeg — exercises weight learning over many conflicts.
/// Larger than 8-queens to ensure the heuristic is meaningfully exercised.
#[test]
fn test_12queens_dom_wdeg() {
    use crate::search::SearchStrategy;
    let mut engine = setup_nqueens(12);
    engine.set_search_strategy(SearchStrategy::DomWDeg);
    match engine.solve() {
        CpSolveResult::Sat(assignment) => verify_nqueens_solution(&assignment, 12),
        other => panic!("12-queens with dom/wdeg should be SAT, got {other:?}"),
    }
}

/// 12-queens with activity — exercises activity bumping over many conflicts.
#[test]
fn test_12queens_activity() {
    use crate::search::SearchStrategy;
    let mut engine = setup_nqueens(12);
    engine.set_search_strategy(SearchStrategy::Activity);
    match engine.solve() {
        CpSolveResult::Sat(assignment) => verify_nqueens_solution(&assignment, 12),
        other => panic!("12-queens with activity should be SAT, got {other:?}"),
    }
}

/// Cumulative + AllDifferent UNSAT with dom/wdeg — exercises combined propagators.
/// 4 tasks of duration 3 on resource capacity 1, with start times in [0,3].
/// The minimum schedule length is 4*3=12, but horizon is only 3+3-1=5. UNSAT.
#[test]
fn test_cumulative_unsat_dom_wdeg() {
    use crate::search::SearchStrategy;
    let mut engine = CpSatEngine::new();
    let s0 = engine.new_int_var(Domain::new(0, 3), Some("s0"));
    let s1 = engine.new_int_var(Domain::new(0, 3), Some("s1"));
    let s2 = engine.new_int_var(Domain::new(0, 3), Some("s2"));
    let s3 = engine.new_int_var(Domain::new(0, 3), Some("s3"));

    let durs = const_vars(&mut engine, &[3, 3, 3, 3]);
    let dems = const_vars(&mut engine, &[1, 1, 1, 1]);
    engine.add_constraint(Constraint::Cumulative {
        starts: vec![s0, s1, s2, s3],
        durations: durs,
        demands: dems,
        capacity: 1,
    });
    engine.add_constraint(Constraint::AllDifferent(vec![s0, s1, s2, s3]));

    engine.set_search_strategy(SearchStrategy::DomWDeg);
    match engine.solve() {
        CpSolveResult::Unsat => {}
        other => panic!("expected UNSAT with dom/wdeg, got {other:?}"),
    }
}

#[test]
fn test_circuit_3_nodes() {
    // 3-node circuit with 1-based indexing: vars[i] = successor of node i
    // Must form a Hamiltonian cycle: e.g., 1→2→3→1 or 1→3→2→1
    let mut engine = CpSatEngine::new();
    let x0 = engine.new_int_var(Domain::new(1, 3), Some("x0"));
    let x1 = engine.new_int_var(Domain::new(1, 3), Some("x1"));
    let x2 = engine.new_int_var(Domain::new(1, 3), Some("x2"));

    engine.add_constraint(Constraint::Circuit(vec![x0, x1, x2]));

    match engine.solve() {
        CpSolveResult::Sat(assignment) => {
            let val =
                |var: IntVarId| -> i64 { assignment.iter().find(|(id, _)| *id == var).unwrap().1 };
            let v0 = val(x0);
            let v1 = val(x1);
            let v2 = val(x2);
            // All different (required for circuit)
            assert_ne!(v0, v1);
            assert_ne!(v0, v2);
            assert_ne!(v1, v2);
            // No self-loops
            assert_ne!(v0, 1, "node 0 (1-based) cannot point to itself");
            assert_ne!(v1, 2, "node 1 (1-based) cannot point to itself");
            assert_ne!(v2, 3, "node 2 (1-based) cannot point to itself");
            // Check it forms a single cycle: follow edges from node 1
            let succ = [0, v0, v1, v2]; // 1-indexed
            let mut visited = [false; 4];
            let mut cur = 1i64;
            for _ in 0..3 {
                assert!(!visited[cur as usize], "visited {cur} twice");
                visited[cur as usize] = true;
                cur = succ[cur as usize];
            }
            assert_eq!(cur, 1, "cycle must return to start");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_circuit_no_self_loop() {
    // 2-node circuit: x0 ∈ {1,2}, x1 ∈ {1,2}
    // Only valid cycle: 1→2→1 (x0=2, x1=1)
    let mut engine = CpSatEngine::new();
    let x0 = engine.new_int_var(Domain::new(1, 2), Some("x0"));
    let x1 = engine.new_int_var(Domain::new(1, 2), Some("x1"));

    engine.add_constraint(Constraint::Circuit(vec![x0, x1]));

    match engine.solve() {
        CpSolveResult::Sat(assignment) => {
            let val =
                |var: IntVarId| -> i64 { assignment.iter().find(|(id, _)| *id == var).unwrap().1 };
            assert_eq!(val(x0), 2, "x0 must be 2");
            assert_eq!(val(x1), 1, "x1 must be 1");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_inverse_3_vars() {
    // inverse(x, y): x[y[i]] = i and y[x[i]] = i (1-based)
    // For n=3 with domain {1,2,3}, x and y are inverse permutations
    let mut engine = CpSatEngine::new();
    let x0 = engine.new_int_var(Domain::new(1, 3), Some("x0"));
    let x1 = engine.new_int_var(Domain::new(1, 3), Some("x1"));
    let x2 = engine.new_int_var(Domain::new(1, 3), Some("x2"));
    let y0 = engine.new_int_var(Domain::new(1, 3), Some("y0"));
    let y1 = engine.new_int_var(Domain::new(1, 3), Some("y1"));
    let y2 = engine.new_int_var(Domain::new(1, 3), Some("y2"));

    engine.add_constraint(Constraint::Inverse {
        x: vec![x0, x1, x2],
        y: vec![y0, y1, y2],
    });

    match engine.solve() {
        CpSolveResult::Sat(assignment) => {
            let val =
                |var: IntVarId| -> i64 { assignment.iter().find(|(id, _)| *id == var).unwrap().1 };
            let xv = [val(x0), val(x1), val(x2)];
            let yv = [val(y0), val(y1), val(y2)];
            // Check inverse property: x[y[i]-1] = i+1 and y[x[i]-1] = i+1
            for i in 0..3 {
                let yi = yv[i] as usize - 1;
                assert_eq!(xv[yi], (i + 1) as i64, "x[y[{i}]-1] should be {}", i + 1);
                let xi = xv[i] as usize - 1;
                assert_eq!(yv[xi], (i + 1) as i64, "y[x[{i}]-1] should be {}", i + 1);
            }
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

/// Test diffn: 3 unit squares must be placed without overlap in a 2x2 grid.
/// Only 3 positions in a 2x2 grid, so SAT (but barely — 4th square would be UNSAT).
#[test]
fn test_diffn_3_unit_squares_in_2x2() {
    let mut engine = CpSatEngine::new();
    let x: Vec<IntVarId> = (0..3)
        .map(|i| engine.new_int_var(Domain::new(0, 1), Some(&format!("x{i}"))))
        .collect();
    let y: Vec<IntVarId> = (0..3)
        .map(|i| engine.new_int_var(Domain::new(0, 1), Some(&format!("y{i}"))))
        .collect();
    let dx = const_vars(&mut engine, &[1, 1, 1]);
    let dy = const_vars(&mut engine, &[1, 1, 1]);

    engine.add_constraint(Constraint::Diffn {
        x: x.clone(),
        y: y.clone(),
        dx,
        dy,
    });

    match engine.solve() {
        CpSolveResult::Sat(assignment) => {
            let val =
                |v: IntVarId| -> i64 { assignment.iter().find(|(id, _)| *id == v).unwrap().1 };
            // Verify no overlap: for each pair, at least one separation holds
            for i in 0..3 {
                for j in (i + 1)..3 {
                    let xi = val(x[i]);
                    let xj = val(x[j]);
                    let yi = val(y[i]);
                    let yj = val(y[j]);
                    // At least one of the four non-overlap directions
                    let sep = (xi < xj) || (xj < xi) || (yi < yj) || (yj < yi);
                    assert!(
                        sep,
                        "rectangles {i} ({xi},{yi}) and {j} ({xj},{yj}) overlap"
                    );
                }
            }
        }
        other => panic!("expected SAT for 3 unit squares in 2x2, got {other:?}"),
    }
}

/// Test diffn UNSAT: 5 unit squares cannot fit in a 2x2 grid.
#[test]
fn test_diffn_5_unit_squares_unsat() {
    let mut engine = CpSatEngine::new();
    let x: Vec<IntVarId> = (0..5)
        .map(|i| engine.new_int_var(Domain::new(0, 1), Some(&format!("x{i}"))))
        .collect();
    let y: Vec<IntVarId> = (0..5)
        .map(|i| engine.new_int_var(Domain::new(0, 1), Some(&format!("y{i}"))))
        .collect();
    let dx = const_vars(&mut engine, &[1, 1, 1, 1, 1]);
    let dy = const_vars(&mut engine, &[1, 1, 1, 1, 1]);

    engine.add_constraint(Constraint::Diffn { x, y, dx, dy });

    match engine.solve() {
        CpSolveResult::Unsat => {} // expected
        other => panic!("expected UNSAT (5 unit squares in 2x2 grid), got {other:?}"),
    }
}

/// Test diffn with variable-sized rectangles: 2x1 and 1x2 in 2x2 grid.
#[test]
fn test_diffn_variable_sizes() {
    let mut engine = CpSatEngine::new();
    // Rectangle 0: 2x1, Rectangle 1: 1x2
    let x = vec![
        engine.new_int_var(Domain::new(0, 1), Some("x0")),
        engine.new_int_var(Domain::new(0, 1), Some("x1")),
    ];
    let y = vec![
        engine.new_int_var(Domain::new(0, 1), Some("y0")),
        engine.new_int_var(Domain::new(0, 1), Some("y1")),
    ];
    let dx = const_vars(&mut engine, &[2, 1]);
    let dy = const_vars(&mut engine, &[1, 2]);

    engine.add_constraint(Constraint::Diffn {
        x: x.clone(),
        y: y.clone(),
        dx,
        dy,
    });

    match engine.solve() {
        CpSolveResult::Sat(assignment) => {
            let val =
                |v: IntVarId| -> i64 { assignment.iter().find(|(id, _)| *id == v).unwrap().1 };
            let x0 = val(x[0]);
            let y0 = val(y[0]);
            let x1 = val(x[1]);
            let y1 = val(y[1]);
            // Rect 0: (x0, y0) to (x0+2, y0+1)
            // Rect 1: (x1, y1) to (x1+1, y1+2)
            let sep = (x0 + 1 < x1) || (x1 < x0) || (y0 < y1) || (y1 + 1 < y0);
            assert!(
                sep,
                "rectangles overlap: r0=({x0},{y0},2x1) r1=({x1},{y1},1x2)"
            );
        }
        other => panic!("expected SAT for variable-sized rectangles, got {other:?}"),
    }
}

#[test]
fn test_diffn_extreme_big_m_overlap_unsat() {
    let mut engine = CpSatEngine::new();
    let x = const_vars(&mut engine, &[1, 1]);
    let y = const_vars(&mut engine, &[0, 0]);
    let dx = const_vars(&mut engine, &[i64::MAX, 1]);
    let dy = const_vars(&mut engine, &[1, 1]);

    engine.add_constraint(Constraint::Diffn { x, y, dx, dy });

    assert!(
        matches!(engine.solve(), CpSolveResult::Unsat),
        "overlapping rectangles must remain UNSAT when a Big-M bound exceeds i64"
    );
}

/// Regression test: incremental optimization loop must find improving solutions.
///
/// Simulates the optimization loop manually: solve, add upper bound, solve again.
/// The bug was that the SAT solver returned spurious UNSAT after bound tightening,
/// causing the optimizer to declare optimality prematurely.
#[test]
fn test_incremental_optimization_no_spurious_unsat() {
    // Simple problem: x in [0,10], y in [0,10], x + y = obj, obj in [0,20]
    // Constraint: x >= 3 and y >= 2, so minimum obj = 5
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::new(0, 10), Some("x"));
    let y = engine.new_int_var(Domain::new(0, 10), Some("y"));
    let obj = engine.new_int_var(Domain::new(0, 20), Some("obj"));

    // x + y - obj = 0  (obj = x + y)
    use crate::propagator::Constraint;
    engine.add_constraint(Constraint::LinearEq {
        coeffs: vec![1, 1, -1],
        vars: vec![x, y, obj],
        rhs: 0,
    });
    // x >= 3  →  -x <= -3
    engine.add_constraint(Constraint::LinearLe {
        coeffs: vec![-1],
        vars: vec![x],
        rhs: -3,
    });
    // y >= 2  →  -y <= -2
    engine.add_constraint(Constraint::LinearLe {
        coeffs: vec![-1],
        vars: vec![y],
        rhs: -2,
    });

    // Pre-compile to allocate order encoding literals
    engine.pre_compile();

    // First solve: should find some solution
    let r1 = engine.solve();
    let obj1 = match r1 {
        CpSolveResult::Sat(ref assignment) => assignment.iter().find(|(v, _)| *v == obj).unwrap().1,
        other => panic!("first solve should be SAT, got {other:?}"),
    };
    eprintln!("solve 1: obj={obj1}");
    assert!(obj1 >= 5, "obj must be >= 5 (x>=3, y>=2)");

    // Tighten bound: obj <= obj1 - 1
    engine.add_upper_bound(obj, obj1 - 1);

    // Keep solving until UNSAT or we reach obj=5
    let mut best = obj1;
    for iteration in 2..=20 {
        let r = engine.solve();
        match r {
            CpSolveResult::Sat(ref assignment) => {
                let obj_val = assignment.iter().find(|(v, _)| *v == obj).unwrap().1;
                eprintln!("solve {iteration}: obj={obj_val}");
                assert!(
                    obj_val < best,
                    "new solution must be better: got {obj_val}, previous {best}"
                );
                best = obj_val;
                engine.add_upper_bound(obj, obj_val - 1);
            }
            CpSolveResult::Unsat => {
                eprintln!("solve {iteration}: UNSAT (best={best})");
                // Optimal found. The bound obj <= best-1 is infeasible,
                // so best is the optimum.
                assert_eq!(
                    best, 5,
                    "optimal should be 5 (x=3, y=2), but declared optimal at {best}"
                );
                return;
            }
            CpSolveResult::Unknown => {
                panic!("solve {iteration}: Unknown — should not happen on a small problem");
            }
        }
    }
    panic!("did not converge after 20 iterations (best={best})");
}

/// Regression test for #5910: incremental optimization must not produce false
/// UNSAT from stale trail state or empty conflict clauses.
///
/// This test runs multiple incremental solves with tightening bounds (the
/// optimization loop pattern that triggered #5910). Each SAT result is
/// validated against the original constraints. If a false UNSAT appears
/// before the true optimum is reached, the test fails.
#[test]
fn test_incremental_optimization_no_false_unsat_5910() {
    let mut engine = CpSatEngine::new();
    // x in [0..20], y in [0..20]
    let x = engine.new_int_var(Domain::new(0, 20), Some("x"));
    let y = engine.new_int_var(Domain::new(0, 20), Some("y"));

    // Constraint: x + y <= 15
    engine.add_constraint(Constraint::LinearLe {
        coeffs: vec![1, 1],
        vars: vec![x, y],
        rhs: 15,
    });
    // Constraint: 2*x + y <= 20
    engine.add_constraint(Constraint::LinearLe {
        coeffs: vec![2, 1],
        vars: vec![x, y],
        rhs: 20,
    });

    // Objective: maximize x + 2*y (minimize -(x + 2*y))
    // Optimum: x=0, y=15 → obj=30; or x=5, y=10 → obj=25
    // True optimum: x=0, y=15 → x+y=15 ✓, 2*0+15=15 ≤ 20 ✓, obj=30.
    let mut best_obj = i64::MIN;
    for iteration in 0..30 {
        match engine.solve() {
            CpSolveResult::Sat(assignment) => {
                let x_val = assignment.iter().find(|(v, _)| *v == x).unwrap().1;
                let y_val = assignment.iter().find(|(v, _)| *v == y).unwrap().1;

                // Validate against constraints
                assert!(
                    x_val + y_val <= 15,
                    "iter {iteration}: constraint 1 violated: {x_val} + {y_val} > 15"
                );
                assert!(
                    2 * x_val + y_val <= 20,
                    "iter {iteration}: constraint 2 violated: 2*{x_val} + {y_val} > 20"
                );

                let obj = x_val + 2 * y_val;
                if obj > best_obj {
                    best_obj = obj;
                }

                // Tighten: require obj > best (x + 2*y > best → -(x + 2*y) <= -(best+1))
                // Equivalently: add constraint x + 2*y >= best + 1
                // Which is -x - 2*y <= -(best + 1)
                engine.add_constraint(Constraint::LinearLe {
                    coeffs: vec![-1, -2],
                    vars: vec![x, y],
                    rhs: -(best_obj + 1),
                });
            }
            CpSolveResult::Unsat => {
                // Optimum found. Verify it's reasonable.
                assert!(
                    best_obj >= 15,
                    "False UNSAT: best objective {best_obj} is too low. \
                     x=0,y=15 gives obj=30 and satisfies all constraints."
                );
                return;
            }
            CpSolveResult::Unknown => {
                panic!("iter {iteration}: Unknown — should not happen on a small problem");
            }
        }
    }
    panic!("did not converge after 30 iterations (best_obj={best_obj})");
}

/// Test that the Explanation::to_conflict_clause method produces non-empty
/// clauses when given non-empty reasons, and empty when given empty reasons.
///
/// This documents the structural property that an Explanation with zero
/// reasons produces an empty conflict clause, which would cause unconditional
/// UNSAT in the SAT solver. Propagators must never create empty Explanations.
#[test]
fn test_explanation_empty_reasons_produces_empty_clause() {
    use crate::propagator::Explanation;

    // Empty reasons → empty conflict clause
    let empty_expl = Explanation::new(vec![]);
    assert!(
        empty_expl.into_conflict_clause().is_empty(),
        "Empty reasons should produce empty conflict clause"
    );

    // Non-empty reasons → non-empty conflict clause
    let lit = ay_sat::Literal::from_dimacs(1);
    let nonempty_expl = Explanation::new(vec![lit]);
    assert!(
        !nonempty_expl.into_conflict_clause().is_empty(),
        "Non-empty reasons should produce non-empty conflict clause"
    );
}

/// Build a bool2int item selection model for the accap-pattern regression test.
///
/// Returns `(engine, bools, obj, costs)` where bools are selection variables,
/// obj is the objective variable, and costs are the item costs.
fn build_bool2int_selection_model() -> (CpSatEngine, Vec<IntVarId>, IntVarId, [i64; 5]) {
    let mut engine = CpSatEngine::new();
    let costs: [i64; 5] = [10, 25, 15, 30, 20];
    let n = costs.len();

    let bools: Vec<_> = (0..n)
        .map(|i| engine.new_int_var(Domain::new(0, 1), Some(&format!("b{i}"))))
        .collect();

    // cost[i] = [0, c[i]][b[i]] via element constraint
    let cost_vars: Vec<_> = (0..n)
        .map(|i| {
            let cv = engine.new_int_var(Domain::new(0, costs[i]), Some(&format!("cost{i}")));
            let zero = engine.new_int_var(Domain::new(0, 0), Some(&format!("z{i}")));
            let cc = engine.new_int_var(Domain::new(costs[i], costs[i]), Some(&format!("c{i}")));
            engine.add_constraint(Constraint::Element {
                index: bools[i],
                array: vec![zero, cc],
                result: cv,
            });
            cv
        })
        .collect();

    let obj = engine.new_int_var(Domain::new(0, 200), Some("obj"));
    let mut eq_coeffs: Vec<i64> = vec![1; n];
    eq_coeffs.push(-1);
    let mut eq_vars = cost_vars;
    eq_vars.push(obj);
    engine.add_constraint(Constraint::LinearEq {
        coeffs: eq_coeffs,
        vars: eq_vars,
        rhs: 0,
    });
    engine.add_constraint(Constraint::LinearLe {
        coeffs: vec![1; n],
        vars: bools.clone(),
        rhs: 3,
    });
    engine.add_constraint(Constraint::LinearLe {
        coeffs: vec![-1; n],
        vars: bools.clone(),
        rhs: -2,
    });
    engine.pre_compile();

    (engine, bools, obj, costs)
}

// === Post-solve validation tests (#6121) ===
//
// These tests verify that `debug_validate_assignment` correctly detects
// constraint violations. Each test constructs a model, populates
// `debug_constraints`, then calls `debug_validate_assignment` with a
// known-bad assignment. The validator must panic.

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "AllDifferent violated")]
fn test_validate_catches_alldiff_violation() {
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::new(1, 3), None);
    let y = engine.new_int_var(Domain::new(1, 3), None);
    let z = engine.new_int_var(Domain::new(1, 3), None);
    engine
        .debug_constraints
        .push(Constraint::AllDifferent(vec![x, y, z]));
    // x=1, y=1, z=2 — violates AllDifferent
    engine.debug_validate_assignment(&[(x, 1), (y, 1), (z, 2)]);
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "LinearEq violated")]
fn test_validate_catches_linear_eq_violation() {
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::new(0, 10), None);
    let y = engine.new_int_var(Domain::new(0, 10), None);
    engine.debug_constraints.push(Constraint::LinearEq {
        coeffs: vec![1, 1],
        vars: vec![x, y],
        rhs: 5,
    });
    // x=3, y=4 → sum=7 != 5
    engine.debug_validate_assignment(&[(x, 3), (y, 4)]);
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "LinearLe violated")]
fn test_validate_catches_linear_le_violation() {
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::new(0, 10), None);
    let y = engine.new_int_var(Domain::new(0, 10), None);
    engine.debug_constraints.push(Constraint::LinearLe {
        coeffs: vec![1, 1],
        vars: vec![x, y],
        rhs: 5,
    });
    // x=3, y=4 → sum=7 > 5
    engine.debug_validate_assignment(&[(x, 3), (y, 4)]);
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "PairwiseNeq violated")]
fn test_validate_catches_pairwise_neq_violation() {
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::new(1, 5), None);
    let y = engine.new_int_var(Domain::new(1, 5), None);
    engine
        .debug_constraints
        .push(Constraint::PairwiseNeq { x, y, offset: 2 });
    // x=5, y=3 → x - y = 2 == offset
    engine.debug_validate_assignment(&[(x, 5), (y, 3)]);
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "BoolClause violated")]
fn test_validate_catches_bool_clause_violation() {
    let mut engine = CpSatEngine::new();
    let a = engine.new_bool_var(None);
    let b = engine.new_bool_var(None);
    engine.debug_constraints.push(Constraint::BoolClause {
        pos: vec![a],
        neg: vec![b],
    });
    // a=0 (positive not true) and b=1 (negative not false) → violated
    engine.debug_validate_assignment(&[(a, 0), (b, 1)]);
}

#[test]
#[cfg(debug_assertions)]
fn test_validate_accepts_valid_assignment() {
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::new(1, 3), None);
    let y = engine.new_int_var(Domain::new(1, 3), None);
    let z = engine.new_int_var(Domain::new(1, 3), None);
    engine
        .debug_constraints
        .push(Constraint::AllDifferent(vec![x, y, z]));
    engine.debug_constraints.push(Constraint::LinearLe {
        coeffs: vec![1, 1, 1],
        vars: vec![x, y, z],
        rhs: 6,
    });
    // x=1, y=2, z=3 — all different and sum=6 <= 6
    engine.debug_validate_assignment(&[(x, 1), (y, 2), (z, 3)]);
}

#[test]
fn test_pairwise_neq_extreme_offset_and_difference() {
    let mut violated = CpSatEngine::new();
    let x = violated.new_int_var(Domain::singleton(i64::MIN), Some("x"));
    let y = violated.new_int_var(Domain::singleton(0), Some("y"));
    violated.add_constraint(Constraint::PairwiseNeq {
        x,
        y,
        offset: i64::MIN,
    });
    assert!(matches!(violated.solve(), CpSolveResult::Unsat));

    let mut satisfied = CpSatEngine::new();
    let x = satisfied.new_int_var(Domain::singleton(i64::MIN), Some("x"));
    let y = satisfied.new_int_var(Domain::singleton(i64::MAX), Some("y"));
    satisfied.add_constraint(Constraint::PairwiseNeq { x, y, offset: 0 });
    assert!(matches!(satisfied.solve(), CpSolveResult::Sat(_)));
}

#[test]
fn test_alldifferent_pigeon_hole_extreme_values() {
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::singleton(i64::MIN), Some("x"));
    let y = engine.new_int_var(Domain::singleton(i64::MAX), Some("y"));
    engine.add_constraint(Constraint::AllDifferent(vec![x, y]));
    assert!(matches!(engine.solve(), CpSolveResult::Sat(_)));
}

#[test]
fn test_shifted_alldifferent_extreme_shifted_bounds() {
    for fixed in [i64::MIN, i64::MAX] {
        let mut engine = CpSatEngine::new();
        let vars: Vec<_> = (0..3)
            .map(|i| engine.new_int_var(Domain::singleton(fixed), Some(&format!("x{i}"))))
            .collect();
        for i in 0..vars.len() {
            for j in (i + 1)..vars.len() {
                engine.add_constraint(Constraint::PairwiseNeq {
                    x: vars[i],
                    y: vars[j],
                    offset: i as i64 - j as i64,
                });
            }
        }
        assert!(matches!(engine.solve(), CpSolveResult::Sat(_)));
    }
}

#[test]
fn test_disjunctive_extreme_endpoints_detect_overlap() {
    for fixed in [i64::MIN, i64::MAX] {
        let mut engine = CpSatEngine::new();
        let a = engine.new_int_var(Domain::singleton(fixed), Some("a"));
        let b = engine.new_int_var(Domain::singleton(fixed), Some("b"));
        engine.add_constraint(Constraint::Disjunctive {
            starts: vec![a, b],
            durations: vec![1, 1],
        });
        assert!(matches!(engine.solve(), CpSolveResult::Unsat));
    }
}

/// Regression test for #5910 (accap pattern): incremental optimization with
/// element constraints and boolean selection variables must not produce false
/// UNSAT from stale theory lemmas persisting across incremental solves.
#[test]
fn test_incremental_optimization_element_bool2int_5910() {
    let (mut engine, bools, obj, costs) = build_bool2int_selection_model();
    let mut best_obj = i64::MAX;
    let mut found_any = false;

    for iteration in 0..30 {
        match engine.solve() {
            CpSolveResult::Sat(assignment) => {
                found_any = true;
                let obj_val = assignment.iter().find(|(v, _)| *v == obj).unwrap().1;
                let selected: Vec<usize> = bools
                    .iter()
                    .enumerate()
                    .filter(|(_, bv)| assignment.iter().any(|(v, val)| v == *bv && *val == 1))
                    .map(|(i, _)| i)
                    .collect();
                assert!(
                    selected.len() >= 2 && selected.len() <= 3,
                    "iter {iteration}: count {} violates [2,3]",
                    selected.len()
                );
                let expected: i64 = selected.iter().map(|&i| costs[i]).sum();
                assert_eq!(obj_val, expected, "iter {iteration}: obj mismatch");
                assert!(obj_val < best_obj, "iter {iteration}: not improving");
                best_obj = obj_val;
                engine.add_upper_bound(obj, obj_val - 1);
            }
            CpSolveResult::Unsat => {
                assert!(found_any, "iter {iteration}: false UNSAT on first solve");
                assert!(
                    best_obj <= 45,
                    "iter {iteration}: premature UNSAT (best={best_obj})"
                );
                return;
            }
            CpSolveResult::Unknown => {
                panic!("iter {iteration}: Unknown on a small problem");
            }
        }
    }
    panic!("did not converge after 30 iterations (best_obj={best_obj})");
}

/// 4-queens using PairwiseNeq constraints (FlatZinc-style encoding).
/// This exercises detect_alldifferent + detect_shifted_alldifferent + AC lifting.
#[test]
fn test_4queens_pairwise_neq() {
    let n = 4i64;
    let mut engine = CpSatEngine::new();
    let queens: Vec<IntVarId> = (0..n)
        .map(|i| engine.new_int_var(Domain::new(1, n), Some(&format!("q{i}"))))
        .collect();
    for i in 0..n {
        for j in (i + 1)..n {
            engine.add_constraint(Constraint::PairwiseNeq {
                x: queens[i as usize],
                y: queens[j as usize],
                offset: 0,
            });
            engine.add_constraint(Constraint::PairwiseNeq {
                x: queens[i as usize],
                y: queens[j as usize],
                offset: i - j,
            });
            engine.add_constraint(Constraint::PairwiseNeq {
                x: queens[i as usize],
                y: queens[j as usize],
                offset: j - i,
            });
        }
    }
    // Add an unused extra variable to test if mere existence causes UNSAT
    let _extra = engine.new_int_var(Domain::new(0, 10), None);
    match engine.solve() {
        CpSolveResult::Sat(assignment) => {
            // Only check first n vars (queens); extra var is ignored
            let queen_vals: Vec<i64> = assignment
                .iter()
                .take(n as usize)
                .map(|(_, v)| *v)
                .collect();
            assert_eq!(queen_vals.len(), n as usize);
            let mut cols = queen_vals.clone();
            cols.sort_unstable();
            cols.dedup();
            assert_eq!(
                cols.len(),
                n as usize,
                "columns not all-different: {queen_vals:?}"
            );
            for i in 0..n as usize {
                for j in (i + 1)..n as usize {
                    let col_diff = (queen_vals[j] - queen_vals[i]).unsigned_abs();
                    let row_diff = (j - i) as u64;
                    assert_ne!(
                        col_diff, row_diff,
                        "diagonal conflict: q[{i}]={}, q[{j}]={}",
                        queen_vals[i], queen_vals[j]
                    );
                }
            }
        }
        other => panic!("4-queens (pairwise neq + extra var) should be SAT, got {other:?}"),
    }
}

#[test]
fn test_solve_under_assumptions_lns_primitive() {
    // x,y,z in [1,3], all different -> solutions are permutations of {1,2,3}.
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::new(1, 3), Some("x"));
    let y = engine.new_int_var(Domain::new(1, 3), Some("y"));
    let z = engine.new_int_var(Domain::new(1, 3), Some("z"));
    engine.add_constraint(Constraint::AllDifferent(vec![x, y, z]));

    let val = |a: &[(IntVarId, i64)], v| {
        a.iter()
            .find(|(k, _)| *k == v)
            .map(|(_, val)| *val)
            .unwrap()
    };

    // Baseline solve.
    assert!(matches!(engine.solve(), CpSolveResult::Sat(_)));

    // Fix x=1: solution must have x=1 and y,z a distinct pair from {2,3}.
    match engine.solve_under_assumptions(&[(x, 1)]) {
        CpSolveResult::Sat(a) => {
            assert_eq!(val(&a, x), 1, "assumption x=1 must be respected");
            assert_ne!(val(&a, y), val(&a, z), "AllDifferent still enforced");
            assert_ne!(val(&a, y), 1);
            assert_ne!(val(&a, z), 1);
        }
        other => panic!("expected Sat, got {other:?}"),
    }

    // Fix x=1, y=2: only z=3 works.
    match engine.solve_under_assumptions(&[(x, 1), (y, 2)]) {
        CpSolveResult::Sat(a) => {
            assert_eq!((val(&a, x), val(&a, y), val(&a, z)), (1, 2, 3));
        }
        other => panic!("expected Sat, got {other:?}"),
    }

    // Fix x=1, y=1: violates AllDifferent -> UNSAT (soundness under assumptions).
    assert!(
        matches!(
            engine.solve_under_assumptions(&[(x, 1), (y, 1)]),
            CpSolveResult::Unsat
        ),
        "conflicting assumptions must be UNSAT"
    );

    // Assumptions are retracted: a plain solve is SAT again (not stuck at UNSAT).
    assert!(
        matches!(engine.solve(), CpSolveResult::Sat(_)),
        "assumptions must retract; plain solve SAT again"
    );
    // And a fresh assumption set still works (x=3).
    match engine.solve_under_assumptions(&[(x, 3)]) {
        CpSolveResult::Sat(a) => assert_eq!(val(&a, x), 3),
        other => panic!("expected Sat, got {other:?}"),
    }
}

#[test]
fn oversized_order_encoding_fails_closed_before_compilation() {
    let mut engine = CpSatEngine::new();
    let upper = crate::encoder::MAX_PREALLOCATED_ORDER_LITERALS as i64;
    let variable = engine.new_int_var(Domain::new(0, upper), Some("huge"));

    assert!(matches!(
        engine.try_pre_compile(),
        Err(OrderEncodingCapacityError::LiteralLimitExceeded { .. })
    ));
    assert!(!engine.pre_compile());
    assert!(matches!(engine.solve(), CpSolveResult::Unknown));
    assert!(matches!(
        engine.solve_under_assumptions(&[(variable, 0)]),
        CpSolveResult::Unknown
    ));
    assert!(matches!(
        engine.solve_pure_sat_only(),
        CpSolveResult::Unknown
    ));
}

#[test]
fn order_encoding_handles_i64_max_without_a_wrapped_sentinel() {
    let mut engine = CpSatEngine::new();
    let variable = engine.new_int_var(Domain::new(i64::MAX - 2, i64::MAX), Some("endpoint"));
    let assignment = match engine.solve() {
        CpSolveResult::Sat(assignment) => assignment,
        other => panic!("small endpoint domain should solve, got {other:?}"),
    };
    let value = assignment
        .iter()
        .find_map(|&(candidate, value)| (candidate == variable).then_some(value))
        .expect("endpoint variable must be assigned");
    assert!((i64::MAX - 2..=i64::MAX).contains(&value));
}

#[test]
fn variables_added_after_preallocation_fail_closed_in_every_solve_variant() {
    let mut engine = CpSatEngine::new();
    let _first = engine.new_int_var(Domain::new(0, 1), Some("first"));
    assert!(engine.pre_compile());

    let late = engine.new_int_var(Domain::new(10, 11), Some("late"));
    engine.add_constraint(Constraint::LinearEq {
        coeffs: vec![1],
        vars: vec![late],
        rhs: 11,
    });

    assert!(matches!(
        engine.try_pre_compile(),
        Err(
            OrderEncodingCapacityError::VariablesAddedAfterPreallocation {
                allocated: 1,
                registered: 2,
            }
        )
    ));
    assert!(matches!(engine.solve(), CpSolveResult::Unknown));
    assert!(matches!(
        engine.solve_under_assumptions(&[]),
        CpSolveResult::Unknown
    ));
    assert!(matches!(
        engine.solve_pure_sat_only(),
        CpSolveResult::Unknown
    ));

    // The zero-variable preallocation state must be tracked explicitly too.
    let mut empty = CpSatEngine::new();
    assert!(empty.pre_compile());
    empty.new_bool_var(Some("late"));
    assert!(matches!(empty.solve(), CpSolveResult::Unknown));
}
