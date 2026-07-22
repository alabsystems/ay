// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::domain::Domain;
use crate::engine::CpSatEngine;
use ay_sat::Literal;

fn clause_removes_value(
    enc: &IntegerEncoder,
    clause: &[Literal],
    var: IntVarId,
    value: i64,
) -> bool {
    let Some(ge_v) = enc.lookup_ge(var, value) else {
        return false;
    };
    let Some(ge_v1) = enc.lookup_ge(var, value + 1) else {
        return false;
    };
    clause.contains(&ge_v.negated()) && clause.contains(&ge_v1)
}

fn apply_endpoint_pruning(
    trail: &mut IntegerTrail,
    enc: &IntegerEncoder,
    var: IntVarId,
    value: i64,
) {
    if value == trail.lb(var) {
        let lit = enc
            .lookup_ge(var, value + 1)
            .expect("expected upper step literal for lower-bound pruning");
        trail
            .set_lb(var, value + 1, lit, None)
            .expect("endpoint pruning should not wipe out domain");
        return;
    }

    if value == trail.ub(var) {
        let lit = enc
            .lookup_le(var, value - 1)
            .expect("expected lower step literal for upper-bound pruning");
        trail
            .set_ub(var, value - 1, lit, None)
            .expect("endpoint pruning should not wipe out domain");
        return;
    }

    panic!("test only replays endpoint removals, got interior value {value}");
}

#[test]
fn test_alldiff_ac_creation() {
    let vars = vec![IntVarId(0), IntVarId(1), IntVarId(2)];
    let values = vec![1, 2, 3];
    let prop = AllDifferentAc::new(vars, values);
    assert_eq!(prop.variables().len(), 3);
    assert_eq!(prop.name(), "alldifferent_ac");
    assert_eq!(prop.n_vals, 3);
}

#[test]
fn test_alldiff_ac_value_index() {
    let vars = vec![IntVarId(0), IntVarId(1)];
    let values = vec![1, 3, 5, 7];
    let prop = AllDifferentAc::new(vars, values);
    assert_eq!(prop.value_index(1), Some(0));
    assert_eq!(prop.value_index(3), Some(1));
    assert_eq!(prop.value_index(5), Some(2));
    assert_eq!(prop.value_index(7), Some(3));
    assert_eq!(prop.value_index(2), None);
    assert_eq!(prop.value_index(4), None);
}

#[test]
fn test_alldiff_ac_sparse_adjacency_excludes_holes() {
    let mut trail = IntegerTrail::new();
    let a = trail.register_domain(Domain::from_values(&[1, 3]));
    let b = trail.register_domain(Domain::from_values(&[1, 2, 3]));
    let d = trail.register_domain(Domain::from_values(&[2, 4]));

    let mut prop = AllDifferentAc::new(vec![a, b, d], vec![1, 2, 3, 4]);
    prop.build_adjacency(&trail);

    let decode = |indices: &[u32]| -> Vec<i64> {
        indices
            .iter()
            .map(|&idx| prop.idx_to_val[idx as usize])
            .collect()
    };

    assert_eq!(
        decode(&prop.ws_adj[0]),
        vec![1, 3],
        "sparse holes must stay excluded"
    );
    assert_eq!(
        decode(&prop.ws_adj[1]),
        vec![1, 2, 3],
        "dense interval should stay intact"
    );
    assert_eq!(
        decode(&prop.ws_adj[2]),
        vec![2, 4],
        "sparse upper hole must stay excluded"
    );
}

/// The canonical witness from the design doc:
///
///   a ∈ {1,3}, b ∈ {1,3}, c ∈ {1,2,3}, d ∈ {2,4}
///   all_different(a,b,c,d)
///
/// Bounds consistency cannot prune c. Domain consistency
/// should detect that c=1 and c=3 are unsupported, leaving c=2.
#[test]
fn test_alldiff_ac_prunes_interior_value() {
    let mut trail = IntegerTrail::new();
    let a = trail.register_domain(Domain::from_values(&[1, 3]));
    let b = trail.register_domain(Domain::from_values(&[1, 3]));
    let c = trail.register_domain(Domain::from_values(&[1, 2, 3]));
    let d = trail.register_domain(Domain::from_values(&[2, 4]));

    let mut enc = IntegerEncoder::new();
    enc.register_var(1, 3); // a
    enc.register_var(1, 3); // b
    enc.register_var(1, 3); // c
    enc.register_var(2, 4); // d
    let mut sat = ay_sat::Solver::new(0);
    enc.pre_allocate_all(&mut sat);

    let all_values = vec![1, 2, 3, 4];
    let mut prop = AllDifferentAc::new(vec![a, b, c, d], all_values);
    let mut saw_c1 = false;
    let mut saw_c3 = false;
    let mut saw_d2 = false;

    for _ in 0..4 {
        match prop.propagate(&trail, &enc) {
            PropagationResult::Propagated(clauses) => {
                for clause in &clauses {
                    if clause_removes_value(&enc, clause, c, 1) {
                        saw_c1 = true;
                        apply_endpoint_pruning(&mut trail, &enc, c, 1);
                    } else if clause_removes_value(&enc, clause, c, 3) {
                        saw_c3 = true;
                        apply_endpoint_pruning(&mut trail, &enc, c, 3);
                    } else if clause_removes_value(&enc, clause, d, 2) {
                        saw_d2 = true;
                        apply_endpoint_pruning(&mut trail, &enc, d, 2);
                    } else {
                        panic!("unexpected pruning clause for sparse witness: {clause:?}");
                    }
                }
            }
            PropagationResult::NoChange => break,
            PropagationResult::Conflict(_) => {
                panic!("should not conflict — problem is satisfiable");
            }
        }
    }

    assert!(saw_c1, "expected AC to remove c=1");
    assert!(saw_c3, "expected AC to remove c=3");
    assert!(saw_d2, "expected AC to remove d=2");
    assert_eq!(trail.fixed_value(c), Some(2), "c should be fixed to 2");
    assert_eq!(trail.fixed_value(d), Some(4), "d should be fixed to 4");
    assert!(
        trail.contains(a, 1) && trail.contains(a, 3),
        "a should stay {{1,3}}"
    );
    assert!(
        trail.contains(b, 1) && trail.contains(b, 3),
        "b should stay {{1,3}}"
    );
}

/// Test that AC correctly detects infeasibility when
/// there are more variables than available values.
#[test]
fn test_alldiff_ac_detects_conflict() {
    let mut trail = IntegerTrail::new();
    // Three variables, all with domain {1, 2} — pigeonhole conflict.
    let x = trail.register_domain(Domain::new(1, 2));
    let y = trail.register_domain(Domain::new(1, 2));
    let z = trail.register_domain(Domain::new(1, 2));

    let mut enc = IntegerEncoder::new();
    enc.register_var(1, 2);
    enc.register_var(1, 2);
    enc.register_var(1, 2);
    let mut sat = ay_sat::Solver::new(0);
    enc.pre_allocate_all(&mut sat);

    let mut prop = AllDifferentAc::new(vec![x, y, z], vec![1, 2]);
    let result = prop.propagate(&trail, &enc);

    assert!(
        matches!(result, PropagationResult::Conflict(_)),
        "should detect pigeonhole conflict"
    );
}

/// Verify that AC produces NoChange when n_vars == n_vals (perfect matching).
/// No free values exist, all edges participate in some maximum matching.
#[test]
fn test_alldiff_ac_no_prune_perfect_matching() {
    let mut trail = IntegerTrail::new();
    let x = trail.register_domain(Domain::new(0, 2));
    let y = trail.register_domain(Domain::new(0, 2));
    let z = trail.register_domain(Domain::new(0, 2));

    let mut enc = IntegerEncoder::new();
    enc.register_var(0, 2);
    enc.register_var(0, 2);
    enc.register_var(0, 2);
    let mut sat = ay_sat::Solver::new(0);
    enc.pre_allocate_all(&mut sat);

    let mut prop = AllDifferentAc::new(vec![x, y, z], vec![0, 1, 2]);
    let result = prop.propagate(&trail, &enc);

    assert!(
        matches!(result, PropagationResult::NoChange),
        "no pruning with 3 vars / 3 vals (all edges supportable), got {result:?}"
    );
}

/// Verify that AC propagation produces NoChange on a dense domain
/// where all values are supported (3 vars in [0,4], no pruning expected).
#[test]
fn test_alldiff_ac_no_prune_when_slack() {
    let mut trail = IntegerTrail::new();
    let x = trail.register_domain(Domain::new(0, 4));
    let y = trail.register_domain(Domain::new(0, 4));
    let z = trail.register_domain(Domain::new(0, 4));

    let mut enc = IntegerEncoder::new();
    enc.register_var(0, 4);
    enc.register_var(0, 4);
    enc.register_var(0, 4);
    let mut sat = ay_sat::Solver::new(0);
    enc.pre_allocate_all(&mut sat);

    let all_values = vec![0, 1, 2, 3, 4];
    let mut prop = AllDifferentAc::new(vec![x, y, z], all_values);
    let result = prop.propagate(&trail, &enc);

    assert!(
        matches!(result, PropagationResult::NoChange),
        "no pruning expected with 3 vars and 5 values, got {result:?}"
    );
}

/// Test that 15 vars with identical domain [1,17] produce no pruning.
/// This mimics the Golomb-6 difference variables.
#[test]
fn test_alldiff_ac_15vars_17vals_no_prune() {
    let mut trail = IntegerTrail::new();
    let mut vars = Vec::new();
    let mut enc = IntegerEncoder::new();
    for _ in 0..15 {
        let v = trail.register_domain(Domain::new(1, 17));
        enc.register_var(1, 17);
        vars.push(v);
    }
    let mut sat = ay_sat::Solver::new(0);
    enc.pre_allocate_all(&mut sat);

    let all_values: Vec<i64> = (1..=17).collect();
    let mut prop = AllDifferentAc::new(vars, all_values);
    let result = prop.propagate(&trail, &enc);

    match &result {
        PropagationResult::NoChange => {} // expected
        PropagationResult::Propagated(clauses) => {
            panic!(
                "expected no pruning for 15 vars in [1,17], got {} clauses",
                clauses.len()
            );
        }
        PropagationResult::Conflict(clause) => {
            panic!(
                "expected no conflict for 15 vars in [1,17], got conflict with {} lits",
                clause.len()
            );
        }
    }
}

/// End-to-end test: solve the design-doc witness problem through
/// the full CP-SAT engine with AC enabled, and verify c=2.
#[test]
fn test_alldiff_ac_engine_solves_sparse_witness() {
    let mut engine = CpSatEngine::new();

    let a = engine.new_int_var(Domain::from_values(&[1, 3]), Some("a"));
    let b = engine.new_int_var(Domain::from_values(&[1, 3]), Some("b"));
    let c = engine.new_int_var(Domain::from_values(&[1, 2, 3]), Some("c"));
    let d = engine.new_int_var(Domain::from_values(&[2, 4]), Some("d"));

    engine.add_constraint(crate::propagator::Constraint::AllDifferent(vec![
        a, b, c, d,
    ]));

    match engine.solve() {
        crate::engine::CpSolveResult::Sat(assignment) => {
            let get_val = |var: IntVarId| -> i64 {
                assignment
                    .iter()
                    .find(|&&(v, _)| v == var)
                    .map(|&(_, val)| val)
                    .unwrap()
            };

            let va = get_val(a);
            let vb = get_val(b);
            let vc = get_val(c);
            let vd = get_val(d);

            // c must be 2 (only supported value).
            assert_eq!(vc, 2, "c must be 2, got {vc}");
            // d must be 4 (since d ∈ {2,4} and c=2).
            assert_eq!(vd, 4, "d must be 4, got {vd}");
            // a and b must be {1,3} in some order.
            assert!(
                (va == 1 && vb == 3) || (va == 3 && vb == 1),
                "a,b must be {{1,3}} permutation, got a={va}, b={vb}"
            );
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}
