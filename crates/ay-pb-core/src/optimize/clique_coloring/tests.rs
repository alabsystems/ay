// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::types::{PbLit, PbObjective, PbTerm};

fn pos(var: u32) -> PbLit {
    PbLit {
        var,
        negated: false,
    }
}
fn term(coeff: i128, var: u32) -> PbTerm {
    PbTerm {
        coeff,
        lits: vec![pos(var)],
    }
}

/// Builds the canonical clique-coloring OPB for `(n, t)` exactly as the
/// normalized instances are laid out (edges, obj, g1, g2). Used by the tests
/// as ground truth for the recogniser and the brute-force cross-check.
fn canonical_instance(n: usize, t: usize) -> (PbInstance, PbObjective) {
    let c = n * (n - 1) / 2;
    let base_g1 = c + n;
    let g1_vars = n * n;
    let base_g2 = base_g1 + g1_vars;
    let shape = CliqueColoringShape {
        n,
        t,
        base_obj: c,
        base_g1,
        base_g2,
    };
    let g2_vars = n * t;
    let num_vars = base_g2 + g2_vars;
    let mut constraints: Vec<PbConstraint> = Vec::new();
    // A
    for i in 1..=n {
        let mut terms = vec![term(1, shape.obj_var(i) as u32)];
        for b in 1..=n {
            terms.push(term(1, shape.g1_var(b, i) as u32));
        }
        constraints.push(PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs: 1,
        });
    }
    // B
    for b in 1..=n {
        let terms = (1..=n)
            .map(|sl| term(-1, shape.g1_var(b, sl) as u32))
            .collect();
        constraints.push(PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs: -1,
        });
    }
    // C
    for a in 1..=n {
        for b in (a + 1)..=n {
            let e = shape.edge_var(a, b) as u32;
            for p in 1..=n {
                for q in 1..=n {
                    if p == q {
                        continue;
                    }
                    constraints.push(PbConstraint {
                        terms: vec![
                            term(1, e),
                            term(-1, shape.g1_var(a, p) as u32),
                            term(-1, shape.g1_var(b, q) as u32),
                        ],
                        rel: PbRel::Ge,
                        rhs: -1,
                    });
                }
            }
        }
    }
    // D
    for b in 1..=n {
        let terms = (1..=t)
            .map(|k| term(1, shape.g2_var(b, k) as u32))
            .collect();
        constraints.push(PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs: 1,
        });
    }
    // E
    for a in 1..=n {
        for b in (a + 1)..=n {
            let e = shape.edge_var(a, b) as u32;
            for k in 1..=t {
                constraints.push(PbConstraint {
                    terms: vec![
                        term(-1, e),
                        term(-1, shape.g2_var(a, k) as u32),
                        term(-1, shape.g2_var(b, k) as u32),
                    ],
                    rel: PbRel::Ge,
                    rhs: -2,
                });
            }
        }
    }
    let objective = PbObjective {
        terms: (1..=n).map(|i| term(1, shape.obj_var(i) as u32)).collect(),
    };
    let instance = PbInstance {
        num_vars: num_vars as u32,
        num_constraints: constraints.len() as u32,
        constraints,
        objective: Some(objective.clone()),
    };
    (instance, objective)
}

/// Brute-force the true optimum over all `2^num_vars` assignments (tiny only).
fn brute_force_opt(instance: &PbInstance, objective: &PbObjective) -> Option<i128> {
    let nv = instance.num_vars as usize;
    assert!(nv <= 22, "brute force only for tiny instances");
    let mut best: Option<i128> = None;
    for mask in 0u32..(1u32 << nv) {
        let a: Vec<bool> = (0..nv).map(|v| (mask >> v) & 1 == 1).collect();
        if verify_all_constraints(&instance.constraints, &a) {
            let val = eval_objective(objective, &a);
            best = Some(best.map_or(val, |b| b.min(val)));
        }
    }
    best
}

#[test]
fn detect_recovers_parameters() {
    let (inst, obj) = canonical_instance(5, 3);
    let shape = detect(&inst, &obj).expect("n=5,t=3 detected");
    assert_eq!(shape.n, 5);
    assert_eq!(shape.t, 3);
}

#[test]
fn n5_t3_certifies_optimum_two() {
    // Matches the real corpus instance: opt = n - t = 2.
    let (inst, obj) = canonical_instance(5, 3);
    let sol = try_solve(&inst, &obj).expect("n=5,t=3 certifies");
    assert_eq!(sol.status, PbStatus::OptimumFound);
    assert_eq!(sol.objective, Some(2));
    assert!(verify_all_constraints(&inst.constraints, &sol.assignment));
}

#[test]
fn n7_t3_certifies_optimum_four() {
    // The SAT-only gap instance family member: opt = 4, which AY's heuristic
    // does not reach on its own.
    let (inst, obj) = canonical_instance(7, 3);
    let sol = try_solve(&inst, &obj).expect("n=7,t=3 certifies");
    assert_eq!(sol.objective, Some(4));
    assert!(verify_all_constraints(&inst.constraints, &sol.assignment));
}

#[test]
fn brute_force_cross_check_n3_t1() {
    // Tiny: 3 + 3 + 9 + 3 = 18 vars. t=1 forces a single colour, so any
    // active edge is a colouring conflict -> all blocks must share one slot
    // -> opt = n - t = 2. Brute force confirms against raw OPB semantics.
    let (inst, obj) = canonical_instance(3, 1);
    let sol = try_solve(&inst, &obj).expect("n=3,t=1 certifies");
    assert_eq!(sol.objective, Some(2));
    let brute = brute_force_opt(&inst, &obj).expect("feasible");
    assert_eq!(brute, 2);
    assert_eq!(sol.objective, Some(brute));
}

#[test]
fn brute_force_cross_check_n3_t2() {
    // 3 + 3 + 9 + 6 = 21 vars. opt = n - t = 1. The clique=colouring duality:
    // two of three blocks may share a slot (so G is bipartite, 2-colourable)
    // but not all three distinct (K_3 needs 3 > t=2 colours).
    let (inst, obj) = canonical_instance(3, 2);
    let sol = try_solve(&inst, &obj).expect("n=3,t=2 certifies");
    assert_eq!(sol.objective, Some(1));
    let brute = brute_force_opt(&inst, &obj).expect("feasible");
    assert_eq!(brute, 1);
    assert_eq!(sol.objective, Some(brute));
}

#[test]
fn brute_force_cross_check_n2_t1() {
    // Minimal member: 1 + 2 + 4 + 2 = 9 vars. opt = n - t = 1.
    let (inst, obj) = canonical_instance(2, 1);
    let sol = try_solve(&inst, &obj).expect("n=2,t=1 certifies");
    assert_eq!(sol.objective, Some(1));
    assert_eq!(brute_force_opt(&inst, &obj), Some(1));
}

#[test]
fn missing_coloring_constraint_does_not_certify() {
    // Drop ONE family-E (proper-colouring) constraint. The instance is no
    // longer the canonical family: the clique LB theorem's hypotheses fail,
    // so detection must DECLINE rather than emit a (now unproven) optimum.
    let (mut inst, obj) = canonical_instance(3, 2);
    // Find and remove a family-E constraint (rhs == -2).
    let pos = inst
        .constraints
        .iter()
        .position(|c| c.rhs == -2)
        .expect("has an E constraint");
    inst.constraints.remove(pos);
    inst.num_constraints -= 1;
    assert!(detect(&inst, &obj).is_none());
    assert!(try_solve(&inst, &obj).is_none());
}

#[test]
fn extra_constraint_does_not_certify() {
    // An EXTRA constraint (count mismatch) is rejected: the structural match
    // is exact, so even a redundant addition declines (defence in depth).
    let (mut inst, obj) = canonical_instance(3, 2);
    inst.constraints.push(PbConstraint {
        terms: vec![term(1, 1)],
        rel: PbRel::Ge,
        rhs: 0,
    });
    inst.num_constraints += 1;
    assert!(detect(&inst, &obj).is_none());
}

#[test]
fn unrelated_instance_declines() {
    // A generic vertex-cover-style instance must not be mistaken for the
    // clique-coloring family.
    let constraints = vec![
        PbConstraint {
            terms: vec![term(1, 1), term(1, 2)],
            rel: PbRel::Ge,
            rhs: 1,
        },
        PbConstraint {
            terms: vec![term(1, 2), term(1, 3)],
            rel: PbRel::Ge,
            rhs: 1,
        },
    ];
    let objective = PbObjective {
        terms: vec![term(1, 1), term(1, 2), term(1, 3)],
    };
    let inst = PbInstance {
        num_vars: 3,
        num_constraints: 2,
        constraints,
        objective: Some(objective.clone()),
    };
    assert!(try_solve(&inst, &objective).is_none());
}

#[test]
fn wrong_value_would_not_be_emitted() {
    // Sanity: the constructed colouring's objective equals n - t for a range
    // of parameters, so the `value == lower_bound` gate always passes on the
    // real family (and would decline if construction were off).
    for (n, t) in [(4usize, 2usize), (5, 3), (6, 4), (7, 3), (8, 6)] {
        let (inst, obj) = canonical_instance(n, t);
        let sol = try_solve(&inst, &obj).expect("certifies");
        assert_eq!(sol.objective, Some((n - t) as i128));
        assert!(verify_all_constraints(&inst.constraints, &sol.assignment));
    }
}
