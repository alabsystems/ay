//! Unit tests for `super` (am1_bound.rs).
//! Extracted verbatim to keep the production module readable.

use super::*;
use crate::eval::verify_all_constraints;
use crate::parser::parse_opb;
use crate::solver::eval_objective;
use crate::types::{PbObjective, PbTerm};

/// Brute-force exact minimum objective over all feasible 2^n assignments.
fn brute_force_optimum(instance: &PbInstance, objective: &PbObjective) -> Option<i128> {
    let n = instance.num_vars as usize;
    assert!(n <= 22, "brute force only for tiny instances");
    let mut best: Option<i128> = None;
    for mask in 0u32..(1u32 << n) {
        let assignment: Vec<bool> = (0..n).map(|i| (mask >> i) & 1 == 1).collect();
        if !verify_all_constraints(&instance.constraints, &assignment) {
            continue;
        }
        let value = eval_objective(objective, &assignment);
        best = Some(best.map_or(value, |b| b.min(value)));
    }
    best
}

/// Extracts the soft selectors (relaxation vars) and weights from a converted
/// PBO objective so the AM1 bound can be evaluated directly.
fn softs_from_objective(objective: &PbObjective) -> Vec<Am1Soft> {
    objective
        .terms
        .iter()
        .filter_map(|t| {
            let [lit] = t.lits.as_slice() else {
                return None;
            };
            (t.coeff > 0).then_some(Am1Soft {
                literal: *lit,
                weight: t.coeff,
            })
        })
        .collect()
}

#[test]
fn am1_bound_is_zero_when_no_incompatibility() {
    // Two independent at-least-one constraints; the cheapest model pays 0 for
    // each selector (selectors can all be free). No AM1 structure.
    let input = "* #variable= 4 #constraint= 2\n\
        min: +1 x3 +1 x4 ;\n\
        +1 x1 +1 x2 +5 x3 >= 1 ;\n\
        +1 x1 +1 x2 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse");
    let objective = instance.objective.clone().expect("obj");
    let softs = softs_from_objective(&objective);
    let bound = am1_clique_lower_bound_for_instance(&instance, &softs, || false);
    // No mutual exclusion among selectors -> no positive bound.
    assert!(bound.is_none() || bound == Some(0));
}

#[test]
fn am1_bound_single_exactly_one_pigeonhole() {
    // Three booleans, exactly-one structure enforced by hard constraints, and
    // each "extra" selection costs. Encode an at-most-one group of THREE
    // selectors via reified constraints so assuming any free selector forces
    // the others paid. We test the bound never exceeds the true optimum.
    //
    // Hard: x1 + x2 + x3 = 1 (exactly one). Selectors s1,s2,s3 with
    // s_i = 0 meaning "x_i may be chosen". Use the relaxation form directly:
    //   x_i + M*s_i >= 1  (s_i free => x_i must be 1)
    // With exactly-one, at most one x_i is 1, so at most one s_i can be free.
    let input = "* #variable= 6 #constraint= 4\n\
        min: +1 x4 +1 x5 +1 x6 ;\n\
        +1 x1 +1 x2 +1 x3 = 1 ;\n\
        +1 x1 +1 x4 >= 1 ;\n\
        +1 x2 +1 x5 >= 1 ;\n\
        +1 x3 +1 x6 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse");
    let objective = instance.objective.clone().expect("obj");
    let softs = softs_from_objective(&objective);
    let bound = am1_clique_lower_bound_for_instance(&instance, &softs, || false).unwrap_or(0);
    let bf = brute_force_optimum(&instance, &objective).expect("feasible");
    // SOUNDNESS: the bound must never exceed the true optimum.
    assert!(bound <= bf, "AM1 bound {bound} exceeds true optimum {bf}");
    // The exactly-one + relaxation structure forces >= 2 of the 3 selectors
    // paid (at most one x_i is 1, so at most one s_i free): bound should reach
    // the optimum here.
    assert_eq!(bf, 2, "expected optimum 2, got {bf}");
    assert_eq!(bound, 2, "AM1 bound should close this pigeonhole");
}

#[test]
fn am1_bound_forced_paid_selector_full_weight() {
    // A selector whose free polarity is infeasible: x1 must be 1 (hard unit),
    // and s1 free forces x1 = 0 -> conflict. So s1 is forced paid (weight 7).
    let input = "* #variable= 2 #constraint= 2\n\
        min: +7 x2 ;\n\
        +1 x1 >= 1 ;\n\
        -1 x1 +1 x2 >= 0 ;\n";
    // Constraint 2: -x1 + x2 >= 0  i.e. x2 >= x1. With x1=1 forced, x2=1 forced.
    // Selector here is x2 (paid). Free polarity ~x2 forces x1<=0, conflict with
    // x1>=1. So forced-paid, contributing 7.
    let instance = parse_opb(input).expect("parse");
    let objective = instance.objective.clone().expect("obj");
    let softs = softs_from_objective(&objective);
    let bound = am1_clique_lower_bound_for_instance(&instance, &softs, || false).unwrap_or(0);
    let bf = brute_force_optimum(&instance, &objective).expect("feasible");
    assert!(bound <= bf, "bound {bound} exceeds optimum {bf}");
    assert_eq!(bf, 7);
    assert_eq!(
        bound, 7,
        "forced-paid selector should contribute full weight"
    );
}

#[test]
fn am1_bound_never_exceeds_brute_force_random() {
    // Differential soundness: over random small weighted instances with
    // exactly-one + relaxation structure, the AM1 bound is ALWAYS <= the true
    // optimum. A bound that exceeds the optimum would be a false floor.
    let mut seed: u64 = 0xD1B5_4A32_D192_ED03;
    let mut next = || {
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        seed >> 33
    };
    for _ in 0..200 {
        // n in 2..=4 groups, each an exactly-one over 2 base vars + a selector.
        let groups = 2 + (next() % 3) as u32; // 2..=4
        let mut constraints = Vec::new();
        let mut obj_terms = Vec::new();
        // Build `groups` independent exactly-one pairs sharing a global pool.
        // base vars: 2 per group; selector: 1 per group.
        let base_per = 2u32;
        let total_base = groups * base_per;
        // exactly-one over each group's base vars.
        for g in 0..groups {
            let start = g * base_per + 1;
            let lits: Vec<PbTerm> = (0..base_per)
                .map(|k| PbTerm {
                    coeff: 1,
                    lits: vec![PbLit {
                        var: start + k,
                        negated: false,
                    }],
                })
                .collect();
            constraints.push(crate::types::PbConstraint {
                terms: lits,
                rel: crate::types::PbRel::Eq,
                rhs: 1,
            });
        }
        let mut var = total_base + 1;
        // For each base var, a selector relaxation: base + M*sel >= 1.
        for b in 1..=total_base {
            let sel = var;
            var += 1;
            let w = 1 + (next() % 9) as i128; // 1..=9
            constraints.push(crate::types::PbConstraint {
                terms: vec![
                    PbTerm {
                        coeff: 1,
                        lits: vec![PbLit {
                            var: b,
                            negated: false,
                        }],
                    },
                    PbTerm {
                        coeff: 1,
                        lits: vec![PbLit {
                            var: sel,
                            negated: false,
                        }],
                    },
                ],
                rel: crate::types::PbRel::Ge,
                rhs: 1,
            });
            obj_terms.push(PbTerm {
                coeff: w,
                lits: vec![PbLit {
                    var: sel,
                    negated: false,
                }],
            });
        }
        let num_vars = var - 1;
        if num_vars > 20 {
            continue;
        }
        let instance = PbInstance {
            num_vars,
            num_constraints: constraints.len() as u32,
            constraints,
            objective: Some(PbObjective {
                terms: obj_terms.clone(),
            }),
        };
        let objective = instance.objective.clone().unwrap();
        let softs = softs_from_objective(&objective);
        let bound = am1_clique_lower_bound_for_instance(&instance, &softs, || false).unwrap_or(0);
        let bf = brute_force_optimum(&instance, &objective);
        if let Some(bf) = bf {
            assert!(
                bound <= bf,
                "AM1 bound {bound} exceeds brute-force optimum {bf}"
            );
            assert!(bound >= 0, "AM1 bound must be non-negative");
        }
    }
}

#[test]
fn implied_literals_at_root_restores_solver_state() {
    // State-restoration gate: solving an instance, calling the probe, then
    // solving again must give the same result and leave the solver clean.
    let input = "* #variable= 6 #constraint= 4\n\
        min: +1 x4 +1 x5 +1 x6 ;\n\
        +1 x1 +1 x2 +1 x3 = 1 ;\n\
        +1 x1 +1 x4 >= 1 ;\n\
        +1 x2 +1 x5 >= 1 ;\n\
        +1 x3 +1 x6 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse");
    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, &mut || false);
    let first = solver.solve_with_assumptions(&[]);
    // Probe a selector's free literal a few times; state must be restored each
    // time so the subsequent solve matches the first.
    for var in [4u32, 5, 6, 1, 2, 3] {
        let _ = solver.implied_literals_at_root(PbLit { var, negated: true });
        let _ = solver.implied_literals_at_root(PbLit {
            var,
            negated: false,
        });
    }
    let second = solver.solve_with_assumptions(&[]);
    match (first, second) {
        (
            crate::cdcl::PbCdclAssumptionResult::Satisfiable(_),
            crate::cdcl::PbCdclAssumptionResult::Satisfiable(_),
        ) => {}
        (a, b) => panic!("state not restored: first {a:?} second {b:?}"),
    }
}
