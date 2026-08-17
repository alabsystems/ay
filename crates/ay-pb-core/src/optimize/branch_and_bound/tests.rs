// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::types::{PbConstraint, PbLit, PbObjective, PbRel, PbTerm};

fn lit(var: u32) -> PbLit {
    PbLit {
        var,
        negated: false,
    }
}

fn term(coeff: i128, var: u32) -> PbTerm {
    PbTerm {
        coeff,
        lits: vec![lit(var)],
    }
}

fn ge(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
    PbConstraint {
        terms,
        rel: PbRel::Ge,
        rhs,
    }
}

fn instance(num_vars: u32, constraints: Vec<PbConstraint>) -> PbInstance {
    PbInstance {
        num_vars,
        num_constraints: constraints.len() as u32,
        constraints,
        objective: None,
    }
}

fn never_stop() -> bool {
    false
}

/// Tiny deterministic xorshift PRNG (no dev-deps).
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn range(&mut self, lo: i128, hi: i128) -> i128 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next() % span) as i128
    }
}

/// Brute-force the true integer optimum over all 2^n feasible assignments,
/// or `None` if no assignment satisfies the constraints (infeasible).
fn brute_force_optimum(
    obj: &PbObjective,
    constraints: &[PbConstraint],
    n: u32,
) -> Option<(i128, Vec<bool>)> {
    let mut best: Option<(i128, Vec<bool>)> = None;
    for mask in 0u32..(1u32 << n) {
        let x: Vec<bool> = (0..n).map(|b| (mask >> b) & 1 == 1).collect();
        if verify_all_constraints(constraints, &x) {
            let v = eval_objective(obj, &x);
            let take = match &best {
                Some((bv, _)) => v < *bv,
                None => true,
            };
            if take {
                best = Some((v, x));
            }
        }
    }
    best
}

/// Generates a random satisfiable linear PB instance with <= 14 vars, returning
/// `(instance, objective, brute_force_optimum_value)`. Retries until feasible.
fn random_feasible_instance(rng: &mut Rng) -> (PbInstance, PbObjective, i128) {
    loop {
        let n: u32 = rng.range(1, 14) as u32;

        // Random small-coeff objective (single literals only, linear).
        let mut obj_terms = Vec::new();
        for v in 1..=n {
            let coeff = rng.range(0, 5);
            if coeff != 0 {
                obj_terms.push(term(coeff, v));
            }
        }
        if obj_terms.is_empty() {
            obj_terms.push(term(1, 1));
        }
        let obj = PbObjective { terms: obj_terms };

        // A few random cardinality / knapsack `>=` rows.
        let num_c = rng.range(0, 4);
        let mut constraints = Vec::new();
        for _ in 0..num_c {
            let mut terms = Vec::new();
            let mut total = 0i128;
            for v in 1..=n {
                let coeff = rng.range(0, 4);
                if coeff != 0 {
                    total += coeff;
                    terms.push(term(coeff, v));
                }
            }
            if terms.is_empty() {
                terms.push(term(1, 1));
                total = 1;
            }
            // rhs in a range that keeps the row satisfiable when all vars true.
            let rhs = rng.range(1, total.max(1));
            constraints.push(ge(terms, rhs));
        }

        let inst = instance(n, constraints.clone());
        if let Some((opt, _)) = brute_force_optimum(&obj, &constraints, n) {
            return (inst, obj, opt);
        }
        // Infeasible (rare with all-nonneg coeffs and rhs<=sum, but guard anyway);
        // retry with a fresh draw.
    }
}

#[test]
fn bnb_matches_bruteforce_optimum() {
    let mut rng = Rng(0xC0FF_EE12_3456_789A);
    let mut tested = 0usize;
    for _ in 0..200 {
        let (inst, obj, brute_opt) = random_feasible_instance(&mut rng);
        tested += 1;

        let result = solve_branch_and_bound(&inst, &obj, None, 1_000_000, &never_stop)
            .expect("feasible instance must yield an incumbent");

        assert!(
            result.proven_optimal,
            "large budget must prove optimality\nconstraints={:?}\nobj={:?}",
            inst.constraints, obj
        );
        assert_eq!(
            result.value, brute_opt,
            "B&B optimum {} != brute force {}\nconstraints={:?}\nobj={:?}",
            result.value, brute_opt, inst.constraints, obj
        );
        // Incumbent must be feasible with a matching objective value.
        assert!(
            verify_all_constraints(&inst.constraints, &result.assignment),
            "returned assignment must be feasible"
        );
        assert_eq!(
            eval_objective(&obj, &result.assignment),
            result.value,
            "assignment objective must match reported value"
        );
    }
    assert!(tested >= 200, "expected 200 instances, got {tested}");
}

#[test]
fn bnb_small_budget_never_claims_wrong_optimum() {
    let mut rng = Rng(0x1357_9BDF_2468_ACE0);
    let mut tested = 0usize;
    let mut proven_count = 0usize;
    for _ in 0..400 {
        let (inst, obj, brute_opt) = random_feasible_instance(&mut rng);
        tested += 1;

        // Tiny node budget: search almost always cut off. The ONLY soundness
        // requirement is: IF it claims proven_optimal, the value is correct; and
        // any returned assignment is always feasible with a matching value.
        let budget = rng.range(1, 6) as u64;
        let Some(result) = solve_branch_and_bound(&inst, &obj, None, budget, &never_stop) else {
            continue; // no incumbent found within the tiny budget: nothing to check.
        };

        assert!(
            verify_all_constraints(&inst.constraints, &result.assignment),
            "any returned assignment must be feasible"
        );
        assert_eq!(
            eval_objective(&obj, &result.assignment),
            result.value,
            "assignment objective must match reported value"
        );
        if result.proven_optimal {
            proven_count += 1;
            assert_eq!(
                result.value, brute_opt,
                "CLAIMED optimum {} != brute force {} under tiny budget\nconstraints={:?}\nobj={:?}",
                result.value, brute_opt, inst.constraints, obj
            );
        } else {
            // Not proven: still a valid upper bound (>= the true optimum).
            assert!(
                result.value >= brute_opt,
                "incumbent {} below true optimum {} (impossible if feasible)",
                result.value,
                brute_opt
            );
        }
    }
    assert!(tested >= 400, "expected 400 instances, got {tested}");
    // Sanity: at least some tiny-budget runs should still prove optimality on
    // trivial instances, exercising the proven==true branch under small budget.
    assert!(
        proven_count > 0,
        "expected some tiny-budget runs to prove optimality"
    );
}

#[test]
fn bnb_fixing_polarity() {
    // min x1 + x2  s.t.  x1 + x2 >= 1.
    // True optimum: pick exactly one => value 1.
    let obj = PbObjective {
        terms: vec![term(1, 1), term(1, 2)],
    };
    let constraints = vec![ge(vec![term(1, 1), term(1, 2)], 1)];
    let inst = instance(2, constraints);

    // Unconstrained B&B: optimum is 1.
    let base = solve_branch_and_bound(&inst, &obj, None, 1_000_000, &never_stop).unwrap();
    assert!(base.proven_optimal);
    assert_eq!(base.value, 1);

    // Now verify the unit-fixing polarity through augmented_constraints directly:
    // forcing x1 TRUE must make x1=1 satisfy "+1 x1 >= 1", and x1=0 violate it.
    let force_true = augmented_constraints(&inst.constraints, &[(1, true)]);
    assert!(
        verify_all_constraints(&force_true, &[true, false]),
        "x1=true must satisfy a true-fixing"
    );
    assert!(
        !verify_all_constraints(&force_true, &[false, true]),
        "x1=false must violate a true-fixing"
    );

    // Forcing x1 FALSE must make x1=0 satisfy "-1 x1 >= 0", and x1=1 violate it.
    let force_false = augmented_constraints(&inst.constraints, &[(1, false)]);
    assert!(
        verify_all_constraints(&force_false, &[false, true]),
        "x1=false must satisfy a false-fixing"
    );
    assert!(
        !verify_all_constraints(&force_false, &[true, false]),
        "x1=true must violate a false-fixing"
    );

    // End-to-end through the LP: an instance where forcing a var changes the
    // optimum. min x1 + 2 x2  s.t.  x1 + x2 >= 1.
    //   free optimum: x1=1, x2=0 => 1.
    //   forcing x1=false: must take x2 => value 2.
    let obj2 = PbObjective {
        terms: vec![term(1, 1), term(2, 2)],
    };
    let c2 = vec![ge(vec![term(1, 1), term(1, 2)], 1)];
    // Free.
    let free = solve_branch_and_bound(
        &instance(2, c2.clone()),
        &obj2,
        None,
        1_000_000,
        &never_stop,
    )
    .unwrap();
    assert_eq!(free.value, 1);
    assert!(free.proven_optimal);
    // Forcing x1=false at the instance level: add -1 x1 >= 0 as a real constraint.
    let mut forced = c2.clone();
    forced.push(ge(vec![term(-1, 1)], 0)); // x1 <= 0
    let forced_inst = instance(2, forced);
    let forced_res =
        solve_branch_and_bound(&forced_inst, &obj2, None, 1_000_000, &never_stop).unwrap();
    assert!(forced_res.proven_optimal);
    assert_eq!(
        forced_res.value, 2,
        "forcing x1=false should force taking x2"
    );
    assert!(
        !forced_res.assignment[0],
        "x1 must be false under the forcing"
    );
}

#[test]
fn bnb_seed_incumbent_respected() {
    // min x1 + x2 + x3  s.t.  x1 + x2 + x3 >= 2.  True optimum = 2.
    let obj = PbObjective {
        terms: vec![term(1, 1), term(1, 2), term(1, 3)],
    };
    let constraints = vec![ge(vec![term(1, 1), term(1, 2), term(1, 3)], 2)];
    let inst = instance(3, constraints);

    // A correct but non-optimal seed (all true => value 3).
    let seed = (vec![true, true, true], 3i128);
    let result = solve_branch_and_bound(&inst, &obj, Some(seed), 1_000_000, &never_stop).unwrap();
    assert!(result.proven_optimal);
    assert_eq!(
        result.value, 2,
        "seed must not prevent finding the true optimum"
    );
    assert!(verify_all_constraints(
        &inst.constraints,
        &result.assignment
    ));

    // An optimal seed: still yields the correct proven optimum (== seed value).
    let opt_seed = (vec![true, true, false], 2i128);
    let result2 =
        solve_branch_and_bound(&inst, &obj, Some(opt_seed), 1_000_000, &never_stop).unwrap();
    assert!(result2.proven_optimal);
    assert_eq!(result2.value, 2);
    assert!(verify_all_constraints(
        &inst.constraints,
        &result2.assignment
    ));

    // A BAD seed (infeasible / wrong value) must be discarded, not trusted: the
    // search still proves the true optimum.
    let bad_seed = (vec![false, false, false], 0i128); // infeasible, wrong value
    let result3 =
        solve_branch_and_bound(&inst, &obj, Some(bad_seed), 1_000_000, &never_stop).unwrap();
    assert!(result3.proven_optimal);
    assert_eq!(result3.value, 2);
    assert!(verify_all_constraints(
        &inst.constraints,
        &result3.assignment
    ));
}

#[test]
fn bnb_infeasible_returns_none() {
    // x1 >= 1 AND -1 x1 >= 0 (x1 <= 0): contradictory => no incumbent.
    let obj = PbObjective {
        terms: vec![term(1, 1)],
    };
    let constraints = vec![ge(vec![term(1, 1)], 1), ge(vec![term(-1, 1)], 0)];
    let inst = instance(1, constraints);
    let result = solve_branch_and_bound(&inst, &obj, None, 1_000_000, &never_stop);
    assert!(
        result.is_none(),
        "infeasible instance must yield no incumbent"
    );
}

#[test]
fn bnb_lp_gap_knapsack_like() {
    // A small LP-gap instance: min x1 + x2  s.t.  2 x1 + 2 x2 >= 3.
    // LP optimum = 3/2 -> ceil 2; integer optimum = 2 (both vars). Exercise B&B
    // end-to-end on an instance whose LP relaxation is fractional.
    let obj = PbObjective {
        terms: vec![term(1, 1), term(1, 2)],
    };
    let constraints = vec![ge(vec![term(2, 1), term(2, 2)], 3)];
    let inst = instance(2, constraints);
    let result = solve_branch_and_bound(&inst, &obj, None, 1_000_000, &never_stop).unwrap();
    assert!(result.proven_optimal);
    assert_eq!(result.value, 2);
}

#[test]
fn bnb_proves_weighted_cover_optimum_with_bounded_nodes() {
    // Selecting at least three items with costs 1..=8 has the unique value
    // floor 1+2+3=6.  This distils the old corpus power probe into a fixed
    // branch-and-bound closure and verifies the returned witness exactly.
    let objective = PbObjective {
        terms: (1..=8).map(|var| term(i128::from(var), var)).collect(),
    };
    let constraint = ge((1..=8).map(|var| term(1, var)).collect(), 3);
    let inst = instance(8, vec![constraint]);
    let result = solve_branch_and_bound(&inst, &objective, None, 100_000, &never_stop)
        .expect("cover is feasible");

    assert!(result.proven_optimal);
    assert_eq!(result.value, 6);
    assert!(verify_all_constraints(
        &inst.constraints,
        &result.assignment
    ));
    assert_eq!(eval_objective(&objective, &result.assignment), 6);
}
