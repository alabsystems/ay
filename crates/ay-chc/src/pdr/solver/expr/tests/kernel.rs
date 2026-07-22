// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn is_symbolic_diff_bound_with_coeff_limit(
    expr: &ChcExpr,
    var0: &str,
    var1: &str,
    rhs_var: &str,
    max_coeff: i128,
) -> bool {
    let ChcExpr::Op(ChcOp::Ge, ge_args) = expr else {
        return false;
    };
    if ge_args.len() != 2 {
        return false;
    }
    let lhs = ge_args[0].as_ref();
    let rhs = ge_args[1].as_ref();

    let ChcExpr::Op(ChcOp::Sub, sub_args) = lhs else {
        return false;
    };
    if sub_args.len() != 2 {
        return false;
    }

    let (lhs0, lhs1) = (sub_args[0].as_ref(), sub_args[1].as_ref());
    let (ChcExpr::Var(v0), ChcExpr::Var(v1)) = (lhs0, lhs1) else {
        return false;
    };
    let is_target_pair =
        (v0.name == var0 && v1.name == var1) || (v0.name == var1 && v1.name == var0);
    if !is_target_pair {
        return false;
    }

    match rhs {
        ChcExpr::Var(v) => v.name == rhs_var && max_coeff >= 1,
        ChcExpr::Op(ChcOp::Mul, mul_args) if mul_args.len() == 2 => {
            let (a, b) = (mul_args[0].as_ref(), mul_args[1].as_ref());
            matches!((a, b), (ChcExpr::Int(c), ChcExpr::Var(v)) if *c >= 1 && *c <= max_coeff && v.name == rhs_var)
        }
        _ => false,
    }
}

fn is_var_diff_eq_zero(expr: &ChcExpr, a: &ChcVar, b: &ChcVar) -> bool {
    fn is_var(expr: &ChcExpr, v: &ChcVar) -> bool {
        matches!(expr, ChcExpr::Var(var) if var.name == v.name)
    }

    fn is_neg_var(expr: &ChcExpr, v: &ChcVar) -> bool {
        matches!(expr, ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 && is_var(args[0].as_ref(), v))
    }

    fn is_diff(expr: &ChcExpr, a: &ChcVar, b: &ChcVar) -> bool {
        let ChcExpr::Op(ChcOp::Add, args) = expr else {
            return false;
        };
        if args.len() != 2 {
            return false;
        }
        let (x, y) = (args[0].as_ref(), args[1].as_ref());
        (is_var(x, a) && is_neg_var(y, b)) || (is_var(x, b) && is_neg_var(y, a))
    }

    let ChcExpr::Op(ChcOp::Eq, eq_args) = expr else {
        return false;
    };
    if eq_args.len() != 2 {
        return false;
    }
    let (lhs, rhs) = (eq_args[0].as_ref(), eq_args[1].as_ref());
    match (lhs, rhs) {
        (lhs, ChcExpr::Int(0)) | (ChcExpr::Int(0), lhs) => is_diff(lhs, a, b),
        _ => false,
    }
}

#[test]
fn kernel_affine_discovery_uses_reachable_samples() {
    let input = r#"
(set-logic HORN)

(declare-fun |P| ( Int Int ) Bool)

(assert
  (forall ( (x Int) (y Int) )
(=>
  (and (= x 0) (= y 0))
  (P x y)
)
  )
)
(assert
  (forall ( (x Int) (y Int) (x1 Int) (y1 Int) )
(=>
  (and
    (P x y)
    (= x1 (+ x 1))
    (= y1 (+ y 1))
  )
  (P x1 y1)
)
  )
)

(check-sat)
(exit)
"#;

    let problem = ChcParser::parse(input).expect("parse P kernel fixture");
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let pred = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "P")
        .expect("missing P")
        .id;
    let vars = solver
        .canonical_vars(pred)
        .expect("canonical vars for P")
        .to_vec();

    // Degenerate init: only one init sample exists (0,0). Add a reachable point so
    // kernel synthesis has enough data to infer x=y.
    solver.reachability.must_summaries.add(
        1,
        pred,
        ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(vars[0].clone()), ChcExpr::int(1)),
            ChcExpr::eq(ChcExpr::var(vars[1].clone()), ChcExpr::int(1)),
        ),
    );

    solver.discover_affine_invariants_via_kernel(None);

    let inferred = solver.frames[1].lemmas.iter().any(|lemma| {
        lemma.predicate == pred && is_var_diff_eq_zero(&lemma.formula, &vars[0], &vars[1])
    });
    assert!(
        inferred,
        "expected kernel-discovered invariant using reachable samples"
    );
}

#[test]
fn s_mutants_16_m_000_no_unvalidated_symbolic_diff_bounds() {
    // Embedded fixture for hermetic testing (see #1873)
    let input = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/embedded/s_mutants_16_m_000.smt2"
    ));

    let problem = ChcParser::parse(input).expect("parse s_mutants_16_m_000");
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let itp = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "itp")
        .expect("missing itp predicate")
        .id;
    let itp1 = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "itp1")
        .expect("missing itp1 predicate")
        .id;

    // Seed frame[1] with any invariant for the predecessor predicate so
    // entry-domain inference is available for itp1.
    let itp_vars = solver
        .canonical_vars(itp)
        .expect("canonical vars for itp")
        .to_vec();
    solver.frames[1].add_lemma(Lemma::new(
        itp,
        ChcExpr::ge(ChcExpr::var(itp_vars[0].clone()), ChcExpr::int(0)),
        1,
    ));
    assert!(
        solver.entry_domain_constraint(itp1, 1).is_some(),
        "expected entry domain constraint for itp1 at level 1"
    );

    solver.discover_difference_invariants();

    let itp1_vars = solver
        .canonical_vars(itp1)
        .expect("canonical vars for itp1")
        .to_vec();
    let (a0, a1, a2) = (&itp1_vars[0].name, &itp1_vars[1].name, &itp1_vars[2].name);

    let bad = solver.frames[1].lemmas.iter().any(|lemma| {
        if lemma.predicate != itp1 {
            return false;
        }
        is_symbolic_diff_bound_with_coeff_limit(&lemma.formula, a0, a1, a2, 6)
    });
    assert!(
        !bad,
        "unexpected symbolic diff bounds were added for itp1 in s_mutants_16_m_000"
    );
}

#[test]
fn propagated_symbolic_diff_bound_is_upgraded_for_algebraic_model() {
    let input = r#"
(set-logic HORN)

(declare-fun src (Int Int Int) Bool)
(declare-fun dst (Int Int Int) Bool)

(assert
  (forall ((A Int) (B Int) (C Int))
    (=>
      (and (= A 3) (= B 0) (= C 1))
      (src A B C)
    )
  )
)
(assert
  (forall ((A Int) (B Int) (C Int))
    (=>
      (and (src A B C) (>= (- A B) C))
      (dst A B C)
    )
  )
)
(assert
  (forall ((A Int) (B Int) (C Int) (A2 Int) (B2 Int))
    (=>
      (and (dst A B C) (= A2 (+ A 1)) (= B2 (+ B 1)))
      (dst A2 B2 C)
    )
  )
)
(assert
  (forall ((A Int) (B Int) (C Int))
    (=>
      (and (dst A B C) (< A 0))
      false
    )
  )
)

(check-sat)
"#;

    let problem = ChcParser::parse(input).expect("parse synthetic symbolic diff benchmark");
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    solver.discover_difference_invariants();

    let dst = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "dst")
        .expect("missing dst predicate")
        .id;
    let dst_vars = solver
        .canonical_vars(dst)
        .expect("canonical vars for dst")
        .to_vec();
    let (a0, a1, a2) = (&dst_vars[0].name, &dst_vars[1].name, &dst_vars[2].name);
    let dst_frame_lemmas: Vec<_> = solver.frames[1]
        .lemmas
        .iter()
        .filter(|lemma| lemma.predicate == dst)
        .map(|lemma| format!("{} [alg={}]", lemma.formula, lemma.algebraically_verified))
        .collect();

    let upgraded: Vec<_> = solver.frames[1]
        .lemmas
        .iter()
        .filter(|lemma| {
            lemma.predicate == dst
                && is_symbolic_diff_bound_with_coeff_limit(&lemma.formula, a0, a1, a2, 1)
        })
        .collect();
    assert_eq!(
        upgraded.len(),
        1,
        "expected exactly one propagated dst symbolic diff bound in frame 1; canonical vars={dst_vars:?}; dst frame[1] lemmas={dst_frame_lemmas:?}"
    );
    assert!(
        upgraded[0].algebraically_verified,
        "expected propagated dst symbolic diff bound to be marked algebraically_verified"
    );

    let alg_model = solver.build_model_from_algebraic_lemmas(1);
    let dst_formula = &alg_model
        .get(&dst)
        .expect("algebraic model should contain dst")
        .formula;
    let alg_contains_bound = dst_formula
        .collect_conjuncts()
        .iter()
        .any(|expr| is_symbolic_diff_bound_with_coeff_limit(expr, a0, a1, a2, 1));
    assert!(
        alg_contains_bound,
        "algebraic model should retain the propagated dst symbolic diff bound"
    );
}

#[test]
fn simulate_forward_samples_produces_diverse_states() {
    // Test that forward simulation generates multiple iteration steps.
    // Self-loop: P(x) => P(x + 1)
    // Init: x = 0
    // Expected samples: (0), (1), (2), ..., up to n_steps
    let input = r#"
(set-logic HORN)

(declare-fun |P| ( Int ) Bool)

; Fact: x = 0 ==> P(x)
(assert
  (forall ( (x Int) )
(=>
  (= x 0)
  (P x)
)
  )
)

; Self-loop: P(x) ==> P(x + 1)
(assert
  (forall ( (x Int) (y Int) )
(=>
  (and (P x) (= y (+ x 1)))
  (P y)
)
  )
)

(check-sat)
(exit)
"#;

    let problem = ChcParser::parse(input).expect("parse simple counter fixture");
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let pred = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "P")
        .expect("missing P")
        .id;
    let vars = solver
        .canonical_vars(pred)
        .expect("canonical vars for P")
        .to_vec();

    let mut samples = solver.sample_init_models(pred, 3);
    let forward = solver.simulate_forward_samples_from_init_samples(pred, &samples, 5);
    samples.extend(forward);

    // Should have at least 3 samples: init (0) + at least 2 forward steps
    assert!(
        samples.len() >= 3,
        "expected at least 3 samples from forward simulation, got {}",
        samples.len()
    );

    // Verify we have diverse values, not all the same
    let values: Vec<i128> = samples
        .iter()
        .filter_map(|m| m.get(&vars[0].name).copied())
        .collect();
    let unique_values: ay_core::kani_compat::DetHashSet<i128> = values.iter().copied().collect();
    assert!(
        unique_values.len() >= 3,
        "expected at least 3 unique values from forward simulation, got {unique_values:?}"
    );

    // Verify values are consecutive (0, 1, 2, ...)
    assert!(
        unique_values.contains(&0),
        "expected forward simulation to include init value 0"
    );
    assert!(
        unique_values.contains(&1),
        "expected forward simulation to include value 1 from first step"
    );
}

#[test]
fn simulate_forward_samples_tries_all_ite_split_self_loops() {
    // Regression for #2061: forward simulation must try all ITE-split self-loop clauses.
    //
    // P(x) => P(ite(x < 0, x + 1, x - 1)) is split into two self-loops. The splitting pass
    // emits the else-branch first, which is incompatible with the init sample x = -1.
    // Forward simulation must therefore try the second clause to produce x = 0.
    let input = r#"
(set-logic HORN)

(declare-fun |P| ( Int ) Bool)

; Fact: x = -1 ==> P(x)
(assert
  (forall ( (x Int) )
(=>
  (= x (- 1))
  (P x)
)
  )
)

; Self-loop: P(x) ==> P(ite(x < 0, x + 1, x - 1))
(assert
  (forall ( (x Int) )
(=>
  (P x)
  (P (ite (< x 0) (+ x 1) (- x 1)))
)
  )
)

(check-sat)
(exit)
"#;

    let mut problem = ChcParser::parse(input).expect("parse ITE split fixture");
    // Force ITE splitting for hermetic regression coverage (#2061).
    problem.try_split_ites_in_clauses(32, false);

    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let pred = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "P")
        .expect("missing P")
        .id;

    let canonical_vars = solver
        .canonical_vars(pred)
        .expect("canonical vars for P")
        .to_vec();
    let int_vars: Vec<ChcVar> = canonical_vars
        .iter()
        .filter(|v| matches!(v.sort, ChcSort::Int))
        .cloned()
        .collect();
    assert_eq!(
        int_vars.len(),
        1,
        "expected exactly one int canonical var for P"
    );

    let self_loops: Vec<HornClause> = solver
        .problem
        .clauses_defining(pred)
        .filter(|c| {
            crate::lemma_hints::RecurrenceConservedEqualityProvider::is_self_loop(c)
                .map(|(pid, _, _)| pid == pred)
                .unwrap_or(false)
        })
        .cloned()
        .collect();
    assert!(
        self_loops.len() >= 2,
        "expected ITE splitting to produce >=2 self-loop clauses, got {}",
        self_loops.len()
    );

    let samples = solver.sample_init_models(pred, 1);
    assert_eq!(samples.len(), 1, "expected exactly one init sample");

    let x_name = canonical_vars[0].name.clone();
    assert_eq!(
        samples[0].get(&x_name).copied(),
        Some(-1),
        "expected init sample x=-1"
    );

    // Sanity: the first ITE-split clause is (currently) the else-branch and is incompatible.
    assert!(
        solver
            .apply_self_loop_transition(&self_loops[0], &samples[0], &canonical_vars, &int_vars)
            .is_none(),
        "expected first ITE-split self-loop clause to be incompatible with init sample"
    );

    let forward = solver.simulate_forward_samples_from_init_samples(pred, &samples, 3);
    assert!(
        forward.iter().any(|m| m.get(&x_name).copied() == Some(0)),
        "expected forward simulation to reach x=0 using a compatible ITE-split clause, got {forward:?}"
    );
}
