// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the multi-group proof substrate (C-P1) and its script /
//! conversion helpers. Owner: WP-D1-P (Workstream D Rung 1,
//! `DESIGN_lra_interp_tpa.md` §9): masks and recipes under every validation
//! policy, path interpolants on a 3-step chain with the sequence property,
//! the fail-closed paths (locality against the caller's set, invalid masks,
//! fragment gate, SAT pairs, budget), the pinned Real constant forms, the
//! sort-preserving converter, and the proof_backed QF_LRA route.

use super::*;
use crate::interpolation::proof_script::{
    dag_var_names, dpll_term_to_chc_expr, parse_const_text, scan_logic, ProofLogic,
};
use crate::{ChcOp, ChcVar};
use ay_dpll::api::Logic;

const BUDGET: Duration = Duration::from_secs(20);

fn rvar(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Real))
}

fn ivar(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

fn real(n: i64) -> ChcExpr {
    ChcExpr::Real(n, 1)
}

fn names(ns: &[&str]) -> FxHashSet<String> {
    ns.iter().map(|s| (*s).to_string()).collect()
}

fn unsat(expr: &ChcExpr) -> bool {
    is_unsat_result(&SmtContext::new().check_sat(expr))
}

/// A = { x < y, y < z }, B = { z <= x } over Reals (shared x, z).
fn chain_pair() -> (Vec<ChcExpr>, Vec<ChcExpr>) {
    (
        vec![
            ChcExpr::lt(rvar("x"), rvar("y")),
            ChcExpr::lt(rvar("y"), rvar("z")),
        ],
        vec![ChcExpr::le(rvar("z"), rvar("x"))],
    )
}

fn refute(groups: &[&[ChcExpr]]) -> ProofRefutation {
    match proof_check_groups(groups, BUDGET, DEFAULT_DAG_CAPS) {
        ProofCheck::Unsat(r) => r,
        ProofCheck::Sat => panic!("expected UNSAT, got SAT"),
        ProofCheck::Unknown(u) => panic!("expected UNSAT, got unknown ({})", u.name()),
    }
}

#[test]
fn board_names_are_stable() {
    assert_eq!(ItpRecipe::McMillanPrime.name(), "mcmillan_prime");
    assert_eq!(ItpUnknown::ParseMismatch.name(), "parse_mismatch");
    assert_eq!(ItpFail::CraigUnknown.name(), "craig_unknown");
    assert_eq!(ItpFail::UnsupportedStep.name(), "unsupported_step");
    assert_eq!(GroupMask(0b101), GroupMask(5));
}

#[test]
fn two_groups_every_recipe_is_craig_valid_under_full_validation() {
    let (a, b) = chain_pair();
    let mut r = refute(&[&a, &b]);
    let shared = names(&["x", "z"]);
    for recipe in [
        ItpRecipe::Pudlak,
        ItpRecipe::McMillan,
        ItpRecipe::McMillanPrime,
    ] {
        let itp = r
            .interpolant(GroupMask(1), recipe, &shared, ValidatePolicy::Full)
            .unwrap_or_else(|f| panic!("{}: {}", recipe.name(), f.name()));
        assert!(dag_var_names(&itp).is_subset(&shared), "{}", recipe.name());
        // Independent re-check with the plain Verification-lane context.
        assert!(unsat(&ChcExpr::and_vec(vec![
            a[0].clone(),
            a[1].clone(),
            ChcExpr::not(itp.clone())
        ])));
        assert!(unsat(&ChcExpr::and_vec(vec![itp.clone(), b[0].clone()])));
        // Real strict row: the interpolant must not be integer-tightened
        // (x = 0, z = 1/2 satisfies `x < z`).
        let witness = ChcExpr::and_vec(vec![
            itp,
            ChcExpr::eq(rvar("x"), real(0)),
            ChcExpr::eq(rvar("z"), ChcExpr::Real(1, 2)),
        ]);
        assert!(!unsat(&witness), "{}: tightened Real row", recipe.name());
    }
}

#[test]
fn sampled_and_oracle_guarded_policies_serve() {
    let (a, b) = chain_pair();
    let mut r = refute(&[&a, &b]);
    let shared = names(&["x", "z"]);
    for policy in [
        ValidatePolicy::Sampled(2),
        ValidatePolicy::Sampled(2),
        ValidatePolicy::OracleGuarded,
    ] {
        r.interpolant(GroupMask(1), ItpRecipe::McMillan, &shared, policy)
            .unwrap_or_else(|f| panic!("{policy:?}: {}", f.name()));
    }
}

#[test]
fn path_interpolants_on_a_three_step_chain() {
    // x0 = 0; x1 = x0 + 1; x2 = x1 + 1; x2 > 5 (UNSAT).
    let groups: Vec<Vec<ChcExpr>> = vec![
        vec![ChcExpr::eq(rvar("x0"), real(0))],
        vec![ChcExpr::eq(rvar("x1"), ChcExpr::add(rvar("x0"), real(1)))],
        vec![ChcExpr::eq(rvar("x2"), ChcExpr::add(rvar("x1"), real(1)))],
        vec![ChcExpr::gt(rvar("x2"), real(5))],
    ];
    let refs: Vec<&[ChcExpr]> = groups.iter().map(Vec::as_slice).collect();
    let mut r = refute(&refs);
    let shared = vec![names(&["x0"]), names(&["x1"]), names(&["x2"])];
    let itps = r
        .path_interpolants(ItpRecipe::McMillan, &shared, ValidatePolicy::Full)
        .unwrap_or_else(|f| panic!("path interpolants: {}", f.name()));
    assert_eq!(itps.len(), 3);
    for (i, itp) in itps.iter().enumerate() {
        assert!(dag_var_names(itp).is_subset(&shared[i]), "cut {i}");
    }
    // Sequence property: I_i ∧ G_{i+1} ⊨ I_{i+1}.
    for i in 0..2 {
        let q = ChcExpr::and_vec(vec![
            itps[i].clone(),
            groups[i + 1][0].clone(),
            ChcExpr::not(itps[i + 1].clone()),
        ]);
        assert!(unsat(&q), "I{} ∧ G{} must entail I{}", i + 1, i + 2, i + 2);
    }
    // Wrong arity of the shared list fails closed.
    assert_eq!(
        r.path_interpolants(ItpRecipe::McMillan, &shared[..2], ValidatePolicy::Full),
        Err(ItpFail::Conversion)
    );
}

#[test]
fn locality_is_checked_against_the_callers_shared_set() {
    let (a, b) = chain_pair();
    let mut r = refute(&[&a, &b]);
    // The interpolant needs z; a caller set without it must be refused.
    assert_eq!(
        r.interpolant(
            GroupMask(1),
            ItpRecipe::McMillan,
            &names(&["x"]),
            ValidatePolicy::OracleGuarded
        ),
        Err(ItpFail::NonLocal)
    );
}

#[test]
fn invalid_masks_fail_closed() {
    let (a, b) = chain_pair();
    let mut r = refute(&[&a, &b]);
    let shared = names(&["x", "z"]);
    for mask in [0u128, 0b11, 0b100] {
        assert_eq!(
            r.interpolant(
                GroupMask(mask),
                ItpRecipe::Pudlak,
                &shared,
                ValidatePolicy::Full
            ),
            Err(ItpFail::Conversion),
            "mask {mask:#b}"
        );
    }
}

#[test]
fn craig_valid_rejects_non_interpolants() {
    let (a, b) = chain_pair();
    let r = refute(&[&a, &b]);
    let shared = names(&["x", "z"]);
    // `true ∧ B` is satisfiable.
    assert_eq!(
        r.craig_valid(GroupMask(1), &ChcExpr::Bool(true), &shared),
        Err(ItpFail::CraigInvalid)
    );
    // `A ⊭ z < x`.
    assert_eq!(
        r.craig_valid(GroupMask(1), &ChcExpr::lt(rvar("z"), rvar("x")), &shared),
        Err(ItpFail::CraigInvalid)
    );
    assert_eq!(
        r.craig_valid(GroupMask(1), &ChcExpr::lt(rvar("x"), rvar("z")), &shared),
        Ok(())
    );
}

#[test]
fn sat_pairs_and_fragments_are_reported() {
    let a = vec![ChcExpr::lt(rvar("x"), rvar("y"))];
    let b = vec![ChcExpr::lt(rvar("y"), rvar("z"))];
    assert!(matches!(
        proof_check_groups(&[&a, &b], BUDGET, DEFAULT_DAG_CAPS),
        ProofCheck::Sat
    ));
    // Int + Real mix.
    let mixed = vec![ChcExpr::lt(ivar("n"), ChcExpr::int(3))];
    assert!(matches!(
        proof_check_groups(&[&a, &mixed], BUDGET, DEFAULT_DAG_CAPS),
        ProofCheck::Unknown(ItpUnknown::Fragment)
    ));
    // Bit-vectors are outside the fragment.
    let bv = vec![ChcExpr::eq(
        ChcExpr::var(ChcVar::new("v", ChcSort::BitVec(8))),
        ChcExpr::BitVec(1, 8),
    )];
    assert!(matches!(
        proof_check_groups(&[&a, &bv], BUDGET, DEFAULT_DAG_CAPS),
        ProofCheck::Unknown(ItpUnknown::Fragment)
    ));
    // A single group is not an interpolation query.
    assert!(matches!(
        proof_check_groups(&[&a], BUDGET, DEFAULT_DAG_CAPS),
        ProofCheck::Unknown(ItpUnknown::Size)
    ));
    // Nonlinear products are outside the fragment.
    let nl = vec![ChcExpr::lt(ChcExpr::mul(rvar("x"), rvar("y")), real(0))];
    assert!(matches!(
        proof_check_groups(&[&nl, &b], BUDGET, DEFAULT_DAG_CAPS),
        ProofCheck::Unknown(ItpUnknown::Fragment)
    ));
}

#[test]
fn zero_budget_is_a_budget_unknown() {
    let (a, b) = chain_pair();
    assert!(matches!(
        proof_check_groups(&[&a, &b], Duration::ZERO, DEFAULT_DAG_CAPS),
        ProofCheck::Unknown(ItpUnknown::Budget)
    ));
}

#[test]
fn fragment_logic_dispatch() {
    let (a, b) = chain_pair();
    let lra: Vec<&ChcExpr> = a.iter().chain(b.iter()).collect();
    assert_eq!(scan_logic(&lra, 1000), Ok(ProofLogic::QfLra));
    let lia = [ChcExpr::lt(ivar("n"), ChcExpr::int(3))];
    assert_eq!(scan_logic(&[&lia[0]], 1000), Ok(ProofLogic::QfLia));
    let mixed = [ChcExpr::lt(ivar("n"), ChcExpr::int(3)), a[0].clone()];
    assert_eq!(
        scan_logic(&[&mixed[0], &mixed[1]], 1000),
        Err(ItpUnknown::Fragment)
    );
    // The same name with two sorts is outside the fragment.
    let clash = [ChcExpr::lt(ivar("x"), ChcExpr::int(3)), a[0].clone()];
    assert_eq!(
        scan_logic(&[&clash[0], &clash[1]], 1000),
        Err(ItpUnknown::Fragment)
    );
    // The unique-node cap counts DAG nodes, not tree nodes.
    let mut node = std::sync::Arc::new(rvar("r"));
    for _ in 0..40 {
        node = std::sync::Arc::new(ChcExpr::Op(
            ChcOp::Add,
            vec![std::sync::Arc::clone(&node), std::sync::Arc::clone(&node)],
        ));
    }
    let wide = ChcExpr::lt((*node).clone(), real(0));
    assert_eq!(scan_logic(&[&wide], 100), Ok(ProofLogic::QfLra));
    assert_eq!(scan_logic(&[&wide], 10), Err(ItpUnknown::Size));
}

#[test]
fn parse_const_text_pinned_forms() {
    let r = ChcSort::Real;
    let i = ChcSort::Int;
    assert_eq!(parse_const_text("5.0", &r), Ok(ChcExpr::Real(5, 1)));
    assert_eq!(parse_const_text("(- 5.0)", &r), Ok(ChcExpr::Real(-5, 1)));
    assert_eq!(parse_const_text("(/ 3 2)", &r), Ok(ChcExpr::Real(3, 2)));
    assert_eq!(
        parse_const_text("(- (/ 3 2))", &r),
        Ok(ChcExpr::Real(-3, 2))
    );
    assert_eq!(parse_const_text("(/ 7.0 2.0)", &r), Ok(ChcExpr::Real(7, 2)));
    assert_eq!(parse_const_text("1.25", &r), Ok(ChcExpr::Real(5, 4)));
    assert_eq!(parse_const_text("7", &r), Ok(ChcExpr::Real(7, 1)));
    assert_eq!(parse_const_text("42", &i), Ok(ChcExpr::Int(42)));
    assert_eq!(parse_const_text("(- 12)", &i), Ok(ChcExpr::Int(-12)));
    assert_eq!(parse_const_text("(/ 3 2)", &i), Err(ItpFail::Conversion));
    assert_eq!(
        parse_const_text("true", &ChcSort::Bool),
        Ok(ChcExpr::Bool(true))
    );
    assert_eq!(parse_const_text("x", &r), Err(ItpFail::Conversion));
    assert_eq!(
        parse_const_text("1180591620717411303424.0", &r),
        Err(ItpFail::CoefficientOverflow)
    );
    assert_eq!(
        parse_const_text("(/ 1 1180591620717411303424)", &r),
        Err(ItpFail::CoefficientOverflow)
    );
}

#[test]
fn conversion_is_sort_preserving() {
    let mut s = Solver::try_new(Logic::QfLra).expect("QF_LRA");
    let terms = s
        .parse_smtlib2("(declare-const x Real)\n(assert (<= x (/ 1 3)))\n")
        .expect("parses");
    let sorts: FxHashMap<String, ChcSort> =
        [("x".to_string(), ChcSort::Real)].into_iter().collect();
    let mut budget = 1000;
    let e = dpll_term_to_chc_expr(&s, terms[0], &sorts, &mut budget).expect("converts");
    assert_eq!(e, ChcExpr::le(rvar("x"), ChcExpr::Real(1, 3)));

    let mut s = Solver::try_new(Logic::QfLia).expect("QF_LIA");
    let terms = s
        .parse_smtlib2("(declare-const n Int)\n(assert (<= n (- 12)))\n")
        .expect("parses");
    let sorts: FxHashMap<String, ChcSort> = [("n".to_string(), ChcSort::Int)].into_iter().collect();
    let mut budget = 1000;
    let e = dpll_term_to_chc_expr(&s, terms[0], &sorts, &mut budget).expect("converts");
    assert!(
        matches!(&e, ChcExpr::Op(ChcOp::Le, args) if *args[1] == ChcExpr::Int(-12)),
        "{e:?}"
    );

    // Unrepresentable Real constants and unknown names fail closed.
    let mut s = Solver::try_new(Logic::QfLra).expect("QF_LRA");
    let terms = s
        .parse_smtlib2(
            "(declare-const x Real)\n(declare-const w Real)\n\
             (assert (<= x 1180591620717411303424.0))\n(assert (<= w 0.0))\n",
        )
        .expect("parses");
    let sorts: FxHashMap<String, ChcSort> =
        [("x".to_string(), ChcSort::Real)].into_iter().collect();
    let mut budget = 1000;
    assert_eq!(
        dpll_term_to_chc_expr(&s, terms[0], &sorts, &mut budget),
        Err(ItpFail::CoefficientOverflow)
    );
    let mut budget = 1000;
    assert_eq!(
        dpll_term_to_chc_expr(&s, terms[1], &sorts, &mut budget),
        Err(ItpFail::Conversion)
    );
    let mut budget = 0;
    assert_eq!(
        dpll_term_to_chc_expr(&s, terms[0], &sorts, &mut budget),
        Err(ItpFail::Budget)
    );
}

#[test]
fn proof_backed_serves_lra_through_proof_groups() {
    let (a, b) = chain_pair();
    let shared = names(&["x", "z"]);
    let (served_before, ..) = super::super::proof_interpolant_stats();
    let itp = super::super::proof_backed::try_proof_derived_interpolant(&a, &b, &shared, BUDGET)
        .expect("a QF_LRA pair must be served by the proof substrate");
    let (served_after, ..) = super::super::proof_interpolant_stats();
    assert!(served_after > served_before);
    assert!(dag_var_names(&itp).is_subset(&shared));
    assert!(unsat(&ChcExpr::and_vec(vec![
        a[0].clone(),
        a[1].clone(),
        ChcExpr::not(itp.clone())
    ])));
    assert!(unsat(&ChcExpr::and_vec(vec![itp, b[0].clone()])));
}
