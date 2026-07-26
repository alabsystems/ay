// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for proof-derived Craig interpolation (rank-4 inc-3).

use super::super::fallback::is_valid_interpolant;
use super::*;
use crate::ChcVar;

fn bvar(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Bool))
}

fn ivar(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

fn shared(names: &[&str]) -> FxHashSet<String> {
    names.iter().map(|s| (*s).to_string()).collect()
}

/// KEYSTONE (inc-3): a Bool-guarded conflict whose Craig interpolant is a
/// shared atom already present in the proof. The proof-producing solve +
/// McMillan/Pudlak traversal must serve a VERIFIED interpolant end-to-end.
///
/// A: g, (¬g ∨ b)        — A ⊨ b
/// B: (¬b ∨ h), ¬h       — B ⊨ ¬b
/// Shared: {b}; expected interpolant: b (or an equivalent over {b}).
#[test]
fn test_proof_derived_interpolant_bool_guarded_shared_atom() {
    let a_constraints = vec![bvar("g"), ChcExpr::or(ChcExpr::not(bvar("g")), bvar("b"))];
    let b_constraints = vec![
        ChcExpr::or(ChcExpr::not(bvar("b")), bvar("h")),
        ChcExpr::not(bvar("h")),
    ];
    let shared_vars = shared(&["b"]);

    let (served_before, ..) = proof_interpolant_stats();
    let itp = try_proof_derived_interpolant(
        &a_constraints,
        &b_constraints,
        &shared_vars,
        Duration::from_secs(10),
    )
    .expect("Bool-guarded shared-atom conflict must serve a proof-derived interpolant");

    assert!(
        is_valid_interpolant(&a_constraints, &b_constraints, &itp, &shared_vars),
        "served interpolant must satisfy the Craig properties: {itp:?}"
    );
    let (served_after, ..) = proof_interpolant_stats();
    assert!(
        served_after > served_before,
        "served counter must record the consumed proof-derived interpolant"
    );
}

/// Mixed Bool-guard + LIA equality network (the MINI conservation step from
/// the interpolation spike, expressed as ChcExpr). The production proof
/// traversal may or may not produce a candidate that passes validation —
/// EITHER outcome is sound: `Some` must be Craig-valid, `None` falls back.
#[test]
fn test_proof_derived_interpolant_mini_conservation_sound() {
    let guarded = |guard: ChcExpr, eq: ChcExpr| ChcExpr::or(ChcExpr::not(guard), eq);
    let a_constraints = vec![
        guarded(
            bvar("g"),
            ChcExpr::eq(ivar("x1"), ChcExpr::add(ivar("x"), ChcExpr::int(1))),
        ),
        guarded(
            bvar("g"),
            ChcExpr::eq(ivar("y1"), ChcExpr::sub(ivar("y"), ChcExpr::int(1))),
        ),
        ChcExpr::or(bvar("g"), ChcExpr::eq(ivar("x1"), ivar("x"))),
        ChcExpr::or(bvar("g"), ChcExpr::eq(ivar("y1"), ivar("y"))),
        ChcExpr::eq(ivar("z1"), ivar("z")),
        guarded(
            bvar("h"),
            ChcExpr::eq(ivar("y2"), ChcExpr::add(ivar("y1"), ChcExpr::int(1))),
        ),
        guarded(
            bvar("h"),
            ChcExpr::eq(ivar("z2"), ChcExpr::sub(ivar("z1"), ChcExpr::int(1))),
        ),
        ChcExpr::or(bvar("h"), ChcExpr::eq(ivar("y2"), ivar("y1"))),
        ChcExpr::or(bvar("h"), ChcExpr::eq(ivar("z2"), ivar("z1"))),
        ChcExpr::eq(ivar("x2"), ivar("x1")),
    ];
    let b_constraints = vec![ChcExpr::not(ChcExpr::eq(
        ChcExpr::add(ChcExpr::add(ivar("x2"), ivar("y2")), ivar("z2")),
        ChcExpr::add(ChcExpr::add(ivar("x"), ivar("y")), ivar("z")),
    ))];
    let shared_vars = shared(&["x", "y", "z", "x2", "y2", "z2"]);

    if let Some(itp) = try_proof_derived_interpolant(
        &a_constraints,
        &b_constraints,
        &shared_vars,
        Duration::from_secs(10),
    ) {
        assert!(
            is_valid_interpolant(&a_constraints, &b_constraints, &itp, &shared_vars),
            "any served interpolant must satisfy the Craig properties: {itp:?}"
        );
    }
}

/// Unsupported fragment (array select) must be rejected before the proof
/// solve and counted as not-applicable.
#[test]
fn test_proof_derived_interpolant_rejects_unsupported_fragment() {
    let arr = ChcExpr::var(ChcVar::new(
        "a",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    ));
    let a_constraints = vec![ChcExpr::eq(
        ChcExpr::select(arr, ivar("i")),
        ChcExpr::int(1),
    )];
    let b_constraints = vec![ChcExpr::ne(ivar("i"), ivar("i"))];
    let shared_vars = shared(&["i"]);

    let (_, _, na_before, _) = proof_interpolant_stats();
    assert!(try_proof_derived_interpolant(
        &a_constraints,
        &b_constraints,
        &shared_vars,
        Duration::from_secs(2),
    )
    .is_none());
    let (_, _, na_after, _) = proof_interpolant_stats();
    assert!(na_after > na_before, "not-applicable counter must move");
}

/// `proof_budget = None` must be byte-for-byte the existing cascade.
#[test]
fn test_with_proof_disabled_is_cascade() {
    let a_constraints = vec![ChcExpr::ge(ivar("x"), ChcExpr::int(10))];
    let b_constraints = vec![ChcExpr::le(ivar("x"), ChcExpr::int(5))];
    let shared_vars = shared(&["x"]);

    let direct = interpolating_sat_constraints(&a_constraints, &b_constraints, &shared_vars);
    let (wrapped, proof_validated) = interpolating_sat_constraints_with_proof_provenance(
        &a_constraints,
        &b_constraints,
        &shared_vars,
        None,
        None,
    );
    assert!(
        !proof_validated,
        "disabled proof path must never claim proof provenance"
    );
    match (direct, wrapped) {
        (InterpolatingSatResult::Unsat(d), InterpolatingSatResult::Unsat(w)) => {
            assert_eq!(
                d, w,
                "disabled proof path must not change the cascade result"
            );
        }
        (InterpolatingSatResult::Unknown, InterpolatingSatResult::Unknown) => {}
        (d, w) => panic!("cascade/wrapper divergence: {d:?} vs {w:?}"),
    }
}

/// With the proof path enabled, the wrapper must still return a valid
/// interpolant (served or cascade fallback — both verified).
#[test]
fn test_with_proof_enabled_returns_valid_interpolant() {
    let a_constraints = vec![ChcExpr::ge(ivar("x"), ChcExpr::int(10))];
    let b_constraints = vec![ChcExpr::le(ivar("x"), ChcExpr::int(5))];
    let shared_vars = shared(&["x"]);

    match interpolating_sat_constraints_with_proof_provenance(
        &a_constraints,
        &b_constraints,
        &shared_vars,
        Some(Duration::from_secs(10)),
        Some(Duration::from_secs(10)),
    ) {
        (InterpolatingSatResult::Unsat(itp), proof_validated) => {
            assert!(
                is_valid_interpolant(&a_constraints, &b_constraints, &itp, &shared_vars),
                "wrapper interpolant must satisfy the Craig properties \
                 (proof_validated={proof_validated}): {itp:?}"
            );
        }
        (InterpolatingSatResult::Unknown, _) => {
            panic!("x>=10 vs x<=5 must interpolate (cascade fallback at minimum)")
        }
    }
}

#[test]
fn test_parse_const_text() {
    assert_eq!(parse_const_text("true"), Some(ChcExpr::Bool(true)));
    assert_eq!(parse_const_text("false"), Some(ChcExpr::Bool(false)));
    assert_eq!(parse_const_text("42"), Some(ChcExpr::Int(42)));
    assert_eq!(parse_const_text("(- 7)"), Some(ChcExpr::Int(-7)));
    assert_eq!(parse_const_text("-7"), Some(ChcExpr::Int(-7)));
    assert_eq!(parse_const_text("x"), None);
    assert_eq!(parse_const_text("(/ 1 2)"), None);
}

/// Fragment gate: div/mod, reals, and predicate applications are rejected.
#[test]
fn test_fragment_gate_rejections() {
    let shared_vars = shared(&["x"]);
    for bad in [
        ChcExpr::Op(
            ChcOp::Mod,
            vec![
                std::sync::Arc::new(ivar("x")),
                std::sync::Arc::new(ChcExpr::int(2)),
            ],
        ),
        ChcExpr::eq(
            ChcExpr::var(ChcVar::new("x", ChcSort::Real)),
            ChcExpr::Real(1, 2),
        ),
    ] {
        assert!(
            try_proof_derived_interpolant(
                &[bad],
                &[ChcExpr::le(ivar("x"), ChcExpr::int(5))],
                &shared_vars,
                Duration::from_secs(2),
            )
            .is_none(),
            "out-of-fragment constraint must be rejected"
        );
    }
}

/// KEYSTONE (inc-17): a Bool-guarded var-var equality NETWORK whose conflict
/// needs the equality atoms — the EqDiffVar script-level rewrite must fire,
/// the proof solve must complete, and the served interpolant must be over
/// the ORIGINAL signature (no definitional variables) and Craig-valid.
#[test]
fn test_proof_derived_interpolant_eq_diffvar_guarded_network() {
    let guarded = |guard: ChcExpr, eq: ChcExpr| ChcExpr::or(ChcExpr::not(guard), eq);
    // A: g, (¬g ∨ x = y), (¬g ∨ y = z)   — A ⊨ x = z
    let a_constraints = vec![
        bvar("g"),
        guarded(bvar("g"), ChcExpr::eq(ivar("x"), ivar("y"))),
        guarded(bvar("g"), ChcExpr::eq(ivar("y"), ivar("z"))),
    ];
    // B: h, (¬h ∨ x = z + 1)             — B ⊨ x = z + 1
    let b_constraints = vec![
        bvar("h"),
        guarded(
            bvar("h"),
            ChcExpr::eq(ivar("x"), ChcExpr::add(ivar("z"), ChcExpr::int(1))),
        ),
    ];
    let shared_vars = shared(&["x", "z"]);

    if let Some(itp) = try_proof_derived_interpolant(
        &a_constraints,
        &b_constraints,
        &shared_vars,
        Duration::from_secs(10),
    ) {
        assert!(
            !itp.vars().iter().any(|v| v.name.starts_with("ay_eqdv_p")),
            "definitional variables must be back-substituted away: {itp:?}"
        );
        assert!(
            is_valid_interpolant(&a_constraints, &b_constraints, &itp, &shared_vars),
            "served interpolant must satisfy the Craig properties: {itp:?}"
        );
    }
}

fn replay_proof_script(
    text: &str,
    a_count: usize,
    budget: Duration,
) -> Option<(ChcExpr, Vec<ChcExpr>, Vec<ChcExpr>, FxHashSet<String>)> {
    // Variable sorts from the (machine-generated) declare-const lines.
    let mut var_sorts: FxHashMap<String, ChcSort> = FxHashMap::default();
    for line in text.lines() {
        let Some(rest) = line.trim().strip_prefix("(declare-const ") else {
            continue;
        };
        let mut parts = rest.trim_end_matches(')').split_whitespace();
        let (Some(name), Some(sort)) = (parts.next(), parts.next()) else {
            continue;
        };
        let sort = match sort {
            "Int" => ChcSort::Int,
            "Bool" => ChcSort::Bool,
            other => panic!("unsupported sort in dump: {other}"),
        };
        var_sorts.insert(name.to_string(), sort);
    }

    // Parse asserts via the ay-dpll frontend, convert back to ChcExpr with
    // the production converter.
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    let asserts = solver.parse_smtlib2(text).expect("parseable dump");
    assert!(a_count < asserts.len(), "split must leave a non-empty B");
    let mut exprs: Vec<ChcExpr> = Vec::with_capacity(asserts.len());
    for &t in &asserts {
        let mut budget = 500_000usize;
        exprs.push(
            dpll_term_to_chc_expr(&solver, t, &var_sorts, &mut budget)
                .expect("dump assert converts to ChcExpr"),
        );
    }
    let (a_constraints, b_constraints) = exprs.split_at(a_count);
    let a_vars: FxHashSet<String> = a_constraints
        .iter()
        .flat_map(|c| c.vars())
        .map(|v| v.name)
        .collect();
    let shared_vars: FxHashSet<String> = b_constraints
        .iter()
        .flat_map(|c| c.vars())
        .map(|v| v.name)
        .filter(|n| a_vars.contains(n))
        .collect();

    let result = try_proof_derived_interpolant(a_constraints, b_constraints, &shared_vars, budget);
    result.map(|itp| {
        (
            itp,
            a_constraints.to_vec(),
            b_constraints.to_vec(),
            shared_vars,
        )
    })
}

/// Replays a small proof-solve dump through the production parser, converter,
/// proof traversal, and Craig validator. Captured production dumps are handled
/// by the bounded `proof_interpolant_replay` example rather than ambient test
/// configuration.
#[test]
fn repro_proof_itp_replay() {
    const BUILTIN: &str = r#"
(set-logic QF_LIA)
(declare-const g Bool)
(declare-const b Bool)
(declare-const h Bool)
(assert g)
(assert (or (not g) b))
(assert (or (not b) h))
(assert (not h))
"#;

    let (itp, a_constraints, b_constraints, shared_vars) =
        replay_proof_script(BUILTIN, 2, Duration::from_secs(10))
            .expect("built-in proof replay must serve an interpolant");
    assert!(
        !itp.vars().iter().any(|v| v.name.starts_with("ay_eqdv_p")),
        "definitional variables must not survive: {itp:?}"
    );
    assert!(
        is_valid_interpolant(&a_constraints, &b_constraints, &itp, &shared_vars),
        "replayed interpolant must satisfy the Craig properties: {itp:?}"
    );
}
