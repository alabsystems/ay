// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The deductive-checks `Map<u32,(u32,u32)>` false-claim obligation, replayed through
//! the Rust API exactly as deductive-checks's encoder issues it (C-4 of the 2026-09-16
//! solver-fix round, `collection_tuple_element_capability::
//! map_tuple_false_counterexamples`).
//!
//! The SMT-LIB reconstruction of the same query answers `sat` (see
//! `executor_tests::smt::dt_array_quoted_carrier`), but the in-process solve
//! differs in ways the text cannot express: the datatype is declared through
//! `try_declare_datatype` and its constructor/selector handles are ADOPTED
//! through `try_declare_fun`, the selector-over-constructor goal is built with
//! `try_apply` (never folded by the elaborator), the solver carries deductive-checks's
//! settings (`Readable` counterexamples, proofs, unsat cores, a wall backstop),
//! and the obligation is the SECOND `check_sat` of one incremental session
//! (push / named negated goal / check / pop, twice). z3 answers `sat` on the
//! faithful reconstruction.
//!
//! KNOWN GAP (C-4 residual, measured 2026-09-16): every variant of this API
//! construction — with or without the `Readable` style, proofs/cores, the
//! prior push/pop obligation, named asserts, and even with the goal folded
//! the way the elaborator folds it — is fail-closed by the independent gate
//! ("datatype sort requires a constructor-bearing value"): the array leaf
//! `m` is marked read-conflicted by the completion pass because an earlier
//! completion round installed the cell `m[0] = (u32_u32_Tuple 1 2)` (from the
//! EUF lane's free field values) while the datatype construction pins the
//! same class to its default `(u32_u32_Tuple 0 0)`; the two engines never
//! agree on one value per class. The SMT-LIB text of the same query answers
//! `sat`, so the divergence is in API-side term construction. The sentinels
//! below pin the CURRENT fail-closed verdict so the fix re-keys them loudly;
//! they never accept `unsat`.

use std::time::Duration;

use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Logic, Solver, Sort};
use ay_dpll::CounterexampleStyle;

fn bv32() -> Sort {
    Sort::bitvec(32)
}

struct Shape {
    deductive_checks_settings: bool,
    prior_obligation: bool,
}

fn run(shape: Shape) -> ay_dpll::api::SolveDetails {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    if shape.deductive_checks_settings {
        solver.set_counterexample_style(CounterexampleStyle::Readable);
        solver.set_produce_proofs(true);
        solver.set_produce_unsat_cores(true);
        solver.set_timeout(Some(Duration::from_millis(30_000)));
    }

    let dt_name = "(u32, u32)";
    let dt = DatatypeSort {
        name: dt_name.to_string(),
        constructors: vec![DatatypeConstructor {
            name: "u32_u32_Tuple".to_string(),
            fields: vec![
                DatatypeField {
                    name: "u32_u32_Tuple_0".to_string(),
                    sort: bv32(),
                },
                DatatypeField {
                    name: "u32_u32_Tuple_1".to_string(),
                    sort: bv32(),
                },
            ],
        }],
    };
    solver.try_declare_datatype(&dt).expect("declare datatype");
    let carrier = Sort::Uninterpreted(dt_name.to_string());
    // Adopted handles over the native members (deductive-checks's encoder shape).
    let ctor = solver
        .try_declare_fun("u32_u32_Tuple", &[bv32(), bv32()], carrier.clone())
        .expect("adopt constructor");
    let _sel0 = solver
        .try_declare_fun("u32_u32_Tuple_0", &[carrier.clone()], bv32())
        .expect("adopt selector 0");
    let sel1 = solver
        .try_declare_fun("u32_u32_Tuple_1", &[carrier.clone()], bv32())
        .expect("adopt selector 1");
    let _tester = solver
        .try_declare_fun("is-u32_u32_Tuple", &[carrier.clone()], Sort::Bool)
        .expect("adopt tester");

    let dom = solver
        .try_declare_const("m_dom", Sort::array(bv32(), Sort::Bool))
        .expect("dom");
    let seed = solver
        .try_declare_const("__ground_seed_m", carrier.clone())
        .expect("seed");
    let m = solver
        .try_declare_const("m", Sort::array(bv32(), carrier.clone()))
        .expect("m");
    let l3 = solver
        .try_declare_const("__map_len_insert_3", Sort::Int)
        .expect("l3");
    let l4 = solver
        .try_declare_const("__map_len_insert_4", Sort::Int)
        .expect("l4");

    let f = solver.bool_const(false);
    let const_false = solver.try_const_array(bv32(), f).expect("const array");
    let dom_eq = solver.try_eq(dom, const_false).expect("dom eq");
    solver.try_assert_named(dom_eq, "dn0").expect("assert");
    let zero32 = solver.try_bv_const(0, 32).expect("bv 0");
    let read0 = solver.try_select(m, zero32).expect("select m 0");
    let seed_eq = solver.try_eq(read0, seed).expect("seed eq");
    solver.try_assert_named(seed_eq, "dn1").expect("assert");
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let l3_lo = solver.try_le(zero, l3).expect("l3 lo");
    solver.try_assert_named(l3_lo, "dn2").expect("assert");
    let l3_hi = solver.try_le(l3, one).expect("l3 hi");
    solver.try_assert_named(l3_hi, "dn3").expect("assert");

    if shape.prior_obligation {
        // First obligation: a trivially true claim, so its negation is `false`.
        solver.try_push().expect("push 1");
        let negated_trivial = solver.bool_const(false);
        solver
            .try_assert_named(negated_trivial, "negated_target_0")
            .expect("assert");
        let first = solver.check_sat_with_details();
        assert!(
            first.result.is_unsat(),
            "first obligation: {:?}",
            first.result
        );
        solver.try_pop().expect("pop 1");
        // The proven claim is assumed as a fact.
        let t = solver.bool_const(true);
        solver.try_assert_named(t, "dn4").expect("assert");
    }
    let l4_lo = solver.try_le(zero, l4).expect("l4 lo");
    solver.try_assert_named(l4_lo, "dn5").expect("assert");
    let l4_hi = solver.try_le(l4, one).expect("l4 hi");
    solver.try_assert_named(l4_hi, "dn6").expect("assert");

    // The obligation: `m.get(1).1 == 999` where the tuple is `(7, 8)`.
    solver.try_push().expect("push 2");
    let seven = solver.try_bv_const(7, 32).expect("bv 7");
    let eight = solver.try_bv_const(8, 32).expect("bv 8");
    let tuple = solver.try_apply(&ctor, &[seven, eight]).expect("ctor app");
    let field1 = solver.try_apply(&sel1, &[tuple]).expect("selector app");
    let nine99 = solver.try_bv_const(999, 32).expect("bv 999");
    let claim = solver.try_eq(field1, nine99).expect("claim");
    let negated = solver.try_not(claim).expect("negated claim");
    solver
        .try_assert_named(negated, "negated_target_1")
        .expect("assert");
    let second = solver.check_sat_with_details();
    solver.try_pop().expect("pop 2");
    second
}

/// The verdict this construction currently gets. `sat` is the intended
/// verdict (z3 agrees); the fail-closed `unknown` is the pinned gap. `unsat`
/// would be a soundness bug and is never accepted.
fn assert_known_gap_or_fixed(label: &str, details: &ay_dpll::api::SolveDetails) {
    assert!(
        !details.result.is_unsat(),
        "{label}: a genuinely satisfiable false claim must never be refuted: {:?}",
        details.result
    );
    if details.result.is_sat() {
        return;
    }
    let detail = details
        .unknown_diagnostic
        .as_ref()
        .and_then(|d| d.detail.clone())
        .unwrap_or_default();
    assert!(
        detail.contains("datatype sort requires a constructor-bearing value"),
        "{label}: the pinned gap changed shape (re-key this sentinel): {:?} / {:?}",
        details.result,
        details.unknown_diagnostic
    );
}

#[test]
fn deductive_checks_map_tuple_false_claim_full_shape_sentinel() {
    let details = run(Shape {
        deductive_checks_settings: true,
        prior_obligation: true,
    });
    assert_known_gap_or_fixed("full deductive-checks shape", &details);
}

#[test]
fn deductive_checks_map_tuple_false_claim_bare_api_shape_sentinel() {
    let details = run(Shape {
        deductive_checks_settings: false,
        prior_obligation: false,
    });
    assert_known_gap_or_fixed("bare API shape", &details);
}
