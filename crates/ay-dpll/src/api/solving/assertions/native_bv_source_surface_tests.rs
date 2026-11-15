// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual native Solver construction; separate genuine-source preservation controls.

use super::*;
use crate::api::{Logic, Sort as ApiSort};
use ay_frontend::NativeAssertionSurfaces;
use std::time::Duration;

fn native_problem() -> (Solver, Vec<TermId>) {
    let mut solver = Solver::new(Logic::QfBv);
    solver.set_timeout(Some(Duration::from_millis(10_000)));
    let x = solver.declare_const("native_surface_x", ApiSort::bitvec(4));
    let zero = solver.bv_const(0, 4);
    let one = solver.bv_const(1, 4);
    let a = solver.eq(x, zero);
    let b = solver.eq(x, one);
    solver.assert_term(a);
    solver.assert_term(b);
    let originals = solver.executor.context().assertions.clone();
    (solver, originals)
}

#[test]
fn actual_public_native_solver_retains_sentinels_and_classifies_exact_roots() {
    // This positive uses ONLY Rust API operations, no parser/source retention
    // fabrication. It is the route the bare-core proof fixtures did not model.
    let (mut solver, originals) = native_problem();
    let ctx = solver.executor.context();
    assert_eq!(ctx.assertions_parsed().len(), originals.len());
    assert!(ctx.assertions_parsed().iter().all(|surface|
        matches!(surface, ParsedTerm::Symbol(name) if name == NATIVE_API_ASSERTION_PLACEHOLDER)));
    assert_eq!(
        ctx.native_assertion_surfaces_for(&originals, 64, &mut |_| true),
        Some(NativeAssertionSurfaces::Native)
    );
    let result = solver.check_sat();
    assert!(
        result.is_unsat() && result.has_unsat_emission_witness(),
        "{result:?}"
    );
    assert!(result.was_unsat_strictly_verified(), "{result:?}");
    assert!(!result.was_unsat_corroborated(), "{result:?}");
    assert!(result
        .accept_for_consumer()
        .expect("strict public native UNSAT")
        .is_unsat());
}

#[test]
fn native_surface_routing_rejects_wrong_roots_order_and_capacity() {
    let (solver, originals) = native_problem();
    let ctx = solver.executor.context();
    let mut reversed = originals.clone();
    reversed.reverse();
    assert_ne!(reversed, originals);
    assert_eq!(
        ctx.native_assertion_surfaces_for(&reversed, 64, &mut |_| true),
        Some(NativeAssertionSurfaces::Unavailable)
    );
    assert_eq!(
        ctx.native_assertion_surfaces_for(&originals[..1], 64, &mut |_| true),
        Some(NativeAssertionSurfaces::Unavailable)
    );
    assert_eq!(
        ctx.native_assertion_surfaces_for(&originals, 1, &mut |_| true),
        Some(NativeAssertionSurfaces::Unavailable)
    );
}

#[test]
fn genuine_and_mixed_retained_source_keep_their_existing_route() {
    // Genuine-source negatives deliberately use the parser; the native case
    // above never does. A real expression mentioning a name is not a sentinel.
    let mut parsed = Solver::new(Logic::QfBv);
    parsed
        .parse_smtlib2(
            "(declare-const parsed_surface_x (_ BitVec 4)) (assert (= parsed_surface_x #x0))",
        )
        .expect("genuine parsed source");
    let ctx = parsed.executor.context();
    assert_eq!(
        ctx.native_assertion_surfaces_for(&ctx.assertions, 64, &mut |_| true),
        Some(NativeAssertionSurfaces::Other)
    );

    let mut mixed = Solver::new(Logic::QfBv);
    let x = mixed.declare_const("mixed_surface_x", ApiSort::bitvec(4));
    let zero = mixed.bv_const(0, 4);
    let eq = mixed.eq(x, zero);
    mixed.assert_term(eq);
    mixed
        .parse_smtlib2("(assert (= mixed_surface_x #x1))")
        .expect("genuine added source");
    let ctx = mixed.executor.context();
    assert_eq!(
        ctx.native_assertion_surfaces_for(&ctx.assertions, 64, &mut |_| true),
        Some(NativeAssertionSurfaces::Other)
    );
}

#[test]
fn genuine_retention_off_source_is_other_and_still_certifies() {
    let mut solver = Solver::new(Logic::QfBv);
    solver.set_timeout(Some(Duration::from_millis(10_000)));
    solver
        .executor
        .context_mut_internal()
        .set_retain_parsed_assertions(false);
    solver.parse_smtlib2("(declare-const unretained_surface_x (_ BitVec 4)) (assert (= unretained_surface_x #x0)) (assert (= unretained_surface_x #x1))")
        .expect("genuine unretained source");
    let ctx = solver.executor.context();
    assert!(ctx.assertions_parsed().is_empty());
    assert_eq!(
        ctx.native_assertion_surfaces_for(&ctx.assertions, 64, &mut |_| true),
        Some(NativeAssertionSurfaces::Other)
    );
    let result = solver.check_sat();
    assert!(
        result.is_unsat() && result.has_unsat_emission_witness(),
        "{result:?}"
    );
}

#[test]
fn sentinel_names_cannot_claim_native_source_ownership() {
    let (mut solver, originals) = native_problem();
    assert!(solver
        .try_declare_const(NATIVE_API_ASSERTION_PLACEHOLDER, ApiSort::Bool)
        .is_err());
    assert!(solver
        .parse_smtlib2("(declare-const |__ay_api_assertion__| Bool)")
        .is_err());
    // Adversarial metadata bypass: even a host-forged live declaration cannot
    // turn its same-spelled surface into native routing permission.
    let ctx = solver.executor.context_mut_internal();
    let collision = ctx
        .terms
        .mk_fresh_named_var("surface_collision", Sort::Bool);
    ctx.register_symbol(
        NATIVE_API_ASSERTION_PLACEHOLDER.to_string(),
        collision,
        Sort::Bool,
    );
    assert_eq!(
        ctx.native_assertion_surfaces_for(&originals, 64, &mut |_| true),
        Some(NativeAssertionSurfaces::Unavailable)
    );
}

#[test]
fn genuine_duplicate_source_beyond_native_cap_still_certifies() {
    for retain in [true, false] {
        let mut solver = Solver::new(Logic::QfBv);
        solver.set_timeout(Some(Duration::from_millis(10_000)));
        solver
            .executor
            .context_mut_internal()
            .set_retain_parsed_assertions(retain);
        let mut script = String::from("(declare-const duplicate_surface_x (_ BitVec 4))");
        for _ in 0..64 {
            script.push_str(" (assert (= duplicate_surface_x #x0))");
        }
        script.push_str(" (assert (= duplicate_surface_x #x1))");
        solver
            .parse_smtlib2(&script)
            .expect("65 genuine assertions, two distinct roots");
        let ctx = solver.executor.context();
        assert_eq!(ctx.assertions.len(), 65);
        assert_eq!(
            ctx.native_assertion_surfaces_for(&ctx.assertions, 64, &mut |_| true),
            Some(NativeAssertionSurfaces::Other)
        );
        let result = solver.check_sat();
        assert!(
            result.is_unsat() && result.has_unsat_emission_witness(),
            "retain={retain}: {result:?}"
        );
        assert!(
            result.was_unsat_strictly_verified(),
            "retain={retain}: {result:?}"
        );
    }
}

#[test]
fn mixed_genuine_row_after_native_cap_is_metered_and_keeps_legacy_route() {
    let mut solver = Solver::new(Logic::QfBv);
    solver.set_timeout(Some(Duration::from_millis(10_000)));
    let x = solver.declare_const("mixed_duplicate_x", ApiSort::bitvec(4));
    let zero = solver.bv_const(0, 4);
    let eq = solver.eq(x, zero);
    for _ in 0..64 {
        solver.assert_term(eq);
    }
    solver
        .parse_smtlib2("(assert (= mixed_duplicate_x #x1))")
        .expect("genuine row 65");
    let ctx = solver.executor.context();
    assert_eq!(ctx.assertions.len(), 65);
    let mut remaining = 65usize; // initial visit +64 native rows, no grant for row65
    assert_eq!(
        ctx.native_assertion_surfaces_for(&ctx.assertions, 64, &mut |work| {
            let Some(next) = remaining.checked_sub(work) else {
                return false;
            };
            remaining = next;
            true
        }),
        None
    );
    assert_eq!(remaining, 0);
    assert_eq!(
        ctx.native_assertion_surfaces_for(&ctx.assertions, 64, &mut |_| true),
        Some(NativeAssertionSurfaces::Other)
    );
    let result = solver.check_sat();
    assert!(
        result.is_unsat() && result.has_unsat_emission_witness(),
        "{result:?}"
    );
    assert!(result.was_unsat_strictly_verified(), "{result:?}");
}

#[test]
fn native_only_65_duplicate_rows_remain_ineligible() {
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("native_capacity_x", ApiSort::bitvec(4));
    let zero = solver.bv_const(0, 4);
    let duplicate = solver.eq(x, zero);
    for _ in 0..65 {
        solver.assert_term(duplicate);
    }
    let ctx = solver.executor.context();
    assert_eq!(ctx.assertions.len(), 65);
    assert_eq!(
        ctx.native_assertion_surfaces_for(&ctx.assertions, 64, &mut |_| true),
        Some(NativeAssertionSurfaces::Unavailable)
    );
}
