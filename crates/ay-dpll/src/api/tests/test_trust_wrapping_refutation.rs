// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native-API certification parity for the deductive-checks wrapping-refutation lane.
//!
//! The VerifierConsumer compiler's in-process refutation lane asserts the wrapping
//! roundtrip obligation THROUGH THE NATIVE API — no SMT-LIB text, no parse —
//! so `assertions_parsed()` carries no authored surface. The same query
//! certifies via `ay solve` (the parser populates the surface zip); a native
//! decline that downgrades the UNSAT to "rejected by mandatory strict
//! certification" is exactly the CLI/embedded asymmetry these tests pin.

use num_bigint::BigInt;

use crate::api::{Logic, Solver, Sort, Term};

/// `(ite (< 2147483647 (+ v adj)) (= out (+ v wrap_hi)) (ite (< (+ v adj)
/// (- 2147483648)) (= out (+ v wrap_lo)) (= out (+ v adj))))` — one signed
/// i32 wrapping step, exactly as the captured production query spells it.
fn signed_wrapping_step(
    solver: &mut Solver,
    out: Term,
    v: Term,
    adj: i64,
    wrap_hi: i64,
    wrap_lo: i64,
) -> Term {
    let adj = solver.int_const(adj);
    let stepped = solver.add(v, adj);
    let int_max = solver.int_const(2_147_483_647);
    let int_min = solver.int_const(-2_147_483_648);
    let over = solver.lt(int_max, stepped);
    let under = solver.lt(stepped, int_min);
    let wrap_hi = solver.int_const(wrap_hi);
    let wrapped_hi = solver.add(v, wrap_hi);
    let eq_hi = solver.eq(out, wrapped_hi);
    let wrap_lo = solver.int_const(wrap_lo);
    let wrapped_lo = solver.add(v, wrap_lo);
    let eq_lo = solver.eq(out, wrapped_lo);
    let eq_plain = solver.eq(out, stepped);
    let inner = solver.ite(under, eq_lo, eq_plain);
    solver.ite(over, eq_hi, inner)
}

/// `(and (<= lo v) (<= v hi))`, pushed as the two captured conjuncts.
fn push_signed_i32_bounds(solver: &mut Solver, conjuncts: &mut Vec<Term>, v: Term) {
    let lo = solver.int_const(-2_147_483_648);
    conjuncts.push(solver.le(lo, v));
    let hi = solver.int_const(2_147_483_647);
    conjuncts.push(solver.le(v, hi));
}

/// The captured production obligation (query-86706-00000): the i32
/// `x.wrapping_add(1).wrapping_sub(1) == x` roundtrip as ONE top-level
/// conjunction — bounds, two nested formula-level wrapping ITEs, and the
/// refuted identity — built natively, term by term.
fn assert_wrapping_roundtrip_obligation(solver: &mut Solver) {
    let r = solver.declare_const("__trust_u__3", Sort::Int);
    let s = solver.declare_const("__trust_u__4", Sort::Int);
    let x = solver.declare_const("__trust_u_x", Sort::Int);

    let mut conjuncts = Vec::new();
    push_signed_i32_bounds(solver, &mut conjuncts, x);
    conjuncts.push(signed_wrapping_step(
        solver,
        r,
        s,
        -1,
        -4_294_967_297,
        4_294_967_295,
    ));
    push_signed_i32_bounds(solver, &mut conjuncts, s);
    conjuncts.push(signed_wrapping_step(
        solver,
        s,
        x,
        1,
        -4_294_967_295,
        4_294_967_297,
    ));
    let identity = solver.eq(r, x);
    conjuncts.push(solver.not(identity));

    let obligation = solver.and_many(&conjuncts);
    solver
        .try_assert_named(obligation, "dn0")
        .expect("obligation asserts");
}

/// Regression pin for the embedded/native certification asymmetry
/// (#wrapping-refutation-t5): the captured wrapping-roundtrip UNSAT must
/// publish a strictly certified UNSAT through the native API, exactly as it
/// does through `ay solve`. Before the fix, `rebuild_arith_ite_case_split_farkas`
/// required a parsed-surface zip that native consumers cannot supply, the
/// proof kept its `trust` closer, and mandatory strict certification
/// downgraded the verdict.
#[test]
fn test_trust_native_wrapping_roundtrip_publishes_certified_unsat() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    // Mirror the VerifierConsumer in-process backend exactly: proof production ON (its
    // soundness rule degrades any UNSAT without a strict-checked proof).
    solver.set_produce_proofs(true);
    solver.set_produce_unsat_cores(true);
    assert_wrapping_roundtrip_obligation(&mut solver);

    let details = solver.check_sat_with_details();
    assert!(
        details.result.is_unsat(),
        "native wrapping-roundtrip obligation must publish UNSAT, got {:?} \
         (unknown_reason: {:?}, executor_error: {:?})",
        details.result.result(),
        details.unknown_reason,
        details.executor_error,
    );
    assert!(
        details.result.was_unsat_strictly_verified(),
        "native UNSAT must be strictly certified, not a trust-backed downgrade"
    );
    assert!(details.verification.unsat_proof_available);
    assert_eq!(details.verification.unsat_proof_checker_failures, 0);

    let proof = solver
        .executor
        .last_proof()
        .expect("UNSAT publishes a proof");
    assert!(
        ay_proof::terminal_trust_report(proof).is_trust_free(),
        "the empty-clause derivation must not depend on trust"
    );
    let quality = ay_proof::check_proof_strict(proof, solver.executor.terms())
        .expect("native wrapping-refutation UNSAT has a strict proof");
    assert_eq!(
        quality.trust_count, 0,
        "proof must be trust-free: {quality}"
    );
}

/// The unsat core must still attribute the single named obligation — the
/// certification fix must not disturb native named-core reporting.
#[test]
fn test_trust_native_wrapping_roundtrip_core_names_obligation() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    solver.set_produce_unsat_cores(true);
    assert_wrapping_roundtrip_obligation(&mut solver);

    assert!(solver.check_sat().is_unsat());
    let core = solver.try_get_unsat_core().expect("core available");
    assert_eq!(core, vec!["dn0".to_string()]);
}

/// Sanity floor for the native encoding itself: dropping the refuted identity
/// leaves a satisfiable wrapping model, so the UNSAT above is genuinely about
/// the roundtrip identity and not an encoding artifact.
#[test]
fn test_trust_native_wrapping_step_without_identity_is_sat() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let s = solver.declare_const("__trust_u__4", Sort::Int);
    let x = solver.declare_const("__trust_u_x", Sort::Int);
    let mut conjuncts = Vec::new();
    push_signed_i32_bounds(&mut solver, &mut conjuncts, x);
    push_signed_i32_bounds(&mut solver, &mut conjuncts, s);
    conjuncts.push(signed_wrapping_step(
        &mut solver,
        s,
        x,
        1,
        -4_294_967_295,
        4_294_967_297,
    ));
    let step = solver.and_many(&conjuncts);
    solver.assert_term(step);

    let details = solver.check_sat_with_details();
    assert!(details.result.is_sat(), "wrapping step alone must be SAT");
    let model = solver.model_map().expect("SAT produces a model");
    let x_val = model.get("__trust_u_x").expect("x in model");
    let s_val = model.get("__trust_u__4").expect("s in model");
    let (x_int, s_int) = (
        x_val.as_int().expect("Int x").clone(),
        s_val.as_int().expect("Int s").clone(),
    );
    let wrapped = BigInt::from(i64::from(
        i32::try_from(x_int).expect("i32 x").wrapping_add(1),
    ));
    assert_eq!(s_int, wrapped, "model must satisfy the wrapping step");
}
