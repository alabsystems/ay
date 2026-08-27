// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! A NATIVE-API declaration is an ordinary projection binding.
//!
//! `api::Solver::declare_const` / `declare_fun` allocate their term in the
//! same operation that records its frontend metadata
//! (`SymbolBindingOrigin::NativeApiDeclaration`), so they carry the same
//! "this is the source program's own free declaration" guarantee a parsed
//! `(declare-fun ...)` does. `check_projection_declaration` used to test the
//! narrower parsed-only origin, so EVERY projection-binding consumer — the
//! constant-interpretation and finite-table SAT certificates among them —
//! declined outright for API-route embedders with
//! `NonOrdinaryBinding { symbol }`.
//!
//! The measured cost was a refutation-completeness hole in deductive-checks: its
//! guarded-broadcast refutation query
//!
//! ```text
//! (declare-const y Int) (declare-fun f1 (Int) Int)
//! (assert (forall ((x Int)) (! (or (not (< 100 y)) (< x (f1 x))) )))  ; trigger {f1(x)}
//! (assert (<= y 100))
//! ```
//!
//! is SAT under `y := 0, f1 := λ_. 0` — the forall is VACUOUS through its
//! first disjunct — but the triggered forall never e-matches (no ground `f1`
//! occurrence), the matching loop self-feeds until the round cap, and with
//! the certificates declined the genuinely SAT counterexample surfaced as
//! `Unknown (quantifier-unhandled)`. deductive-checks's
//! `implies_antecedent_scope` leak probe lost its Counterexample to exactly
//! this (its KNOWN-OPEN note names the reason string).
//!
//! The pins below drive the API route precisely as deductive-checks does
//! (`with_limits`: wall timeout + `:rlimit`), with and without the user
//! trigger.

use ay_dpll::api::{Logic, Solver, Sort, Term};

struct GuardedUf {
    solver: Solver,
}

/// `forall x. (100 < y) => (x < f1(x))` + `y <= 100`, exactly the captured
/// deductive-checks production query (modulo the `:named` wrappers, which do not
/// participate in the decision).
fn guarded_uf(triggered: bool) -> GuardedUf {
    let mut s = Solver::new(Logic::All);
    let _ = s.try_set_option("produce-unsat-cores", "true");
    s.set_timeout(Some(std::time::Duration::from_millis(30_000)));
    let _ = s.try_set_option("rlimit", "1200000");
    let y = s.declare_const("y", Sort::Int);
    let f1 = s.declare_fun("f1", &[Sort::Int], Sort::Int);
    let x = s.fresh_var("x", Sort::Int);
    let fx = s.try_apply(&f1, &[x]).unwrap();
    let c100 = s.int_const(100);
    let guard = s.try_lt(c100, y).unwrap();
    let nguard = s.try_not(guard).unwrap();
    let cons = s.try_lt(x, fx).unwrap();
    let body = s.try_or(nguard, cons).unwrap();
    let q = if triggered {
        let trigger: &[Term] = &[fx];
        s.try_forall_with_triggers(&[x], body, &[trigger]).unwrap()
    } else {
        s.try_forall(&[x], body).unwrap()
    };
    s.try_assert_term(q).unwrap();
    let goal = s.try_le(y, c100).unwrap();
    s.try_assert_term(goal).unwrap();
    GuardedUf { solver: s }
}

/// The regression: a USER-TRIGGERED forall over an API-declared head must
/// still reach the SAT-certificate lanes once E-matching saturates. Before
/// the projection-binding fix this was `Unknown (quantifier-unhandled)`.
#[test]
fn triggered_guarded_uf_forall_over_api_declarations_is_sat() {
    let mut g = guarded_uf(true);
    let d = g.solver.check_sat_with_details();
    assert!(
        d.unknown_reason.is_none(),
        "expected a certified Sat, got unknown: {:?}",
        d.unknown_reason
    );
    assert!(
        d.verification.sat_model_validated,
        "the certificate must publish a VALIDATED witness model"
    );
}

/// Control: the identical untriggered forall was already Sat before the fix
/// (CEGQI handles it); it must stay Sat.
#[test]
fn untriggered_guarded_uf_forall_over_api_declarations_is_sat() {
    let mut g = guarded_uf(false);
    let d = g.solver.check_sat_with_details();
    assert!(
        d.unknown_reason.is_none(),
        "expected Sat, got unknown: {:?}",
        d.unknown_reason
    );
    assert!(d.verification.sat_model_validated);
}
