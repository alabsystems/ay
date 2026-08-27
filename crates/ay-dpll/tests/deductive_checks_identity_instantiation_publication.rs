// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! PUBLICATION pin for the capture guard: a quantifier whose binder is the
//! AMBIENT symbol the instance is taken at.
//!
//! REGRESSION PINNED: `96cb6b968` ("fix(ematching): the capture guard refused
//! on spelling, not on scope"), which repaired `52b3d386e`
//! ("fix(ematching): keep nested trigger proofs capture-safe").
//!
//! `52b3d386e` added a pre-pass that refuses any substitution whose
//! REPLACEMENT term mentions a name that is also a binder of the quantifier
//! being instantiated. Applied unconditionally it also refuses the DEGENERATE
//! case — the identity substitution `x := x` over a quantifier-free body,
//! where the instance carries no binder at all and nothing can be captured.
//! `subst_vars_exact_qf` returns `None`,
//! `ProofTracker::add_forall_instantiated_assertion` declines the step, and on
//! a consumer that requests no strict proof presentation the whole solve
//! fail-closes: a genuinely refuted obligation stops being reported as
//! refuted.
//!
//! WHY THIS FILE EXISTS ALONGSIDE `96cb6b968`'s OWN TESTS. That commit pinned
//! the producer (`ematching::tests`) and the checker
//! (`ay-proof` `quantifier::tests`) at the SUBSTITUTION layer — neither runs a
//! solve, so neither observes that the whole verdict is lost. The defect is a
//! PUBLICATION failure, and it is only visible end to end.
//!
//! WHY NOTHING ELSE IN THE SUITE SAW IT. The shape needs the binder Term and a
//! top-level ground Term to be the SAME hash-consed node. SMT-LIB text cannot
//! express that — a `(declare-const x …)` shadowed by `(forall ((x …)) …)`
//! parses to two identities — so the whole `.smt2` corpus is blind to it. It
//! arises only on the NATIVE `Solver` surface.
//!
//! SCOPE — WHAT THIS FILE DOES *NOT* CLAIM. It does not claim the ambient
//! binder is a shape deductive-checks emits. It is not: every binder in deductive-checks's
//! encoder comes from `Solver::fresh_var`, and `try_fresh_var` mints
//! `<prefix>_<id>` (`ay-dpll` `api/terms/variables.rs`), so a hash-cons
//! identity with a top-level `declare_const` is impossible by construction.
//! deductive-checks's real emission is this file's FRESH-BINDER TWIN. What is pinned
//! here is `96cb6b968`'s effect at the PUBLICATION layer on the shape ay's own
//! native API admits — a guard that refused on spelling rather than on scope
//! could only be caught end to end, and this is the cheapest end-to-end
//! statement of it (0.05 s at HEAD). The twins are what tie it to deductive-checks's
//! posture; the ambient tests are what make the guard's overreach observable.
//!
//! Each test carries its FRESH-BINDER TWIN. The twin is byte-identical except
//! that the binder is a fresh variable, and it was already `unsat` at the
//! broken revision — so a failure here localises to the identity substitution
//! and cannot be read as "quantifiers got worse in general".
//!
//! MEASURED (dev profile, `--test-threads=1`):
//!
//! | revision                    | ambient binder | fresh-binder twin |
//! |-----------------------------|----------------|-------------------|
//! | `229a99971` (96cb6b968^)    | Unknown        | Unsat             |
//! | `96cb6b968` (the fix)       | Unsat          | Unsat             |
//! | `284248ce1` (HEAD)          | Unsat          | Unsat             |
//!
//! Each row is 3/3 runs. Note that the two ambient-binder pins do NOT move
//! together, and the file deliberately does not claim they do:
//! `ambient_symbol_as_binder_still_publishes_unsat` is green at `52b3d386e`
//! itself and only turns red later in that window, while
//! `ambient_self_as_trait_axiom_binder_still_publishes_unsat` is red at
//! `52b3d386e` AND at its parent `0402e4109` — there under the older checker
//! message "argument is not a bounded ground term for the source binders".
//! So `96cb6b968`'s narrowing closed a restriction that predates the guard as
//! well as the guard's own overreach. What is pinned here, and measured, is
//! the `96cb6b968^` -> `96cb6b968` transition.
//!
//! `ambient_index_as_array_frame_binder_still_publishes_unsat` is NOT a
//! discriminator: it is green at every revision measured, because the array
//! theory closes that obligation before the instantiation lane is reached. It
//! is kept as breadth — it exercises the `select`-triggered `∀` over a
//! BV-indexed carrier through the same publication gate — and NOT as evidence
//! for `96cb6b968`. Its FRESH-binder partner
//! (`fresh_index_array_frame_twin_publishes_unsat`) is the one that mirrors
//! deductive-checks's actual `assert_store_preservation` emission
//! (`deductive-checks-core` `encoder/array_axioms.rs`, which binds a `fresh_var`).

#![allow(clippy::panic)]

use ay_dpll::api::{Logic, Solver, Sort, VerifiedSolveResult};

/// deductive-checks's consumer posture, verbatim: `Logic::All`, unsat cores on, every
/// assertion `:named`, no `produce-proofs` and no self-check. That posture is
/// exactly the one in which the refusal escalates from a declined proof step
/// to a lost verdict.
fn deductive_checks_posture() -> Solver {
    let mut solver = Solver::new(Logic::All);
    solver.set_produce_unsat_cores(true);
    solver
}

/// `∀x. f(x) = 0` together with `f(x) ≠ 0`, where `x` is a top-level constant.
///
/// `ambient_binder` selects whether the quantifier binds THAT constant (the
/// identity-substitution case) or a fresh variable (the control twin).
fn uf_obligation(ambient_binder: bool) -> (Solver, VerifiedSolveResult) {
    let mut solver = deductive_checks_posture();
    let f = solver
        .try_declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = solver.try_declare_const("x", Sort::Int).expect("declare x");
    let binder = if ambient_binder {
        x
    } else {
        solver
            .try_fresh_var("bound", Sort::Int)
            .expect("fresh binder")
    };
    let f_binder = solver.try_apply(&f, &[binder]).expect("apply f");
    let zero = solver.int_const(0);
    let body = solver.eq(f_binder, zero);
    let axiom = solver.try_forall(&[binder], body).expect("forall");
    solver.try_assert_named(axiom, "dn0").expect("assert axiom");

    let f_x = solver.try_apply(&f, &[x]).expect("apply f at x");
    let equality = solver.eq(f_x, zero);
    let goal = solver.not(equality);
    solver.try_assert_named(goal, "dn1").expect("assert goal");

    let result = solver.try_check_sat().expect("check-sat");
    (solver, result)
}

/// A `select`-triggered `∀` over a BV-indexed array carrier — the theory
/// posture of deductive-checks's `assert_store_preservation`, with `ambient_binder`
/// selecting between the ambient index constant (the native-API-only identity
/// case) and a fresh variable. The FRESH arm is the shape deductive-checks emits;
/// `assert_store_preservation` binds `fresh_var("__{label}_idx", …)`.
fn array_frame_obligation(ambient_binder: bool) -> (Solver, VerifiedSolveResult) {
    let mut solver = deductive_checks_posture();
    let idx_sort = Sort::bitvec(64);
    let elem_sort = Sort::bitvec(32);
    let array_sort = Sort::array(idx_sort.clone(), elem_sort.clone());
    let source = solver
        .try_declare_const("__seq_source", array_sort.clone())
        .expect("declare source");
    let shifted = solver
        .try_declare_const("__seq_shifted", array_sort)
        .expect("declare shifted");
    let index = solver
        .try_declare_const("__seq_idx", idx_sort.clone())
        .expect("declare index");
    let binder = if ambient_binder {
        index
    } else {
        solver
            .try_fresh_var("__seq_bound", idx_sort)
            .expect("fresh binder")
    };
    let read_shifted = solver.try_select(shifted, binder).expect("select shifted");
    let read_source = solver.try_select(source, binder).expect("select source");
    let body = solver.eq(read_shifted, read_source);
    let axiom = solver
        .try_forall_with_triggers(&[binder], body, &[&[read_shifted][..]])
        .expect("forall with trigger");
    solver.try_assert_named(axiom, "dn0").expect("assert axiom");

    let at_index_shifted = solver.try_select(shifted, index).expect("select shifted");
    let at_index_source = solver.try_select(source, index).expect("select source");
    let equality = solver.eq(at_index_shifted, at_index_source);
    let goal = solver.not(equality);
    solver.try_assert_named(goal, "dn1").expect("assert goal");

    let result = solver.try_check_sat().expect("check-sat");
    (solver, result)
}

/// The trait-axiom shape `96cb6b968` names in its own doc comment: a `∀` over
/// an uninterpreted sort whose binder is spelled `self`, instantiated at the
/// ambient `self` it shadows.
fn trait_self_obligation(ambient_binder: bool) -> (Solver, VerifiedSolveResult) {
    let mut solver = deductive_checks_posture();
    let carrier = Sort::Uninterpreted("S".to_string());
    let measure = solver
        .try_declare_fun("measure", &[carrier.clone()], Sort::Int)
        .expect("declare measure");
    let receiver = solver
        .try_declare_const("self", carrier.clone())
        .expect("declare self");
    let binder = if ambient_binder {
        receiver
    } else {
        solver
            .try_fresh_var("self_b", carrier)
            .expect("fresh binder")
    };
    let measure_binder = solver.try_apply(&measure, &[binder]).expect("apply");
    let zero = solver.int_const(0);
    let body = solver.try_ge(measure_binder, zero).expect("ge");
    let axiom = solver.try_forall(&[binder], body).expect("forall");
    solver.try_assert_named(axiom, "dn0").expect("assert axiom");

    let measure_self = solver.try_apply(&measure, &[receiver]).expect("apply");
    let goal = solver.try_lt(measure_self, zero).expect("lt");
    solver.try_assert_named(goal, "dn1").expect("assert goal");

    let result = solver.try_check_sat().expect("check-sat");
    (solver, result)
}

/// A refuted obligation must be REPORTED as refuted, not merely computed.
///
/// `accept_for_consumer` is the bit deductive-checks actually reads: a verdict string
/// of `unsat` that the acceptance gate declines still becomes
/// `VerifyResult::Unknown` downstream, so asserting the string alone would be
/// blind to exactly this class of regression.
fn assert_published_unsat(label: &str, result: &VerifiedSolveResult) {
    assert!(
        result.result().is_unsat(),
        "{label}: the obligation is refutable and must be PUBLISHED unsat, not \
         withheld — a withheld refutation is a lost verifier obligation. got {result:?}"
    );
    result.accept_for_consumer().unwrap_or_else(|e| {
        panic!("{label}: consumer acceptance refused the published unsat: {e}")
    });
}

/// THE PIN. `∀x. f(x) = 0` binding the ambient `x`, refuted at that same `x`.
///
/// At `229a99971` this answers `Unknown`; the identity substitution `x := x`
/// is refused on spelling even though the body binds nothing.
#[test]
fn ambient_symbol_as_binder_still_publishes_unsat() {
    let (_solver, result) = uf_obligation(true);
    assert_published_unsat("ambient binder, UF body", &result);
}

/// CONTROL TWIN — already green at `229a99971`. Identical but for a fresh
/// binder, so a red pin above localises to the identity substitution.
#[test]
fn fresh_binder_twin_publishes_unsat() {
    let (_solver, result) = uf_obligation(false);
    assert_published_unsat("fresh binder, UF body", &result);
}

/// BREADTH, not a discriminator: the ambient-binder arm of the
/// `select`-triggered array frame. Green at `229a99971` too — the array theory
/// closes it before the instantiation lane runs. See the module doc.
#[test]
fn ambient_index_as_array_frame_binder_still_publishes_unsat() {
    let (_solver, result) = array_frame_obligation(true);
    assert_published_unsat("ambient binder, select-triggered array frame", &result);
}

/// CONTROL TWIN for the array frame.
#[test]
fn fresh_index_array_frame_twin_publishes_unsat() {
    let (_solver, result) = array_frame_obligation(false);
    assert_published_unsat("fresh binder, select-triggered array frame", &result);
}

/// THE PIN, on the trait-axiom shape the fix's own doc comment names.
#[test]
fn ambient_self_as_trait_axiom_binder_still_publishes_unsat() {
    let (_solver, result) = trait_self_obligation(true);
    assert_published_unsat(
        "ambient binder, trait axiom over an uninterpreted sort",
        &result,
    );
}

/// CONTROL TWIN for the trait axiom.
#[test]
fn fresh_self_trait_axiom_twin_publishes_unsat() {
    let (_solver, result) = trait_self_obligation(false);
    assert_published_unsat(
        "fresh binder, trait axiom over an uninterpreted sort",
        &result,
    );
}

/// SOUNDNESS DIRECTION. Narrowing the capture guard must not make a
/// SATISFIABLE obligation refutable: the same ambient-binder axiom with a goal
/// it does not contradict must NOT come back unsat.
#[test]
fn ambient_binder_axiom_does_not_refute_a_consistent_goal() {
    let mut solver = deductive_checks_posture();
    let f = solver
        .try_declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = solver.try_declare_const("x", Sort::Int).expect("declare x");
    let f_x = solver.try_apply(&f, &[x]).expect("apply f");
    let zero = solver.int_const(0);
    let body = solver.eq(f_x, zero);
    let axiom = solver.try_forall(&[x], body).expect("forall");
    solver.try_assert_named(axiom, "dn0").expect("assert axiom");
    let y = solver.try_declare_const("y", Sort::Int).expect("declare y");
    let consistent = solver.eq(y, zero);
    solver
        .try_assert_named(consistent, "dn1")
        .expect("assert goal");
    let result = solver.try_check_sat().expect("check-sat");
    assert!(
        !result.result().is_unsat(),
        "`∀x. f(x) = 0` with `y = 0` is satisfiable; refuting it would mean the \
         narrowed guard admitted an unsound instance. got {result:?}"
    );
}

/// The nested-binder capture the guard EXISTS for must still be refused, and
/// refused fail-closed: `∀x. (p x) ∧ (∀x. q x)` re-binds the source spelling,
/// so a witness spelled `x` is captured at the second conjunct. This must not
/// answer `unsat` on the strength of a captured instance.
#[test]
fn rebound_spelling_under_a_nested_binder_is_not_refuted_by_capture() {
    let mut solver = deductive_checks_posture();
    let p = solver
        .try_declare_fun("p", &[Sort::Int], Sort::Bool)
        .expect("declare p");
    let q = solver
        .try_declare_fun("q", &[Sort::Int], Sort::Bool)
        .expect("declare q");
    let x = solver.try_declare_const("x", Sort::Int).expect("declare x");
    let p_x = solver.try_apply(&p, &[x]).expect("apply p");
    let q_x = solver.try_apply(&q, &[x]).expect("apply q");
    let inner = solver.try_forall(&[x], q_x).expect("inner forall");
    let body = solver.and(p_x, inner);
    let axiom = solver.try_forall(&[x], body).expect("outer forall");
    solver.try_assert_named(axiom, "dn0").expect("assert axiom");
    // `∀x. (p x ∧ ∀x. q x)` entails `q x` for the ambient x, so asserting
    // `¬ q x` is genuinely UNSAT; what must NOT happen is an `unsat` that the
    // acceptance gate cannot stand behind.
    let not_q_x = solver.not(q_x);
    solver
        .try_assert_named(not_q_x, "dn1")
        .expect("assert goal");
    let result = solver.try_check_sat().expect("check-sat");
    if result.result().is_unsat() {
        result.accept_for_consumer().unwrap_or_else(|e| {
            panic!("a published unsat under a re-binding body must be consumer-acceptable: {e}")
        });
    }
}
