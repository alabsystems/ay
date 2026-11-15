// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Finite-domain expansion instances derived by the refuting lane itself,
//! checked by pinned carcara (#fde-forall-provenance).
//!
//! The finite-domain expander replaces an authored guarded universal by the
//! conjunction of its instances over the guard range, each with its closed
//! guard evaluated away. It recorded the instance values but no derivation, so
//! a ground refutation through those instances rested on an underived leaf.
//! `PINNED_INSTANCE` answered `unknown` under `:produce-proofs` (measured on
//! 8e2f8867b): its refutation is a plain resolution over the expanded
//! instance at `#x04`, which no authored cascade member rebuilds (the index
//! reaches the instance only through the pin `k = #x04`, so no authored or
//! closed guard discharges an instance at `k`). The lane now derives each
//! instance from the authored universal (`forall_inst` at the recorded value,
//! `or`, `evaluate` of the closed guard), and the document must be `valid`.
//!
//! Twins: `PINNED_OUTSIDE_SAT` pins `k` to the guard's excluded bound and must
//! never publish `unsat`; `PINNED_DEFINE_FUN` spells the bound through a
//! `define-fun` carcara reads as declared, and `PINNED_ALPHA_RESPELLED` /
//! `PINNED_WRAPPED_ROOT` give the universal a second or a wrapped spelling,
//! so the lane declines each (it stays the `unknown` it was) and none may
//! publish a refused or unverified proof. `DISTINCT_GUARD` pins the honest
//! remainder: a plain guard whose authored-to-internal bridge the printer
//! cannot spell publishes `unsat` with one disclosed `hole`, never a `trust`,
//! a refused export or an `invalid` document. And forty expansions beside a
//! ground conflict that needs none of them must not cost that conflict its
//! `valid` refutation: the lane's solve-wide cap bounds what it adds.

use super::Executor;
use super::{carcara_verdict_without_allowances, CarcaraVerdict};
use super::{exact_carcara_verdict, parse, require_carcara_or_skip};
use super::{solve_or_fail_closed_and_maybe_get_proof, solve_unsat_and_get_proof};
use ntest::timeout;

const PINNED_INSTANCE: &str = r#"
(set-logic ALL)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(declare-const fill (_ BitVec 8))
(declare-const k (_ BitVec 8))
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= fill (f x)))
(assert (= k (_ bv4 8)))
(assert (forall ((i (_ BitVec 8))) (=> (bvult i (_ bv9 8)) (= (select a i) (f x)))))
(assert (distinct (select a k) fill))
(check-sat)
"#;

/// `(bvult #x09 #x09)` is false: the universal says nothing about cell 9.
const PINNED_OUTSIDE_SAT: &str = r#"
(set-logic ALL)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(declare-const fill (_ BitVec 8))
(declare-const k (_ BitVec 8))
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= fill (f x)))
(assert (= k (_ bv9 8)))
(assert (forall ((i (_ BitVec 8))) (=> (bvult i (_ bv9 8)) (= (select a i) (f x)))))
(assert (distinct (select a k) fill))
(check-sat)
"#;

const PINNED_DEFINE_FUN: &str = r#"
(set-logic ALL)
(define-fun lim () (_ BitVec 8) #x09)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(declare-const fill (_ BitVec 8))
(declare-const k (_ BitVec 8))
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= fill (f x)))
(assert (= k (_ bv4 8)))
(assert (forall ((i (_ BitVec 8))) (=> (bvult i lim) (= (select a i) (f x)))))
(assert (distinct (select a k) fill))
(check-sat)
"#;

#[test]
#[timeout(120_000)]
fn pinned_instance_of_a_finite_expansion_publishes_trust_free() {
    let label = "finite_expansion_pinned_instance";
    let proof = solve_unsat_and_get_proof(PINNED_INSTANCE, label);
    for rule in [":rule hole", ":rule trust"] {
        assert!(
            !proof.contains(rule),
            "{label}: the document must carry no `{rule}` step:\n{proof}"
        );
    }
    for rule in ["forall_inst", "evaluate"] {
        assert!(
            proof.contains(&format!(":rule {rule}")),
            "{label}: expected a `{rule}` step:\n{proof}"
        );
    }
    if let Some(carcara) = require_carcara_or_skip() {
        let (valid, diagnostic) = exact_carcara_verdict(&carcara, PINNED_INSTANCE, &proof);
        assert!(
            valid,
            "{label}: pinned carcara must check the document trust-free: {diagnostic}\n{proof}"
        );
    }
}

#[test]
#[timeout(120_000)]
fn satisfiable_twin_never_publishes_unsat() {
    let script = format!("(set-option :produce-proofs true)\n{PINNED_OUTSIDE_SAT}");
    let commands = parse(&script).expect("fixture parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("fixture runs");
    assert_ne!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "cell 9 lies outside the guard; a refutation would be wrong"
    );
}

#[test]
#[timeout(120_000)]
fn define_fun_bound_never_publishes_a_refused_or_invalid_proof() {
    let label = "finite_expansion_define_fun_bound";
    let Some(proof) = solve_or_fail_closed_and_maybe_get_proof(PINNED_DEFINE_FUN, label) else {
        return;
    };
    assert!(
        !proof.contains("UNVERIFIABLE PROOF"),
        "{label}: an unsat whose export is refused must stay unknown:\n{proof}"
    );
    if let Some(carcara) = require_carcara_or_skip() {
        let (valid, diagnostic) = exact_carcara_verdict(&carcara, PINNED_DEFINE_FUN, &proof);
        assert!(
            valid,
            "{label}: a published refutation must be carcara-valid: {diagnostic}\n{proof}"
        );
    }
}

/// One authored universal spelled twice, alpha-renamed: the store interns
/// both to one root, which then has two authored surfaces.
const PINNED_ALPHA_RESPELLED: &str = r#"
(set-logic ALL)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(declare-const fill (_ BitVec 8))
(declare-const k (_ BitVec 8))
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= fill (f x)))
(assert (= k (_ bv4 8)))
(assert (forall ((j (_ BitVec 8))) (=> (bvult j (_ bv9 8)) (= (select a j) (f x)))))
(assert (forall ((i (_ BitVec 8))) (=> (bvult i (_ bv9 8)) (= (select a i) (f x)))))
(assert (distinct (select a k) fill))
(check-sat)
"#;

/// The universal under a Boolean wrapper that elaboration folds away.
const PINNED_WRAPPED_ROOT: &str = r#"
(set-logic ALL)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(declare-const fill (_ BitVec 8))
(declare-const k (_ BitVec 8))
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= fill (f x)))
(assert (= k (_ bv4 8)))
(assert (=> true (forall ((i (_ BitVec 8))) (=> (bvult i (_ bv9 8)) (= (select a i) (f x))))))
(assert (distinct (select a k) fill))
(check-sat)
"#;

/// Unscreened, the respelled root published `unsat` whose export is refused
/// (`proof was not generated`) and the wrapped one a `hole`; both were
/// fail-closed `unknown` before the lane derived anything.
#[test]
#[timeout(120_000)]
fn respelled_or_wrapped_roots_never_publish_a_refused_or_unverified_proof() {
    for (label, problem) in [
        ("finite_expansion_alpha_respelled", PINNED_ALPHA_RESPELLED),
        ("finite_expansion_wrapped_root", PINNED_WRAPPED_ROOT),
    ] {
        let Some(proof) = solve_or_fail_closed_and_maybe_get_proof(problem, label) else {
            continue;
        };
        if let Some(carcara) = require_carcara_or_skip() {
            let (valid, diagnostic) = exact_carcara_verdict(&carcara, problem, &proof);
            assert!(
                valid,
                "{label}: a published refutation must be carcara-valid: {diagnostic}\n{proof}"
            );
        }
    }
}

/// A plain guard the printer cannot bridge: elaboration turns the ternary
/// `distinct` into the disjuncts `(= i #x3)` and `(= i #x7)` of the internal
/// `or`, and no printed rule relates that disjunction to the authored
/// `(=> (distinct i #x3 #x7) (p i))`.
const DISTINCT_GUARD: &str = r#"
(set-logic ALL)
(declare-fun p ((_ BitVec 4)) Bool)
(assert (forall ((i (_ BitVec 4))) (=> (distinct i #x3 #x7) (p i))))
(assert (not (p #x5)))
(check-sat)
"#;

/// The honest outcome of an unbridgeable authored body, pinned so it cannot
/// silently widen. Before the lane derived its instances this answered
/// `unknown` (measured on 938ec0327); the derivation is strict-checked, so
/// `unsat` now publishes, and the printer holes the one `or` step whose
/// authored-to-internal bridge it cannot spell. The document must carry no
/// `trust`, at most that one `hole`, and never be refused or `invalid`; a
/// printer bridge that makes it `valid` later passes too.
#[test]
#[timeout(120_000)]
fn unbridgeable_guard_publishes_at_most_one_disclosed_hole() {
    let label = "finite_expansion_distinct_guard";
    let proof = solve_unsat_and_get_proof(DISTINCT_GUARD, label);
    assert!(
        !proof.contains(":rule trust") && !proof.contains("UNVERIFIABLE PROOF"),
        "{label}: no trust step and no refused export:\n{proof}"
    );
    assert!(
        proof.contains(":rule forall_inst"),
        "{label}: the lane's forall_inst must reach the document:\n{proof}"
    );
    let holes = proof.matches(":rule hole").count();
    assert!(holes <= 1, "{label}: {holes} holes:\n{proof}");
    if let Some(carcara) = require_carcara_or_skip() {
        let verdict = carcara_verdict_without_allowances(&carcara, label, DISTINCT_GUARD, &proof);
        let expected = if holes == 0 {
            CarcaraVerdict::Valid
        } else {
            CarcaraVerdict::Holey
        };
        assert_eq!(verdict, expected, "{label}:\n{proof}");
    }
}

/// Forty guarded universals of 254 instances each, and a ground conflict on
/// `x` that needs none of them.
fn many_expansions_beside_a_ground_conflict() -> String {
    let mut problem = String::from(
        "(set-logic ALL)\n\
         (declare-fun f ((_ BitVec 8)) (_ BitVec 8))\n\
         (declare-const x (_ BitVec 8))\n",
    );
    for array in 0..40 {
        problem.push_str(&format!(
            "(declare-const a{array} (Array (_ BitVec 8) (_ BitVec 8)))\n\
             (assert (forall ((i (_ BitVec 8))) (=> (bvult i #xfe) (= (select a{array} i) (f x)))))\n"
        ));
    }
    problem.push_str("(assert (= x #x01))\n(assert (= x #x02))\n(check-sat)\n");
    problem
}

/// The lane's blast radius stays bounded. Every derived instance stays in the
/// unpruned tracker proof and takes one entry of the printer's 8192-entry
/// authored-surface override table, so deriving all 10160 instances here
/// turned the carcara-`valid` refutation (measured on 938ec0327 with the lane
/// off) into `unknown`: "the provisional UNSAT verdict has no proof". The
/// solve-wide cap keeps it `valid`.
#[test]
#[timeout(120_000)]
fn many_expansions_never_cost_an_unrelated_valid_refutation() {
    let label = "finite_expansion_many_universals_ground_conflict";
    let problem = many_expansions_beside_a_ground_conflict();
    let proof = solve_unsat_and_get_proof(&problem, label);
    if let Some(carcara) = require_carcara_or_skip() {
        let (valid, diagnostic) = exact_carcara_verdict(&carcara, &problem, &proof);
        assert!(
            valid,
            "{label}: the ground refutation must stay carcara-valid: {diagnostic}"
        );
    }
}
