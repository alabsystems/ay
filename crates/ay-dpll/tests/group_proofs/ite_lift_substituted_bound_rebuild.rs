// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Producer-side tests for the SUBSTITUTED-BOUND ite-lift rebuild
//! (`plan_ite_lift_over_substituted_bound` in `proof_trust_surgery.rs`).
//!
//! THE DEFECT. deductive-checks lowers `int::div_euclid`/`rem_euclid` to an authored
//! Euclidean decomposition `a = 2q + r`, `0 <= r < 2` plus a ceiling-division
//! postcondition over a TERM-level `ite`. Preprocessing first substitutes
//! `a := (+ (* q 2) r)` and only then lifts the term-ite to the formula
//! level, so the proof's `assume` leaf is
//! `(ite (= r 0) (< (* q 2) (+ (* q 2) r)) (< (+ (* q 2) 2) (+ (* q 2) r)))`
//! — a term no problem assertion equals. The demotion pass therefore exported
//! it as a premiseless `:rule trust` step, `check_proof_strict` rejected the
//! whole refutation ("step tN uses unverified trust rule"), and the mandatory
//! UNSAT certification downgraded a CORRECT `unsat` to `unknown`.
//!
//! The two pre-existing ite-lift variants cannot recognise it: both require
//! the lifted branches to equal `P[s/u]` / `P[s/v]` by exact `TermId`, and
//! `P[s/u]` here still mentions `a`. The third variant admits the second
//! authored assertion as a premise of the transfer lemmas.
//!
//! WHAT IS ACTUALLY ASSERTED HERE. Every proof below is checked by the
//! UNCHANGED `ay_proof::check_proof_strict` — the emitter's own output, not a
//! shape assertion — and is required to carry ZERO trust and ZERO hole steps.
//! The transfer lemmas export as `la_generic` with explicit coefficients that
//! the strict checker recomputes semantically, so nothing is accepted on
//! annotation presence alone.

use ay_dpll::Executor;
use ay_frontend::parse;
use ay_proof::{check_proof_strict, ProofQuality};
use ntest::timeout;

/// Solve an UNSAT script with proofs enabled; return the executor and the
/// rendered Alethe text.
fn solve_unsat(script: &str) -> (Executor, String) {
    let commands = parse(script).expect("parse SMT-LIB script");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute SMT-LIB script");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "expected UNSAT, got {outputs:?}"
    );
    let alethe = outputs.last().cloned().unwrap_or_default();
    (exec, alethe)
}

/// Run the emitter's OWN proof object through the real strict checker.
fn strict_quality(exec: &Executor) -> ProofQuality {
    let proof = exec
        .last_proof()
        .expect("last proof after UNSAT (a rejected certification leaves none)");
    check_proof_strict(proof, exec.terms())
        .expect("strict checker rejected the rebuilt proof (trust/hole or invalid step)")
}

fn assert_trust_free(exec: &Executor, alethe: &str) {
    let quality = strict_quality(exec);
    assert_eq!(quality.trust_count, 0, "no trust steps: {quality}");
    assert_eq!(quality.hole_count, 0, "no hole steps: {quality}");
    assert!(
        !alethe.contains(":rule trust") && !alethe.contains(":rule hole"),
        "printed Alethe must be trust-free:\n{alethe}"
    );
}

/// THE REPRODUCER, reduced from deductive-checks's `ceil_div_by2_rounds_up`
/// (`crates/deductive-checks-core/tests/fixtures/ay_refutation_step_realbody.rs`).
/// `a = 2q + r`, `0 <= r < 2`, and the negated postcondition
/// `ceil_div(a,2) * 2 < a` over a term-level `ite`.
///
/// Before the substituted-bound variant this published `unknown`
/// (self-check-rejected) with "step t1 uses unverified trust rule".
#[test]
#[timeout(30_000)]
fn test_euclidean_ceil_div_ite_lift_over_substituted_bound_rebuilds_strict() {
    let script = r#"
        (set-option :produce-proofs true)
        (set-logic ALL)
        (declare-const a Int)
        (declare-const q Int)
        (declare-const r Int)
        (assert (= a (+ (* q 2) r)))
        (assert (<= 0 r))
        (assert (< r 2))
        (assert (< (* (ite (= 0 r) q (+ q 1)) 2) a))
        (check-sat)
        (get-proof)
    "#;
    let (exec, alethe) = solve_unsat(script);
    assert_trust_free(&exec, &alethe);

    // The derivation must be the real ite-lift bridge, not an unrelated
    // route that happens to be trust-free: `ite_intro` on the authored
    // assertion, `ite1`/`ite2` for the term-ite's defining equalities, and
    // the certified `la_generic` transfer lemmas.
    for rule in [
        ":rule ite_intro",
        ":rule ite1",
        ":rule ite2",
        ":rule la_generic",
    ] {
        assert!(
            alethe.contains(rule),
            "expected {rule} in the rebuilt derivation:\n{alethe}"
        );
    }
    // The transfer lemma needs a NON-UNIT coefficient on the ite-defining
    // equality (the ite term occurs as `(* s 2)`). An all-ones annotation
    // cannot certify it, which is why the coefficients are searched and
    // verified rather than hardcoded.
    assert!(
        alethe.contains(":rule la_generic :args (2 1 -1 1)"),
        "expected the verified non-unit transfer coefficients:\n{alethe}"
    );
    // Every assume must be one of the four authored assertions.
    for line in alethe.lines().filter(|l| l.contains("(assume ")) {
        assert!(
            line.contains("(< r 2)")
                || line.contains("(<= 0 r)")
                || line.contains("(= a (+ (* q 2) r))")
                || line.contains("(< (* (ite (= 0 r) q (+ q 1)) 2) a)"),
            "assume outside the authored problem obligation: {line}"
        );
    }
}

/// The FULL deductive-checks verification condition, verbatim from the dumped query
/// (`__euclid_q_N`/`__euclid_r_N` auxiliaries, four Euclidean decompositions
/// of the same `a`). Exercises the variant when many candidate `(P, E)` pairs
/// are in scope, so the semantic search — not a lucky single candidate — has
/// to pick the right one.
#[test]
#[timeout(30_000)]
fn test_deductive_checks_ceil_div_by2_full_vc_rebuilds_strict() {
    let script = r#"
        (set-option :produce-proofs true)
        (set-logic ALL)
        (declare-const result Int)
        (declare-const a Int)
        (declare-const __euclid_q_2 Int)
        (declare-const __euclid_r_3 Int)
        (declare-const __euclid_q_8 Int)
        (declare-const __euclid_r_9 Int)
        (assert (= a (+ (* __euclid_q_2 2) __euclid_r_3)))
        (assert (<= 0 __euclid_r_3))
        (assert (< __euclid_r_3 2))
        (assert (ite (= __euclid_r_3 0)
                     (= result __euclid_q_2)
                     (= result (+ __euclid_q_2 1))))
        (assert (= a (+ (* __euclid_q_8 2) __euclid_r_9)))
        (assert (<= 0 __euclid_r_9))
        (assert (< __euclid_r_9 2))
        (assert (< (* (ite (= 0 __euclid_r_9) __euclid_q_8 (+ __euclid_q_8 1)) 2) a))
        (check-sat)
        (get-proof)
    "#;
    let (exec, alethe) = solve_unsat(script);
    assert_trust_free(&exec, &alethe);
}

/// NON-VACUITY / DIRECTION CONTROL. The same shape with the round-up dropped
/// (`floor(a/2) * 2 >= a`) is NOT valid — for odd `a` it is false — so the
/// negation is SATISFIABLE. The rebuild must not manufacture a refutation.
/// This is deductive-checks's own `floor_div_by2_wrong` control.
#[test]
#[timeout(30_000)]
fn test_floor_division_undershoot_stays_satisfiable() {
    let script = r#"
        (set-option :produce-proofs true)
        (set-logic ALL)
        (declare-const a Int)
        (declare-const q Int)
        (declare-const r Int)
        (assert (= a (+ (* q 2) r)))
        (assert (<= 0 r))
        (assert (< r 2))
        (assert (< (* q 2) a))
        (check-sat)
    "#;
    let commands = parse(script).expect("parse SMT-LIB script");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute SMT-LIB script");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("sat"),
        "floor division undershoots for odd `a`; the negation must be SAT, got {outputs:?}"
    );
}

/// SOUNDNESS CONTROL for the semantic search. The same syntactic shape with a
/// decomposition that does NOT support the branch bound (`a = 2q + r` replaced
/// by an unrelated `a = 2q + r + 5`) is genuinely satisfiable, so no transfer
/// lemma can be certified and no refutation may be published. Guards against
/// the search accepting a merely similar `(P, E)` pair.
#[test]
#[timeout(30_000)]
fn test_unrelated_decomposition_is_not_refuted() {
    let script = r#"
        (set-option :produce-proofs true)
        (set-logic ALL)
        (declare-const a Int)
        (declare-const q Int)
        (declare-const r Int)
        (assert (= a (+ (* q 2) r 5)))
        (assert (<= 0 r))
        (assert (< r 2))
        (assert (< (* (ite (= 0 r) q (+ q 1)) 2) a))
        (check-sat)
    "#;
    let commands = parse(script).expect("parse SMT-LIB script");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute SMT-LIB script");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("sat"),
        "with a shifted decomposition the query is satisfiable, got {outputs:?}"
    );
}
