// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The `EqDiffVar` derivation lane in the RETENTION-OFF configuration (#4751).
//!
//! # Why this file exists — the lane was built, tested and unreachable
//!
//! [`Executor::derive_eq_diffvar_rewritten_assertions`] was wired into
//! `finish_input_syntax_rewrite` only, which
//! [`Executor::apply_input_syntax_rewrites_to_proof`] reaches ONLY when a
//! parsed-assertion prefix was retained. The CLI drops that prefix for
//! `--no-proof`, `--z3-mode` and competition mode (#rss-vs-z3), taking the
//! NARROWED subset [`Executor::run_assumption_authority_passes_without_parsed_syntax`]
//! instead — and that subset did not call this lane.
//!
//! Those two conditions compose into a hole with no residual: `EqDiffVar` runs
//! ONLY when the caller did not ask for a proof (`!is_producing_proofs()`, see
//! `Executor::eq_diffvar_pass_enabled`), which is the same set of runs the CLI
//! drops the parsed prefix for. So every difference variable AY mints from the
//! command line landed in the one authority subset that could not discharge it.
//!
//! MEASURED at the commit that added this file, `ay solve --no-proof -T:10`:
//!
//! * `QF_IDL/mathsat/fischer/FISCHER7-3-ninc.smt2` — 25 of the proof's 146
//!   premiseless `trust` leaves mention `__ay_eqdv`, and the lane logged no
//!   call at all while the provenance store held 45 atom folds and 454
//!   rewrites. With the call added it plans 322 chains and the leaf count falls
//!   to 10.
//! * this file's own fixture — 5 folded leaves under retention OFF against 0
//!   under retention ON, from one solve of the same script.
//!
//! # MUTATION LEDGER — 2 mutations, both RED
//!
//! | # | guard | mutation | result |
//! |---|---|---|---|
//! | 1 | the `derive_eq_diffvar_rewritten_assertions` call in `run_assumption_authority_passes_without_parsed_syntax` | delete it | **RED**, 2 tests: `a_rewritten_assertion_is_derived_with_the_parsed_prefix_dropped`, `the_retention_off_derivation_cites_its_definition` |
//! | 2 | `Executor::eq_diffvar_lane_fits_retention_off_bound` | make it `true` unconditionally | **RED** `a_proof_past_the_retention_off_bound_is_not_offered_to_the_lane` |
//!
//! The retention-ON row of `a_rewritten_assertion_is_derived_with_the_parsed_prefix_dropped`
//! is the CONTROL: it passed before the call was added and must keep passing,
//! so a mutation that breaks the lane outright fails both rows and is
//! distinguishable from one that only breaks the wiring. The two
//! fragment-level tests call the lane DIRECTLY, so they are deliberately blind
//! to mutation 1 — they pin what the lane emits, not where it is called from.

use ay_core::{AletheRule, Proof, ProofStep, TermId, TheoryLemmaKind};
use ay_frontend::parse;

use crate::Executor;

/// The `EqDiffVar` pass's own target shape — a Bool-guarded var-var equality
/// chain whose atoms sit NESTED under `or`, which is the only position the pass
/// folds. UNSAT: `g1` forces `a = x, b = y` and `¬g1` forces `a = y, b = x`, so
/// `a + b = x + y` either way, while the last two assertions demand
/// `x + y ≠ 1 = a + b`.
const GUARDED_UNSAT: &str = r#"
    (set-logic QF_LIA)
    (declare-const g1 Bool)
    (declare-const g2 Bool)
    (declare-const x Int)
    (declare-const y Int)
    (declare-const a Int)
    (declare-const b Int)
    (assert (or (not g1) (= a x)))
    (assert (or (not g1) (= b y)))
    (assert (or g1 (= a y)))
    (assert (or g1 (= b x)))
    (assert (or (not g2) (= (+ x y) 1)))
    (assert (or g2 (= (+ a b) 1)))
    (assert (not (= (+ x y) 1)))
    (check-sat)
"#;

/// Solve with the parsed-assertion prefix retained or DROPPED. Dropping it is
/// exactly what `crates/ay/src/run.rs` does for `--no-proof`, `--z3-mode` and
/// competition mode, i.e. the whole mandatory-certificate regime.
fn solve_with_retention(retain_parsed: bool) -> Executor {
    let commands = parse(GUARDED_UNSAT).expect("parse");
    let mut exec = Executor::new();
    exec.set_retain_parsed_assertions(retain_parsed);
    assert_eq!(
        exec.execute_all(&commands).expect("exec"),
        vec!["unsat"],
        "the fixture must be a complete refutation"
    );
    assert_eq!(
        exec.ctx.assertions_parsed().is_empty(),
        !retain_parsed,
        "the fixture must actually model the configuration under test"
    );
    assert!(
        exec.statistics()
            .get_int("preprocess.eq_diffvar.rewritten_atoms")
            .is_some_and(|n| n > 0),
        "the reduction must actually have run, or this test proves nothing"
    );
    exec
}

fn mentions_diff_var(exec: &Executor, term: TermId) -> bool {
    ay_proof::format_term_alethe(&exec.ctx.terms, term).contains("__ay_eqdv")
}

/// Every premiseless `trust` step whose clause mentions a difference variable.
/// This is the population the lane exists to remove.
fn premiseless_trust_over_diff_vars(exec: &Executor) -> usize {
    exec.last_proof.as_ref().map_or(0, |proof| {
        proof
            .steps
            .iter()
            .filter(|step| {
                let ProofStep::Step {
                    rule: AletheRule::Trust,
                    clause,
                    premises,
                    ..
                } = step
                else {
                    return false;
                };
                premises.is_empty() && clause.iter().any(|&term| mentions_diff_var(exec, term))
            })
            .count()
    })
}

fn steps_with_rule(exec: &Executor, wanted: &AletheRule) -> usize {
    exec.last_proof.as_ref().map_or(0, |proof| {
        proof
            .steps
            .iter()
            .filter(|step| matches!(step, ProofStep::Step { rule, .. } if rule == wanted))
            .count()
    })
}

#[test]
fn a_rewritten_assertion_is_derived_with_the_parsed_prefix_dropped() {
    // The row under test. Before the wiring this was 5.
    assert_eq!(
        premiseless_trust_over_diff_vars(&solve_with_retention(false)),
        0,
        "no assertion the pass rewrote may stay an unverified premiseless \
         `trust` step just because the session dropped its parsed prefix"
    );
    // The CONTROL row, which passed before the wiring too.
    assert_eq!(
        premiseless_trust_over_diff_vars(&solve_with_retention(true)),
        0,
        "the retention-ON path must be unchanged"
    );
}

#[test]
fn the_retention_off_derivation_cites_its_definition() {
    // A test that only asserts an ABSENCE would pass with the lane deleted, so
    // pin the positive side: in the retention-off configuration the derivation
    // must cite the definitional bounds as CHECKED `fresh_def_bound` steps and
    // assemble the atom equivalence from its two implications.
    let exec = solve_with_retention(false);
    assert!(
        steps_with_rule(&exec, &AletheRule::FreshDefBound) > 0,
        "the derivation must cite the definitional bounds it rests on"
    );
    assert!(
        steps_with_rule(&exec, &AletheRule::EquivNeg1) > 0
            && steps_with_rule(&exec, &AletheRule::EquivNeg2) > 0,
        "the atom equivalence must be assembled from its two implications"
    );
    let triangles = exec.last_proof.as_ref().map_or(0, |proof| {
        proof
            .steps
            .iter()
            .filter(|step| {
                matches!(
                    step,
                    ProofStep::TheoryLemma {
                        kind: TheoryLemmaKind::ArithEqTriangle,
                        ..
                    }
                )
            })
            .count()
    });
    assert!(
        triangles > 0,
        "each implication must close through the `la_disequality` triangle"
    );
}

#[test]
fn the_retention_off_unsat_is_still_backed_by_a_certificate() {
    let exec = solve_with_retention(false);
    assert!(
        exec.last_command_unsat_was_strictly_verified()
            || exec.last_command_unsat_was_independently_verified()
            || exec.last_command_unsat_was_exact_semantically_verified(),
        "the `unsat` must stay backed by a real certificate"
    );
}

#[test]
fn the_retention_off_promotion_never_produces_a_rejected_fresh_definition() {
    // A `fresh_def_bound` the registry declined would be a HARD rejection —
    // strictly worse than the rescuable `trust` step the lane replaced — so
    // assert the specific classes never appear, whatever the overall verdict.
    let exec = solve_with_retention(false);
    let proof = exec.last_proof.as_ref().expect("a proof was reconstructed");
    if let Err(error) = exec.check_proof_strict_with_datatypes(proof) {
        let rendered = error.to_string();
        for forbidden in [
            "fresh definition",
            "cong",
            "trans",
            "equiv_neg",
            "la_disequality",
            "arithmetic equality triangle",
        ] {
            assert!(
                !rendered.contains(forbidden),
                "the lane emitted a step the checker rejects ({forbidden}): {rendered}"
            );
        }
    }
}

/// TWO-SIDED pin on the retention-off size bound.
///
/// The bound is what stops this wiring from LOSING correct `unsat` verdicts:
/// unbounded, on the SMT-LIB QF_IDL 900-file sample, 44 files degraded from a
/// trust-family rejection to `ResourceLimit` — which reaches the deferred
/// discharge lane with nothing collected and falls through to a whole-problem
/// re-solve — and 5 crossed `-T:10` and published `unknown` where a correct
/// `unsat` had published before. Both rows are asserted, so a mutation that
/// removes the bound fails the second and a mutation that clamps it to zero
/// fails the first.
#[test]
fn a_proof_past_the_retention_off_bound_is_not_offered_to_the_lane() {
    let mut small = Proof::new();
    let mut large = Proof::new();
    let mut exec = Executor::new();
    let atom = exec.ctx.terms.mk_var("padding", ay_core::Sort::Bool);
    for index in 0..4_096 {
        if index < 4_095 {
            small.add_rule_step(AletheRule::Trust, vec![atom], Vec::new(), Vec::new());
        }
        large.add_rule_step(AletheRule::Trust, vec![atom], Vec::new(), Vec::new());
    }
    assert_eq!(small.steps.len(), 4_095);
    assert_eq!(large.steps.len(), 4_096);
    assert!(
        Executor::eq_diffvar_lane_fits_retention_off_bound(&small),
        "a proof the strict checker can still finish must reach the lane"
    );
    assert!(
        !Executor::eq_diffvar_lane_fits_retention_off_bound(&large),
        "a proof past the measured degradation threshold must NOT be enlarged: \
         `FISCHER4-3-ninc` stays trust-family at 3,911 steps and \
         `FISCHER5-3-ninc` degrades at 5,117"
    );
}

// ===== the isolated fragment: a COMPLETE REFUTATION that STARTS REJECTED =====

/// A complete refutation of `goal` whose only foreign leaf is `goal` itself:
/// `(cl goal)` and `(cl (not goal))` as premiseless `trust` steps, resolved to
/// the empty clause. The closer is a `trust` step and NOT an `assume`, so no
/// `assume` in the finished proof mentions the difference variable and the
/// checker's freshness question is the one under test.
fn leaf_proof(exec: &mut Executor, goal: TermId) -> Proof {
    let negated = exec.ctx.terms.mk_not_raw(goal);
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, vec![goal], Vec::new(), Vec::new());
    proof.add_rule_step(AletheRule::Trust, vec![negated], Vec::new(), Vec::new());
    proof.add_rule_step(
        AletheRule::Resolution,
        Vec::new(),
        vec![ay_core::ProofId(0), ay_core::ProofId(1)],
        Vec::new(),
    );
    proof
}

fn premiseless_unit_trust_leaves(proof: &Proof) -> usize {
    proof
        .steps
        .iter()
        .filter(|step| {
            matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::Trust,
                    clause,
                    premises,
                    args,
                } if premises.is_empty() && args.is_empty() && clause.len() == 1
            )
        })
        .count()
}

/// An executor whose `EqDiffVar` provenance is populated by a real
/// RETENTION-OFF solve, plus one rewritten assertion the pass produced.
fn retention_off_fixture() -> (Executor, TermId) {
    let exec = solve_with_retention(false);
    let rewritten = exec
        .propagated_value_provenance
        .eq_diffvar_rewrites
        .iter()
        .map(|record| record.after)
        .find(|&term| mentions_diff_var(&exec, term))
        .expect("the pass must have rewritten at least one assertion over a difference variable");
    (exec, rewritten)
}

#[test]
fn the_retention_off_lane_derives_a_complete_refutations_only_foreign_leaf() {
    let (mut exec, rewritten) = retention_off_fixture();
    let scope = exec.complete_problem_assertions_for_strict_proof();
    assert!(
        !scope.contains(&rewritten),
        "the rewritten assertion must NOT be authored — otherwise it would be \
         an `assume`, not a `trust` step, and this test proves nothing"
    );

    let mut proof = leaf_proof(&mut exec, rewritten);
    // STARTS REJECTED: two premiseless `trust` leaves, and the strict checker
    // refuses the refutation because of them.
    assert_eq!(premiseless_unit_trust_leaves(&proof), 2);
    let before = exec
        .check_proof_strict_with_datatypes(&proof)
        .expect_err("a refutation resting on `trust` must start REJECTED");
    assert!(
        before.to_string().contains("trust"),
        "the fixture must start rejected FOR the trust step: {before}"
    );

    exec.derive_eq_diffvar_rewritten_assertions(&mut proof, &scope);

    assert_eq!(
        premiseless_unit_trust_leaves(&proof),
        1,
        "only the fixture's own closer may survive; the rewritten assertion \
         must have been DERIVED"
    );
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::FreshDefBound,
                ..
            }
        )),
        "the derivation must cite the definitional bounds"
    );
}

/// PRINTER PIN on the exact wire text the retention-off derivation emits.
///
/// `fresh_def_bound` is certified INTERNALLY by `ay_proof`'s
/// `FreshDefRegistry` and is deliberately UNCHECKABLE externally — Alethe has
/// no notion of a solver introducing a symbol and defining it — so it lowers to
/// an honest `hole`, byte for byte what the premiseless `trust` it replaces
/// already rendered as. That is the established convention, pinned by
/// `ay-proof`'s `alethe_printer_fresh_def_tests`. What this lane must never do
/// is leave a `:rule trust` on the wire, or emit `hole :args (..)`, which the
/// pinned carcara build rejects outright and which would take the document from
/// `holey` to `invalid` — strictly worse than the step it replaced.
#[test]
fn the_retention_off_derivation_prints_no_trust_on_the_wire() {
    let (mut exec, rewritten) = retention_off_fixture();
    let scope = exec.complete_problem_assertions_for_strict_proof();
    let mut proof = leaf_proof(&mut exec, rewritten);
    exec.derive_eq_diffvar_rewritten_assertions(&mut proof, &scope);

    // The bound atoms are passed as extra problem scope ON PURPOSE: a proof
    // carrying `fresh_def_bound` is free in the introduced symbol and the
    // exporter refuses such a document outright (#8821), a PRE-EXISTING
    // property of the step this lane cites and orthogonal to the rule lowering
    // asked about here.
    let mut wide = exec.ctx.assertions.clone();
    for step in &proof.steps {
        if let ProofStep::Step {
            rule: AletheRule::FreshDefBound,
            clause,
            ..
        } = step
        {
            wide.extend(clause.iter().copied());
        }
    }
    let document = ay_proof::export_alethe_with_problem_scope_and_overrides(
        &proof,
        &exec.ctx.terms,
        &wide,
        None,
    );

    assert_eq!(
        document.matches(":rule trust").count(),
        0,
        "no `trust` step may reach the wire:\n{document}"
    );
    assert!(
        !document.contains("hole :args"),
        "`hole :args (..)` is rejected outright and turns the document invalid:\n{document}"
    );
    assert!(
        !document.contains("UNVERIFIABLE"),
        "the document must render once the introduced symbols are in scope:\n{}",
        document.lines().next().unwrap_or_default()
    );
    for expected in [
        "(step t1 (cl (<= __ay_eqdv!6 (+ x (- a)))) :rule hole)",
        "(step t2 (cl (<= (+ x (- a)) __ay_eqdv!6)) :rule hole)",
        ":rule la_disequality",
        ":rule equiv_neg1",
        ":rule equiv_neg2",
        ":rule th_resolution",
    ] {
        assert!(
            document.contains(expected),
            "missing `{expected}` on the wire:\n{document}"
        );
    }
    let checkable = ay_proof::checkable_rule_names();
    for line in document.lines() {
        let Some(rest) = line.split(":rule ").nth(1) else {
            continue;
        };
        let rule = rest
            .split([' ', ')'])
            .next()
            .expect("a :rule is followed by its name");
        assert!(
            rule == "hole" || checkable.contains(&rule),
            "rule `{rule}` is neither externally checkable nor an honest hole: {line}"
        );
    }
}
