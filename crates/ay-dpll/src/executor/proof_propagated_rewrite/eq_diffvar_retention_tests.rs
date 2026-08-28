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
//! # MUTATION LEDGER — measured, `cargo test -p ay-dpll --lib` UNFILTERED
//!
//! (Mutation G was re-measured against the retention suite after its wiring
//! fixture gained the tail-observable conjunct leaf; every other row is the
//! unfiltered harness's own output.)
//!
//! | # | guard | mutation | result |
//! |---|---|---|---|
//! | 1 | the `derive_eq_diffvar_rewritten_assertions` call in the retention-off subset | delete it | **RED**, 2 tests: `a_rewritten_assertion_is_derived_with_the_parsed_prefix_dropped`, `the_retention_off_derivation_cites_its_definition` (measured at the bound-era wiring; the call is now also load-bearing for the commit-gate tests) |
//! | A | `eq_diffvar_presentation_commit_decision` | always `Commit` | **RED x2** — `the_commit_gate_decides_all_four_tiers_against_the_real_walk`, `a_refused_subset_run_equals_the_never_spliced_run_and_latches` |
//! | B | the decision | always `Revert` | **RED x3** — the four-tiers test and BOTH solve-level capability tests (`a_rewritten_assertion_is_derived_with_the_parsed_prefix_dropped`, `the_retention_off_derivation_cites_its_definition`): a gate that always reverts undoes the lane |
//! | C | the decision | revert on ANY `Err` (cheap typed included) | **RED x3** — the same three: the real solve's finished document is a cheap typed rejection, which must COMMIT |
//! | D | the `REPEATABLE_CHECK_WORK` comparison | dropped (every typed verdict commits) | **RED** — the four-tiers test's budget tier |
//! | E | `remember` | never latch | **RED x2** — the four-tiers test (both remembered tiers) and the wiring test's latch assertion |
//! | F | `remember` | latch on `Cancelled` too | **RED** — the four-tiers test's cancellation tier |
//! | G | the tail RE-RUN after a revert | deleted | **RED** — `a_refused_subset_run_equals_the_never_spliced_run_and_latches`: the authored-conjunct leaf its fixture carries is the TAIL's work, and skipping the re-run leaves it a premiseless `trust` step |
//! | H | the `eqdv_spliced` conjunct on the gate | gate runs even when the lane spliced nothing | measured **GREEN**, recorded honestly: with no splice the revert restores a byte-identical proof and the re-run tail reproduces the same output, so no behavioural test can see it. The conjunct is COST, not correctness — it is what keeps a no-candidate rebuild from paying a whole-document walk — and the paired corpus wall measurement is its evidence |
//!
//! (The pre-gate ledger row for the former 4,096-step call-site size bound is
//! superseded: the charge-accuracy fix in `ay-proof` and the commit gate above
//! replace the bound, and `the_commit_gate_decides_all_four_tiers_against_the_real_walk`
//! documents why a size bound cannot express the criterion.)
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
    (declare-const h1 Bool)
    (declare-const h2 Bool)
    (assert (or (not g1) (= a x)))
    (assert (or (not g1) (= b y)))
    (assert (or g1 (= a y)))
    (assert (or g1 (= b x)))
    (assert (or (not g2) (= (+ x y) 1)))
    (assert (or g2 (= (+ a b) 1)))
    (assert (not (= (+ x y) 1)))
    (assert (and h1 h2))
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

/// A crafted proof whose strict walk REFUSES on the aggregate envelope after
/// the leading `trust` leaf is derived: one derivable leaf FIRST, then a step
/// whose General/Farkas precharge is cubic in its tree-unfolded payload (a
/// ~1,500-node chain unfolds past 3,000 nodes and precharges >= 2.7e10 — two
/// orders of magnitude over the 350M envelope), then the foreign closer.
fn envelope_refused_fixture(exec: &mut Executor, rewritten: TermId) -> Proof {
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, vec![rewritten], Vec::new(), Vec::new());
    let zero = exec.ctx.terms.mk_int(0.into());
    let mut chain = exec.ctx.terms.mk_var("envelope_pad", ay_core::Sort::Int);
    for _ in 0..1_500 {
        chain = exec.ctx.terms.mk_app(
            ay_core::Symbol::named("+"),
            vec![chain, chain],
            ay_core::Sort::Int,
        );
    }
    let wide_atom = exec.ctx.terms.mk_app(
        ay_core::Symbol::named("<="),
        vec![chain, zero],
        ay_core::Sort::Bool,
    );
    proof.add_theory_lemma_with_farkas_and_kind(
        "LIA",
        vec![wide_atom],
        ay_core::FarkasAnnotation::from_ints(&[1]),
        TheoryLemmaKind::LraFarkas,
    );
    let negated = exec.ctx.terms.mk_not_raw(rewritten);
    proof.add_rule_step(AletheRule::Trust, vec![negated], Vec::new(), Vec::new());
    proof.add_rule_step(
        AletheRule::Resolution,
        Vec::new(),
        vec![ay_core::ProofId(0), ay_core::ProofId(2)],
        Vec::new(),
    );
    proof
}

/// A crafted proof whose strict walk reaches a TYPED verdict (the trailing
/// foreign leaf) but only after consuming more metered work than
/// `REPEATABLE_CHECK_WORK`: valid `eq_reflexive` steps over a large unshared
/// term chain accumulate their linearithmic `ClauseIdentityRoute` charges
/// past the repeatable budget while staying inside the full envelope.
fn repeat_budget_exceeded_fixture(
    exec: &mut Executor,
    rewritten: TermId,
    extra_leaves: &[TermId],
) -> Proof {
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, vec![rewritten], Vec::new(), Vec::new());
    let mut chain = exec.ctx.terms.mk_var("repeat_pad", ay_core::Sort::Int);
    for level in 0..30_000 {
        let leaf = exec
            .ctx
            .terms
            .mk_var(format!("repeat_pad_{level}"), ay_core::Sort::Int);
        chain = exec.ctx.terms.mk_app(
            ay_core::Symbol::named("+"),
            vec![chain, leaf],
            ay_core::Sort::Int,
        );
    }
    let reflexive = exec.ctx.terms.mk_app(
        ay_core::Symbol::named("="),
        vec![chain, chain],
        ay_core::Sort::Bool,
    );
    proof.add_rule_step(
        AletheRule::EqReflexive,
        vec![reflexive],
        Vec::new(),
        Vec::new(),
    );
    let negated = exec.ctx.terms.mk_not_raw(rewritten);
    proof.add_rule_step(AletheRule::Trust, vec![negated], Vec::new(), Vec::new());
    // Extra premiseless leaves sit BEFORE the closer so the proof keeps its
    // terminal empty clause — the whole-proof gates every tail lane runs
    // reject a non-terminal document outright.
    for &leaf in extra_leaves {
        proof.add_rule_step(AletheRule::Trust, vec![leaf], Vec::new(), Vec::new());
    }
    proof.add_rule_step(
        AletheRule::Resolution,
        Vec::new(),
        vec![ay_core::ProofId(0), ay_core::ProofId(2)],
        Vec::new(),
    );
    proof
}

/// The COMMIT-GATE DECISION, all four tiers, against the real strict walk.
///
/// The decision is `Executor::eq_diffvar_presentation_commit_decision`, which
/// the retention-off subset consults on its FINISHED output (see
/// `run_assumption_authority_passes_without_parsed_syntax`). Each tier is put
/// to the real gate on a proof the strict checker genuinely walks:
///
///  * an envelope refusal reverts AND is remembered — at mint time that exact
///    outcome reaches `discharge_trust_steps_for_certification` with nothing
///    collected and falls through to a whole-problem re-solve (the measured
///    `planning/plan-8..14` degradation);
///  * a typed verdict past `REPEATABLE_CHECK_WORK` reverts AND is remembered —
///    the walk is re-run ~60 times across assemblies, and a near-envelope walk
///    multiplies into seconds (`inf-bakery-mutex-18`: 60 x 287-295M = +6.4s,
///    crossing `-T:10` with no refusal anywhere);
///  * a CHEAP typed verdict commits — same rescuable trust-family class as
///    pre-splice, affordable to re-check;
///  * a cancellation reverts WITHOUT being remembered — it is load-dependent,
///    and letting it latch would make WHICH leaves get derived depend on
///    machine load.
#[test]
fn the_commit_gate_decides_all_four_tiers_against_the_real_walk() {
    use super::EqDiffVarCommitDecision;

    // Tier 1: envelope refusal -> revert, remembered. The decision is made
    // on the SPLICED document (the subset's finished output), so splice the
    // leading leaf first; the walk then gets past it and meets the envelope.
    let (mut exec, rewritten) = retention_off_fixture();
    let scope = exec.complete_problem_assertions_for_strict_proof();
    let mut refused = envelope_refused_fixture(&mut exec, rewritten);
    assert!(
        exec.derive_eq_diffvar_rewritten_assertions(&mut refused, &scope),
        "the lane must splice the leading leaf, or the tier is not exercised"
    );
    let (outcome, _) = exec.check_proof_strict_with_datatypes_reporting_work(&refused);
    assert!(
        matches!(outcome, Err(ay_proof::ProofCheckError::ResourceLimit)),
        "the fixture must genuinely refuse on the envelope: {outcome:?}"
    );
    assert_eq!(
        exec.eq_diffvar_presentation_commit_decision(&refused),
        EqDiffVarCommitDecision::Revert { remember: true },
    );

    // Tier 2: typed verdict past the repeatable budget -> revert, remembered.
    let mut expensive = repeat_budget_exceeded_fixture(&mut exec, rewritten, &[]);
    assert!(
        exec.derive_eq_diffvar_rewritten_assertions(&mut expensive, &scope),
        "the lane must splice the leading leaf, or the tier is not exercised"
    );
    let (outcome, consumed) = exec.check_proof_strict_with_datatypes_reporting_work(&expensive);
    let error = outcome.expect_err("the trailing foreign leaf must keep the walk rejected");
    assert!(
        !matches!(
            error,
            ay_proof::ProofCheckError::ResourceLimit | ay_proof::ProofCheckError::Cancelled
        ),
        "the fixture must reach a TYPED verdict, not an envelope refusal: {error}"
    );
    assert!(
        consumed > crate::executor::proof::REPEATABLE_CHECK_WORK,
        "the fixture must genuinely exceed the repeatable budget: {consumed}"
    );
    assert_eq!(
        exec.eq_diffvar_presentation_commit_decision(&expensive),
        EqDiffVarCommitDecision::Revert { remember: true },
    );

    // Tier 3: cheap typed verdict -> commit.
    let cheap = leaf_proof(&mut exec, rewritten);
    let (outcome, consumed) = exec.check_proof_strict_with_datatypes_reporting_work(&cheap);
    assert!(outcome.is_err(), "the two trust leaves keep it rejected");
    assert!(consumed <= crate::executor::proof::REPEATABLE_CHECK_WORK);
    assert_eq!(
        exec.eq_diffvar_presentation_commit_decision(&cheap),
        EqDiffVarCommitDecision::Commit,
    );

    // Tier 4: cancellation -> revert, NOT remembered.
    let now = std::time::Instant::now();
    let expired = now
        .checked_sub(std::time::Duration::from_millis(50))
        .unwrap_or(now);
    exec.set_solve_controls(None, Some(expired));
    assert_eq!(
        exec.eq_diffvar_presentation_commit_decision(&cheap),
        EqDiffVarCommitDecision::Revert { remember: false },
        "a stop must revert without latching: nothing was learned"
    );
}

/// The COMMIT-GATE WIRING: a subset run whose finished output the gate
/// refuses must be INDISTINGUISHABLE from a subset run in which the lane
/// never fired — the "outcome not worse than pre-lane" contract, asserted as
/// literal proof equality against a latched control — and the decline must
/// latch so later assemblies skip the same doomed walk.
///
/// A mutant that deletes the gate (always commit) diverges from the control
/// on the spliced derivation; a mutant that skips the tail re-run after a
/// revert diverges on the tail lanes' missing work; a mutant that never
/// latches fails the latch assertion.
/// The conjunct of the fixture problem's authored `(and h1 h2)` assertion —
/// a leaf the TAIL's authored-conjunct lane derives, which is what makes a
/// skipped tail re-run OBSERVABLE in the wiring test below.
fn authored_conjunct(exec: &Executor) -> TermId {
    exec.ctx
        .assertions
        .iter()
        .copied()
        .find_map(|assertion| match exec.ctx.terms.get(assertion) {
            ay_core::term::TermData::App(symbol, args)
                if symbol.name() == "and" && !args.is_empty() =>
            {
                Some(args[0])
            }
            _ => None,
        })
        .expect("the fixture problem asserts (and h1 h2)")
}

#[test]
fn a_refused_subset_run_equals_the_never_spliced_run_and_latches() {
    // The arm under test: lane eligible, gate must revert on the envelope.
    // The extra premiseless leaf over the authored `(and h1 h2)` conjunct is
    // the TAIL's work — `derive_authored_conjunct_leaves` derives it — so a
    // mutant that skips the tail re-run after the revert leaves it a bare
    // `trust` step and diverges from the control.
    let (mut exec, rewritten) = retention_off_fixture();
    let conjunct = authored_conjunct(&exec);
    let mut proof = repeat_budget_exceeded_fixture(&mut exec, rewritten, &[conjunct]);
    exec.run_assumption_authority_passes_without_parsed_syntax(&mut proof);
    assert!(
        exec.eqdv_retention_off_declined_at_steps.get() != 0,
        "the deterministic decline must latch"
    );
    assert!(
        !proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::Trust,
                clause,
                premises,
                ..
            } if premises.is_empty() && clause.as_slice() == [conjunct]
        )),
        "the tail must have run after the revert: the authored-conjunct leaf \
         must be DERIVED, not left a premiseless trust step"
    );

    // The CONTROL arm: an identical executor and proof, with the lane
    // pre-latched so it never fires. The fixture solve is deterministic, so
    // the two executors' stores build identical fixtures.
    let (mut control, control_rewritten) = retention_off_fixture();
    let control_conjunct = authored_conjunct(&control);
    let mut control_proof =
        repeat_budget_exceeded_fixture(&mut control, control_rewritten, &[control_conjunct]);
    control.eqdv_retention_off_declined_at_steps.set(usize::MAX);
    control.run_assumption_authority_passes_without_parsed_syntax(&mut control_proof);

    assert_eq!(
        format!("{:?}", proof.steps),
        format!("{:?}", control_proof.steps),
        "a reverted subset run must be indistinguishable from one in which \
         the lane never fired"
    );

    // And a latched executor keeps skipping: a proof the lane WOULD splice
    // stays unspliced on the next assembly.
    let mut later = leaf_proof(&mut exec, rewritten);
    let mut later_control = leaf_proof(&mut control, control_rewritten);
    exec.run_assumption_authority_passes_without_parsed_syntax(&mut later);
    control.run_assumption_authority_passes_without_parsed_syntax(&mut later_control);
    assert_eq!(
        format!("{:?}", later.steps),
        format!("{:?}", later_control.steps),
        "a remembered decline must keep skipping the lane on later assemblies"
    );
}

/// The decline latch's SIZE SCOPE, two-sided: a similar-sized document is
/// covered (skip: same economic question), and a document under half the
/// declined size re-asks (measured: `super_queen5-1`'s final assembly shrinks
/// to 201 steps, splices cheaply and strict-certifies; an unscoped latch
/// deterministically cost it that certification, 3/3 reps).
#[test]
fn the_decline_latch_is_scoped_to_document_size() {
    let mut exec = Executor::new();
    let atom = exec.ctx.terms.mk_var("scope_pad", ay_core::Sort::Bool);
    let proof_at = |steps: usize| {
        let mut proof = Proof::new();
        for _ in 0..steps {
            proof.add_rule_step(AletheRule::Trust, vec![atom], Vec::new(), Vec::new());
        }
        proof
    };
    let same = proof_at(1_000);
    let boundary = proof_at(500);
    let smaller = proof_at(499);

    assert!(
        !exec.eq_diffvar_retention_off_decline_covers(&same),
        "no decline recorded yet: nothing is covered"
    );
    exec.eqdv_retention_off_declined_at_steps.set(1_000);
    assert!(
        exec.eq_diffvar_retention_off_decline_covers(&same),
        "a same-sized document re-asks nothing"
    );
    assert!(
        exec.eq_diffvar_retention_off_decline_covers(&boundary),
        "half the declined size is still covered (2x rule, inclusive)"
    );
    assert!(
        !exec.eq_diffvar_retention_off_decline_covers(&smaller),
        "under half the declined size is a different economic question and \
         must re-ask the gate"
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

    let _spliced = exec.derive_eq_diffvar_rewritten_assertions(&mut proof, &scope);

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
    let _spliced = exec.derive_eq_diffvar_rewritten_assertions(&mut proof, &scope);

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
        "(step t1 (cl (<= __ay_eqdv!8 (+ x (- a)))) :rule hole)",
        "(step t2 (cl (<= (+ x (- a)) __ay_eqdv!8)) :rule hole)",
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
