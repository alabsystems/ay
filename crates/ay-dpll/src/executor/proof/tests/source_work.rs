// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Measured source-work envelope regressions.

use super::*;

/// A parsed assertion stack whose complete single-pass source work lands
/// between the old sixteen-fold pre-charge threshold and the envelope itself.
fn pre_charge_refused_script(rows: usize, width: usize) -> String {
    let mut script =
        String::from("(set-logic QF_UF)\n(declare-fun envelope_leaf_00000000 () Bool)\n");
    for _ in 0..rows {
        script.push_str("(assert (and");
        for _ in 0..width {
            script.push_str(" envelope_leaf_00000000");
        }
        script.push_str("))\n");
    }
    script
}

/// A 25-assertion problem whose whole parsed source stack costs ~3 MiB of
/// rendering work used to be refused a proof outright: `proof_sources_are_oversized`
/// charged every parsed assertion SIXTEEN times — the worst reachable clone/format
/// count of every later pass, billed up front whether or not any of them ran —
/// against a 32 MiB budget, so `build_unsat_proof` installed the one-line
/// `(step t0 (cl) :rule hole)` poison and mandatory certification published
/// `unknown`. Measured on QF_UF `QG-classification/qg5/iso_brn673.smt2`
/// (25 assertions, 48 KB, refuted in 0.13 s cpu): 2.87 MiB of single-pass source
/// work, 45.9 MiB after the pre-charge.
///
/// The passes now charge themselves against one shared envelope, so this stack
/// is admitted — while a stack that genuinely cannot be rendered inside
/// `MAX_AGGREGATE_SOURCE_WORK` still fails closed on its first pass.
#[test]
fn a_pre_charge_sized_source_stack_no_longer_vetoes_proof_production() {
    use crate::executor::proof_repair::proof_trust_surgery_surface_audit::surface_pass_work;

    let commands = parse(&pre_charge_refused_script(25, 700)).expect("script parses");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("script executes");

    let work = surface_pass_work(exec.ctx.assertions_parsed())
        .expect("every authored row is individually bounded");
    assert!(
        work.saturating_mul(16) > 32 * 1024 * 1024,
        "fixture must reproduce the pre-charge refusal (single-pass work {work})",
    );

    assert!(
        !exec.proof_sources_are_oversized(),
        "a source stack one pass can render must not be refused a proof",
    );
}

/// The same predicate still refuses a stack whose SINGLE pass cannot be
/// rendered inside the envelope — the ceiling did not move, only the
/// pre-charge went away.
#[test]
fn a_genuinely_oversized_source_stack_still_installs_the_poison() {
    let commands = parse(&pre_charge_refused_script(400, 700)).expect("script parses");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("script executes");

    let mechanism = exec
        .proof_source_decline()
        .expect("one pass over this stack exceeds the aggregate envelope and must fail closed");
    assert!(
        exec.proof_sources_are_oversized(),
        "the boolean view of the same decision must agree with the attributed one",
    );
    exec.install_uncertifiable_proof_poison(mechanism);
    assert!(matches!(
        exec.last_proof
            .as_ref()
            .expect("poison is installed")
            .steps
            .as_slice(),
        [ProofStep::Step {
            rule: AletheRule::Trust,
            ..
        }],
    ));
}

/// A refusal must say WHICH refusal it is. The two source-side mechanisms have
/// opposite remedies — a root nothing can render at any budget wants a per-root
/// bound that reflects real work, a stack of individually renderable roots that
/// does not fit wants a bigger or better-spent envelope — and before this they
/// produced the same anonymous `(step t0 (cl) :rule hole)`.
#[test]
fn the_source_decline_names_which_bound_refused() {
    // 400 rows x 700 leaves: every row is individually renderable (well under
    // MAX_SURFACE_NODES), the stack as a whole is not affordable.
    let commands = parse(&pre_charge_refused_script(400, 700)).expect("script parses");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("script executes");
    assert_eq!(
        exec.proof_source_decline(),
        Some(ProofDeclineMechanism::AuthoredSourceAggregateBudget),
        "bounded roots that do not fit the envelope are an aggregate-budget refusal",
    );

    // One row of 20,000 leaves: a single root past MAX_SURFACE_NODES, which no
    // budget can rescue. This is the QF_DT `barrett-jsat/typed` class — the
    // measured population is one authored assertion of 11,054 to 128,309 nodes.
    let commands = parse(&pre_charge_refused_script(1, 20_000)).expect("script parses");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("script executes");
    assert_eq!(
        exec.proof_source_decline(),
        Some(ProofDeclineMechanism::AuthoredSourceRootUnbounded),
        "a root past the per-root surface bound is not an aggregate-budget refusal",
    );
}

/// The ceiling on REAL work still holds after the attributed split, and a
/// refusal still debits nothing. Both are the properties the pre-charge removal
/// traded on, re-proved against the envelope directly.
#[test]
fn a_refused_pass_debits_nothing_and_the_ceiling_still_binds() {
    use crate::executor::proof_repair::proof_trust_surgery_surface_audit::{
        surface_pass_work, ProofSourcePass,
    };

    let commands = parse(&pre_charge_refused_script(25, 700)).expect("script parses");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("script executes");
    let single = surface_pass_work(exec.ctx.assertions_parsed()).expect("roots are bounded");

    // A pass that cannot be afforded leaves the envelope untouched.
    exec.proof_source_work.set_remaining_for_test(single - 1);
    assert!(
        !exec.proof_source_work.spend(
            ProofSourcePass::UnsatProofBuild,
            exec.ctx.assertions_parsed()
        ),
        "an unaffordable pass must decline",
    );
    assert_eq!(
        exec.proof_source_work.remaining_for_test(),
        single - 1,
        "a refusal must debit nothing",
    );

    // The conjunct-eval rebuild is metered like every other pass: FOUR
    // source-scale traversals (deep clone, raw re-intern, override-aware
    // render, full re-parse), charged, and refused when they do not fit. It
    // cannot spend work the aggregate ceiling has not authorized. Charging it
    // as 2 cost +5.6s at 400 roots that nothing authorized.
    exec.proof_source_work
        .set_remaining_for_test(4 * single - 1);
    assert!(
        !exec.proof_source_work.spend(
            ProofSourcePass::AuthoredConjunctEvalRebuild,
            exec.ctx.assertions_parsed()
        ),
        "the rebuild charges all four of its traversals",
    );
    exec.proof_source_work.set_remaining_for_test(4 * single);
    assert!(
        exec.proof_source_work.spend(
            ProofSourcePass::AuthoredConjunctEvalRebuild,
            exec.ctx.assertions_parsed()
        ),
        "and is admitted at exactly its cost",
    );
    assert_eq!(exec.proof_source_work.remaining_for_test(), 0);
}
