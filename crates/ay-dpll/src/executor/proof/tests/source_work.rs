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

/// Rows x width of a stack whose single build traversal does not fit the
/// envelope: 640 rows of ~14.7 KB each, at the traversal's factor of four,
/// is ~37.6 MiB against 32 MiB. (400 rows used to suffice when the build
/// pass was priced as a per-subtree rendering.)
const OVERSIZED_ROWS: usize = 640;
const OVERSIZED_WIDTH: usize = 700;

/// The same predicate still refuses a stack whose SINGLE pass cannot be
/// afforded inside the envelope — the ceiling did not move, only the
/// pre-charge went away.
#[test]
fn a_genuinely_oversized_source_stack_still_installs_the_poison() {
    let commands =
        parse(&pre_charge_refused_script(OVERSIZED_ROWS, OVERSIZED_WIDTH)).expect("script parses");
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
    // Every row is individually traversable, the stack as a whole is not
    // affordable.
    let commands =
        parse(&pre_charge_refused_script(OVERSIZED_ROWS, OVERSIZED_WIDTH)).expect("script parses");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("script executes");
    assert_eq!(
        exec.proof_source_decline(),
        Some(ProofDeclineMechanism::AuthoredSourceAggregateBudget),
        "bounded roots that do not fit the envelope are an aggregate-budget refusal",
    );

    // One root deeper than MAX_SURFACE_DEPTH, which no budget can rescue:
    // even the build pass's single traversal refuses it.
    let commands = parse(&deep_not_chain_script(300)).expect("script parses");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("script executes");
    assert_eq!(
        exec.proof_source_decline(),
        Some(ProofDeclineMechanism::AuthoredSourceRootUnbounded),
        "a root past the traversal's per-root bound is not an aggregate-budget refusal",
    );
}

/// One authored assertion that is a `not` chain `depth` deep.
fn deep_not_chain_script(depth: usize) -> String {
    let mut script = String::from("(set-logic QF_UF)\n(declare-fun deep_leaf () Bool)\n(assert ");
    for _ in 0..depth {
        script.push_str("(not ");
    }
    script.push_str("deep_leaf");
    for _ in 0..depth {
        script.push(')');
    }
    script.push_str(")\n");
    script
}

/// The build pass is ONE traversal and is priced as one. A root that only a
/// per-subtree renderer cannot afford — here 20,000 leaves under one `and`,
/// past `MAX_SURFACE_NODES` — used to be refused the WHOLE proof
/// (`authored-source-root-unbounded`, the one-line trust poison) before any
/// reconstruction ran. That is the QF_DT `barrett-jsat/typed` class (one
/// authored assertion of 11,054 to 128,309 nodes) and external-codegen's large
/// packed-vector and half-precision obligations (8,511 to 133,990 nodes).
/// The per-subtree bound still holds, at the sites that render per subtree.
#[test]
fn a_root_only_per_subtree_renderers_refuse_is_admitted_to_the_build() {
    use crate::executor::proof_repair::proof_trust_surgery_surface_audit::{
        surface_source_is_bounded, surface_source_work_probe_as, SurfaceWorkModel,
    };

    let commands = parse(&pre_charge_refused_script(1, 20_000)).expect("script parses");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("script executes");
    let root = &exec.ctx.assertions_parsed()[0];
    assert!(
        !surface_source_is_bounded(root),
        "fixture must be past the per-subtree rendering bound",
    );
    assert!(surface_source_work_probe_as(root, SurfaceWorkModel::Traversal).is_ok());
    let before = exec.proof_source_work.remaining_for_test();
    assert_eq!(
        exec.proof_source_decline(),
        None,
        "the build pass's single traversal of a 20,001-node root is affordable",
    );
    assert!(
        exec.proof_source_work.remaining_for_test() < before,
        "and it is charged for that traversal",
    );
}

/// The ceiling on REAL work still holds after the attributed split, and a
/// refusal still debits nothing. Both are the properties the pre-charge removal
/// traded on, re-proved against the envelope directly.
#[test]
fn a_refused_pass_debits_nothing_and_the_ceiling_still_binds() {
    use crate::executor::proof_repair::proof_trust_surgery_surface_audit::{
        surface_pass_work, surface_pass_work_as, ProofSourcePass, SurfaceWorkModel,
    };

    let commands = parse(&pre_charge_refused_script(25, 700)).expect("script parses");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("script executes");
    let single = surface_pass_work(exec.ctx.assertions_parsed()).expect("roots are bounded");
    let traversal = surface_pass_work_as(exec.ctx.assertions_parsed(), SurfaceWorkModel::Traversal)
        .expect("roots are traversable");
    assert!(
        traversal < single,
        "one traversal costs less than rendering every subtree"
    );

    // A pass that cannot be afforded leaves the envelope untouched.
    exec.proof_source_work.set_remaining_for_test(traversal - 1);
    assert!(
        !exec.proof_source_work.spend(
            ProofSourcePass::UnsatProofBuild,
            exec.ctx.assertions_parsed()
        ),
        "an unaffordable pass must decline",
    );
    assert_eq!(
        exec.proof_source_work.remaining_for_test(),
        traversal - 1,
        "a refusal must debit nothing",
    );
    exec.proof_source_work.set_remaining_for_test(traversal);
    assert!(
        exec.proof_source_work.spend(
            ProofSourcePass::UnsatProofBuild,
            exec.ctx.assertions_parsed()
        ),
        "the build pass is admitted at exactly its traversal cost",
    );
    assert_eq!(exec.proof_source_work.remaining_for_test(), 0);

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

/// A balanced `bvadd` tree over `leaves` alternating 8-bit leaves.
fn balanced_bvadd(leaves: usize) -> String {
    if leaves == 1 {
        return "wide_bv_x".to_string();
    }
    let left = leaves / 2;
    format!(
        "(bvadd {} {})",
        balanced_bvadd(left),
        balanced_bvadd(leaves - left).replacen("wide_bv_x", "wide_bv_y", 1)
    )
}

/// END TO END: a refuted QF_BV obligation whose single authored assertion is
/// past the per-subtree rendering bound (16,383 nodes of bit-vector
/// arithmetic, the shape of external-codegen's packed-vector obligations) now gets its
/// strict-checkable proof. It used to get the one-line trust poison
/// (`authored-source-root-unbounded`) before any reconstruction ran.
#[test]
fn a_wide_bv_obligation_past_the_per_subtree_bound_gets_a_strict_proof() {
    use crate::executor::proof_repair::proof_trust_surgery_surface_audit::surface_source_is_bounded;

    let side = balanced_bvadd(8_192);
    let script = format!(
        "(set-option :produce-proofs true)\n(set-logic QF_BV)\n\
         (declare-const wide_bv_x (_ BitVec 8))\n(declare-const wide_bv_y (_ BitVec 8))\n\
         (assert (not (= {side} {side})))\n(check-sat)\n"
    );
    let commands = parse(&script).expect("script parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("script executes");
    assert_eq!(outputs, vec!["unsat"]);
    assert!(
        !surface_source_is_bounded(&exec.ctx.assertions_parsed()[0]),
        "fixture must be past the per-subtree rendering bound",
    );
    assert_ne!(
        exec.last_proof_decline(),
        Some(ProofDeclineMechanism::AuthoredSourceRootUnbounded),
    );
    let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
    let quality = ay_proof::check_proof_strict(proof, &exec.ctx.terms)
        .expect("the proof must pass the strict checker");
    assert_eq!(quality.trust_count, 0);
    let text = exec.get_proof();
    assert!(!text.contains(":rule trust"), "no trust step:\n{text}");
    assert!(!text.contains(":rule hole"), "no hole step:\n{text}");
}
