// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #certify-before-presentation — what a declined authored-surface override
//! plan does with the derivation behind it: a SHAPE-only decline keeps the
//! derivation for certification and withholds the document; a SIZE decline
//! keeps the one-line `(cl)` poison.

use ay_core::{AletheRule, Proof, ProofStep};

use crate::executor::{Executor, ProofDeclineMechanism, UnboundedCensus};

/// The authored roots `(and p (forall ((x Int)) (= x x)))` and `(not p)`: the
/// quantified conjunct trips the plan's binder-shape veto, and `p` is a
/// conjunct the refutation uses. Returns `(p, (not p))`.
fn assert_binder_root_beside_its_complement(
    exec: &mut Executor,
    padding_conjuncts: usize,
) -> (ay_core::TermId, ay_core::TermId) {
    use ay_core::Sort;
    use ay_frontend::command::Term as FrontendTerm;

    let p = exec.ctx.terms.mk_var("withheld_p", Sort::Bool);
    let x = exec.ctx.terms.mk_var("withheld_x", Sort::Int);
    let body = exec
        .ctx
        .terms
        .mk_app(ay_core::Symbol::named("="), vec![x, x], Sort::Bool);
    let binder = exec
        .ctx
        .terms
        .mk_forall(vec![("withheld_x".to_string(), Sort::Int)], body);
    let padding: Vec<(ay_core::TermId, String)> = (0..padding_conjuncts)
        .map(|index| {
            let name = format!("withheld_pad_{index}");
            (exec.ctx.terms.mk_var(&name, Sort::Bool), name)
        })
        .collect();
    let root = exec.ctx.terms.mk_and(
        [p, binder]
            .into_iter()
            .chain(padding.iter().map(|(term, _)| *term))
            .collect(),
    );
    let not_p = exec.ctx.terms.mk_not(p);
    exec.ctx.add_assertion_with_parsed(
        root,
        FrontendTerm::App(
            "and".to_string(),
            [
                FrontendTerm::Symbol("withheld_p".to_string()),
                FrontendTerm::Forall(
                    vec![(
                        "withheld_x".to_string(),
                        ay_frontend::command::Sort::Simple("Int".to_string()),
                    )],
                    Box::new(FrontendTerm::App(
                        "=".to_string(),
                        vec![
                            FrontendTerm::Symbol("withheld_x".to_string()),
                            FrontendTerm::Symbol("withheld_x".to_string()),
                        ],
                    )),
                ),
            ]
            .into_iter()
            .chain(
                padding
                    .into_iter()
                    .map(|(_, name)| FrontendTerm::Symbol(name)),
            )
            .collect(),
        ),
    );
    exec.ctx.add_assertion_with_parsed(
        not_p,
        FrontendTerm::App(
            "not".to_string(),
            vec![FrontendTerm::Symbol("withheld_p".to_string())],
        ),
    );

    (p, not_p)
}

/// #certify-before-presentation. When a real empty-clause derivation stands
/// behind the declined override plan, the plan withholds the DOCUMENT and
/// keeps the derivation for certification instead of replacing it with the
/// one-line `(cl)` trust poison.
#[test]
fn a_declined_override_plan_keeps_a_derivation_and_withholds_the_document() {
    let mut exec = Executor::new();
    let (p, not_p) = assert_binder_root_beside_its_complement(&mut exec, 0);

    let mut proof = Proof::new();
    let leaf_p = proof.add_assume(p, None);
    let leaf_not_p = proof.add_assume(not_p, None);
    proof.add_resolution(Vec::new(), p, leaf_p, leaf_not_p);
    exec.apply_input_syntax_rewrites_to_proof(&mut proof);

    assert_eq!(
        exec.last_proof_decline(),
        Some(ProofDeclineMechanism::AuthoredSurfaceOverridePlanUnbounded)
    );
    assert!(
        !proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::Trust,
                clause,
                ..
            } if clause.is_empty()
        )),
        "a derivation behind a declined plan must not be replaced by the `(cl)` poison"
    );
    assert!(
        proof
            .steps
            .iter()
            .any(|step| matches!(step, ProofStep::Resolution { clause, .. } if clause.is_empty())),
        "the empty-clause derivation must survive the declined plan"
    );
    assert!(
        exec.last_unsat_proof_reconstruction_suppressed,
        "the document must be withheld when the plan declines"
    );
    assert_eq!(
        exec.last_proof_surface_withheld,
        Some(ProofDeclineMechanism::AuthoredSurfaceOverridePlanUnbounded)
    );
}

/// #certify-before-presentation. The derivation kept behind a presentation
/// bound goes through the same assumption-authority tail this posture runs
/// when no bound fires, so a leaf that is a CONJUNCT of a large authored
/// assertion is derived from it (`and_pos`) rather than demoted to a `trust`
/// step the funnel can only corroborate by a re-solve. The narrower
/// retention-off subset reaches conjuncts only through the authored-conjunct
/// lane, whose root-work bound (`MAX_CONJUNCT_ROOT_WORK`) declines a root this
/// size and leaves the leaf trusted. The same shape as QF_IDL
/// `parity/16.100.graph` (one large `(let … (and …))` root whose parsed
/// surface exhausts the source-work envelope): the subset left 4 such leaves,
/// admitted `discharged-trust`; the default tail derives them, admitted
/// `strict-proof`.
#[test]
fn a_withheld_derivation_derives_the_conjuncts_of_a_large_authored_root() {
    const PADDING: usize = 70_000;
    let is_trust = |step: &ProofStep| {
        matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::Trust | AletheRule::Hole,
                ..
            }
        )
    };
    let refutation = |p, not_p| {
        let mut proof = Proof::new();
        let leaf_p = proof.add_assume(p, None);
        let leaf_not_p = proof.add_assume(not_p, None);
        proof.add_resolution(Vec::new(), p, leaf_p, leaf_not_p);
        proof
    };

    let mut narrow = Executor::new();
    let (p, not_p) = assert_binder_root_beside_its_complement(&mut narrow, PADDING);
    let mut narrow_proof = refutation(p, not_p);
    narrow.run_assumption_authority_passes_without_parsed_syntax(&mut narrow_proof);
    assert!(
        narrow_proof.steps.iter().any(is_trust),
        "fixture premise: the retention-off subset leaves this conjunct trusted"
    );

    let mut exec = Executor::new();
    let (p, not_p) = assert_binder_root_beside_its_complement(&mut exec, PADDING);
    let mut proof = refutation(p, not_p);
    exec.apply_input_syntax_rewrites_to_proof(&mut proof);
    assert_eq!(
        exec.last_proof_surface_withheld,
        Some(ProofDeclineMechanism::InputSyntaxRewriteSourceBudget),
        "a parsed root this size exhausts the source-work envelope, which must withhold \
         the surface and keep the derivation"
    );
    let trust_leaves: Vec<&ProofStep> = proof.steps.iter().filter(|step| is_trust(step)).collect();
    assert!(
        trust_leaves.is_empty(),
        "the conjunct `p` of an authored `and` must be derived, not trusted: {trust_leaves:?}"
    );
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::AndPos(_),
                ..
            }
        )),
        "the conjunct is derived by `and_pos` from its authored root"
    );
}

/// #certify-before-presentation. A plan that declined on SIZE keeps the
/// one-line poison even with a derivation behind it: the size refusal is a
/// statement about the terms that derivation carries (measured: a kept
/// derivation over a 674M-node expansion ran the process out of memory).
#[test]
fn a_size_declined_override_plan_keeps_the_poison_even_with_a_derivation() {
    use ay_core::Sort;
    use ay_frontend::command::Term as FrontendTerm;

    let mut exec = Executor::new();
    let p = exec.ctx.terms.mk_var("sized_p", Sort::Bool);
    let x = exec.ctx.terms.mk_var("sized_x", Sort::Int);
    // A 24-level doubling DAG: 25 unique nodes, ~16.7M per-occurrence visits.
    let mut doubled = x;
    for _ in 0..24 {
        doubled = exec.ctx.terms.mk_app(
            ay_core::Symbol::named("sized_f"),
            vec![doubled, doubled],
            Sort::Int,
        );
    }
    let big = exec
        .ctx
        .terms
        .mk_app(ay_core::Symbol::named("="), vec![doubled, x], Sort::Bool);
    let root = exec.ctx.terms.mk_and(vec![p, big]);
    let not_p = exec.ctx.terms.mk_not(p);
    exec.ctx
        .add_assertion_with_parsed(root, FrontendTerm::Symbol("sized_root".to_string()));
    exec.ctx.add_assertion_with_parsed(
        not_p,
        FrontendTerm::App(
            "not".to_string(),
            vec![FrontendTerm::Symbol("sized_p".to_string())],
        ),
    );

    let mut proof = Proof::new();
    let leaf_p = proof.add_assume(p, None);
    let leaf_not_p = proof.add_assume(not_p, None);
    proof.add_resolution(Vec::new(), p, leaf_p, leaf_not_p);
    exec.apply_input_syntax_rewrites_to_proof(&mut proof);

    assert_eq!(
        exec.last_proof_decline(),
        Some(ProofDeclineMechanism::AuthoredSurfaceOverridePlanUnbounded)
    );
    let Some(UnboundedCensus::OverridePlan(census)) = exec.last_unbounded_census() else {
        panic!("the override-plan decline must carry an override-plan census");
    };
    assert!(
        census.canonical_roots_refused_size > 0,
        "the fixture must decline on SIZE: {census:?}"
    );
    assert!(matches!(
        proof.steps.as_slice(),
        [ProofStep::Step {
            rule: AletheRule::Trust,
            ..
        }],
    ));
    assert!(!exec.last_unsat_proof_reconstruction_suppressed);
    assert_eq!(exec.last_proof_surface_withheld, None);
}
