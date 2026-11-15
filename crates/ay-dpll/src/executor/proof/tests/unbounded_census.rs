// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #unbounded-population — the census taken at the two "unbounded" declines.
//!
//! These tests pin three things: that the census is TAKEN at each site (a
//! decline with no census is the anonymous decline this instrument exists to
//! replace), that the refusal it names is the bound that actually fired, and
//! that it is write-only — the poison is byte-identical with and without it.

use ay_core::{AletheRule, Proof, ProofStep};
use ay_frontend::parse;

use crate::executor::proof_repair::proof_trust_surgery_surface_audit::{
    surface_source_work, surface_source_work_probe, SurfaceSourceRefusal,
};
use crate::executor::proof_trust_surgery_provenance::{
    canonical_term_work, canonical_term_work_refusal, CanonicalWorkRefusal,
};
use crate::executor::{Executor, OverridePlanExit, ProofDeclineMechanism, UnboundedCensus};

fn wide_row_script(rows: usize, width: usize) -> String {
    let mut script =
        String::from("(set-logic QF_UF)\n(declare-fun census_leaf_00000000 () Bool)\n");
    for _ in 0..rows {
        script.push_str("(assert (and");
        for _ in 0..width {
            script.push_str(" census_leaf_00000000");
        }
        script.push_str("))\n");
    }
    script
}

/// The probe and the `Option` view are the same decision. Every existing
/// caller reads the `Option`; the census reads the probe; they must not drift.
#[test]
fn the_source_probe_agrees_with_the_option_view_and_names_the_bound() {
    use ay_frontend::command::Term as FrontendTerm;

    let bounded = FrontendTerm::App(
        "and".to_string(),
        vec![FrontendTerm::Symbol("p".to_string()); 8],
    );
    assert!(surface_source_work(&bounded).is_some());
    assert!(surface_source_work_probe(&bounded).is_ok());

    // 20_000 leaves under one `and`: past MAX_SURFACE_NODES, so `Nodes`.
    let wide = FrontendTerm::App(
        "and".to_string(),
        vec![FrontendTerm::Symbol("p".to_string()); 20_000],
    );
    assert!(surface_source_work(&wide).is_none());
    assert_eq!(
        surface_source_work_probe(&wide),
        Err(SurfaceSourceRefusal::Nodes)
    );

    // A `not` chain past MAX_SURFACE_DEPTH: `Depth`, not `Nodes`.
    let mut deep = FrontendTerm::Symbol("p".to_string());
    for _ in 0..300 {
        deep = FrontendTerm::App("not".to_string(), vec![deep]);
    }
    assert!(surface_source_work(&deep).is_none());
    assert_eq!(
        surface_source_work_probe(&deep),
        Err(SurfaceSourceRefusal::Depth)
    );
}

/// Same contract for the canonical estimator, whose `None` on a binder is a
/// SHAPE veto the census must not report as a size.
#[test]
fn the_canonical_probe_separates_a_binder_veto_from_a_size_refusal() {
    use ay_core::{Sort, Symbol, TermStore};

    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let x = terms.mk_var("x", Sort::Int);
    let body = terms.mk_app(Symbol::named("="), vec![x, x], Sort::Bool);
    let binder = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
    let wrapped = terms.mk_and(vec![p, binder]);
    assert!(canonical_term_work(&terms, wrapped).is_none());
    assert_eq!(
        canonical_term_work_refusal(&terms, wrapped),
        Err(CanonicalWorkRefusal::Binder)
    );

    // A DAG whose per-occurrence expansion is astronomically large but whose
    // unique node count is tiny: a chain of `and`s each citing the previous
    // twice. This is the shape a per-occurrence walk cannot afford and a
    // DAG-aware one prices in microseconds.
    // `mk_and` deduplicates identical conjuncts at construction, so the
    // doubling has to go through an uninterpreted symbol.
    let mut chain = p;
    for _ in 0..40 {
        chain = terms.mk_app(Symbol::named("dup"), vec![chain, chain], Sort::Bool);
    }
    assert!(canonical_term_work(&terms, chain).is_none());
    assert_eq!(
        canonical_term_work_refusal(&terms, chain),
        Err(CanonicalWorkRefusal::Visits)
    );
    let shape = {
        let mut memo = super::super::unbounded_census::CanonicalShapeMemo::default();
        memo.shape(&terms, chain)
    };
    assert!(
        shape.unique_nodes < 64,
        "a 40-deep doubling chain has ~41 unique nodes, measured {}",
        shape.unique_nodes
    );
    assert!(
        shape.expanded_nodes > 1 << 40,
        "its per-occurrence expansion is over 2^40, measured {}",
        shape.expanded_nodes
    );
    assert_eq!(shape.depth, 40);
    assert_eq!(shape.binders, 0);
}

/// One authored assertion that is a `not` chain `depth` deep.
fn deep_not_chain_script(depth: usize) -> String {
    let mut script = String::from("(set-logic QF_UF)\n(declare-fun census_leaf () Bool)\n(assert ");
    for _ in 0..depth {
        script.push_str("(not ");
    }
    script.push_str("census_leaf");
    for _ in 0..depth {
        script.push(')');
    }
    script.push_str(")\n");
    script
}

/// The source-root decline carries a census naming the bound, with the true
/// size of the root that tripped it, and the poison it installs is unchanged.
#[test]
fn the_source_root_decline_censuses_the_refused_root() {
    let commands = parse(&deep_not_chain_script(300)).expect("script parses");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("script executes");
    let mechanism = exec
        .proof_source_decline()
        .expect("a 300-deep root is past the per-root bound");
    assert_eq!(
        mechanism,
        ProofDeclineMechanism::AuthoredSourceRootUnbounded
    );
    assert!(
        exec.last_unbounded_census().is_none(),
        "the census is taken when the poison is installed, not before"
    );

    exec.install_uncertifiable_proof_poison(mechanism);

    let Some(UnboundedCensus::SourceRoot(census)) = exec.last_unbounded_census() else {
        panic!("the source-root decline must carry a source-root census");
    };
    assert_eq!(census.roots, 1);
    assert_eq!(census.refused_roots, 1);
    assert_eq!(census.refusal, Some(SurfaceSourceRefusal::Depth));
    // 300 `not` nodes + the leaf, counted without the bound.
    assert_eq!(census.first_refused.nodes, 301);
    assert_eq!(census.first_refused.depth, 300);
    assert_eq!(census.first_refused.let_bindings, 0);
    assert_eq!(census.largest_refused, census.first_refused);
    assert_eq!(census.bounded_roots_work, 0);
    // No `(check-sat)` ran, so no public-query epoch was ever bound and there
    // is NO authenticated pre-split authored stack to read. The census says so
    // and reports no canonical root at all. It deliberately does NOT fall back
    // to `ctx.assertions`: that stack is rewritten in place, and reading it is
    // the exact defect `the_source_root_census_reports_the_authored_root_not_
    // the_split_window` pins.
    assert_eq!(census.first_canonical_source, "unavailable");
    assert_eq!(census.first_canonical_kind, "unavailable");
    assert_eq!(census.authored_roots, 0);
    assert_eq!(census.first_canonical, Default::default());

    // Write-only: the artifact is the same one-line poison it always was.
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
    assert_eq!(
        exec.last_proof_decline(),
        Some(ProofDeclineMechanism::AuthoredSourceRootUnbounded)
    );
}

/// The census must report the term the REFUSED PARSED ROOT elaborated to, not
/// whatever sits at the same index of the solve-time window.
///
/// This is the defect that withdrew a published reading. `ctx.assertions` is
/// rewritten in place and `FlattenAnd` splits a top-level conjunction into one
/// entry per conjunct, so `ctx.assertions[0]` is the first CONJUNCT, not the
/// root — which is how five single-assertion problems AY answers `unsat` came
/// to be reported as having a root of `v` or `(not v)`, a shape that is
/// satisfiable and therefore cannot be the root of a refuted problem.
///
/// The script reproduces exactly that: one authored root that trips the
/// per-root bound — its first conjunct is `census_p` under 300 negations —
/// and elaborates to `(and p q r)`, which the split takes apart into three
/// window entries whose first is the bare variable `p`.
#[test]
fn the_source_root_census_reports_the_authored_root_not_the_split_window() {
    let mut script = String::from(
        "(set-logic QF_UF)\n(declare-fun census_p () Bool)\n(declare-fun census_q \
                      () Bool)\n(declare-fun census_r () Bool)\n(assert (and ",
    );
    for _ in 0..300 {
        script.push_str("(not ");
    }
    script.push_str("census_p");
    for _ in 0..300 {
        script.push(')');
    }
    script.push_str(" census_q census_r))\n(assert (not census_q))\n(check-sat)\n");

    let commands = parse(&script).expect("script parses");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("script executes");

    let authored = exec
        .unsat_query_epoch_authored_assertions()
        .expect("`(check-sat)` binds the immutable public-query epoch");
    assert_eq!(authored.len(), 2);
    assert_eq!(exec.ctx.assertions_parsed().len(), 2);

    // Reproduce the defect's CAUSE, not a pass that happens to fire: replace
    // the solve-time window with the conjuncts of the authored root, exactly
    // what an in-place pass such as `FlattenAnd` does to it. The parsed stack
    // is untouched, so the window's entry 0 is now the bare variable while
    // authored root 0 is still the whole conjunction.
    let conjuncts = match exec.ctx.terms.get(authored[0]) {
        ay_core::term::TermData::App(_, args) => args.clone(),
        other => panic!("the authored root must be an application, got {other:?}"),
    };
    assert!(conjuncts.len() > 1, "the root must have several conjuncts");
    exec.ctx.assertions = conjuncts;
    assert_eq!(
        super::super::unbounded_census::term_kind(&exec.ctx.terms, exec.ctx.assertions[0]),
        "var",
        "the window's entry 0 is the split conjunct the old field reported"
    );

    let mechanism = exec
        .proof_source_decline()
        .expect("a 301-deep root is past the per-root bound");
    exec.install_uncertifiable_proof_poison(mechanism);
    let Some(UnboundedCensus::SourceRoot(census)) = exec.last_unbounded_census() else {
        panic!("the source-root decline must carry a source-root census");
    };

    assert_eq!(census.roots, 2);
    assert_eq!(census.refused_roots, 1);
    assert_eq!(census.authored_roots, 2);
    assert_eq!(census.solve_window_roots, 3);
    assert_eq!(census.first_canonical_source, "epoch");
    // The authored root is the conjunction, not its first conjunct. The even
    // negation chain folds to `census_p`, so the DAG is
    // `(and census_p census_q census_r)`: four unique nodes at depth one.
    assert_eq!(census.first_canonical_kind, "app");
    assert_eq!(census.first_canonical.unique_nodes, 4);
    assert_eq!(census.first_canonical.depth, 1);
}

/// A stack the AGGREGATE envelope refuses is not this class, and must not
/// carry this class's census.
#[test]
fn an_aggregate_budget_decline_carries_no_unbounded_census() {
    let commands = parse(&wide_row_script(640, 700)).expect("script parses");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("script executes");
    let mechanism = exec
        .proof_source_decline()
        .expect("640 x 700 exceeds the envelope");
    assert_eq!(
        mechanism,
        ProofDeclineMechanism::AuthoredSourceAggregateBudget
    );
    exec.install_uncertifiable_proof_poison(mechanism);
    assert!(exec.last_unbounded_census().is_none());
}

/// The override plan's decline names its exit. Here: a canonical root with a
/// binder below it — a shape veto, which the census reports as SHAPE, with
/// the size refusal count at zero.
#[test]
fn the_override_plan_decline_censuses_its_exit() {
    use ay_core::Sort;
    use ay_frontend::command::Term as FrontendTerm;

    let mut exec = Executor::new();
    let p = exec.ctx.terms.mk_var("census_p", Sort::Bool);
    let x = exec.ctx.terms.mk_var("census_x", Sort::Int);
    let body = exec
        .ctx
        .terms
        .mk_app(ay_core::Symbol::named("="), vec![x, x], Sort::Bool);
    let binder = exec
        .ctx
        .terms
        .mk_forall(vec![("census_x".to_string(), Sort::Int)], body);
    // `(and p (forall ...))`: the binder is INTERIOR, which the estimator
    // refuses at any size.
    let root = exec.ctx.terms.mk_and(vec![p, binder]);
    exec.ctx.add_assertion_with_parsed(
        root,
        FrontendTerm::App(
            "and".to_string(),
            vec![
                FrontendTerm::Symbol("census_p".to_string()),
                FrontendTerm::Forall(
                    vec![(
                        "census_x".to_string(),
                        ay_frontend::command::Sort::Simple("Int".to_string()),
                    )],
                    Box::new(FrontendTerm::App(
                        "=".to_string(),
                        vec![
                            FrontendTerm::Symbol("census_x".to_string()),
                            FrontendTerm::Symbol("census_x".to_string()),
                        ],
                    )),
                ),
            ],
        ),
    );

    let mut proof = Proof::new();
    proof.add_assume(root, None);
    exec.apply_input_syntax_rewrites_to_proof(&mut proof);

    assert_eq!(
        exec.last_proof_decline(),
        Some(ProofDeclineMechanism::AuthoredSurfaceOverridePlanUnbounded)
    );
    let Some(UnboundedCensus::OverridePlan(census)) = exec.last_unbounded_census() else {
        panic!("the override-plan decline must carry an override-plan census");
    };
    assert_eq!(census.exit, Some(OverridePlanExit::CanonicalRootsUnbounded));
    assert_eq!(census.pair_specs, 1);
    assert_eq!(census.canonical_roots_refused_shape, 1);
    assert_eq!(census.canonical_roots_refused_size, 0);
    assert_eq!(
        census.canonical_first_refusal,
        Some(CanonicalWorkRefusal::Binder)
    );
    assert_eq!(census.largest_canonical.binders, 1);
    // Write-only, and an `assume`-only proof has no derivation behind the
    // bound to certify (#certify-before-presentation), so the plan still
    // poisons exactly as before.
    assert!(matches!(
        proof.steps.as_slice(),
        [ProofStep::Step {
            rule: AletheRule::Trust,
            ..
        }],
    ));
    assert!(!exec.last_unsat_proof_reconstruction_suppressed);
}
