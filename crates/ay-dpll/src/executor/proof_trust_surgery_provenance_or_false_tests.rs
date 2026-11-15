// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Producer tests for the FALSE-DISJUNCT provenance-OR repair
//! (`plan_provenance_or_false_disjunct` in
//! `proof_trust_surgery_provenance_or.rs`).
//!
//! THE DEFECT. Substitute-and-simplify folds a disjunct of an authored `or`
//! to the literal `false` (`(or (= a 1) B)` under authored `(= a 0)` becomes
//! `(or false B)`) and exports the folded clause as a premiseless trust leaf.
//! No prior provenance-OR lane covers it: the exact-transfer lane requires
//! source and target to share NO atom, and the conflict lanes require EVERY
//! disjunct refutable. The `inc_some_list` dual-vocabulary probe
//! (`dt_uf_bridge_congruence`) carries exactly this leaf
//! (`(or false (not ((_ is Nil) self_current)))` from
//! `(or (= aux 1) (not ((_ is Nil) self_current)))` + `(= aux 0)`).
//!
//! WHAT IS ASSERTED. The rebuilt proof is checked by the UNCHANGED
//! `ay_proof::check_proof_strict` with ZERO trust steps, and the emitted
//! Alethe wire text is pinned EXACTLY: the `or` decomposition, the checked
//! two-row `la_generic` refutation with its exact coefficients, and the
//! `or_neg`/`contraction` packing. The falsify-once negative plants the
//! byte-identical step sequence whose `la_generic` rows do NOT conflict, over
//! a SATISFIABLE assertion set, and requires the untouched strict checker to
//! reject it.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{AletheRule, Proof, TermId};
use ay_frontend::command::{Command, Constant, Sort as FrontendSort, Term as FrontendTerm};

use super::theories::solve_harness::ProofProblemAssertionProvenance;
use super::Executor;

fn declare(executor: &mut Executor, name: &str, sort: &str) -> TermId {
    executor
        .ctx
        .process_command(&Command::DeclareConst(
            name.to_string(),
            FrontendSort::Simple(sort.to_string()),
        ))
        .expect("fixture declaration succeeds");
    executor
        .ctx
        .elaborate_surface_subterm(&FrontendTerm::Symbol(name.to_string()))
        .expect("declared fixture symbol elaborates")
}

fn numeral(value: &str) -> FrontendTerm {
    FrontendTerm::Const(Constant::Numeral(value.to_string()))
}

fn app(head: &str, operands: impl IntoIterator<Item = FrontendTerm>) -> FrontendTerm {
    FrontendTerm::App(head.to_string(), operands.into_iter().collect())
}

struct Fixture {
    executor: Executor,
    orig: TermId,
    parsed_orig: FrontendTerm,
    equality: TermId,
    parsed_equality: FrontendTerm,
    kept: TermId,
    goal: TermId,
}

/// Authored `(or (= a 1) (<= x 0))` and `(= a 0)`; the folded leaf is
/// `(or false (<= x 0))`.
fn false_disjunct_fixture() -> Fixture {
    let mut executor = Executor::new();
    let _ = declare(&mut executor, "a", "Int");
    let _ = declare(&mut executor, "x", "Int");
    let parsed_orig = app(
        "or",
        [
            app("=", [FrontendTerm::Symbol("a".to_string()), numeral("1")]),
            app("<=", [FrontendTerm::Symbol("x".to_string()), numeral("0")]),
        ],
    );
    let orig = executor
        .ctx
        .elaborate_surface_subterm(&parsed_orig)
        .expect("authored or elaborates");
    let parsed_equality = app("=", [FrontendTerm::Symbol("a".to_string()), numeral("0")]);
    let equality = executor
        .ctx
        .elaborate_surface_subterm(&parsed_equality)
        .expect("authored equality elaborates");
    let kept = executor
        .ctx
        .elaborate_surface_subterm(&app(
            "<=",
            [FrontendTerm::Symbol("x".to_string()), numeral("0")],
        ))
        .expect("kept disjunct elaborates");
    let false_term = executor.ctx.terms.false_term();
    // `mk_or` folds a `false` disjunct away; the preprocessor's substituted
    // clause is raw-interned, so raw-intern the fixture goal the same way.
    let goal = executor.ctx.terms.mk_app(
        ay_core::Symbol::named("or"),
        [false_term, kept],
        ay_core::Sort::Bool,
    );
    assert_eq!(
        {
            let ay_core::TermData::App(_, disjuncts) = executor.ctx.terms.get(goal) else {
                panic!("goal must intern as a packed or");
            };
            disjuncts.clone()
        },
        vec![false_term, kept],
        "the fixture goal must keep the folded literal order",
    );

    let mut assertion_sources = HashMap::default();
    assertion_sources.insert(goal, vec![vec![orig]]);
    executor.proof_problem_assertion_provenance = Some(ProofProblemAssertionProvenance {
        original_problem_assertions: vec![orig, equality],
        problem_assertions: vec![orig, equality],
        assertion_sources,
    });
    Fixture {
        executor,
        orig,
        parsed_orig,
        equality,
        parsed_equality,
        kept,
        goal,
    }
}

fn trust_refutation(executor: &mut Executor, goal: TermId) -> Proof {
    let mut proof = Proof::new();
    let trust = proof.add_rule_step(AletheRule::Trust, vec![goal], Vec::new(), Vec::new());
    let not_goal = executor.ctx.terms.mk_not_raw(goal);
    let complement = proof.add_assume(not_goal, None);
    let _ = proof.add_resolution(Vec::new(), goal, trust, complement);
    proof
}

fn fixture_originals(fixture: &Fixture) -> Vec<(TermId, FrontendTerm)> {
    vec![
        (fixture.orig, fixture.parsed_orig.clone()),
        (fixture.equality, fixture.parsed_equality.clone()),
    ]
}

/// The folded clause is a preprocessing product with NO authored surface (the
/// `inc_some_list` probe installs it natively); its complement original
/// therefore carries the native-API placeholder, exactly as production does.
fn native_placeholder() -> FrontendTerm {
    FrontendTerm::Symbol(crate::executor::NATIVE_API_ASSERTION_PLACEHOLDER.to_string())
}

/// Install the print-surface overrides the executor would carry after a real
/// export (the finalize replay validates the rebuilt rendering against them).
fn install_surface_overrides(executor: &mut Executor, originals: &[(TermId, FrontendTerm)]) {
    let mut overrides = HashMap::default();
    for (canonical, parsed) in originals {
        assert!(
            crate::executor::proof_surface_syntax::collect_surface_term_overrides(
                &mut executor.ctx,
                *canonical,
                parsed,
                &mut overrides,
            ),
            "fixture surfaces must collect"
        );
    }
    executor.last_proof_term_overrides = Some(overrides);
}

#[test]
fn false_disjunct_or_rebuilds_strictly_with_exact_wire_text() {
    let mut fixture = false_disjunct_fixture();
    let mut proof = trust_refutation(&mut fixture.executor, fixture.goal);
    let not_goal = fixture.executor.ctx.terms.mk_not_raw(fixture.goal);
    let mut originals = fixture_originals(&fixture);
    install_surface_overrides(&mut fixture.executor, &originals);
    originals.push((not_goal, native_placeholder()));

    assert!(
        fixture
            .executor
            .try_rebuild_with_trust_surgery(&mut proof, &originals),
        "the false-disjunct or must be recognized and rebuilt"
    );
    let quality = ay_proof::check_proof_strict(&proof, &fixture.executor.ctx.terms)
        .expect("rebuilt false-disjunct or must be strict");
    assert_eq!(quality.trust_count, 0, "no trust steps: {quality}");
    assert_eq!(quality.hole_count, 0, "no hole steps: {quality}");

    // EXACT wire text: the or decomposition of the authored premise, the
    // two-row la_generic refutation of the folded disjunct with its exact
    // searched coefficients, and the or_neg/contraction packing.
    let alethe = ay_proof::export_alethe(&proof, &fixture.executor.ctx.terms);
    for line in [
        "(assume t0 (not (or false (<= x 0))))",
        "(assume t1 (or (= a 1) (<= x 0)))",
        "(assume t2 (= a 0))",
        "(step t3 (cl (= a 1) (<= x 0)) :rule or :premises (t1))",
        "(step t4 (cl (not (= a 0)) (not (= a 1))) :rule la_generic :args (-1 1))",
        "(step t5 (cl (not (= a 1))) :rule resolution :premises (t4 t2))",
        "(step t6 (cl (<= x 0)) :rule resolution :premises (t3 t5))",
        "(step t7 (cl (or false (<= x 0)) (not (<= x 0))) :rule or_neg :args (1))",
        "(step t8 (cl (or false (<= x 0))) :rule resolution :premises (t6 t7))",
        "(step t9 (cl (or false (<= x 0))) :rule contraction :premises (t8))",
        "(step t10 (cl) :rule resolution :premises (t9 t0))",
    ] {
        assert!(
            alethe.contains(line),
            "expected exact wire line {line:?} in:\n{alethe}"
        );
    }
    assert!(
        !alethe.contains(":rule trust") && !alethe.contains(":rule hole"),
        "printed Alethe must be trust-free:\n{alethe}"
    );
}

#[test]
fn false_disjunct_or_requires_recorded_provenance() {
    let mut fixture = false_disjunct_fixture();
    fixture.executor.proof_problem_assertion_provenance = None;
    let mut proof = trust_refutation(&mut fixture.executor, fixture.goal);
    let steps_before = proof.steps.len();
    let originals = fixture_originals(&fixture);
    assert!(
        !fixture
            .executor
            .try_rebuild_with_trust_surgery(&mut proof, &originals),
        "without provenance the folded or must fail closed"
    );
    assert_eq!(proof.steps.len(), steps_before);
}

#[test]
fn false_disjunct_or_requires_an_authored_refuting_equality() {
    let mut fixture = false_disjunct_fixture();
    let mut proof = trust_refutation(&mut fixture.executor, fixture.goal);
    let steps_before = proof.steps.len();
    // The or alone: `(= a 0)` is NOT among the authored originals, so no
    // authored equality refutes the folded disjunct.
    let originals = vec![(fixture.orig, fixture.parsed_orig.clone())];
    assert!(
        !fixture
            .executor
            .try_rebuild_with_trust_surgery(&mut proof, &originals),
        "without the authored equality the folded or must fail closed"
    );
    assert_eq!(proof.steps.len(), steps_before);
}

#[test]
fn false_disjunct_or_rejects_a_consistent_equality() {
    let mut fixture = false_disjunct_fixture();
    // Replace the authored `(= a 0)` by `(= a 1)`: consistent with the folded
    // disjunct, so NO coefficient vector certifies a conflict and the repair
    // must decline rather than emit an unsound lemma.
    let parsed_equality = app("=", [FrontendTerm::Symbol("a".to_string()), numeral("1")]);
    let equality = fixture
        .executor
        .ctx
        .elaborate_surface_subterm(&parsed_equality)
        .expect("consistent equality elaborates");
    let mut proof = trust_refutation(&mut fixture.executor, fixture.goal);
    let steps_before = proof.steps.len();
    let originals = vec![
        (fixture.orig, fixture.parsed_orig.clone()),
        (equality, parsed_equality),
    ];
    assert!(
        !fixture
            .executor
            .try_rebuild_with_trust_surgery(&mut proof, &originals),
        "a consistent equality certifies nothing; the repair must fail closed"
    );
    assert_eq!(proof.steps.len(), steps_before);
}

/// The CANONICAL spelling of the same fold (#false-disjunct-canonical):
/// `64d468871` rebuilds substituted Boolean connectives through `mk_or`, which
/// drops the `false` disjunct and returns the sole survivor bare, so the leaf
/// the `inc_some_list` probe carries is now `(not (is-Nil self_current))`
/// itself -- here `(<= x 0)`. Provenance and authored sources are unchanged.
fn canonical_sole_survivor_fixture() -> Fixture {
    let mut fixture = false_disjunct_fixture();
    let false_term = fixture.executor.ctx.terms.false_term();
    let canonical = fixture
        .executor
        .ctx
        .terms
        .mk_or(vec![false_term, fixture.kept]);
    assert_eq!(
        canonical, fixture.kept,
        "mk_or must drop the folded literal and return the sole survivor bare"
    );
    let mut assertion_sources = HashMap::default();
    assertion_sources.insert(canonical, vec![vec![fixture.orig]]);
    fixture.executor.proof_problem_assertion_provenance = Some(ProofProblemAssertionProvenance {
        original_problem_assertions: vec![fixture.orig, fixture.equality],
        problem_assertions: vec![fixture.orig, fixture.equality],
        assertion_sources,
    });
    fixture.goal = canonical;
    fixture
}

/// RED before the canonical arm: the planner required a literal `false`
/// disjunct, so the canonical leaf stayed a trust step and surgery declined.
#[test]
fn canonical_sole_survivor_rebuilds_strictly_without_repacking() {
    let mut fixture = canonical_sole_survivor_fixture();
    let mut proof = trust_refutation(&mut fixture.executor, fixture.goal);
    let not_goal = fixture.executor.ctx.terms.mk_not_raw(fixture.goal);
    let mut originals = fixture_originals(&fixture);
    install_surface_overrides(&mut fixture.executor, &originals);
    originals.push((not_goal, native_placeholder()));

    assert!(
        fixture
            .executor
            .try_rebuild_with_trust_surgery(&mut proof, &originals),
        "the canonical sole survivor of a folded or must be recognized and rebuilt"
    );
    let quality = ay_proof::check_proof_strict(&proof, &fixture.executor.ctx.terms)
        .expect("rebuilt canonical survivor must be strict");
    assert_eq!(quality.trust_count, 0, "no trust steps: {quality}");
    assert_eq!(quality.hole_count, 0, "no hole steps: {quality}");

    // The same authored decomposition and checked refutation as the
    // positional form, ending at the survivor itself.
    let alethe = ay_proof::export_alethe(&proof, &fixture.executor.ctx.terms);
    for line in [
        "(step t3 (cl (= a 1) (<= x 0)) :rule or :premises (t1))",
        "(step t4 (cl (not (= a 0)) (not (= a 1))) :rule la_generic :args (-1 1))",
        "(step t6 (cl (<= x 0)) :rule resolution :premises (t3 t5))",
    ] {
        assert!(
            alethe.contains(line),
            "expected exact wire line {line:?} in:\n{alethe}"
        );
    }
    assert!(
        !alethe.contains(":rule or_neg") && !alethe.contains(":rule contraction"),
        "a sole survivor IS the goal; nothing may be re-packed:\n{alethe}"
    );
    assert!(
        !alethe.contains(":rule trust") && !alethe.contains(":rule hole"),
        "printed Alethe must be trust-free:\n{alethe}"
    );
}

#[test]
fn canonical_sole_survivor_requires_recorded_provenance() {
    let mut fixture = canonical_sole_survivor_fixture();
    fixture.executor.proof_problem_assertion_provenance = None;
    let mut proof = trust_refutation(&mut fixture.executor, fixture.goal);
    let steps_before = proof.steps.len();
    let originals = fixture_originals(&fixture);
    assert!(
        !fixture
            .executor
            .try_rebuild_with_trust_surgery(&mut proof, &originals),
        "without provenance the canonical survivor must fail closed"
    );
    assert_eq!(proof.steps.len(), steps_before);
}

/// Membership pairing is exact: a canonical target literal that restates NO
/// source disjunct leaves every source disjunct to be refuted, and the
/// surviving `(<= x 0)` is not refutable from `(= a 0)`, so the leaf stays
/// trusted rather than being "derived" from an unrelated authored `or`.
#[test]
fn canonical_target_must_restate_a_source_disjunct() {
    let mut fixture = false_disjunct_fixture();
    let stray = fixture
        .executor
        .ctx
        .elaborate_surface_subterm(&app(
            "<=",
            [FrontendTerm::Symbol("x".to_string()), numeral("1")],
        ))
        .expect("stray literal elaborates");
    let mut assertion_sources = HashMap::default();
    assertion_sources.insert(stray, vec![vec![fixture.orig]]);
    fixture.executor.proof_problem_assertion_provenance = Some(ProofProblemAssertionProvenance {
        original_problem_assertions: vec![fixture.orig, fixture.equality],
        problem_assertions: vec![fixture.orig, fixture.equality],
        assertion_sources,
    });
    let mut proof = trust_refutation(&mut fixture.executor, stray);
    let steps_before = proof.steps.len();
    let originals = fixture_originals(&fixture);
    assert!(
        !fixture
            .executor
            .try_rebuild_with_trust_surgery(&mut proof, &originals),
        "a target that restates no source disjunct must fail closed"
    );
    assert_eq!(proof.steps.len(), steps_before);
}

/// Two survivors: the canonical target is `mk_or` of both (sorted, no
/// `false`), so each survivor is an operand of the goal and the plan re-packs
/// them with `or_neg` + `contraction` exactly as for the positional spelling.
#[test]
fn canonical_survivor_or_repacks_strictly() {
    let mut executor = Executor::new();
    let _ = declare(&mut executor, "a", "Int");
    let _ = declare(&mut executor, "x", "Int");
    let _ = declare(&mut executor, "y", "Int");
    let x_le = app("<=", [FrontendTerm::Symbol("x".to_string()), numeral("0")]);
    let y_le = app("<=", [FrontendTerm::Symbol("y".to_string()), numeral("0")]);
    let parsed_orig = app(
        "or",
        [
            app("=", [FrontendTerm::Symbol("a".to_string()), numeral("1")]),
            x_le.clone(),
            y_le.clone(),
        ],
    );
    let orig = executor
        .ctx
        .elaborate_surface_subterm(&parsed_orig)
        .expect("authored or elaborates");
    let parsed_equality = app("=", [FrontendTerm::Symbol("a".to_string()), numeral("0")]);
    let equality = executor
        .ctx
        .elaborate_surface_subterm(&parsed_equality)
        .expect("authored equality elaborates");
    let kept_x = executor
        .ctx
        .elaborate_surface_subterm(&x_le)
        .expect("first survivor elaborates");
    let kept_y = executor
        .ctx
        .elaborate_surface_subterm(&y_le)
        .expect("second survivor elaborates");
    let false_term = executor.ctx.terms.false_term();
    let goal = executor.ctx.terms.mk_or(vec![false_term, kept_x, kept_y]);
    let ay_core::TermData::App(_, goal_disjuncts) = executor.ctx.terms.get(goal) else {
        panic!("two survivors must intern as an or");
    };
    assert!(
        goal_disjuncts.len() == 2 && !goal_disjuncts.contains(&false_term),
        "the canonical goal must keep both survivors and drop the folded literal"
    );
    let mut assertion_sources = HashMap::default();
    assertion_sources.insert(goal, vec![vec![orig]]);
    executor.proof_problem_assertion_provenance = Some(ProofProblemAssertionProvenance {
        original_problem_assertions: vec![orig, equality],
        problem_assertions: vec![orig, equality],
        assertion_sources,
    });
    let mut proof = trust_refutation(&mut executor, goal);
    let not_goal = executor.ctx.terms.mk_not_raw(goal);
    let mut originals = vec![(orig, parsed_orig), (equality, parsed_equality)];
    install_surface_overrides(&mut executor, &originals);
    originals.push((not_goal, native_placeholder()));

    assert!(
        executor.try_rebuild_with_trust_surgery(&mut proof, &originals),
        "the canonical survivor or must be recognized and rebuilt"
    );
    let quality = ay_proof::check_proof_strict(&proof, &executor.ctx.terms)
        .expect("rebuilt canonical survivor or must be strict");
    assert_eq!(quality.trust_count, 0, "no trust steps: {quality}");
    assert_eq!(quality.hole_count, 0, "no hole steps: {quality}");
    let alethe = ay_proof::export_alethe(&proof, &executor.ctx.terms);
    assert!(
        alethe.contains(":rule or_neg") && alethe.contains(":rule contraction"),
        "two survivors are re-packed into the canonical goal:\n{alethe}"
    );
    assert!(
        !alethe.contains(":rule trust") && !alethe.contains(":rule hole"),
        "printed Alethe must be trust-free:\n{alethe}"
    );
}

/// FALSIFY-ONCE. The byte-identical false-disjunct derivation — same rules,
/// same step order the emitter produces — planted with a support equality
/// `(= a 1)` that does NOT conflict with the folded disjunct `(= a 1)`, over
/// the SATISFIABLE assertion set `{(or (= a 1) (<= x 0)), (= a 1)}`. The
/// untouched strict checker must reject the `la_generic` step (its rows sum
/// to no conflict under every printed coefficient).
#[test]
fn planted_false_disjunct_derivation_over_satisfiable_instance_is_rejected() {
    let mut fixture = false_disjunct_fixture();
    let executor = &mut fixture.executor;
    let disjunct = {
        let ay_core::TermData::App(_, disjuncts) = executor.ctx.terms.get(fixture.orig) else {
            panic!("orig is an or");
        };
        disjuncts[0]
    };
    let terms = &mut executor.ctx.terms;
    let not_disjunct = terms.mk_not_raw(disjunct);
    let not_goal = terms.mk_not_raw(fixture.goal);

    let mut proof = Proof::new();
    let or_assume = proof.add_assume(fixture.orig, None);
    // The planted "support": the disjunct itself, satisfiable alongside the or.
    let eq_assume = proof.add_assume(disjunct, None);
    let downstream = proof.add_assume(not_goal, None);
    let decomposed = proof.add_rule_step(
        AletheRule::Or,
        vec![disjunct, fixture.kept],
        vec![or_assume],
        Vec::new(),
    );
    let lemma = proof.add_step(ay_core::ProofStep::TheoryLemma {
        theory: "LRA".to_string(),
        clause: vec![not_disjunct, not_disjunct],
        farkas: Some(ay_core::FarkasAnnotation::from_ints(&[1, -1])),
        kind: ay_core::TheoryLemmaKind::LraFarkas,
        lia: None,
    });
    let unit = proof.add_resolution(vec![not_disjunct], disjunct, lemma, eq_assume);
    let survived = proof.add_resolution(vec![fixture.kept], disjunct, decomposed, unit);
    let not_kept = fixture.executor.ctx.terms.mk_not_raw(fixture.kept);
    let link = proof.add_rule_step(
        AletheRule::OrNeg,
        vec![fixture.goal, not_kept],
        Vec::new(),
        Vec::new(),
    );
    let packed = proof.add_resolution(vec![fixture.goal], fixture.kept, survived, link);
    let contracted = proof.add_rule_step(
        AletheRule::Contraction,
        vec![fixture.goal],
        vec![packed],
        Vec::new(),
    );
    let _ = proof.add_resolution(Vec::new(), fixture.goal, contracted, downstream);

    let rejection = ay_proof::check_proof_strict(&proof, &fixture.executor.ctx.terms);
    assert!(
        rejection.is_err(),
        "the planted la_generic rows do not conflict; strict must reject"
    );
}
