// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Producer tests for the GUARDED THEN-PROJECTION ite-lift repair
//! (`plan_ite_lift_guarded_then` in `proof_trust_surgery/trichotomy.rs`).
//!
//! THE DEFECT. Arithmetic-ITE clausification of an authored `P` containing a
//! term-level `(ite c u v)` emits the guarded pair `(or (not c) P[s/u])` /
//! `(or c P[s/v])`. When the else clause is trivially true (`(<= 0 (ite c X
//! 0))` gives `(or c (<= 0 0))`), it folds away and ONLY the guarded then
//! clause survives — as a premiseless trust leaf no problem assertion equals.
//! The packed ite-lift recognizer requires the goal to BE a formula `ite`, so
//! the leaf stayed unrepaired: `check_proof_strict` rejected the refutation
//! and a correct `unsat` published `unknown`. The `inc_some_list`
//! dual-vocabulary probe (`dt_uf_bridge_congruence`) is the integration case.
//!
//! WHAT IS ASSERTED. The rebuilt proof is checked by the UNCHANGED
//! `ay_proof::check_proof_strict` — the emitter's own output, not a shape
//! assertion — with ZERO trust steps, and the emitted Alethe wire text is
//! pinned EXACTLY for the derivation's key steps. The falsify-once negative
//! plants the byte-identical step sequence with a conclusion the premises do
//! not entail, over a SATISFIABLE assertion set, and requires the untouched
//! strict checker to reject it.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{AletheRule, Proof, Sort, TermId};
use ay_frontend::command::{Command, Constant, Sort as FrontendSort, Term as FrontendTerm};

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
    parsed_goal: FrontendTerm,
    cond: TermId,
    goal: TermId,
}

/// Authored `(<= 0 (ite (= y 0) x 0))`; the surviving clausification leaf is
/// `(or (not (= y 0)) (<= 0 x))` — the else clause `(or (= y 0) (<= 0 0))`
/// folds away. The condition is COMPOSITE, as in every measured producer
/// shape (the `inc_some_list` probe's guard is a datatype tester): the
/// retained-surface audit requires a registered spelling for the guard, which
/// only a composite surface carries.
fn guarded_then_fixture() -> Fixture {
    let mut executor = Executor::new();
    let y = declare(&mut executor, "y", "Int");
    let x = declare(&mut executor, "x", "Int");
    let _ = (x, y);
    let parsed_cond = app("=", [FrontendTerm::Symbol("y".to_string()), numeral("0")]);
    let cond = executor
        .ctx
        .elaborate_surface_subterm(&parsed_cond)
        .expect("guard elaborates");
    // Intern the guard BEFORE the branch literal: `mk_or` orders disjuncts by
    // `TermId`, and the clausifier's surviving leaf spells the guard first.
    let not_cond = executor.ctx.terms.mk_not_raw(cond);
    let parsed_orig = app(
        "<=",
        [
            numeral("0"),
            app(
                "ite",
                [
                    parsed_cond,
                    FrontendTerm::Symbol("x".to_string()),
                    numeral("0"),
                ],
            ),
        ],
    );
    let orig = executor
        .ctx
        .elaborate_surface_subterm(&parsed_orig)
        .expect("authored guarded source elaborates");
    let lifted_then = executor
        .ctx
        .elaborate_surface_subterm(&app(
            "<=",
            [numeral("0"), FrontendTerm::Symbol("x".to_string())],
        ))
        .expect("lifted then branch elaborates");
    let goal = executor.ctx.terms.mk_or(vec![not_cond, lifted_then]);
    let parsed_goal = app(
        "or",
        [
            app(
                "not",
                [app(
                    "=",
                    [FrontendTerm::Symbol("y".to_string()), numeral("0")],
                )],
            ),
            app("<=", [numeral("0"), FrontendTerm::Symbol("x".to_string())]),
        ],
    );
    assert_eq!(
        {
            let ay_core::TermData::App(_, disjuncts) = executor.ctx.terms.get(goal) else {
                panic!("goal must intern as a packed or");
            };
            disjuncts.clone()
        },
        vec![not_cond, lifted_then],
        "the fixture goal must keep the guarded-then literal order",
    );
    // The scrutinee inside `orig` must be the exact interned x-ite.
    assert!(matches!(executor.ctx.terms.sort(orig), Sort::Bool));
    Fixture {
        executor,
        orig,
        parsed_orig,
        parsed_goal,
        cond,
        goal,
    }
}

/// The trust refutation the exporter leaves behind: a premiseless trust leaf
/// of the guarded clause resolved against its assumed complement.
fn trust_refutation(executor: &mut Executor, goal: TermId) -> Proof {
    let mut proof = Proof::new();
    let trust = proof.add_rule_step(AletheRule::Trust, vec![goal], Vec::new(), Vec::new());
    let not_goal = executor.ctx.terms.mk_not_raw(goal);
    let complement = proof.add_assume(not_goal, None);
    let _ = proof.add_resolution(Vec::new(), goal, trust, complement);
    proof
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
fn guarded_then_projection_rebuilds_strictly_with_exact_wire_text() {
    let mut fixture = guarded_then_fixture();
    let mut proof = trust_refutation(&mut fixture.executor, fixture.goal);
    let not_goal = fixture.executor.ctx.terms.mk_not_raw(fixture.goal);
    let originals = vec![
        (fixture.orig, fixture.parsed_orig.clone()),
        (not_goal, app("not", [fixture.parsed_goal.clone()])),
    ];
    install_surface_overrides(&mut fixture.executor, &originals);

    assert!(
        fixture
            .executor
            .try_rebuild_with_trust_surgery(&mut proof, &originals),
        "the guarded then-projection must be recognized and rebuilt"
    );
    let quality = ay_proof::check_proof_strict(&proof, &fixture.executor.ctx.terms)
        .expect("rebuilt guarded then-projection must be strict");
    assert_eq!(quality.trust_count, 0, "no trust steps: {quality}");
    assert_eq!(quality.hole_count, 0, "no hole steps: {quality}");

    // EXACT wire text of the emitted derivation. Every step of the guarded
    // route is pinned: the ite_intro definition chain, the checked
    // `la_generic` transfer with its exact coefficients, and the
    // `or_neg`/`contraction` packing into the goal `or`.
    let alethe = ay_proof::export_alethe(&proof, &fixture.executor.ctx.terms);
    for line in [
        "(assume t0 (not (or (not (= y 0)) (<= 0 x))))",
        "(assume t1 (<= 0 (ite (= y 0) x 0)))",
        "(step t2 (cl (= (<= 0 (ite (= y 0) x 0)) (and (<= 0 (ite (= y 0) x 0)) (ite (= y 0) (= (ite (= y 0) x 0) x) (= (ite (= y 0) x 0) 0))))) :rule ite_intro)",
        "(step t3 (cl (not (= (<= 0 (ite (= y 0) x 0)) (and (<= 0 (ite (= y 0) x 0)) (ite (= y 0) (= (ite (= y 0) x 0) x) (= (ite (= y 0) x 0) 0))))) (not (<= 0 (ite (= y 0) x 0))) (and (<= 0 (ite (= y 0) x 0)) (ite (= y 0) (= (ite (= y 0) x 0) x) (= (ite (= y 0) x 0) 0)))) :rule equiv_pos2)",
        "(step t4 (cl (not (<= 0 (ite (= y 0) x 0))) (and (<= 0 (ite (= y 0) x 0)) (ite (= y 0) (= (ite (= y 0) x 0) x) (= (ite (= y 0) x 0) 0)))) :rule resolution :premises (t3 t2))",
        "(step t5 (cl (and (<= 0 (ite (= y 0) x 0)) (ite (= y 0) (= (ite (= y 0) x 0) x) (= (ite (= y 0) x 0) 0)))) :rule resolution :premises (t4 t1))",
        "(step t6 (cl (not (and (<= 0 (ite (= y 0) x 0)) (ite (= y 0) (= (ite (= y 0) x 0) x) (= (ite (= y 0) x 0) 0)))) (ite (= y 0) (= (ite (= y 0) x 0) x) (= (ite (= y 0) x 0) 0))) :rule and_pos :args (1))",
        "(step t7 (cl (ite (= y 0) (= (ite (= y 0) x 0) x) (= (ite (= y 0) x 0) 0))) :rule resolution :premises (t6 t5))",
        "(step t8 (cl (not (= y 0)) (= (ite (= y 0) x 0) x)) :rule ite2 :premises (t7))",
        "(step t9 (cl (not (= (ite (= y 0) x 0) x)) (not (<= 0 (ite (= y 0) x 0))) (<= 0 x)) :rule la_generic :args (-1 1 1))",
        "(step t10 (cl (not (= y 0)) (not (<= 0 (ite (= y 0) x 0))) (<= 0 x)) :rule resolution :premises (t8 t9))",
        "(step t11 (cl (not (= y 0)) (<= 0 x)) :rule resolution :premises (t10 t1))",
        "(step t12 (cl (or (not (= y 0)) (<= 0 x)) (= y 0)) :rule or_neg :args (0))",
        "(step t13 (cl (<= 0 x) (or (not (= y 0)) (<= 0 x))) :rule resolution :premises (t11 t12))",
        "(step t14 (cl (or (not (= y 0)) (<= 0 x)) (not (<= 0 x))) :rule or_neg :args (1))",
        "(step t15 (cl (or (not (= y 0)) (<= 0 x)) (or (not (= y 0)) (<= 0 x))) :rule resolution :premises (t13 t14))",
        "(step t16 (cl (or (not (= y 0)) (<= 0 x))) :rule contraction :premises (t15))",
        "(step t17 (cl) :rule resolution :premises (t16 t0))",
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
fn guarded_then_projection_requires_the_exact_then_substitution() {
    let mut fixture = guarded_then_fixture();
    // `(or (not p) (<= 1 x))` is NOT the then substitution of any authored
    // assertion; recognition must decline and the trust leaf must survive
    // untouched (the surgery reports failure and leaves the proof alone).
    let one_le_x = fixture
        .executor
        .ctx
        .elaborate_surface_subterm(&app(
            "<=",
            [numeral("1"), FrontendTerm::Symbol("x".to_string())],
        ))
        .expect("forged branch elaborates");
    let not_cond = fixture.executor.ctx.terms.mk_not_raw(fixture.cond);
    let forged_goal = fixture.executor.ctx.terms.mk_or(vec![not_cond, one_le_x]);
    let mut proof = trust_refutation(&mut fixture.executor, forged_goal);
    let steps_before = proof.steps.len();
    let not_forged_goal = fixture.executor.ctx.terms.mk_not_raw(forged_goal);
    let parsed_forged_goal = app(
        "or",
        [
            app(
                "not",
                [app(
                    "=",
                    [FrontendTerm::Symbol("y".to_string()), numeral("0")],
                )],
            ),
            app("<=", [numeral("1"), FrontendTerm::Symbol("x".to_string())]),
        ],
    );
    let originals = vec![
        (fixture.orig, fixture.parsed_orig.clone()),
        (not_forged_goal, app("not", [parsed_forged_goal])),
    ];

    assert!(
        !fixture
            .executor
            .try_rebuild_with_trust_surgery(&mut proof, &originals),
        "a mismatched then substitution must fail closed"
    );
    assert_eq!(
        proof.steps.len(),
        steps_before,
        "declined repair must not mutate the proof"
    );
}

/// FALSIFY-ONCE. The byte-identical guarded derivation — same rules, same
/// coefficients, same step order the emitter produces — planted with a
/// conclusion `(<= 1 x)` the premises do not entail, over the SATISFIABLE
/// assertion set `{(<= 0 (ite (= y 0) x 0))}`. The untouched strict checker must
/// reject it (the `la_generic` transfer row is arithmetically invalid).
#[test]
fn planted_guarded_derivation_over_satisfiable_instance_is_rejected() {
    let mut fixture = guarded_then_fixture();
    let executor = &mut fixture.executor;
    let orig = fixture.orig;
    let cond = fixture.cond;
    let x = executor
        .ctx
        .elaborate_surface_subterm(&FrontendTerm::Symbol("x".to_string()))
        .expect("x elaborates");
    let zero = executor
        .ctx
        .elaborate_surface_subterm(&numeral("0"))
        .expect("0 elaborates");
    let ay_core::TermData::App(_, operands) = executor.ctx.terms.get(orig).clone() else {
        panic!("orig is an application");
    };
    let ite_term = operands[1];
    let (eq_then, eq_else, ite_def, and_term, intro_eq) = executor
        .build_ite_lift_connectives(orig, cond, ite_term, x, zero)
        .expect("connectives build for the authored source");

    // Forged conclusion: entailed is (<= 0 x); planted is (<= 1 x).
    let forged_then = executor
        .ctx
        .elaborate_surface_subterm(&app(
            "<=",
            [numeral("1"), FrontendTerm::Symbol("x".to_string())],
        ))
        .expect("forged conclusion elaborates");
    let terms = &mut executor.ctx.terms;
    let not_cond = terms.mk_not_raw(cond);
    let goal = terms.mk_or(vec![not_cond, forged_then]);
    let not_goal = terms.mk_not_raw(goal);
    let not_intro_eq = terms.mk_not_raw(intro_eq);
    let not_orig = terms.mk_not_raw(orig);
    let not_and = terms.mk_not_raw(and_term);
    let not_eq_then = terms.mk_not_raw(eq_then);
    let _ = eq_else;

    let mut proof = Proof::new();
    let assume = proof.add_assume(orig, None);
    let downstream = proof.add_assume(not_goal, None);
    let intro = proof.add_rule_step(AletheRule::IteIntro, vec![intro_eq], Vec::new(), Vec::new());
    let equiv = proof.add_rule_step(
        AletheRule::EquivPos2,
        vec![not_intro_eq, not_orig, and_term],
        Vec::new(),
        Vec::new(),
    );
    let equality = proof.add_resolution(vec![not_orig, and_term], intro_eq, equiv, intro);
    let conjunction = proof.add_resolution(vec![and_term], orig, equality, assume);
    let and_pos = proof.add_rule_step(
        AletheRule::AndPos(1),
        vec![not_and, ite_def],
        Vec::new(),
        Vec::new(),
    );
    let definition = proof.add_resolution(vec![ite_def], and_term, and_pos, conjunction);
    let ite_then = proof.add_rule_step(
        AletheRule::Ite2,
        vec![not_cond, eq_then],
        vec![definition],
        Vec::new(),
    );
    let bridge = proof.add_step(ay_core::ProofStep::TheoryLemma {
        theory: "LRA".to_string(),
        clause: vec![not_eq_then, not_orig, forged_then],
        farkas: Some(ay_core::FarkasAnnotation::from_ints(&[1, 1, 1])),
        kind: ay_core::TheoryLemmaKind::LraFarkas,
        lia: None,
    });
    let transferred = proof.add_resolution(
        vec![not_cond, not_orig, forged_then],
        eq_then,
        ite_then,
        bridge,
    );
    let projected = proof.add_resolution(vec![not_cond, forged_then], orig, transferred, assume);
    let link_guard =
        proof.add_rule_step(AletheRule::OrNeg, vec![goal, cond], Vec::new(), Vec::new());
    let packed_guard =
        proof.add_resolution(vec![forged_then, goal], not_cond, projected, link_guard);
    let not_forged_then = fixture.executor.ctx.terms.mk_not_raw(forged_then);
    let link_then = proof.add_rule_step(
        AletheRule::OrNeg,
        vec![goal, not_forged_then],
        Vec::new(),
        Vec::new(),
    );
    let packed = proof.add_resolution(vec![goal, goal], forged_then, packed_guard, link_then);
    let contracted = proof.add_rule_step(
        AletheRule::Contraction,
        vec![goal],
        vec![packed],
        Vec::new(),
    );
    let _ = proof.add_resolution(Vec::new(), goal, contracted, downstream);

    let rejection = ay_proof::check_proof_strict(&proof, &fixture.executor.ctx.terms);
    assert!(
        rejection.is_err(),
        "the planted derivation's la_generic row is invalid; strict must reject"
    );
}
