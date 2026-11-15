// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The guarded collapse asked before the promotion: where the cascade will
//! ask it about the same roots whatever the promotion decides, the stage takes
//! the cascade's own decisions in the cascade's own order, stops where one
//! turns on the promoted incumbent, and leaves every other proof to the
//! promotion and the cascade.

use super::*;
use ay_core::{AletheRule, Sort, Symbol, TermData, TermId};

/// An authored memory round-trip whose single root reads an array: its
/// guarded candidate certifies through the checker's array lane and prints
/// clean.
const ARRAY_ROOT: &str = include_str!(
    "../../../../../../ay-proof/src/alethe_printer/bv_packed/fixtures/aggregate_scalar_pair.smt2"
);

/// One authored root that reads an array and is contradictory on its own;
/// its candidate prints a `hole`.
const ARRAY_READ_SINGLE: &str = include_str!("array-read-single.smt2");

/// Two array-read roots, contradictory only together; the joint candidate
/// prints a `hole`.
const ARRAY_READ_JOINT: &str = "(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 32)))
(declare-fun y () (_ BitVec 32))
(assert (= (select a #x0) #x00000000))
(assert (bvugt (select (store a #x1 (bvmul (select a #x0) y)) #x1) #x00000000))
(check-sat)
";

/// One pure bit-vector root, contradictory on its own.
const PURE_BV: &str = "(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (not (= (bvadd x y) (bvadd y x))))
(check-sat)
";

fn solved(problem: &str) -> Executor {
    solved_with(problem, true)
}

/// `problem` solved, with a proof document observable when `proofs` is set.
fn solved_with(problem: &str, proofs: bool) -> Executor {
    let mut executor = Executor::new();
    executor.set_produce_proofs(proofs);
    let results = executor
        .execute_all(&ay_frontend::parse(problem).unwrap())
        .unwrap();
    assert_eq!(
        results.first().map(String::as_str),
        Some("unsat"),
        "{:?}",
        executor.unknown_reason()
    );
    executor
}

/// `(cl (not (bvult p q)) (not (bvult q p)))` over 64-bit `p`, `q`: true,
/// multi-literal, and decided only by the proof producer.
fn producer_lemma(executor: &mut Executor) -> Vec<TermId> {
    let terms = &mut executor.ctx.terms;
    let sort = Sort::bitvec(64);
    let p = terms.mk_var("before_promotion_p", sort.clone());
    let q = terms.mk_var("before_promotion_q", sort);
    let pq = terms.mk_app(Symbol::named("bvult"), [p, q], Sort::Bool);
    let qp = terms.mk_app(Symbol::named("bvult"), [q, p], Sort::Bool);
    let clause = vec![terms.mk_not_raw(pq), terms.mk_not_raw(qp)];
    assert!(ay_proof::bv_bitblast_requires_proof_producer(
        &executor.ctx.terms,
        &clause
    ));
    clause
}

/// A proof the strict checker rejects whose only Generic lemma is
/// [`producer_lemma`], plus, when `unit` is set, a one-literal Generic lemma
/// the promotion may yet make publishable.
fn awaiting_promotion(executor: &mut Executor, unit: bool) -> Proof {
    let clause = producer_lemma(executor);
    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("bv", clause.clone(), TheoryLemmaKind::Generic);
    if unit {
        proof.add_theory_lemma_with_kind("bv", vec![clause[0]], TheoryLemmaKind::Generic);
    }
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    proof
}

fn before_promotion(executor: &mut Executor, incumbent: &Proof) -> Proof {
    let mut proof = incumbent.clone();
    executor.promote_bv_guarded_collapse_before_promotion(&mut proof);
    proof
}

fn has_generic_lemma(proof: &Proof) -> bool {
    proof.steps.iter().any(|step| {
        matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::Generic,
                ..
            }
        )
    })
}

/// The one-literal `BvBitBlast` lemma refuting an assumed raw root.
fn refutes_an_assumed_root(executor: &Executor, proof: &Proof) -> bool {
    proof.steps.iter().any(|step| match step {
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::BvBitBlast,
            clause,
            ..
        } => matches!(clause.as_slice(), [literal] if matches!(
            executor.ctx.terms.get(*literal),
            TermData::Not(root) if super::super::proof_already_assumes(proof, *root)
        )),
        _ => false,
    })
}

fn assert_complete_scoped_clean(executor: &mut Executor, proof: &Proof) {
    assert!(Executor::proof_derives_empty_clause(proof));
    assert!(executor
        .check_proof_strict_with_datatypes(proof)
        .is_ok_and(|quality| quality.is_complete()));
    ay_proof::validate_reachable_assumes_in_problem_scope(
        proof,
        &executor.proof_export_scope_assertions(),
    )
    .expect("every reachable assumption belongs to the actual source scope");
    assert!(executor.proof_renders_without_unproved_step(proof));
}

#[test]
fn supported_array_read_refutations_remain_complete_scoped_and_publishable() {
    for problem in [ARRAY_ROOT, ARRAY_READ_SINGLE] {
        let mut executor = solved(problem);
        let incumbent = awaiting_promotion(&mut executor, false);
        assert!(executor.bv_promotion_leaves_known_wire_gap(&incumbent));
        let replaced = before_promotion(&mut executor, &incumbent);
        assert!(refutes_an_assumed_root(&executor, &replaced));
        assert!(!has_generic_lemma(&replaced));
        assert_complete_scoped_clean(&mut executor, &replaced);
    }
}

/// `(= m (bvadd (bvmul (bvudiv m n) n) (bvurem m n)))` over 4 bits as the
/// positive unit `BvBitBlast` lemma the screen admits: only the complete
/// bit-blast spells it, and it does.
fn admitted_lemma(executor: &mut Executor) -> Proof {
    let terms = &mut executor.ctx.terms;
    let m = terms.mk_var("before_promotion_m", Sort::bitvec(4));
    let n = terms.mk_var("before_promotion_n", Sort::bitvec(4));
    let mut op =
        |name: &str, args: [TermId; 2]| terms.mk_app(Symbol::named(name), args, Sort::bitvec(4));
    let quotient = op("bvudiv", [m, n]);
    let product = op("bvmul", [quotient, n]);
    let remainder = op("bvurem", [m, n]);
    let sum = op("bvadd", [product, remainder]);
    let identity = terms.mk_app(Symbol::named("="), [m, sum], Sort::Bool);
    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("bv", vec![identity], TheoryLemmaKind::BvBitBlast);
    proof
}

/// The trigger's screen half. Every proof above also carries a `trust` step,
/// a gap whatever the promotion decides; here nothing else is one. Promoted,
/// the producer's multi-literal lemma is a known wire gap by itself (the
/// screen's bit-blast question spells unit lemmas only:
/// `ay_proof::alethe_printer::complete_blast::clause`), so the trigger holds
/// for a proof whose every other step the screen admits. A lowering that let
/// the screen admit such a lemma would turn the trigger off here.
#[test]
fn the_promoted_producer_lemma_is_the_screened_gap_by_itself() {
    let mut executor = solved(ARRAY_ROOT);
    let admitted = admitted_lemma(&mut executor);
    assert!(!executor.proof_has_known_wire_gap(&admitted));
    assert!(!executor.bv_promotion_leaves_known_wire_gap(&admitted));
    let clause = producer_lemma(&mut executor);
    let mut promoted = admitted.clone();
    promoted.add_theory_lemma_with_kind("bv", clause.clone(), TheoryLemmaKind::BvBitBlast);
    assert!(executor.proof_has_known_wire_gap(&promoted));
    let mut incumbent = admitted;
    incumbent.add_theory_lemma_with_kind("bv", clause, TheoryLemmaKind::Generic);
    assert!(executor.bv_promotion_leaves_known_wire_gap(&incumbent));
}

/// The trigger's twin: a one-literal Generic lemma the promotion may make
/// publishable keeps the usual order, as does a proof with no Generic lemma.
#[test]
fn a_lemma_the_promotion_may_settle_keeps_the_usual_order() {
    let mut executor = solved(ARRAY_ROOT);
    let incumbent = awaiting_promotion(&mut executor, true);
    assert!(!executor.bv_promotion_leaves_known_wire_gap(&incumbent));
    assert_eq!(
        format!("{:?}", before_promotion(&mut executor, &incumbent).steps),
        format!("{:?}", incumbent.steps)
    );
    let mut settled = Proof::new();
    settled.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    assert!(!executor.bv_promotion_leaves_known_wire_gap(&settled));
}

/// A deferred stage must not turn an unsupported incumbent into a claimed
/// complete proof. The cascade's candidate is checked on its own merits;
/// exact native step ordering is not publication authority.
#[test]
fn a_decision_the_promotion_may_change_is_left_to_the_cascade() {
    for problem in [PURE_BV, ARRAY_READ_JOINT] {
        let mut executor = solved(problem);
        let incumbent = awaiting_promotion(&mut executor, false);
        assert!(executor.bv_promotion_leaves_known_wire_gap(&incumbent));
        assert_eq!(
            executor.guarded_collapse_follows_any_promotion(&incumbent),
            problem != PURE_BV,
            "{problem}"
        );
        let deferred = before_promotion(&mut executor, &incumbent);
        assert!(has_generic_lemma(&deferred), "{problem}");
        assert!(executor
            .check_proof_strict_with_datatypes(&deferred)
            .is_err());
        let mut repaired = incumbent.clone();
        assert!(
            executor.promote_bv_guarded_collapse(&mut repaired, GuardedCollapseStage::Cascade),
            "{problem}"
        );
        assert!(!has_generic_lemma(&repaired), "{problem}");
        assert_eq!(
            executor.proof_renders_without_unproved_step(&repaired),
            problem == PURE_BV,
            "{problem}"
        );
    }
}

/// A pure bit-vector root that holds on its own.
const SATISFIABLE_BV: &str = "(declare-const sx (_ BitVec 8))
(assert (bvuge (bvadd #x08 sx) sx))";

/// A pure bit-vector root that is contradictory on its own.
const CONTRADICTORY_BV: &str = "(declare-const rx (_ BitVec 8))
(declare-const ry (_ BitVec 8))
(assert (not (= (bvadd rx ry) (bvadd ry rx))))";

/// An array-read root that holds on its own; its candidate prints a `hole`
/// and the strict checker rejects it.
const SATISFIABLE_READ: &str = "(declare-const sm (Array (_ BitVec 8) (_ BitVec 8)))
(declare-const si (_ BitVec 8))
(assert (= (bvmul (select sm si) (select sm si)) #x04))";

/// [`ARRAY_READ_SINGLE`]'s contradictory root. Its observed document now
/// has a checked opaque-array-word lowering; unobserved policy is separate.
const CONTRADICTORY_READ: &str = "(declare-const hm (Array (_ BitVec 8) (_ BitVec 8)))
(declare-const hi (_ BitVec 8))
(assert (= (bvmul (select hm hi) (select hm hi)) #x02))";

/// [`ARRAY_ROOT`] with `extra` declared and asserted ahead of (`ahead`) or
/// after its own root.
fn array_root_with(extra: &str, ahead: bool) -> String {
    let declarations = "(declare-const mem_default (_ BitVec 8))\n";
    assert!(ARRAY_ROOT.contains(declarations));
    if ahead {
        ARRAY_ROOT.replacen(declarations, &format!("{declarations}{extra}\n"), 1)
    } else {
        ARRAY_ROOT.replacen("(check-sat)", &format!("{extra}\n(check-sat)"), 1)
    }
}

/// The authored roots `proof` assumes, as printed, or `None` when `proof`
/// is still `incumbent`.
fn installed(executor: &Executor, proof: &Proof, incumbent: &Proof) -> Option<Vec<String>> {
    (format!("{:?}", proof.steps) != format!("{:?}", incumbent.steps)).then(|| {
        proof
            .steps
            .iter()
            .filter_map(|step| match step {
                ProofStep::Assume(term) => {
                    Some(ay_proof::format_term_alethe(&executor.ctx.terms, *term))
                }
                _ => None,
            })
            .collect()
    })
}

/// What the collapse installs over `problem`'s roots at `stage` (the stage
/// before the promotion through its entry point), from a fresh solve.
fn collapse(problem: &str, proofs: bool, stage: GuardedCollapseStage) -> Option<Vec<String>> {
    let mut executor = solved_with(problem, proofs);
    let incumbent = awaiting_promotion(&mut executor, false);
    assert!(executor.guarded_collapse_follows_any_promotion(&incumbent));
    let mut proof = incumbent.clone();
    if stage == GuardedCollapseStage::BeforePromotion {
        executor.promote_bv_guarded_collapse_before_promotion(&mut proof);
    } else {
        let _replaced = executor.promote_bv_guarded_collapse(&mut proof, stage);
    }
    installed(&executor, &proof, &incumbent)
}

/// Each stage may choose any refuted authored root. Publication requires a
/// complete proof over the actual input scope for every side-root ordering.
#[test]
fn side_root_orderings_keep_complete_scoped_publishable_refutations() {
    for (extra, ahead) in [
        (SATISFIABLE_BV, true),
        (CONTRADICTORY_BV, true),
        (SATISFIABLE_READ, true),
        (CONTRADICTORY_READ, false),
        (CONTRADICTORY_READ, true),
    ] {
        let problem = array_root_with(extra, ahead);
        for stage in [
            GuardedCollapseStage::BeforePromotion,
            GuardedCollapseStage::Cascade,
        ] {
            let mut executor = solved_with(&problem, true);
            let incumbent = awaiting_promotion(&mut executor, false);
            let mut proof = incumbent;
            if stage == GuardedCollapseStage::BeforePromotion {
                executor.promote_bv_guarded_collapse_before_promotion(&mut proof);
            } else {
                executor.promote_bv_guarded_collapse(&mut proof, stage);
            }
            assert_complete_scoped_clean(&mut executor, &proof);
        }
    }
}

#[test]
fn satisfiable_array_read_is_not_a_refutation() {
    let mut executor = Executor::new();
    executor.set_produce_proofs(true);
    let outputs = executor
        .execute_all(&ay_frontend::parse(&format!("{SATISFIABLE_READ}(check-sat)")).unwrap())
        .unwrap();
    assert_eq!(outputs, ["sat"]);
    assert!(executor.last_unsat_certificate.is_none());
    assert!(executor.last_proof().is_none());
}

/// With no proof document observable, the cascade's decisions never turn on
/// the incumbent, and the stage takes every one of them.
#[test]
fn without_an_observable_document_the_stage_is_the_cascades_walk() {
    for (extra, ahead) in [
        (CONTRADICTORY_READ, true),
        (SATISFIABLE_READ, true),
        (CONTRADICTORY_READ, false),
    ] {
        let problem = array_root_with(extra, ahead);
        assert_eq!(
            collapse(&problem, false, GuardedCollapseStage::BeforePromotion),
            collapse(&problem, false, GuardedCollapseStage::Cascade),
            "{extra} ahead={ahead}"
        );
    }
}

/// [`ARRAY_ROOT`]'s root behind the nullary macro `aggregate_root`, asserted
/// after a pure bit-vector root that holds: the pure bit-vector ground
/// closure, which passes over a macro, sees a pure bit-vector query.
fn array_root_behind_a_macro() -> String {
    assert_eq!(ARRAY_ROOT.matches("(assert ").count(), 1);
    ARRAY_ROOT
        .replacen("(assert ", "(define-fun aggregate_root () Bool ", 1)
        .replacen(
            "(check-sat)",
            &format!("{SATISFIABLE_BV}\n(assert aggregate_root)\n(check-sat)"),
            1,
        )
}

/// A pure bit-vector root that is contradictory on its own, beside an
/// integer root: no authored root reads an array.
const BV_BESIDE_INT: &str = "(set-logic ALL)
(declare-const n Int)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (> n 0))
(assert (not (= (bvadd x y) (bvadd y x))))
(check-sat)
";

/// The stage's entry gates. The cascade's guarded collapse replaces each
/// proof below, but the stage waits for it: an authored `false` premise is
/// refuted ahead of the cascade, the pure bit-vector ground closure goes
/// ahead of it, and a query whose roots read no array is not the stage's.
#[test]
fn the_stage_waits_where_the_cascade_may_not_reach_the_collapse_first() {
    for problem in [
        array_root_with("(assert false)", true),
        array_root_behind_a_macro(),
        BV_BESIDE_INT.to_string(),
    ] {
        let mut executor = solved(&problem);
        let incumbent = awaiting_promotion(&mut executor, false);
        assert!(executor.bv_promotion_leaves_known_wire_gap(&incumbent));
        assert!(!executor.guarded_collapse_follows_any_promotion(&incumbent));
        assert_eq!(
            format!("{:?}", before_promotion(&mut executor, &incumbent).steps),
            format!("{:?}", incumbent.steps),
            "{problem}"
        );
        let mut repaired = incumbent.clone();
        assert!(
            executor.promote_bv_guarded_collapse(&mut repaired, GuardedCollapseStage::Cascade),
            "{problem}"
        );
    }
}
