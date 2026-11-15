// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::facts::GroundSearch;
use super::state::{EdgeReason, GroundClosure};
use super::*;
use ay_frontend::parse;

mod boolean_coverage;
mod checked_intrinsics;
mod consumer_whole;
mod offset;
mod operators;
mod outside_range;
mod outside_range_preflight;
mod packing;
mod prefix;
mod read_chain;
mod screen;
mod word_level;
mod worklist;

/// Two aliased carriers of a nested datatype field: a missed write on one
/// side, a different pin of the same cell on the other.
const INNER_MISS: &str = r#"
    (set-option :produce-proofs true)
    (set-logic ALL)
    (declare-datatype Vec ((mk_vec (vec_len (_ BitVec 8)) (vec_data (Array (_ BitVec 8) (_ BitVec 8))))))
    (declare-datatype Term ((mk_term (term_lits Vec))))
    (declare-const a (Array (_ BitVec 8) Term))
    (declare-const b (Array (_ BitVec 8) Term))
    (assert (= a b))
    (assert (= (select (store (vec_data (term_lits (select a #x09))) #x40 #x07) #x41) #x08))
    (assert (= (select (vec_data (term_lits (select b #x09))) #x41) #x09))
    (check-sat)
"#;

/// The newest write hits the read through a closed index spelling.
const NEWEST_HIT: &str = r#"
    (set-option :produce-proofs true)
    (set-logic ALL)
    (declare-datatype Cell ((mk_cell (cell_data (Array (_ BitVec 8) (_ BitVec 8))))))
    (declare-const a (Array (_ BitVec 8) Cell))
    (assert (= (select (store (store (cell_data (select a #x09)) #x40 #x01)
                              (bvadd #x3f #x01) #x02) #x40) #x01))
    (check-sat)
"#;

/// A universal fill pin contradicted at the written index.
const GUARD_INSTANCE: &str = r#"
    (set-option :produce-proofs true)
    (set-logic ALL)
    (declare-const data (Array (_ BitVec 8) (_ BitVec 8)))
    (assert (= data (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x07) #x40 #x08)))
    (assert (forall ((i (_ BitVec 8))) (=> (bvult i #x41) (= (select data i) #x07))))
    (check-sat)
"#;

/// SAT twin of [`INNER_MISS`]: both pins agree.
const INNER_MISS_SAT: &str = r#"
    (set-option :produce-proofs true)
    (set-logic ALL)
    (declare-datatype Vec ((mk_vec (vec_len (_ BitVec 8)) (vec_data (Array (_ BitVec 8) (_ BitVec 8))))))
    (declare-datatype Term ((mk_term (term_lits Vec))))
    (declare-const a (Array (_ BitVec 8) Term))
    (declare-const b (Array (_ BitVec 8) Term))
    (assert (= a b))
    (assert (= (select (store (vec_data (term_lits (select a #x09))) #x40 #x07) #x41) #x08))
    (assert (= (select (vec_data (term_lits (select b #x09))) #x41) #x08))
    (check-sat)
"#;

fn solved(input: &str, expected: &str) -> Executor {
    let commands = parse(input).expect("fixture parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("fixture executes");
    assert_eq!(outputs, vec![expected.to_string()]);
    exec
}

fn placeholder() -> Proof {
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    proof
}

/// Run the lane alone on a rejected placeholder and return what it installed.
fn rebuilt(input: &str) -> (Executor, Proof) {
    let mut exec = solved(input, "unsat");
    let mut proof = placeholder();
    exec.replace_with_raw_authored_ground_closure_refutation(&mut proof);
    let quality = exec
        .check_proof_strict_with_datatypes(&proof)
        .expect("the lane installs only a strictly checked refutation");
    assert!(quality.is_complete(), "no trust or hole step may remain");
    (exec, proof)
}

fn lemma_count(proof: &Proof, wanted: impl Fn(&TheoryLemmaKind, &[TermId]) -> bool) -> usize {
    proof
        .steps
        .iter()
        .filter(|step| matches!(step, ProofStep::TheoryLemma { kind, clause, .. } if wanted(kind, clause)))
        .count()
}

fn intrinsic_count(proof: &Proof, wanted: AletheRule) -> usize {
    proof
        .steps
        .iter()
        .filter(|step| {
            matches!(step,
        ProofStep::Step { rule, .. } if *rule == wanted)
        })
        .count()
}

/// Exercise the mathematically identical general-BV representation through
/// its actual shared checker. New shared wiring can close old packing losses;
/// unsupported forms retain their ordinary expense limits. This is test-only.
fn general_bv_control(proof: &Proof) -> Proof {
    let mut control = proof.clone();
    for step in &mut control.steps {
        if let ProofStep::Step {
            rule,
            clause,
            premises,
            args,
        } = step
        {
            if matches!(
                rule,
                AletheRule::BvReconstructV1 | AletheRule::BvOffsetSpinesV1
            ) {
                assert!(premises.is_empty() && args.is_empty());
                *step = ProofStep::TheoryLemma {
                    theory: "bv".into(),
                    clause: clause.clone(),
                    farkas: None,
                    kind: TheoryLemmaKind::BvBitBlast,
                    lia: None,
                };
            }
        }
    }
    control
}

#[test]
fn explanations_use_only_earlier_edges() {
    let (a, b, c) = (TermId(1), TermId(2), TermId(3));
    let mut closure = GroundClosure::default();
    for term in [a, b, c] {
        assert!(closure.register(term));
    }
    assert!(closure.merge(a, b, EdgeReason::Congruent));
    assert!(closure.merge(b, c, EdgeReason::Congruent));
    assert!(
        !closure.merge(a, c, EdgeReason::Congruent),
        "one class already"
    );
    assert_eq!(closure.path(a, c, 2), Some(vec![0, 1]));
    assert_eq!(closure.path(a, c, 1), None, "edge 1 is outside the limit");
    assert_eq!(closure.path(c, a, 2), Some(vec![1, 0]));
    assert_eq!(closure.path(a, a, 0), Some(Vec::new()));
}

#[test]
fn a_missed_write_under_an_alias_is_refuted_by_row2_and_congruence() {
    let (_, proof) = rebuilt(INNER_MISS);
    assert_eq!(
        lemma_count(&proof, |kind, _| matches!(
            kind,
            TheoryLemmaKind::ArraySelectStore { index_eq: false }
        )),
        1
    );
    assert!(
        lemma_count(&proof, |kind, _| matches!(
            kind,
            TheoryLemmaKind::EufCongruent
        )) >= 3
    );
}

#[test]
fn a_closed_index_spelling_is_evaluated_for_a_guarded_read_hit() {
    let (exec, proof) = rebuilt(NEWEST_HIT);
    let evaluated = lemma_count(&proof, |kind, clause| {
        matches!(kind, TheoryLemmaKind::BvBitBlast)
            && matches!(clause, [literal] if decode_eq_local(&exec.ctx.terms, *literal)
            .is_some_and(|(lhs, _)| matches!(
                exec.ctx.terms.get(lhs),
                TermData::App(symbol, _) if symbol.name() == "bvadd"
            )))
    });
    assert_eq!(evaluated, 1, "the index is joined by one evaluation");
    let guarded = lemma_count(&proof, |kind, clause| {
        matches!(kind, TheoryLemmaKind::ArraySelectStore { index_eq: true }) && clause.len() == 2
    });
    assert_eq!(guarded, 1, "the hit crosses the index equality once");
}

#[test]
fn a_universal_instance_at_the_written_index_is_refuted() {
    let (exec, proof) = rebuilt(GUARD_INSTANCE);
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::ForallInst,
            ..
        }
    )));
    let closed_guard = lemma_count(&proof, |kind, clause| {
        matches!(kind, TheoryLemmaKind::BvBitBlast)
            && matches!(clause, [literal] if matches!(
                exec.ctx.terms.get(*literal),
                TermData::App(symbol, _) if symbol.name() == "bvult"
            ))
    });
    assert_eq!(closed_guard, 1);
}

/// Unsat at `i = 64`, but the guard's bound is the `define-fun` `lim`: the
/// published instance is spelled from the authored body, where `lim` stays a
/// symbol pinned carcara (run without `--apply-function-defs`) cannot unfold.
const MACRO_GUARD: &str = r#"
    (set-option :produce-proofs true)
    (set-logic ALL)
    (define-fun lim () (_ BitVec 64) (_ bv65 64))
    (declare-fun summary (Bool (_ BitVec 64)) (_ BitVec 1))
    (assert (forall ((i (_ BitVec 64))) (=> (bvult i lim) (= (summary false i) (_ bv1 1)))))
    (assert (= (summary false (_ bv64 64)) (_ bv0 1)))
    (check-sat)
"#;

/// NEGATIVE TWIN of the instance path: a universal stated through a source
/// macro is never instantiated, so the lane leaves the proof untouched.
#[test]
fn a_universal_stated_through_a_source_macro_is_not_instantiated() {
    let commands = parse(MACRO_GUARD).expect("fixture parses");
    let mut exec = Executor::new();
    let _ = exec.execute_all(&commands).expect("fixture executes");
    assert!(exec.flat_ground_closure_foralls().is_empty());
    let mut proof = placeholder();
    let before = format!("{:?}", proof.steps);
    exec.replace_with_raw_authored_ground_closure_refutation(&mut proof);
    assert_eq!(format!("{:?}", proof.steps), before);
}

/// NEGATIVE TWIN of the acceptance path: consistent roots are never refuted.
#[test]
fn consistent_roots_leave_the_proof_untouched() {
    let mut exec = solved(INNER_MISS_SAT, "sat");
    let mut proof = placeholder();
    let before = format!("{:?}", proof.steps);
    exec.replace_with_raw_authored_ground_closure_refutation(&mut proof);
    assert_eq!(format!("{:?}", proof.steps), before);
}

fn bv8(exec: &mut Executor, value: i64) -> TermId {
    exec.ctx.terms.mk_bitvec(BigInt::from(value), 8)
}

/// A read-over-write MISS recorded between EQUAL indices is not a theorem;
/// emission must refuse it rather than print a `ROW2` over it.
#[test]
fn a_read_miss_between_equal_indices_is_never_emitted() {
    let mut exec = Executor::new();
    let sort = Sort::array(Sort::bitvec(8), Sort::bitvec(8));
    let base = exec.ctx.terms.mk_var("gc_base", sort);
    let (index, value) = (bv8(&mut exec, 0x40), bv8(&mut exec, 7));
    let store = exec.ctx.terms.mk_app(
        Symbol::named("store"),
        [base, index, value],
        exec.ctx.terms.sort(base).clone(),
    );
    let read = exec
        .ctx
        .terms
        .mk_app(Symbol::named("select"), [store, index], Sort::bitvec(8));
    let base_read = exec
        .ctx
        .terms
        .mk_app(Symbol::named("select"), [base, index], Sort::bitvec(8));
    let equality = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [read, base_read], Sort::Bool);
    let root = exec.ctx.terms.mk_not_raw(equality);
    let mut search = GroundSearch::default();
    for term in [read, base_read, store, base, index, value] {
        search.closure.register(term);
    }
    assert!(search.closure.merge(read, base_read, EdgeReason::ReadMiss));
    let conflict = ClosureConflict::Disequality {
        root,
        equality,
        lhs: read,
        rhs: base_read,
    };
    assert!(exec
        .emit_ground_closure_refutation(&search, conflict)
        .is_none());
}

/// A mis-evaluated closed term yields a candidate that derives the empty
/// clause, and the strict checker, not the producer, refuses it.
#[test]
fn a_mis_evaluated_edge_is_refused_by_the_strict_checker() {
    let mut exec = Executor::new();
    let (one, two, three) = (bv8(&mut exec, 1), bv8(&mut exec, 2), bv8(&mut exec, 3));
    let sum = exec
        .ctx
        .terms
        .mk_app(Symbol::named("bvadd"), [one, one], Sort::bitvec(8));
    let mut search = GroundSearch::default();
    for term in [sum, one, two, three] {
        search.closure.register(term);
    }
    assert!(search.closure.merge(sum, three, EdgeReason::Evaluated));
    assert!(search.closure.merge(sum, two, EdgeReason::Evaluated));
    let candidate = exec
        .emit_ground_closure_refutation(&search, ClosureConflict::ConstantClash(three, two))
        .expect("emission trusts its edges; the checker does not");
    assert!(Executor::proof_derives_empty_clause(&candidate));
    let refusal = exec
        .check_proof_strict_with_datatypes(&candidate)
        .expect_err("1 + 1 = 3 is not a theorem");
    let refusal = refusal.to_string();
    assert!(
        refusal.contains("bv_bitblast") && refusal.contains("falsified"),
        "refused for the forged evaluation itself: {refusal}"
    );
    let mut proof = placeholder();
    let before = format!("{:?}", proof.steps);
    assert!(!exec.commit_raw_ground_closure(&mut proof, candidate, &[]));
    assert_eq!(format!("{:?}", proof.steps), before);
}

/// `branching_vec_query_false` at 8 bits: two record constants aliased to two
/// pinned vectors, queried through field reads in an authored conjunction.
/// Parsed assertions: 0 pin v0, 1 fill v0, 2 pin v1, 3 fill v1, 4 `(= a v0)`,
/// 5 f0, 6 `(= b v1)`, 7 f1, 8 the query.
const RECORD_ALIAS: &str = r#"
    (set-option :produce-proofs true)
    (set-logic ALL)
    (declare-datatype Vec ((mk_vec (vec_len (_ BitVec 8)) (vec_data (Array (_ BitVec 8) (_ BitVec 8))))))
    (declare-const v0 Vec)
    (declare-const f0 (_ BitVec 8))
    (declare-const v1 Vec)
    (declare-const f1 (_ BitVec 8))
    (declare-const a Vec)
    (declare-const b Vec)
    (assert (= v0 (mk_vec #x41 ((as const (Array (_ BitVec 8) (_ BitVec 8))) f0))))
    (assert (forall ((i (_ BitVec 8))) (=> (bvult i (vec_len v0)) (= (select (vec_data v0) i) f0))))
    (assert (= v1 (mk_vec #x41 ((as const (Array (_ BitVec 8) (_ BitVec 8))) f1))))
    (assert (forall ((i (_ BitVec 8))) (=> (bvult i (vec_len v1)) (= (select (vec_data v1) i) f1))))
    (assert (= a v0))
    (assert (= #x07 f0))
    (assert (= b v1))
    (assert (= #x09 f1))
    (assert (and (bvult (_ bv64 8) (vec_len a)) (bvult (_ bv64 8) (vec_len b))
      (= (select (vec_data a) (_ bv64 8)) (select (vec_data b) (_ bv64 8)))))
    (check-sat)
"#;

fn assumed_roots(proof: &Proof) -> Vec<TermId> {
    proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Assume(term) => Some(*term),
            _ => None,
        })
        .collect()
}

fn elaborated_twin(exec: &mut Executor, index: usize) -> TermId {
    let parsed: Vec<FrontendTerm> = exec.ctx.assertions_parsed().to_vec();
    exec.ctx
        .elaborate_surface_subterm(&parsed[index])
        .expect("the assertion elaborates")
}

/// The record equalities and the field-read query enter as their elaborated
/// twins; a pin to a constructor application enters in no form at all.
#[test]
fn record_aliases_are_read_through_their_elaborated_field_twins() {
    let (mut exec, proof) = rebuilt(RECORD_ALIAS);
    let assumed = assumed_roots(&proof);
    for index in [4, 6, 8] {
        let twin = elaborated_twin(&mut exec, index);
        assert!(
            assumed.contains(&twin),
            "assertion {index} is assumed as its twin"
        );
    }
    let parsed: Vec<FrontendTerm> = exec.ctx.assertions_parsed().to_vec();
    assert!(
        exec.raw_intern_surface(&parsed[8]).is_none(),
        "the query has no raw re-intern"
    );
    let pin_twin = elaborated_twin(&mut exec, 0);
    let pin_raw = exec
        .raw_intern_surface(&parsed[0])
        .expect("the pin raw-interns");
    assert!(!assumed.contains(&pin_twin) && !assumed.contains(&pin_raw));
    let instances = proof
        .steps
        .iter()
        .filter(|step| {
            matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::ForallInst,
                    ..
                }
            )
        })
        .count();
    assert_eq!(instances, 2, "one fill instance per vector");
}

/// A record pinned to a constructor APPLICATION, contradicted by a field read:
/// unsat only by selector-over-constructor, which pinned carcara cannot check.
const PINNED_RECORD: &str = r#"
    (set-option :produce-proofs true)
    (set-logic ALL)
    (declare-datatype Vec ((mk_vec (vec_len (_ BitVec 8)) (vec_data (Array (_ BitVec 8) (_ BitVec 8))))))
    (declare-const v Vec)
    (assert (= v (mk_vec #x41 ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x07))))
    (assert (= (vec_len v) #x42))
    (check-sat)
"#;

/// NEGATIVE TWIN of the record path: the pin's field-wise twin is never
/// offered to the search (only the unavailable field read contributes one),
/// so the lane leaves the proof untouched.
#[test]
fn a_record_pinned_to_a_constructor_application_gets_no_twin() {
    let commands = parse(PINNED_RECORD).expect("fixture parses");
    let mut exec = Executor::new();
    let _ = exec.execute_all(&commands).expect("fixture executes");
    let roots = exec.ground_closure_roots().expect("ground roots");
    let pin_twin = elaborated_twin(&mut exec, 0);
    let read_twin = elaborated_twin(&mut exec, 1);
    assert!(!roots.search.contains(&pin_twin));
    assert!(roots.search.contains(&read_twin) && !roots.raw.contains(&read_twin));
    let mut proof = placeholder();
    let before = format!("{:?}", proof.steps);
    exec.replace_with_raw_authored_ground_closure_refutation(&mut proof);
    assert_eq!(format!("{:?}", proof.steps), before);
}

/// NEGATIVE TWIN of the acceptance path: both vectors filled with the same
/// value, so the aliased reads agree and nothing is refuted.
#[test]
fn agreeing_record_aliases_leave_the_proof_untouched() {
    let sat = RECORD_ALIAS.replace("(assert (= #x09 f1))", "(assert (= #x07 f1))");
    let mut exec = solved(&sat, "sat");
    let mut proof = placeholder();
    let before = format!("{:?}", proof.steps);
    exec.replace_with_raw_authored_ground_closure_refutation(&mut proof);
    assert_eq!(format!("{:?}", proof.steps), before);
}

/// A `let`-authored root has no raw re-intern, and its elaborated twin reads
/// no record field: it is not one of the two twin shapes, so the search never
/// sees it (its expansion prints unlike the authored `let`).
const LET_ROOT: &str = r#"
    (set-option :produce-proofs true)
    (set-logic ALL)
    (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
    (assert (let ((y #x01)) (= (select a y) #x02)))
    (assert (= (select a #x01) #x03))
    (check-sat)
"#;

/// NEGATIVE TWIN of the unavailable-raw path: only a twin that reads a record
/// field is offered.
#[test]
fn a_let_root_without_a_field_read_gets_no_twin() {
    let commands = parse(LET_ROOT).expect("fixture parses");
    let mut exec = Executor::new();
    let _ = exec.execute_all(&commands).expect("fixture executes");
    let parsed: Vec<FrontendTerm> = exec.ctx.assertions_parsed().to_vec();
    assert!(exec.raw_intern_surface(&parsed[0]).is_none());
    let let_twin = elaborated_twin(&mut exec, 0);
    let roots = exec.ground_closure_roots().expect("ground roots");
    assert!(!roots.search.contains(&let_twin));
}
