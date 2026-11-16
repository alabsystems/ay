// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_frontend::{parse, Command};

const ORIGINAL: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/external_codegen_actual_e1_local_exit0.smt2"
));

#[test]
fn actual_e1_local_closure_observation() {
    let _probe = ay_core::debug_channel::misc_test_override::set(
        ay_core::debug_channel::misc_cli_flags_with(|flags| flags.probe_cert_reject = true),
    );
    let mut exec = Executor::new();
    for command in parse(ORIGINAL).unwrap() {
        if !matches!(command, Command::CheckSat | Command::Exit) {
            exec.execute_authored(&command).unwrap();
        }
    }
    let source = exec.ctx.assertions_parsed()[0].clone();
    let root = exec.raw_intern_ground_bv_surface(&source).unwrap();
    let mut search = GroundSearch::default();
    exec.register_ground_subterms(&mut search.closure, root)
        .unwrap();
    let conflict = exec.saturate_ground_search(&mut search, &[root], &[]);
    let mut goal = root;
    loop {
        match exec.ctx.terms.get(goal) {
            TermData::App(symbol, args) if symbol.name() == "and" => goal = *args.last().unwrap(),
            TermData::Not(inner) => {
                goal = *inner;
                break;
            }
            _ => panic!("original final conjunct is a negated goal"),
        }
    }
    let body = exec.true_equality_body(goal).unwrap();
    let TermData::App(symbol, args) = exec.ctx.terms.get(body) else {
        panic!("OR body");
    };
    assert_eq!(symbol.name(), "or");
    let member = *args.last().unwrap();
    let (left, right) = decode_eq_local(&exec.ctx.terms, member).unwrap();
    let same = search.closure.same_class(left, right);
    let mut work = MAX_GOAL_WORK;
    let member_holds = exec.ground_goal_holds(&search, member, 0, &mut work, GoalPhase::Final);
    let mut work = MAX_GOAL_WORK;
    let goal_holds = exec.ground_goal_holds(&search, goal, 0, &mut work, GoalPhase::Final);
    println!("ACTUAL_E1_LOCAL closure conflict={conflict:?} nodes={} edges={} facts={} probes={} goal={goal} member={member} lhs={left} rhs={right} same={same} member_holds={member_holds:?} goal_holds={goal_holds:?}",
        search.closure.nodes().len(), search.closure.edges().len(), search.facts.facts().len(), search.probes);
    assert!(
        conflict.is_some(),
        "actual original goal must close from earlier source edges"
    );
    assert!(
        same,
        "actual packed read already reaches the requested source word"
    );
    assert_eq!(member_holds, Some(true));
    assert_eq!(goal_holds, Some(true));
    assert!(
        search
            .read_chains
            .witnesses
            .iter()
            .any(|w| w.skipped.iter().any(|s| s.index_image != s.index)),
        "actual source must exercise checked index representative transport"
    );
    let candidate = exec
        .emit_ground_closure_refutation(&search, conflict.unwrap())
        .unwrap();
    assert!(exec
        .check_proof_strict_derivation_with_datatypes(&candidate)
        .unwrap()
        .is_complete());
    let mut missing_guard = candidate.clone();
    let clause = missing_guard
        .steps
        .iter_mut()
        .find_map(|step| match step {
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::ArrayRowChain,
                clause,
                ..
            } if clause.len() > 1 => Some(clause),
            _ => None,
        })
        .expect("actual skipped-store guard lemma");
    let _ = clause.remove(0);
    assert!(
        exec.check_proof_strict_derivation_with_datatypes(&missing_guard)
            .is_err(),
        "a required ROW guard cannot disappear on the same original source"
    );
}

fn proposed(source: &str) -> (Executor, TermId, Option<Proof>) {
    let mut executor = Executor::new();
    for command in parse(source).unwrap() {
        if !matches!(command, Command::CheckSat | Command::Exit) {
            executor.execute_authored(&command).unwrap();
        }
    }
    let source = executor.ctx.assertions_parsed()[0].clone();
    let root = executor.raw_intern_ground_bv_surface(&source).unwrap();
    let candidate = executor.early_ground_closure_memory_candidate(root);
    (executor, root, candidate)
}

#[test]
fn proved_disjuncts_use_checked_injection_for_nested_and_reversed_goals() {
    let declarations = "(set-logic QF_BV)(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))(declare-const p Bool)(declare-const q Bool)";
    for goal in [
        "(or p (= y x))",
        "(or (not p) (or q (= y x)))",
        "(or (= y x) (= y x))",
    ] {
        let source = format!("{declarations}(assert (and (= x y) (not (= {goal} true))))");
        let (executor, root, candidate) = proposed(&source);
        let candidate = candidate.expect("an earlier proved member entails its disjunction");
        assert!(candidate.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::OrNeg,
                ..
            }
        )));
        assert!(candidate
            .steps
            .iter()
            .all(|step| !matches!(step, ProofStep::Assume(term) if *term != root)));
        assert!(executor
            .check_proof_strict_derivation_with_datatypes(&candidate)
            .unwrap()
            .is_complete());
    }
}

#[test]
fn unknown_or_wrong_disjuncts_do_not_supply_a_fact() {
    let declarations = "(set-logic QF_BV)(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))(declare-const p Bool)";
    for assertion in [
        "(and (= x y) (not (or p (= x (bvadd y #x01)))))",
        "(not (or p (= x y)))",
    ] {
        let source = format!("{declarations}(assert {assertion})");
        let (mut executor, _, candidate) = proposed(&source);
        assert!(candidate.is_none());
        assert!(
            executor.last_proof().is_none()
                && executor.last_proof_raw_original_assertions.is_empty()
        );
        assert_eq!(
            executor
                .execute_authored(&Command::CheckSat)
                .unwrap()
                .as_deref(),
            Some("sat")
        );
    }
}

#[test]
fn disjunct_type_depth_and_work_refusals_do_not_construct_terms() {
    let mut executor = Executor::new();
    let byte = executor.ctx.terms.mk_bitvec(0.into(), 8);
    let malformed = executor
        .ctx
        .terms
        .mk_app(Symbol::named("or"), [byte], Sort::Bool);
    let truth = executor.ctx.terms.true_term();
    let valid = executor
        .ctx
        .terms
        .mk_app(Symbol::named("or"), [truth], Sort::Bool);
    let closure = GroundClosure::default();
    let facts = FactBase::default();
    let before = executor.ctx.terms.len();
    let mut work = MAX_GOAL_WORK;
    assert!(executor
        .proved_goal_disjunct(&closure, &facts, malformed, 0, &mut work)
        .is_none());
    let mut work = 0;
    assert!(executor
        .proved_goal_disjunct(&closure, &facts, valid, 0, &mut work)
        .is_none());
    let mut work = MAX_GOAL_WORK;
    assert!(executor
        .proved_goal_disjunct(&closure, &facts, valid, MAX_GOAL_DEPTH + 1, &mut work)
        .is_none());
    assert_eq!(executor.ctx.terms.len(), before);
}

#[test]
fn coverage_and_injection_share_one_goal_work_allowance() {
    let known = format!("(or (= x x) {})", vec!["q"; 30].join(" "));
    let unknown = format!("(or {})", vec!["q"; 31].join(" "));
    let tail = format!("(or {})", vec!["q"; 27].join(" "));
    let mut members = vec![known];
    members.extend(std::iter::repeat_n(unknown, 126));
    members.push(tail);
    let union = format!("(or {})", members.join(" "));
    let source = format!(
        "(set-logic QF_BV)(declare-const x (_ BitVec 8))
        (declare-const a Bool)(declare-const q Bool)
        (assert (and (= x x) (not (= (or (not a) {union}) true))))"
    );
    let mut exec = Executor::new();
    for command in parse(&source).unwrap() {
        exec.execute_authored(&command).unwrap();
    }
    let authored = exec.ctx.assertions_parsed()[0].clone();
    let root = exec.raw_intern_ground_bv_surface(&authored).unwrap();
    let TermData::App(_, conjuncts) = exec.ctx.terms.get(root) else {
        panic!("root");
    };
    let TermData::Not(goal) = exec.ctx.terms.get(*conjuncts.last().unwrap()) else {
        panic!("negated goal");
    };
    let disjunction = exec.true_equality_body(*goal).unwrap();
    let mut search = GroundSearch::default();
    exec.register_ground_subterms(&mut search.closure, root)
        .unwrap();
    exec.seed_ground_root_facts(&mut search, &[root]).unwrap();
    let mut remaining = MAX_GOAL_WORK;
    assert!(exec
        .ground_boolean_coverage_parts(&search.closure, disjunction, &mut remaining)
        .unwrap()
        .is_none());
    assert_eq!(
        remaining, 3,
        "all4093 actual coverage occurrences are charged"
    );
    assert!(exec
        .proved_goal_disjunct(
            &search.closure,
            &search.facts,
            disjunction,
            0,
            &mut remaining
        )
        .is_none());
    let mut fresh = MAX_GOAL_WORK;
    assert!(
        exec.proved_goal_disjunct(&search.closure, &search.facts, disjunction, 0, &mut fresh)
            .unwrap()
            .is_some(),
        "resetting the budget would admit the same known first member"
    );
    let mut emitter = ClosureEmitter::new(&search);
    assert!(
        exec.emit_ground_goal(&mut emitter, disjunction, 0)
            .is_none(),
        "the public emitter must keep coverage's spent work"
    );
    assert!(exec.last_proof().is_none() && exec.last_proof_raw_original_assertions.is_empty());
}
