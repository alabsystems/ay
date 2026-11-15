// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Verdict-level spec for the demand lane's parked instances
//! (#demand-flush-provenance).
//!
//! The demand lane parks an instance of a self-chaining or bridge-cycle family
//! whose generation is over the frontier, and its flush and fence assert the
//! parked instance as a top-level FACT. That is licensed only for a universal
//! the problem entails. A universal it does not entail (here, one in a
//! disjunct) is a guarded record, never parked: it reaches the guarded lane as
//! `(or (not q) body[t̄])`.
//!
//! A flush used to mark the proof translation incomplete, which sent every
//! later refutation through the quantified-unsat artifact gate; with the proof
//! cycle shed (`--z3-mode`) that gate withheld it. The flush now carries each
//! instance's quantifier and binding, so the marker no longer hides a parked
//! instance that should never have been a fact, and this file pins both sides.
//!
//! The lane belongs to the check-sat that armed it. A refutation that ends with
//! instances still parked leaves them in the lane, and without a `push` the
//! quantifier manager outlives the query, so a later `check-sat-assuming` under
//! different assumptions used to flush them as facts of its own problem. The
//! last group of fixtures pins that.
//!
//! Ground truth for every fixture was checked with z3 4.12.5, with and without
//! MBQI.

/// The length definition sits in a disjunct the model may satisfy with `c`, so
/// the definition is not entailed. Its instance at the minted `(tl l)` has
/// generation 2, over the frontier, so the demand lane met it first. Had it
/// been parked and flushed as a fact, `(len (tl l)) = 1 + (len (tl (tl l)))`
/// would contradict the two pinned lengths below (10 and 0).
/// **GROUND TRUTH: SAT** (`c` true, `len` free).
const GUARDED_SELF_CHAINING_SAT: &str = r#"
(set-logic ALL)
(declare-datatypes ((Lst 0)) (((Nil) (Cons (hd Int) (tl Lst)))))
(declare-fun len (Lst) Int)
(declare-const c Bool)
(declare-const l Lst)
(assert (or c (forall ((x Lst)) (! (= (len x) (ite ((_ is Cons) x) (+ 1 (len (tl x))) 0)) :pattern ((len x))))))
(assert (= l (Cons 1 (Cons 2 (Cons 3 Nil)))))
(assert (= (len l) 7))
(assert (= (len (Cons 2 (Cons 3 Nil))) 10))
(assert (= (len (Cons 3 Nil)) 0))
(check-sat)
"#;

/// `GUARDED_SELF_CHAINING_SAT` with the disjunct forced, so the definition is
/// entailed and its instances are facts. **GROUND TRUTH: UNSAT.**
const GUARDED_SELF_CHAINING: &str = r#"
(set-logic ALL)
(declare-datatypes ((Lst 0)) (((Nil) (Cons (hd Int) (tl Lst)))))
(declare-fun len (Lst) Int)
(declare-const c Bool)
(declare-const l Lst)
(assert (or c (forall ((x Lst)) (! (= (len x) (ite ((_ is Cons) x) (+ 1 (len (tl x))) 0)) :pattern ((len x))))))
(assert (= l (Cons 1 (Cons 2 (Cons 3 Nil)))))
(assert (= (len l) 7))
(assert (= (len (Cons 2 (Cons 3 Nil))) 10))
(assert (= (len (Cons 3 Nil)) 0))
(assert (not c))
(check-sat)
"#;

/// `mut_refs_closures::closure_with_mut_ref_arg_basic`, the first query of the
/// Verus test that z3 4.12.5 refutes and that ay answered `unknown`: z3's unsat
/// core of 16 assertions. Verus's tuple invariant axiom
/// (`has_type` through `tuple%1./tuple%1/0`) arms the demand lane, whose flush
/// used to withhold the refutation in `--z3-mode`. **GROUND TRUTH: UNSAT.**
const VERUS_DEMAND_FLUSH_CLOSURE: &str =
    include_str!("../fixtures/verus_demand_flush_closure.smt2");

/// The same query with the asserted value after the closure call changed from
/// 1 to 2, a genuine verification failure. **GROUND TRUTH: NOT UNSAT** (z3
/// 4.12.5 with Verus's options finds the counterexample: `unknown`).
const VERUS_DEMAND_FLUSH_CLOSURE_SAT: &str =
    include_str!("../fixtures/verus_demand_flush_closure_sat.smt2");

/// Verdicts with the proof cycle shed, the CLI's `--z3-mode` posture.
fn proof_shed_verdicts(smt: &str) -> Vec<String> {
    let commands = ay_frontend::parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = ay_dpll::Executor::new();
    exec.set_competition_mode(true);
    exec.set_timeout(Some(std::time::Duration::from_secs(30)));
    exec.execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}"))
        .iter()
        .map(|line| line.trim().to_string())
        .filter(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .collect()
}

/// An unentailed self-chaining definition is never parked, so no posture
/// refutes the satisfiable fixture.
#[test]
fn a_guarded_family_instance_is_never_flushed_as_a_fact() {
    for results in [
        proof_shed_verdicts(GUARDED_SELF_CHAINING_SAT),
        crate::common::solve_vec(GUARDED_SELF_CHAINING_SAT),
        crate::common::solve_selfcheck_vec(GUARDED_SELF_CHAINING_SAT),
    ] {
        assert!(
            !results.iter().any(|r| r == "unsat"),
            "WRONG ANSWER: GUARDED_SELF_CHAINING_SAT is SATISFIABLE; an instance \
             of a universal in a disjunct reached the solver as a fact. Got \
             {results:?}"
        );
    }
}

/// With the disjunct forced, the same definition is entailed, its instances
/// are facts, and the refutation is published with the proof cycle shed.
#[test]
fn an_entailed_family_still_refutes_through_its_instances() {
    assert_eq!(proof_shed_verdicts(GUARDED_SELF_CHAINING), ["unsat"]);
    for results in [
        crate::common::solve_vec(GUARDED_SELF_CHAINING),
        crate::common::solve_selfcheck_vec(GUARDED_SELF_CHAINING),
    ] {
        assert!(
            !results.iter().any(|r| r == "sat"),
            "WRONG ANSWER: GUARDED_SELF_CHAINING is UNSATISFIABLE; got {results:?}"
        );
    }
}

/// A refutation that needs flushed demand-lane instances is published with the
/// proof cycle shed, and the twin with the failing assertion is never refuted.
#[test]
fn a_refutation_after_a_demand_flush_is_published_in_z3_mode() {
    assert_eq!(proof_shed_verdicts(VERUS_DEMAND_FLUSH_CLOSURE), ["unsat"]);
    for results in [
        proof_shed_verdicts(VERUS_DEMAND_FLUSH_CLOSURE_SAT),
        crate::common::solve_vec(VERUS_DEMAND_FLUSH_CLOSURE_SAT),
    ] {
        assert!(
            !results.iter().any(|r| r == "unsat"),
            "WRONG ANSWER: VERUS_DEMAND_FLUSH_CLOSURE_SAT has a counterexample; \
             got {results:?}"
        );
    }
}

/// Two `check-sat-assuming` queries, no `push`. The length definition is
/// entailed only under the assumption `a`. Under it the demand lane parks two
/// instances over the frontier and the query is refuted at frontier 1 with
/// both still parked. The second query assumes `(not a)`: the definition is
/// no longer entailed, and the lengths it pins contradict it.
/// **GROUND TRUTH (z3 4.12.5): unsat sat.**
const STALE_DEMAND_LANE: &str = r#"
(set-logic ALL)
(declare-datatypes ((Lst 0)) (((Nil) (Cons (hd Int) (tl Lst)))))
(declare-fun len (Lst) Int)
(declare-const a Bool)
(declare-const l Lst)
(assert (=> a (forall ((x Lst)) (! (= (len x) (ite ((_ is Cons) x) (+ 1 (len (tl x))) 0)) :pattern ((len x))))))
(assert (= l (Cons 1 (Cons 2 (Cons 3 Nil)))))
(assert (=> a (= (len l) 7)))
(assert (=> (not a) (and (= (len (Cons 2 (Cons 3 Nil))) 10) (= (len (Cons 3 Nil)) 0) (= (len Nil) 5))))
(check-sat-assuming (a))
(check-sat-assuming ((not a)))
"#;

/// `STALE_DEMAND_LANE` with `a` assumed both times: each query entails the
/// definition and arms a lane of its own. **GROUND TRUTH: unsat unsat.**
const STALE_DEMAND_LANE_TWIN: &str = r#"
(set-logic ALL)
(declare-datatypes ((Lst 0)) (((Nil) (Cons (hd Int) (tl Lst)))))
(declare-fun len (Lst) Int)
(declare-const a Bool)
(declare-const l Lst)
(assert (=> a (forall ((x Lst)) (! (= (len x) (ite ((_ is Cons) x) (+ 1 (len (tl x))) 0)) :pattern ((len x))))))
(assert (= l (Cons 1 (Cons 2 (Cons 3 Nil)))))
(assert (=> a (= (len l) 7)))
(assert (=> (not a) (and (= (len (Cons 2 (Cons 3 Nil))) 10) (= (len (Cons 3 Nil)) 0) (= (len Nil) 5))))
(check-sat-assuming (a))
(check-sat-assuming (a))
"#;

/// Found by fuzzing against z3: a sum definition behind an implication, four
/// assumption sets in a row. The third query repeats the first, after an
/// unsatisfiable second query parked instances.
/// **GROUND TRUTH (z3 4.12.5): sat unsat sat sat.**
const STALE_DEMAND_LANE_FUZZ: &str = r#"
(set-logic ALL)
(declare-datatypes ((Lst 0)) (((Nil) (Cons (hd Int) (tl Lst)))))
(declare-fun sum (Lst) Int)
(declare-const a Bool)
(declare-const b Bool)
(declare-const l Lst)
(assert (=> a (forall ((y Lst)) (! (= (sum y) (ite ((_ is Cons) y) (+ (hd y) (sum (tl y))) 0)) :pattern ((sum y))))))
(assert (= l (Cons 1 (Cons 0 Nil))))
(assert (=> a (= (sum l) 2)))
(assert (=> (not a) (and (= (sum Nil) 2))))
(check-sat-assuming ((not a)))
(check-sat-assuming (a b))
(check-sat-assuming ((not a)))
(check-sat-assuming ((not a) (not b)))
"#;

/// Found by fuzzing against z3: the definition sits in a disjunct.
/// **GROUND TRUTH (z3 4.12.5): unsat sat.**
const STALE_DEMAND_LANE_FUZZ2: &str = r#"
(set-logic ALL)
(declare-datatypes ((Lst 0)) (((Nil) (Cons (hd Int) (tl Lst)))))
(declare-fun sum (Lst) Int)
(declare-const a Bool)
(declare-const b Bool)
(declare-const l Lst)
(assert (or (not a) (forall ((y Lst)) (! (= (sum y) (ite ((_ is Cons) y) (+ (hd y) (sum (tl y))) 0)) :pattern ((sum y))))))
(assert (= l (Cons 3 (Cons 3 (Cons 1 Nil)))))
(assert (=> a (= (sum l) 8)))
(assert (=> (not a) (and (= (sum (Cons 3 (Cons 1 Nil))) 4) (= (sum (Cons 1 Nil)) 5))))
(check-sat-assuming (a b))
(check-sat-assuming ((not a) (not b)))
"#;

/// Each check-sat's verdict with the proof cycle shed, with the number of
/// demand-lane instances that solve left parked.
fn proof_shed_verdicts_and_parked(smt: &str) -> Vec<(String, u64)> {
    let commands = ay_frontend::parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = ay_dpll::Executor::new();
    exec.set_competition_mode(true);
    exec.set_timeout(Some(std::time::Duration::from_secs(30)));
    let mut answers = Vec::new();
    for command in &commands {
        let output = exec
            .execute(command)
            .unwrap_or_else(|err| panic!("execution failed: {err}"));
        let Some(line) = output else { continue };
        let line = line.trim();
        if matches!(line, "sat" | "unsat" | "unknown") {
            let parked = exec
                .statistics()
                .get_int("quantifier.demand.parked_remaining")
                .unwrap_or(0);
            answers.push((line.to_string(), parked));
        }
    }
    answers
}

/// Every answer `ay` commits to must be the reference answer at that position.
fn assert_agrees(fixture: &str, results: &[String], reference: &[&str]) {
    assert_eq!(
        results.len(),
        reference.len(),
        "{fixture}: one answer per check-sat expected, got {results:?}"
    );
    for (index, (got, want)) in results.iter().zip(reference).enumerate() {
        assert!(
            got == "unknown" || got == want,
            "WRONG ANSWER: {fixture} query {} is {want}, ay answered {got} \
             (all answers {results:?})",
            index + 1
        );
    }
}

/// A refutation that leaves demand-lane instances parked must not hand them to
/// the next check-sat. The first query must still leave instances parked, or
/// this fixture no longer reaches the state the second query must not see.
#[test]
fn a_demand_lane_never_outlives_its_check_sat() {
    let answers = proof_shed_verdicts_and_parked(STALE_DEMAND_LANE);
    assert_eq!(answers.len(), 2, "two check-sat-assuming, got {answers:?}");
    assert_eq!(
        answers[0].0, "unsat",
        "STALE_DEMAND_LANE query 1 is a demand-lane refutation; got {answers:?}"
    );
    assert!(
        answers[0].1 > 0,
        "STALE_DEMAND_LANE query 1 no longer ends with instances parked, so the \
         fixture no longer exercises a parked lane; got {answers:?}"
    );
    let verdicts: Vec<String> = answers.into_iter().map(|(verdict, _)| verdict).collect();
    for results in [
        verdicts,
        crate::common::solve_vec(STALE_DEMAND_LANE),
        crate::common::solve_selfcheck_vec(STALE_DEMAND_LANE),
    ] {
        assert_agrees("STALE_DEMAND_LANE", &results, &["unsat", "sat"]);
    }
}

/// The same assumption twice: the second query arms its own lane and is
/// refuted again.
#[test]
fn a_repeated_assumption_refutes_each_time() {
    let answers = proof_shed_verdicts(STALE_DEMAND_LANE_TWIN);
    assert_eq!(answers, ["unsat", "unsat"]);
    for results in [
        crate::common::solve_vec(STALE_DEMAND_LANE_TWIN),
        crate::common::solve_selfcheck_vec(STALE_DEMAND_LANE_TWIN),
    ] {
        assert_agrees("STALE_DEMAND_LANE_TWIN", &results, &["unsat", "unsat"]);
    }
}

/// The two fuzz-found sequences agree with z3 at every answer ay commits to,
/// and each refutation is still published with the proof cycle shed.
#[test]
fn assumption_sequences_after_a_parked_refutation_agree_with_z3() {
    for (fixture, smt, reference) in [
        (
            "STALE_DEMAND_LANE_FUZZ",
            STALE_DEMAND_LANE_FUZZ,
            &["sat", "unsat", "sat", "sat"][..],
        ),
        (
            "STALE_DEMAND_LANE_FUZZ2",
            STALE_DEMAND_LANE_FUZZ2,
            &["unsat", "sat"][..],
        ),
    ] {
        let shed = proof_shed_verdicts(smt);
        assert_agrees(fixture, &shed, reference);
        for (got, want) in shed.iter().zip(reference) {
            if *want == "unsat" {
                assert_eq!(got, want, "{fixture}: refutation lost, got {shed:?}");
            }
        }
        for results in [
            crate::common::solve_vec(smt),
            crate::common::solve_selfcheck_vec(smt),
        ] {
            assert_agrees(fixture, &results, reference);
        }
    }
}
