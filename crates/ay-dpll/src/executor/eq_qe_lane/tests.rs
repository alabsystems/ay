// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! End-to-end tests for the SAT-only equality-QE lane (#eq-qe-lane).
//!
//! Every publishing assertion also reads the lane's own `eq_qe.*`
//! statistics, so a verdict the legacy path happened to reach cannot satisfy
//! a test that is about the lane.

use std::time::Duration;

use ay_frontend::parse;

use crate::Executor;

const QUERY_TIMEOUT: Duration = Duration::from_secs(30);

struct LaneRun {
    verdicts: Vec<String>,
    gate: Option<String>,
    recognized: bool,
    counters: super::EqQeLaneCounters,
}

/// The lane is exercised with the routes that run before it taken out of the
/// way: the QSAT route decides these fixtures first and the lane is its
/// SAT-only fallback (`--no-qsat`), and the qlra lane's nested search runs
/// before this lane and decides most of them itself (`--no-qlra-nested`).
fn lane_alone() -> ay_core::misc_test_override::Guard {
    ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_qsat: true,
        no_qlra_nested: true,
        ..ay_core::misc_cli_flags().clone()
    })
}

fn run_with(smt: &str, z3_mode: bool) -> LaneRun {
    let _lane_alone = lane_alone();
    let commands = parse(smt).expect("parse");
    let mut exec = Executor::new();
    exec.set_timeout(Some(QUERY_TIMEOUT));
    if z3_mode {
        exec.set_competition_mode(true);
        exec.set_retain_parsed_assertions(false);
    }
    let outputs = exec.execute_all(&commands).expect("execute");
    let stats = exec.statistics();
    let text = |key: &str| stats.get_string(key).map(str::to_string);
    LaneRun {
        verdicts: outputs
            .iter()
            .filter(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
            .cloned()
            .collect(),
        gate: text("eq_qe.gate"),
        recognized: stats.extra.contains_key("eq_qe.recognized"),
        counters: exec.eq_qe_lane_counters,
    }
}

fn run(smt: &str) -> LaneRun {
    run_with(smt, true)
}

/// Kopczynski-LOIS `incremental4.smt2` check-sat #746, reduced: a Boolean
/// combination of CLOSED equality sentences under a disjunction. Base
/// answered `unknown (quantifier-unhandled)`: the legacy path proxies every
/// quantifier under the `or`. The first disjunct is valid (take f = g), so
/// the assertion is satisfiable (z3 and cvc5: `sat`).
const CLOSED_COMBINATION: &str = "(set-logic LRA)\
    (assert (or (exists ((f Real) (g Real)) (or (= g f) (exists ((k Real)) (or (= g k) (= f k)))))\
                (and (forall ((f Real) (g Real)) (and (not (= g f))\
                        (forall ((k Real)) (and (not (= g k)) (not (= f k))))))\
                     (exists ((a Real) (b Real)) (and (not (= a b))\
                        (exists ((c Real)) (and (not (= c a)) (not (= c b)))))))))\
    (check-sat)";

#[test]
fn closed_boolean_combination_is_published_sat_by_the_lane() {
    for z3_mode in [true, false] {
        let run = run_with(CLOSED_COMBINATION, z3_mode);
        assert_eq!(run.counters.gate_refused, 0, "z3_mode={z3_mode}");
        assert_eq!(run.verdicts, ["sat"], "z3_mode={z3_mode}");
        assert!(
            run.recognized,
            "z3_mode={z3_mode}: the lane must see the query"
        );
        assert_eq!(
            run.gate.as_deref(),
            Some("confirmed"),
            "z3_mode={z3_mode}: the lane must be the publisher"
        );
    }
}

/// `∃f g. g = f ∨ ∃k. g = k`: an existential nested under a disjunction
/// inside another existential. Valid; base answered
/// `unknown (quantifier-ematching-exists)`.
const NESTED_EXISTS: &str = "(set-logic LRA)\
    (assert (exists ((f Real) (g Real)) (or (= g f) (exists ((k Real)) (= g k)))))\
    (check-sat)";

#[test]
fn nested_existential_is_published_sat_by_the_lane() {
    let run = run(NESTED_EXISTS);
    assert_eq!(run.verdicts, ["sat"]);
    assert_eq!(run.gate.as_deref(), Some("confirmed"));
}

/// `incremental4.smt2` check-sat #1194, reduced: an `∃∀` alternation over a
/// free constant `n` beside a ground distinctness triple. Satisfiable (take
/// `o = n`, `v = w`; z3 and cvc5: `sat`); base answered
/// `unknown (incomplete quantifier-cegqi)`.
const EXISTS_FORALL_1194: &str = "(set-logic LRA)\
    (declare-const n Real) (declare-const a Real) (declare-const b Real) (declare-const c Real)\
    (assert (and (not (= b a)) (not (= b c)) (not (= a c))))\
    (assert (exists ((o Real)) (exists ((v Real) (w Real)) (forall ((q Real))\
        (and (or (and (and (not (= w v)) (not (= w q))) (not (= v q)))\
                 (or (or (= n o) (= n q)) (= o q)))\
             (or (or (or (= w v) (= w q)) (= v q)) (not (= n o))))))))\
    (check-sat)";

#[test]
fn exists_forall_alternation_is_published_sat_by_the_lane() {
    let run = run(EXISTS_FORALL_1194);
    assert_eq!(run.verdicts, ["sat"]);
    assert_eq!(run.gate.as_deref(), Some("confirmed"));
}

/// The kill switch restores the legacy route, which cannot decide this shape:
/// the lane is the only publisher, so the test above is not vacuous.
#[test]
fn kill_switch_restores_the_legacy_unknown() {
    let _guard = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_eq_qe_lane: true,
        no_qsat: true,
        no_qlra_nested: true,
        ..ay_core::MiscCliFlags::default()
    });
    let run = run(EXISTS_FORALL_1194);
    assert!(!run.recognized, "the lane must not run with its switch off");
    assert_eq!(run.counters, super::EqQeLaneCounters::default());
    assert_eq!(run.verdicts, ["unknown"], "legacy route (base behavior)");
}

/// Alternation over free constants, the later-scope shape of the same file:
/// `∀u. ∃w. (w ≠ u ∧ w ≠ c) ∨ (u = c)` is valid over the reals, so with the
/// ground sibling `c ≠ d` the problem is satisfiable.
#[test]
fn forall_exists_over_free_constants_is_published_sat() {
    let smt = "(set-logic LRA)\
        (declare-const c Real) (declare-const d Real)\
        (assert (not (= c d)))\
        (assert (forall ((u Real)) (exists ((w Real)) (or (and (not (= w u)) (not (= w c))) (= u c)))))\
        (check-sat)";
    let run = run(smt);
    assert_eq!(run.verdicts, ["sat"]);
    assert_eq!(run.gate.as_deref(), Some("confirmed"));
}

/// `∃x. x = c ∨ p` eliminates to `true`, so neither `c` nor `p` reaches the
/// ground solve; the gate still has to evaluate the AUTHORED comparison
/// `x = c`, which needs `c` pinned. The lane pins vanished constants.
#[test]
fn vanished_constants_are_pinned_for_the_gate() {
    let smt = "(set-logic LRA)\
        (declare-const c Real) (declare-const p Bool)\
        (assert (exists ((x Real) (y Real)) (and (not (= x y)) (or (= x c) p))))\
        (check-sat)";
    let run = run(smt);
    assert_eq!(run.verdicts, ["sat"]);
    assert_eq!(run.gate.as_deref(), Some("confirmed"));
}

/// NEVER `unsat` from the lane: a false closed sentence eliminates to
/// `false`, the lane's ground solve is `unsat`, and the lane declines. The
/// query must not come back `sat`, and the lane records why it declined.
/// (`∃x. ∀y. x = y` is false over the reals; the depth-2 shape is outside
/// the depth-1 qlra lane, and `run_with` turns the nested search off, which
/// would otherwise decide it first.)
#[test]
fn false_sentence_is_declined_never_published() {
    let smt = "(set-logic LRA)\
        (assert (exists ((x Real)) (forall ((y Real)) (= x y))))\
        (check-sat)";
    let run = run(smt);
    assert_eq!(
        run.counters.ground_unsat, 1,
        "one ground solve per check-sat: an internal retry skips a declined lane ({:?})",
        run.counters
    );
    assert_eq!(
        run.counters.gate_refused, 0,
        "an exact elimination never hands the gate a refutable model"
    );
    assert_ne!(run.verdicts, ["sat"], "a false sentence must never be sat");
    assert_eq!(
        run.counters.refutation_bounds, 0,
        "a single query keeps its whole budget for the legacy refutation"
    );
}

/// In an INCREMENTAL session the same ground refutation bounds the legacy
/// path's remaining time on that check-sat (one uncertifiable refutation
/// must not take every later answer), and the next check-sat still answers.
#[test]
fn ground_refutation_bounds_the_legacy_path_only_when_incremental() {
    let smt = "(set-logic LRA)\
        (push 1)\
        (assert (exists ((x Real)) (forall ((y Real)) (= x y))))\
        (check-sat)\
        (pop 1)\
        (check-sat)";
    let run = run(smt);
    assert!(run.counters.ground_unsat >= 1, "{:?}", run.counters);
    assert!(run.counters.refutation_bounds >= 1, "{:?}", run.counters);
    assert_eq!(run.verdicts.len(), 2, "{:?}", run.verdicts);
    assert_ne!(run.verdicts[0], "sat", "a false sentence must never be sat");
    assert_eq!(run.verdicts[1], "sat", "the empty scope after the pop");
}

/// A ground conflict with a satisfiable quantified sibling: the lane's ground
/// solve is `unsat`, it declines, and the legacy path's ground-core
/// refutation still publishes `unsat` (probe, not pre-empt). The conflict is
/// between bounds, not unit equalities: value propagation in the quantifier
/// preprocessing pipeline refutes `(= c 1.0) (= c 2.0)` before the lane runs.
#[test]
fn declined_lane_leaves_the_legacy_refutation() {
    let smt = "(set-logic LRA)\
        (declare-const c Real)\
        (assert (exists ((x Real)) (not (= x c))))\
        (assert (and (> c 2.0) (< c 1.0)))\
        (check-sat)";
    let run = run(smt);
    assert!(run.counters.ground_unsat >= 1, "{:?}", run.counters);
    assert_eq!(run.verdicts, ["unsat"]);
}

/// Out of the fragment (an order atom over the binder) the lane never
/// engages.
#[test]
fn order_atoms_are_out_of_scope() {
    let smt = "(set-logic LRA)\
        (declare-const c Real)\
        (assert (forall ((x Real)) (or (= x c) (< x c) (> x c))))\
        (check-sat)";
    let run = run(smt);
    assert!(!run.recognized);
    assert_eq!(run.counters.recognized, 0);
}

/// Incremental sessions: the lane runs per check-sat against exactly the
/// live scope. A closed sentence asserted at level 1 is `sat` while live; a
/// ground contradiction pushed above it is refuted (by the legacy path, the
/// lane declines); after popping it the same scope is `sat` again, and a
/// FALSE sentence pushed in a sibling scope is never `sat`.
#[test]
fn incremental_scopes_track_the_live_assertions() {
    let smt = "(set-logic LRA)\
        (declare-const c Real) (declare-const d Real)\
        (push 1)\
        (assert (or (exists ((f Real) (g Real)) (and (not (= f g)) (= f c)))\
                    (forall ((f Real)) (= f d))))\
        (check-sat)\
        (push 1)\
        (assert (= c d))\
        (check-sat)\
        (assert (not (= c d)))\
        (check-sat)\
        (pop 1)\
        (check-sat)\
        (push 1)\
        (assert (forall ((x Real) (y Real)) (= x y)))\
        (check-sat)\
        (pop 1)\
        (check-sat)\
        (pop 1)\
        (check-sat)";
    let commands = parse(smt).expect("parse");
    let mut exec = Executor::new();
    exec.set_timeout(Some(QUERY_TIMEOUT));
    exec.set_competition_mode(true);
    exec.set_retain_parsed_assertions(false);
    let outputs = exec.execute_all(&commands).expect("execute");
    let verdicts: Vec<&str> = outputs
        .iter()
        .map(String::as_str)
        .filter(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .collect();
    assert_eq!(verdicts.len(), 7);
    assert_eq!(verdicts[0], "sat", "live closed-ish sentence: sat");
    assert_eq!(verdicts[1], "sat", "c = d keeps it satisfiable");
    assert_ne!(verdicts[2], "sat", "c = d and c != d is unsat");
    assert_eq!(verdicts[3], "sat", "after pop: sat again");
    assert_ne!(verdicts[4], "sat", "a false sentence in scope");
    assert_eq!(verdicts[5], "sat", "after pop: sat again");
    assert_eq!(verdicts[6], "sat", "empty scope");
}

/// Review reproducer (fuzz `min_flat.smt2`): the lane recognizes the query,
/// its ground problem is `unsat`, and it declines. Base publishes `unsat`
/// through the legacy path. When the lane solved the ground problem IN PLACE,
/// the solve's leftovers (minted terms, fresh-name counters, incremental SAT
/// state) sent the legacy path down a different route that ended `unknown`.
/// The ground probe now runs on a disposable executor and the pass is rolled
/// back, so the legacy path must still publish `unsat`. z3: `unsat`.
const GROUND_UNSAT_DECLINE: &str = "(set-logic LIA)\
    (declare-fun a () Int) (declare-fun b () Int) (declare-fun c () Int) (declare-fun p () Bool)\
    (assert (exists ((b Int)) p))\
    (assert (forall ((z Int) (b Int)) (= (ite (or (distinct (+ c 2) a) (distinct z a))\
        (=> (distinct (+ c 3) z) (distinct z z)) (= 2 b)) p)))\
    (assert (distinct a (+ b 0)))\
    (assert (distinct a c))";

#[test]
fn a_ground_unsat_decline_leaves_the_legacy_refutation_unperturbed() {
    let run = run(&format!("{GROUND_UNSAT_DECLINE}(check-sat)"));
    assert_eq!(run.verdicts, ["unsat"], "base publishes unsat");
    assert_eq!(run.counters.recognized, 1, "{:?}", run.counters);
    assert_eq!(run.counters.ground_unsat, 1, "{:?}", run.counters);
    assert_eq!(run.counters.in_place_declines, 0, "{:?}", run.counters);
}

/// The same reproducer inside a push/pop scope (the in-session form, fuzz
/// `f2_0067` check-sat #4), followed by the empty scope.
#[test]
fn a_ground_unsat_decline_in_a_scope_leaves_the_legacy_refutation_unperturbed() {
    let smt = format!("(push 1){GROUND_UNSAT_DECLINE}(check-sat)(pop 1)(check-sat)");
    let run = run(&smt);
    assert_eq!(run.verdicts, ["unsat", "sat"], "base: unsat, then sat");
    assert_eq!(run.counters.ground_unsat, 1, "{:?}", run.counters);
}

/// What a run leaves behind that the legacy path shapes: the verdict, the
/// term store's size and fresh-name counter, and the SAT search counters.
fn legacy_footprint(smt: &str, lane: bool) -> (Vec<String>, usize, u32, [u64; 3]) {
    let _guard = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_eq_qe_lane: !lane,
        no_qsat: true,
        no_qlra_nested: true,
        ..ay_core::MiscCliFlags::default()
    });
    let commands = parse(smt).expect("parse");
    let mut exec = Executor::new();
    exec.set_timeout(Some(QUERY_TIMEOUT));
    exec.set_competition_mode(true);
    exec.set_retain_parsed_assertions(false);
    let outputs = exec.execute_all(&commands).expect("execute");
    assert_eq!(exec.eq_qe_lane_counters.recognized > 0, lane);
    let stats = exec.statistics();
    (
        outputs,
        exec.ctx.terms.len(),
        exec.ctx.terms.var_counter(),
        [stats.conflicts, stats.decisions, stats.propagations],
    )
}

/// A ground-`unsat` decline is ERASED: with the lane on, the legacy path
/// runs exactly as with the lane switched off — same verdict, same term
/// store, same fresh-name counter, same SAT search. (The in-place ground
/// solve this replaced shifted every later `TermId` and fresh name.)
#[test]
fn a_ground_unsat_decline_is_erased_before_the_legacy_path_runs() {
    let smt = format!("{GROUND_UNSAT_DECLINE}(check-sat)");
    assert_eq!(legacy_footprint(&smt, true), legacy_footprint(&smt, false));
}

/// The lane's ground allowance is an eighth of what remains, capped: a tiny
/// eliminated problem whose split loop blows up (review fuzz `slow3`, 6.2 s
/// ending `unknown`, where base declined in 0.02 s) must not take the time
/// the legacy path needs.
#[test]
fn the_ground_solve_has_its_own_capped_budget() {
    use ay_core::time::Instant;
    let mut exec = Executor::new();
    exec.set_deadline(Some(Instant::now() + Duration::from_secs(8)));
    assert!(exec.eq_qe_ground_budget() <= Duration::from_secs(1));
    exec.set_deadline(Some(Instant::now() + Duration::from_secs(3600)));
    assert_eq!(exec.eq_qe_ground_budget(), super::GROUND_BUDGET_CAP);
    exec.set_deadline(None);
    assert_eq!(exec.eq_qe_ground_budget(), super::GROUND_BUDGET_CAP);
}
