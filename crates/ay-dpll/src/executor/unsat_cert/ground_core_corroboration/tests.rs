// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pins for step (4)'s authored-ground-core corroboration.

use ay_frontend::parse;

use crate::executor::Executor;

/// Two datatypes that both declare `fld_len`/`fld_data` (so the second pair
/// gets `__ay_overload_N` core identities), a nested constant/store array
/// value, a bound-reading universal over it, and a ground query: the shape of
/// `model_checker_consumer_quantified_counterexample/nested_query_false_unsat`, 64-bit
/// indices and 8-bit cells like the row, scaled down to two rows.
///
/// Row 1's cells are all `#x07` by the fact's own constant array. With
/// `forall_cell = #x07` and `query_cell = #x07` the GROUND conjuncts alone are
/// UNSAT. The 64-bit indices are load-bearing for timing, not for the verdict:
/// an 8-bit twin took 2.4 s on an idle slow core and answered `unknown` with
/// four copies sharing that core (its ground-core probe runs near its 2 s
/// budget), while this one prunes to 37 terms, answers in 0.45 s and stays
/// `unsat` with eight copies sharing the core.
fn nested_record_script(forall_cell: &str, query_cell: &str) -> String {
    nested_record_script_with(Some(forall_cell), query_cell)
}

/// The same fixture, and with `forall_cell = None` its authored ground core
/// alone (the universal dropped).
fn nested_record_script_with(forall_cell: Option<&str>, query_cell: &str) -> String {
    let universal = forall_cell.map_or_else(String::new, |cell| {
        format!(
            "(assert (forall ((r (_ BitVec 64)) (c (_ BitVec 64)))
               (=> (and (bvult r (fld_len fact_outer))
                        (bvult c (fld_len (select (fld_data fact_outer) r))))
                   (= (select (fld_data (select (fld_data fact_outer) r)) c) {cell}))))"
        )
    });
    format!(
        "(set-logic ALL)
         (declare-datatype Inner ((mkInner
           (fld_len (_ BitVec 64)) (fld_data (Array (_ BitVec 64) (_ BitVec 8))))))
         (declare-datatype Outer ((mkOuter
           (fld_len (_ BitVec 64)) (fld_data (Array (_ BitVec 64) Inner)))))
         (declare-const fact_outer Outer)
         (declare-const query_outer Outer)
         (assert (= fact_outer
           (let ((cells ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x07)))
             (mkOuter (_ bv2 64)
               (store ((as const (Array (_ BitVec 64) Inner)) (mkInner (_ bv0 64) cells))
                      (_ bv1 64) (mkInner (_ bv3 64) cells))))))
         {universal}
         (assert (= query_outer fact_outer))
         (assert (bvult (_ bv1 64) (fld_len query_outer)))
         (assert (bvult (_ bv2 64) (fld_len (select (fld_data query_outer) (_ bv1 64)))))
         (assert (distinct
           (select (fld_data (select (fld_data query_outer) (_ bv1 64))) (_ bv2 64))
           {query_cell}))
         (check-sat)"
    )
}

/// Solve `script` on a plain `Executor` (the corpus gate's
/// `test_carcara_model_checker_consumer_unsupported_rows_fail_closed` route) and return the
/// executor with its first answer.
fn solve(script: &str) -> (Executor, String) {
    let commands = parse(script).expect("fixture parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("fixture executes");
    let verdict = outputs.first().cloned().unwrap_or_default();
    (exec, verdict)
}

fn plain_verdict(script: &str) -> String {
    solve(script).1
}

/// THE REGRESSION, RE-PINNED (#nested-array-quarantine-datatype-fields). The
/// ground conjuncts refute on their own, and d14c2313e made this publish
/// `unsat` through the ground-core leg plus step (4). But that refutation is
/// a read-over-write through `(store (fld_data ..) 1 (mkInner ..))` into the
/// inner cell array: an UNSAT over arrays nested in datatype fields, admitted
/// only on deferred trust (a fresh executor re-deciding it). It published
/// because `StaticFeatures` read the declared carriers as opaque sorts. Now
/// the ground core, solved alone, is withheld by the nested-array quarantine
/// (as the directly nested twin always was), so the ground-core leg records
/// no refutation and the quantified gate keeps its `quantifier-instantiation`
/// unknown. Counterfactual: re-open the carrier bypass and the core solve
/// answers `unsat` and the full query publishes `unsat` again. Step (4)'s
/// ground-core route stays pinned end to end by the nested-array-free twin
/// below.
#[test]
fn a_ground_refutable_nested_record_query_is_withheld_by_the_quarantine() {
    let (core, core_verdict) = solve(&nested_record_script_with(None, "#x07"));
    assert_eq!(
        (
            core_verdict.as_str(),
            core.statistics().get_string("unknown.phase")
        ),
        ("unknown", Some("array-combination-quarantine")),
        "the nested-record ground core must be withheld by the quarantine, not lost"
    );

    let (exec, verdict) = solve(&nested_record_script("#x07", "#x07"));
    let phase = exec.statistics().get_string("unknown.phase");
    assert_eq!(
        (verdict.as_str(), phase),
        ("unknown", Some("quantifier-instantiation")),
        "a trust-only nested-record refutation must stay withheld"
    );
    assert!(
        exec.authored_ground_core_refutation.is_none(),
        "a withheld ground core must not be recorded for step (4)"
    );
}

/// The nested-array-free twin of the fixture above: `Outer` keeps its row
/// lengths and its cells in two FLAT arrays (cell `r*256+c`), so no array sits
/// inside an array's element; the unused `Inner` keeps the overloaded
/// `fld_len` identities. Its ground conjuncts refute on their own
/// (z3: `unsat`); the ground-core leg records that core and step (4)
/// re-decides it rather than the quantified scope, which is d14c2313e's route
/// end to end. The `#x08` twin is satisfiable (z3: `sat`).
fn flat_cells_record_script(forall_cell: &str, query_cell: &str) -> String {
    format!(
        "(set-logic ALL)
         (declare-datatype Inner ((mkInner
           (fld_len (_ BitVec 64)) (fld_data (Array (_ BitVec 64) (_ BitVec 8))))))
         (declare-datatype Outer ((mkOuter
           (fld_len (_ BitVec 64)) (fld_lens (Array (_ BitVec 64) (_ BitVec 64)))
           (fld_cells (Array (_ BitVec 64) (_ BitVec 8))))))
         (declare-const fact_outer Outer)
         (declare-const query_outer Outer)
         (assert (= fact_outer
           (mkOuter (_ bv2 64)
             (store ((as const (Array (_ BitVec 64) (_ BitVec 64))) (_ bv0 64)) (_ bv1 64) (_ bv3 64))
             ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x07))))
         (assert (forall ((r (_ BitVec 64)) (c (_ BitVec 64)))
           (=> (and (bvult r (fld_len fact_outer))
                    (bvult c (select (fld_lens fact_outer) r)))
               (= (select (fld_cells fact_outer) (bvadd (bvmul r (_ bv256 64)) c)) {forall_cell}))))
         (assert (= query_outer fact_outer))
         (assert (bvult (_ bv1 64) (fld_len query_outer)))
         (assert (bvult (_ bv2 64) (select (fld_lens query_outer) (_ bv1 64))))
         (assert (distinct
           (select (fld_cells query_outer) (bvadd (bvmul (_ bv1 64) (_ bv256 64)) (_ bv2 64)))
           {query_cell}))
         (check-sat)"
    )
}

#[test]
fn a_ground_refutable_nested_array_free_record_query_publishes_through_the_ground_core() {
    let (exec, verdict) = solve(&flat_cells_record_script("#x07", "#x07"));
    assert_eq!(verdict, "unsat");
    assert!(
        exec.authored_ground_core_refutation.is_some(),
        "the verdict must come through the recorded authored ground core"
    );
    let sat_verdict = plain_verdict(&flat_cells_record_script("#x07", "#x08"));
    assert!(
        sat_verdict == "sat" || sat_verdict == "unknown",
        "a satisfiable query must stay sat/unknown, got {sat_verdict}"
    );
}

/// THE SAT TWIN. Identical shape, but the queried cell is compared against a
/// value it does not hold, so the problem is satisfiable (z3: sat). Neither
/// the ground-core leg nor the corroboration may manufacture an `unsat`.
#[test]
fn the_satisfiable_twin_never_publishes_unsat() {
    let verdict = plain_verdict(&nested_record_script("#x07", "#x08"));
    assert!(
        verdict == "sat" || verdict == "unknown",
        "a satisfiable query must stay sat/unknown, got {verdict}"
    );
}

/// THE TWIN THAT REACHES THE NEW CODE WITH A SATISFIABLE CORE. The universal
/// claims every occupied cell is `#x08` while the fact's cells are `#x07`, so
/// the whole problem is UNSAT (z3: unsat) but only THROUGH the universal: the
/// ground conjuncts (queried cell `#x07`, compared against `#x08`) are
/// satisfiable. The main solve refutes it and the quantified gate consults the
/// ground-core leg, whose pruned probe answers SAT. A satisfiable core must
/// never be recorded for step (4), and the answer must never be `sat`.
#[test]
fn a_satisfiable_ground_core_is_never_recorded() {
    let (exec, verdict) = solve(&nested_record_script("#x08", "#x08"));
    assert_ne!(
        verdict, "sat",
        "z3 answers unsat on this premise-false twin"
    );
    assert!(
        exec.authored_ground_core_refutation.is_none(),
        "the ground core is satisfiable, so no refutation may be recorded"
    );
}

/// Under `:produce-proofs` the translated artifact is mandatory and the ground
/// refutation has no strict rules, so the verdict stays fail-closed `unknown`:
/// the corroboration is a plain-mode (deferred-trust) route only.
#[test]
fn proof_mode_stays_fail_closed_on_the_ground_refutable_query() {
    let script = format!(
        "(set-option :produce-proofs true)\n{}",
        nested_record_script("#x07", "#x07")
    );
    assert_eq!(plain_verdict(&script), "unknown");
}

/// The recorded core is admitted only as a quantifier-free SUBSET of the
/// strict-proof problem; anything else leaves step (4) on its ordinary scope.
#[test]
fn the_recorded_core_is_used_only_as_a_quantifier_free_premise_subset() {
    let commands = parse(
        "(set-logic ALL)
         (declare-fun p (Int) Bool)
         (declare-const x Int)
         (assert (= x 1))
         (assert (= x 2))
         (assert (forall ((y Int)) (p y)))",
    )
    .expect("fixture parses");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("fixture executes");
    let problem = exec.ctx.assertions.clone();
    let (ground_a, ground_b, universal) = (problem[0], problem[1], problem[2]);

    assert_eq!(
        exec.ground_core_corroboration_scope(&problem),
        None,
        "unset"
    );

    exec.authored_ground_core_refutation = Some(vec![ground_a, ground_b].into_boxed_slice());
    assert_eq!(
        exec.ground_core_corroboration_scope(&problem),
        Some(vec![ground_a, ground_b])
    );

    let foreign = exec.ctx.terms.mk_var("not_a_premise", ay_core::Sort::Bool);
    exec.authored_ground_core_refutation = Some(vec![ground_a, foreign].into_boxed_slice());
    assert_eq!(
        exec.ground_core_corroboration_scope(&problem),
        None,
        "a term the publication never claimed must not be re-decided"
    );

    exec.authored_ground_core_refutation = Some(vec![ground_a, universal].into_boxed_slice());
    assert_eq!(
        exec.ground_core_corroboration_scope(&problem),
        None,
        "a quantified member would re-enter the instantiation heuristic"
    );

    exec.authored_ground_core_refutation = Some(Vec::new().into_boxed_slice());
    assert_eq!(
        exec.ground_core_corroboration_scope(&problem),
        None,
        "empty"
    );
}

/// Step (4) accepts only a fresh executor's UNSAT re-decision: of the recorded
/// core when that core reconfirms, otherwise of the unchanged ordinary scope.
/// A satisfiable recorded core can never make it accept a satisfiable scope.
#[test]
fn reconfirmation_is_an_unsat_re_decision_of_the_core_or_the_ordinary_scope() {
    let commands = parse(
        "(set-logic QF_LIA)
         (declare-const x Int)
         (declare-const y Int)
         (assert (= x 1))
         (assert (= y 2))
         (assert (= x 2))",
    )
    .expect("fixture parses");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("fixture executes");
    let problem = exec.ctx.assertions.clone();
    let (x_is_1, y_is_2, x_is_2) = (problem[0], problem[1], problem[2]);

    exec.authored_ground_core_refutation = Some(vec![x_is_1, y_is_2].into_boxed_slice());
    assert!(
        exec.fresh_executor_corroboration(
            &problem,
            &[x_is_1, y_is_2],
            &[],
            &exec.certification_discharge_controls()
        )
        .is_none(),
        "a satisfiable core and a satisfiable scope must not reconfirm"
    );
    assert!(
        exec.fresh_executor_corroboration(
            &problem,
            &problem,
            &[],
            &exec.certification_discharge_controls()
        )
        .is_some(),
        "a satisfiable core falls back to the ordinary scope unchanged"
    );

    exec.authored_ground_core_refutation = Some(vec![x_is_1, x_is_2].into_boxed_slice());
    assert!(
        exec.fresh_executor_corroboration(
            &problem,
            &[y_is_2],
            &[],
            &exec.certification_discharge_controls()
        )
        .is_some(),
        "an unsatisfiable premise subset reconfirms on its own"
    );
}

/// A recorded core that is UNSAT but NOT a subset of the problem step (4) is
/// certifying (here: it names an assertion the publication does not claim)
/// must never make a satisfiable problem reconfirm. Soundness rests on the
/// subset check, not on where the record came from.
#[test]
fn a_foreign_unsatisfiable_core_cannot_make_a_satisfiable_problem_reconfirm() {
    let commands = parse(
        "(set-logic QF_LIA)
         (declare-const x Int)
         (declare-const y Int)
         (assert (= x 1))
         (assert (= y 2))
         (assert (= x 2))",
    )
    .expect("fixture parses");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("fixture executes");
    let assertions = exec.ctx.assertions.clone();
    let (x_is_1, y_is_2, x_is_2) = (assertions[0], assertions[1], assertions[2]);
    let satisfiable_problem = [x_is_1, y_is_2];

    exec.authored_ground_core_refutation = Some(vec![x_is_1, x_is_2].into_boxed_slice());
    assert_eq!(
        exec.ground_core_corroboration_scope(&satisfiable_problem),
        None,
        "`x = 2` is not a premise of the problem being certified"
    );
    assert!(
        exec.fresh_executor_corroboration(
            &satisfiable_problem,
            &satisfiable_problem,
            &[],
            &exec.certification_discharge_controls()
        )
        .is_none(),
        "an UNSAT core outside the problem must not reconfirm a satisfiable problem"
    );
}

/// The record lives exactly one public solve.
#[test]
fn the_recorded_core_does_not_outlive_its_public_solve() {
    let commands =
        parse("(set-logic QF_LIA) (declare-const x Int) (assert (= x 1))").expect("fixture parses");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("fixture executes");
    let stale = exec.ctx.assertions.clone();
    exec.authored_ground_core_refutation = Some(stale.into_boxed_slice());
    exec.begin_public_solve(false);
    assert!(exec.authored_ground_core_refutation.is_none());
}
