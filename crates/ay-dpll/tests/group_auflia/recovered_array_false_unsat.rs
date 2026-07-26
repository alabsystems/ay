// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Canonical regressions recovered from the June 2026 array-soundness campaign.
//!
//! Each minimized formula has the reference verdict `sat`.  They previously
//! exposed false-UNSAT paths in exact-select model equalities or quantified
//! array-alias preprocessing.  Keep the formulas inline and minimized so the
//! regression does not depend on a copied scratch corpus.

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};

const EXACT_SELECT_MINIMAL: &str = r#"
(set-logic ALL)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-const d U)
(declare-fun fa (U) (Array Int Int))
(declare-fun ga (U) Int)
(declare-fun toarr (Int) (Array Int Int))
(assert (= (toarr 0) (fa a)))
(assert (= 2 (select (fa a) (ga b))))
(assert (= 3 (select (fa d) (ga b))))
(assert (= 4 (select (fa b) (ga c))))
(check-sat)
"#;

const EXACT_SELECT_VERIFICATION_CONSUMER_SHAPE: &str = r#"
(set-logic ALL)
(declare-fun seq_array ((Seq Int)) (Array Int Int))
(declare-fun seq_len ((Seq Int)) Int)
(declare-fun seq_offset ((Seq Int)) Int)
(declare-fun seq_index_logic ((Seq Int) Int) Int)
(declare-fun to_utf8 (Int) (Seq Int))
(declare-const seq_empty (Seq Int))
(declare-const s_view (Seq Int))
(declare-fun r1 () (Seq Int))
(assert (= ((as const (Array Int Int)) 0) (seq_array seq_empty)))
(assert (forall ((s (Seq Int)) (i Int))
  (= (select (seq_array s) (+ (seq_offset s) i)) (seq_index_logic s i))))
(assert (= 2 (seq_len (to_utf8 195))))
(assert (= 195 (select (seq_array s_view) (seq_offset s_view))))
(assert (= 1 (seq_len s_view)))
(assert (= 0 (seq_offset s_view)))
(assert (or (not (= 1 (seq_len s_view)))
            (not (= 2 (seq_len (to_utf8
              (select (seq_array s_view) (seq_offset s_view))))))
            (and (= 0 (seq_len r1))
                 (= ((as const (Array Int Int)) 0) (seq_array r1))
                 (= 0 (seq_offset r1))
                 (= seq_empty r1))))
(assert (or (not (= (seq_array s_view) (seq_array r1)))
            (not (= (seq_len s_view) (seq_len r1)))
            (not (= (seq_offset s_view) (seq_offset r1)))))
(check-sat)
"#;

const QUANTIFIED_ARRAY_ALIAS_MINIMAL: &str = r#"
(set-logic ALL)
(declare-const a (Array Int Int))
(declare-const c (Array Int Int))
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (= (select c (+ 0 x)) (f x))))
(assert (= a c))
(check-sat)
"#;

#[test]
fn recovered_reference_sat_array_regressions() {
    for (label, smt) in [
        ("false_unsat_QF_minimal", EXACT_SELECT_MINIMAL),
        (
            "ay_false_unsat_clean",
            EXACT_SELECT_VERIFICATION_CONSUMER_SHAPE,
        ),
        ("conflict2_MINIMAL", QUANTIFIED_ARRAY_ALIAS_MINIMAL),
    ] {
        let outcome = run_executor_smt_with_timeout(smt, 10)
            .unwrap_or_else(|error| panic!("{label}: execution failed: {error}"));
        assert_eq!(
            outcome,
            SolverOutcome::Sat,
            "{label}: historical reference verdict is SAT; AY must not regress"
        );
    }
}

/// Maintained replacement for the recovered `fuzz_constarr_qsel.py` campaign.
///
/// Every generated instance has an explicit model: `a`, `b`, `c`, and `d` are
/// distinct; each relevant `fa` application is fixed to a concrete store over a
/// constant array; and `hb` can interpret the universal select bridge exactly.
/// The parameter sweep therefore needs no external reference solver.  `unknown`
/// remains a sound incomplete answer, but `unsat` is necessarily a regression.
#[test]
fn planted_sat_exact_select_variants_never_report_unsat() {
    for seed in 0..12 {
        let default = seed % 3;
        let index_a = seed % 5;
        let index_b = (seed * 3 + 1) % 5;
        let value_a = seed + 10;
        let value_b = seed + 30;
        let value_d = seed + 50;
        let smt = format!(
            r#"
(set-logic ALL)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-const d U)
(declare-fun fa (U) (Array Int Int))
(declare-fun ga (U) Int)
(declare-fun hb (U Int) Int)
(declare-fun toarr (Int) (Array Int Int))
(assert (distinct a b c d))
(assert (= (ga b) {index_a}))
(assert (= (ga c) {index_b}))
(assert (= (fa a)
  (store ((as const (Array Int Int)) {default}) {index_a} {value_a})))
(assert (= (fa b)
  (store ((as const (Array Int Int)) {default}) {index_b} {value_b})))
(assert (= (fa d)
  (store ((as const (Array Int Int)) {default}) {index_a} {value_d})))
(assert (= (toarr 0) (fa a)))
(assert (forall ((u U) (i Int))
  (= (select (fa u) i) (hb u i))))
(assert (= {value_a} (select (fa a) (ga b))))
(assert (= {value_d} (select (fa d) (ga b))))
(assert (= {value_b} (select (fa b) (ga c))))
(check-sat)
"#
        );

        let outcome = run_executor_smt_with_timeout(&smt, 10)
            .unwrap_or_else(|error| panic!("seed {seed}: execution failed: {error}"));
        assert!(
            matches!(outcome, SolverOutcome::Sat | SolverOutcome::Unknown),
            "seed {seed}: planted model proves SAT, but AY returned {outcome:?}"
        );
    }
}
