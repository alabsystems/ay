// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Symbolic `fp.to_bv` congruence canaries for ay#8870.
//!
//! Equal FP inputs should force equal `fp.to_sbv` / `fp.to_ubv` outputs.
//! These negated congruence shapes previously returned `unknown` when the
//! FP/BV linker did not prove both symbolic conversions from the shared FP
//! equality. Keep them strict so the completeness gap cannot reopen silently.

mod common;

use common::{run_executor_smt_with_timeout, SolverOutcome};
use ntest::timeout;

const SYMBOLIC_TIMEOUT_SECS: u64 = 15;

const FP_TO_SBV_CONGRUENCE_SYMBOLIC: &str = r#"
    (set-logic QF_BVFP)
    (declare-const x (_ FloatingPoint 5 11))
    (declare-const y (_ FloatingPoint 5 11))
    (assert (= x y))
    (assert (not (= ((_ fp.to_sbv 8) RNE x)
                    ((_ fp.to_sbv 8) RNE y))))
    (check-sat)
"#;

const FP_TO_UBV_CONGRUENCE_SYMBOLIC: &str = r#"
    (set-logic QF_BVFP)
    (declare-const x (_ FloatingPoint 5 11))
    (declare-const y (_ FloatingPoint 5 11))
    (assert (= x y))
    (assert (not (= ((_ fp.to_ubv 8) RNE x)
                    ((_ fp.to_ubv 8) RNE y))))
    (check-sat)
"#;

const FP_TO_UBV_GUARDED_ROUNDTRIP_FALSE_SAT: &str = r#"
    (set-logic QF_BVFP)
    (declare-const a (_ BitVec 1))
    (assert (bvule a (_ bv0 1)))
    (assert (distinct a ((_ fp.to_ubv 1) RTZ ((_ to_fp 5 11) RNE a))))
    (check-sat)
    (get-value (a))
"#;

const FP_TO_SBV_GUARDED_ROUNDTRIP_FALSE_SAT: &str = r#"
    (set-logic QF_BVFP)
    (declare-const a (_ BitVec 13))
    (assert (bvule a (_ bv0 13)))
    (assert (distinct a ((_ fp.to_sbv 13) RTZ ((_ to_fp 5 11) RNE a))))
    (check-sat)
    (get-value (a))
"#;

const FP_TO_UBV_BVADD_PREDICATE_FALSE_SAT: &str = r#"
    (set-logic QF_BVFP)
    (declare-const a (_ BitVec 1))
    (assert (= a #b0))
    (assert (bvule (bvadd a #b1)
                   ((_ fp.to_ubv 1) RTZ ((_ to_fp 5 11) RNE a))))
    (check-sat)
    (get-value (a))
"#;

const FP_TO_UBV_UNSUPPORTED_COMPOSITE_PREDICATE_NOT_SAT: &str = r#"
    (set-logic QF_BVFP)
    (declare-const a (_ BitVec 1))
    (assert (= a #b0))
    (assert (bvule (bvudiv #b1 a)
                   ((_ fp.to_ubv 1) RTZ ((_ to_fp 5 11) RNE a))))
    (check-sat)
    (get-value (a))
"#;

#[test]
#[timeout(20_000)]
fn test_fp_to_sbv_symbolic_congruence_not_sat_8870() {
    let result =
        run_executor_smt_with_timeout(FP_TO_SBV_CONGRUENCE_SYMBOLIC, SYMBOLIC_TIMEOUT_SECS)
            .expect("run symbolic fp.to_sbv congruence canary");
    assert_eq!(
        result,
        SolverOutcome::Unsat,
        "symbolic fp.to_sbv congruence must be proven unsat"
    );
}

#[test]
#[timeout(20_000)]
fn test_fp_to_ubv_symbolic_congruence_not_sat_8870() {
    let result =
        run_executor_smt_with_timeout(FP_TO_UBV_CONGRUENCE_SYMBOLIC, SYMBOLIC_TIMEOUT_SECS)
            .expect("run symbolic fp.to_ubv congruence canary");
    assert_eq!(
        result,
        SolverOutcome::Unsat,
        "symbolic fp.to_ubv congruence must be proven unsat"
    );
}

#[test]
#[timeout(20_000)]
fn test_fp_to_ubv_guarded_roundtrip_bvule_unsat_8870() {
    let result =
        run_executor_smt_with_timeout(FP_TO_UBV_GUARDED_ROUNDTRIP_FALSE_SAT, SYMBOLIC_TIMEOUT_SECS)
            .expect("run guarded fp.to_ubv roundtrip false-sat canary");
    assert_eq!(
        result,
        SolverOutcome::Unsat,
        "guarded fp.to_ubv roundtrip must be unsat; ay previously returned sat with a=#b1 despite bvule a #b0"
    );
}

#[test]
#[timeout(20_000)]
fn test_fp_to_sbv_guarded_roundtrip_bvule_unsat_8870() {
    let result =
        run_executor_smt_with_timeout(FP_TO_SBV_GUARDED_ROUNDTRIP_FALSE_SAT, SYMBOLIC_TIMEOUT_SECS)
            .expect("run guarded fp.to_sbv roundtrip false-sat canary");
    assert_eq!(
        result,
        SolverOutcome::Unsat,
        "guarded fp.to_sbv roundtrip with BV distinct must be unsat"
    );
}

#[test]
#[timeout(20_000)]
fn test_fp_to_ubv_composite_bvadd_predicate_unsat_8870() {
    let result =
        run_executor_smt_with_timeout(FP_TO_UBV_BVADD_PREDICATE_FALSE_SAT, SYMBOLIC_TIMEOUT_SECS)
            .expect("run composite BV predicate false-sat canary");
    assert_eq!(
        result,
        SolverOutcome::Unsat,
        "composite BV operands in FP-linked BV predicates must be bit-blasted, not fresh unconstrained bits"
    );
}

#[test]
#[timeout(20_000)]
fn test_fp_to_ubv_unsupported_composite_bv_predicate_not_sat_8870() {
    let result = run_executor_smt_with_timeout(
        FP_TO_UBV_UNSUPPORTED_COMPOSITE_PREDICATE_NOT_SAT,
        SYMBOLIC_TIMEOUT_SECS,
    )
    .expect("run unsupported composite BV predicate canary");
    assert!(
        matches!(result, SolverOutcome::Unsat | SolverOutcome::Unknown),
        "unsupported composite BV operands must fail closed instead of returning SAT, got {result:?}"
    );
}

/// THE INCREMENTAL VARIANT of ay#8870 — a canary for a bug that does not exist
/// yet, added before the code that could introduce it.
///
/// The six canaries above are all SINGLE `check-sat` scripts: zero `push`/`pop`
/// between them. They pin the congruence for sites registered within ONE solve,
/// which is the only thing that can go wrong while `solve_fp` builds a fresh
/// `FpSolver` every check-sat — the site list starts empty, so every site is
/// re-registered and re-paired.
///
/// That protection evaporates the moment the FP lane becomes incremental.
/// `register_to_bv_unspec_site` (`ay-theories/fp/src/bitblast.rs`) relates each
/// NEW site only to the sites already in `self.to_bv_unspec_sites`, then appends.
/// If a future `IncrementalFpState` retains the CLAUSES but not that site list,
/// a `to_ubv` created in the second check-sat is never related to one created in
/// the first — while the first's clauses are still in the solver — and the two
/// conversions are free to differ under an asserted input equality. That is a
/// wrong `sat`, and it is the same defect ay#8870 fixed, re-opened by
/// incrementality.
///
/// Below, the site for `x` is registered in the base scope and the site for `y`
/// inside a `push`. With `x = y` and `k` pinned to `to_ubv(x)`, congruence forces
/// `to_ubv(y) = k`, so the second query is UNSAT. It passes today; it is designed
/// to FAIL if persistence is added without persisting the site list.
///
/// See the development design notes.
#[test]
#[timeout(30_000)]
fn fp_to_ubv_congruence_survives_a_push_8870_incremental() {
    use ay_dpll::Executor;
    use ay_frontend::parse;

    let script = r#"
        (set-logic QF_BVFP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const y (_ FloatingPoint 5 11))
        (declare-const k (_ BitVec 8))
        (assert (= x y))
        (assert (= k ((_ fp.to_ubv 8) RNE x)))
        (check-sat)
        (push 1)
        (assert (not (= k ((_ fp.to_ubv 8) RNE y))))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(script).expect("script should parse");
    let mut executor = Executor::new();
    let outputs = executor
        .execute_all(&commands)
        .expect("incremental congruence canary should run");

    let verdicts: Vec<&String> = outputs
        .iter()
        .filter(|o| matches!(o.as_str(), "sat" | "unsat" | "unknown"))
        .collect();
    assert_eq!(
        verdicts.len(),
        2,
        "expected exactly two check-sat verdicts, got {outputs:?}"
    );

    assert_eq!(
        verdicts[0], "sat",
        "the base scope alone is satisfiable; if this is not `sat` the fixture no \
         longer registers a to_ubv site before the push and proves nothing"
    );
    assert_eq!(
        verdicts[1], "unsat",
        "x = y forces to_ubv(x) = to_ubv(y) = k, so negating it inside the push is \
         UNSAT. A `sat` here means a to_ubv site created in the second query was \
         never related to the one from the first — ay#8870 re-opened across a \
         scope boundary"
    );
}
