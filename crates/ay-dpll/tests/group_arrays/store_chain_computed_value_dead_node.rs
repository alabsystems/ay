// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! #store-chain-dead-node: a `store` of a COMPUTED value must not be extracted
//! from the stored expression's cached interior-node bits.
//!
//! `(assert (= arr (store a i (bvadd x y))))` with `x`/`y` pinned by their own
//! equalities: preprocessing substitutes the constants in, the `bvadd` node is
//! folded and never constrained, and its bits read back ALL-ZERO. Extraction
//! committed that fabricated `#x00000000` as `arr[i]`, the independent gate then
//! found the definition-derived candidate (the true `#x0000000a`) disagreeing
//! with it, and completion's taint propagation spread `read_conflicted` from
//! `arr` to the innocent store BASE `a`. `array_from_model` refuses a
//! read-conflicted term, so `a` became unresolvable, the defining store
//! expression could not be evaluated, and a TRIVIALLY SATISFIABLE query came
//! back `unknown: model does not pin this leaf`.
//!
//! The operator was irrelevant — `bvadd` degraded exactly as `bvsdiv` did — and
//! a store of a bare VARIABLE did not degrade, which is what made this look like
//! a division-specific incompleteness for so long.

use anyhow::Result;

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};

/// `(store a 0 <expr>)` asserted as the definition of `arr`, with `x = 7`,
/// `y = 3` pinned separately. Every case is satisfiable: nothing constrains
/// `arr` beyond its own definition.
fn store_of(expr: &str) -> String {
    format!(
        r"
        (set-logic ALL)
        (declare-const arr (Array (_ BitVec 64) (_ BitVec 32)))
        (declare-const a (Array (_ BitVec 64) (_ BitVec 32)))
        (declare-const x (_ BitVec 32))
        (declare-const y (_ BitVec 32))
        (assert (= x #x00000007))
        (assert (= y #x00000003))
        (assert (= arr (store a #x0000000000000000 {expr})))
        (check-sat)
        "
    )
}

/// Every BV operator degraded, not just the division family. `bvadd` is the
/// control that proves this was never about division semantics.
#[test]
#[ntest::timeout(60_000)]
fn test_store_of_computed_value_is_sat_for_every_operator() -> Result<()> {
    for expr in [
        "(bvadd x y)",
        "(bvsub x y)",
        "(bvmul x y)",
        "(bvand x y)",
        "(bvshl x y)",
        "(bvudiv x y)",
        "(bvurem x y)",
        "(bvsdiv x y)",
        "(bvsrem x y)",
        "(bvsmod x y)",
    ] {
        let outcome = run_executor_smt_with_timeout(&store_of(expr), 20)?;
        assert_eq!(
            outcome,
            SolverOutcome::Sat,
            "#store-chain-dead-node: `(store a 0 {expr})` is trivially satisfiable; \
             got {outcome:?} (the cached interior-node bits fabricated the cell)",
        );
    }
    Ok(())
}

/// The half that must NOT change: a store of a bare variable always worked, so
/// a fix that merely made the store-chain interpretation disappear would still
/// pass the case above while silently losing this one.
#[test]
#[ntest::timeout(20_000)]
fn test_store_of_plain_variable_is_still_sat() -> Result<()> {
    let outcome = run_executor_smt_with_timeout(&store_of("x"), 10)?;
    assert_eq!(outcome, SolverOutcome::Sat);
    Ok(())
}

/// DISCRIMINATING CONTROL. The extracted cell is still checked: an assertion
/// that CONTRADICTS the computed stored value must stay `unsat`. A fix that
/// simply stopped committing store-chain cells would answer `sat` here.
#[test]
#[ntest::timeout(20_000)]
fn test_computed_store_value_is_still_refuted_when_contradicted() -> Result<()> {
    let query = r"
        (set-logic ALL)
        (declare-const arr (Array (_ BitVec 64) (_ BitVec 32)))
        (declare-const a (Array (_ BitVec 64) (_ BitVec 32)))
        (declare-const x (_ BitVec 32))
        (declare-const y (_ BitVec 32))
        (assert (= x #x00000007))
        (assert (= y #x00000003))
        (assert (= arr (store a #x0000000000000000 (bvadd x y))))
        (assert (not (= (select arr #x0000000000000000) #x0000000a)))
        (check-sat)
        ";
    let outcome = run_executor_smt_with_timeout(query, 10)?;
    assert_eq!(
        outcome,
        SolverOutcome::Unsat,
        "SOUNDNESS: `arr[0]` is forced to `bvadd(7,3) = 0x0a`; denying it is UNSAT",
    );
    Ok(())
}

/// The positive direction of the same cell: reading back the computed value is
/// satisfiable, so the pair pins the cell to exactly `0x0a`.
#[test]
#[ntest::timeout(20_000)]
fn test_computed_store_value_reads_back_as_computed() -> Result<()> {
    let query = r"
        (set-logic ALL)
        (declare-const arr (Array (_ BitVec 64) (_ BitVec 32)))
        (declare-const a (Array (_ BitVec 64) (_ BitVec 32)))
        (declare-const x (_ BitVec 32))
        (declare-const y (_ BitVec 32))
        (assert (= x #x00000007))
        (assert (= y #x00000003))
        (assert (= arr (store a #x0000000000000000 (bvadd x y))))
        (assert (= (select arr #x0000000000000000) #x0000000a))
        (check-sat)
        ";
    assert_eq!(
        run_executor_smt_with_timeout(query, 10)?,
        SolverOutcome::Sat
    );
    Ok(())
}

/// The ORIGINAL model-checker-consumer query this was found in, verbatim: a `simd_div`
/// harness over `i32x2`. `local_5_0`'s divisor lane is all-zero, so
/// `div_by_zero_check_0` is forced TRUE and the final violation disjunction is
/// satisfied — the query is trivially satisfiable and z3 agrees. It answered
/// `unknown` because the UNREAD `local_7_0` definition, whose stored values are
/// `ite`s over the divisor guard, could not be pinned: the `ite` nodes' cached
/// bits were fabricated, conflicted with the definition-derived candidate, and
/// tainted the chain.
#[test]
#[ntest::timeout(60_000)]
fn test_simd_div_harness_query_is_sat() -> Result<()> {
    let query = r"
(set-logic ALL)
(declare-const memory (Array (_ BitVec 64) (_ BitVec 8)))
(declare-const ay_any_0 (_ BitVec 32))
(declare-const |test_simd_div::local_3_0| (Array (_ BitVec 64) (_ BitVec 32)))
(assert (= (select |test_simd_div::local_3_0| #x0000000000000000) ay_any_0))
(assert (= (select |test_simd_div::local_3_0| #x0000000000000001) ay_any_0))
(declare-datatype i32x2 ((i32x2_mk (fld_0 (Array (_ BitVec 64) (_ BitVec 32))))))
(declare-const |test_simd_div::local_2_0| i32x2)
(assert (= |test_simd_div::local_2_0| (i32x2_mk |test_simd_div::local_3_0|)))
(declare-const |test_simd_div::local_4_0| (_ BitVec 32))
(assert (= |test_simd_div::local_4_0| #x00000000))
(declare-const |test_simd_div::local_6_0| (Array (_ BitVec 64) (_ BitVec 32)))
(assert (= (select |test_simd_div::local_6_0| #x0000000000000000) |test_simd_div::local_4_0|))
(assert (= (select |test_simd_div::local_6_0| #x0000000000000001) |test_simd_div::local_4_0|))
(declare-const |test_simd_div::local_5_0| i32x2)
(assert (= |test_simd_div::local_5_0| (i32x2_mk |test_simd_div::local_6_0|)))
(declare-const ay_violation_div_by_zero_check_0 Bool)
(assert (= ay_violation_div_by_zero_check_0 (= (select (fld_0 |test_simd_div::local_5_0|) #x0000000000000000) #x00000000)))
(declare-const ay_violation_overflow_check_simd_div_rem_1 Bool)
(assert (= ay_violation_overflow_check_simd_div_rem_1 (and (= (select (fld_0 |test_simd_div::local_2_0|) #x0000000000000000) #x80000000) (= (select (fld_0 |test_simd_div::local_5_0|) #x0000000000000000) #xffffffff))))
(declare-const ay_assume_ctx_1 Bool)
(assert (= ay_assume_ctx_1 (and (not (= (select (fld_0 |test_simd_div::local_5_0|) #x0000000000000000) #x00000000)) (not (and (= (select (fld_0 |test_simd_div::local_2_0|) #x0000000000000000) #x80000000) (= (select (fld_0 |test_simd_div::local_5_0|) #x0000000000000000) #xffffffff))))))
(declare-const ay_violation_div_by_zero_check_2 Bool)
(assert (= ay_violation_div_by_zero_check_2 (and ay_assume_ctx_1 (= (select (fld_0 |test_simd_div::local_5_0|) #x0000000000000001) #x00000000))))
(declare-const ay_reach_div_by_zero_check_2 Bool)
(assert (= ay_reach_div_by_zero_check_2 ay_assume_ctx_1))
(declare-const ay_violation_overflow_check_simd_div_rem_3 Bool)
(assert (= ay_violation_overflow_check_simd_div_rem_3 (and ay_assume_ctx_1 (and (= (select (fld_0 |test_simd_div::local_2_0|) #x0000000000000001) #x80000000) (= (select (fld_0 |test_simd_div::local_5_0|) #x0000000000000001) #xffffffff)))))
(declare-const ay_reach_overflow_check_simd_div_rem_3 Bool)
(assert (= ay_reach_overflow_check_simd_div_rem_3 ay_assume_ctx_1))
(declare-const ay_assume_ctx_2 Bool)
(assert (= ay_assume_ctx_2 (and ay_assume_ctx_1 (and (not (= (select (fld_0 |test_simd_div::local_5_0|) #x0000000000000001) #x00000000)) (not (and (= (select (fld_0 |test_simd_div::local_2_0|) #x0000000000000001) #x80000000) (= (select (fld_0 |test_simd_div::local_5_0|) #x0000000000000001) #xffffffff)))))))
(declare-const simd_divrem_poison_3 (_ BitVec 32))
(declare-const simd_divrem_poison_4 (_ BitVec 32))
(declare-const simd_arr_5 (Array (_ BitVec 64) (_ BitVec 32)))
(declare-const |test_simd_div::local_7_0| i32x2)
(assert (= |test_simd_div::local_7_0| (i32x2_mk (store (store simd_arr_5 #x0000000000000000 (ite (= (select (fld_0 |test_simd_div::local_5_0|) #x0000000000000000) #x00000000) simd_divrem_poison_3 (bvsdiv (select (fld_0 |test_simd_div::local_2_0|) #x0000000000000000) (select (fld_0 |test_simd_div::local_5_0|) #x0000000000000000)))) #x0000000000000001 (ite (= (select (fld_0 |test_simd_div::local_5_0|) #x0000000000000001) #x00000000) simd_divrem_poison_4 (bvsdiv (select (fld_0 |test_simd_div::local_2_0|) #x0000000000000001) (select (fld_0 |test_simd_div::local_5_0|) #x0000000000000001)))))))
(assert (or (or (or ay_violation_div_by_zero_check_0 ay_violation_overflow_check_simd_div_rem_1) ay_violation_div_by_zero_check_2) ay_violation_overflow_check_simd_div_rem_3))
(check-sat)
        ";
    assert_eq!(
        run_executor_smt_with_timeout(query, 30)?,
        SolverOutcome::Sat,
        "#store-chain-dead-node: the all-zero divisor lane forces \
         div_by_zero_check_0, so the violation disjunction is satisfiable",
    );
    Ok(())
}

/// The minimized `model-checker-consumer` `simd_insert` shape from model-checker-consumer commit
/// `3bb5d0e53`: the result constructor wraps a two-deep store chain, and both
/// store values are selects through a constructor-equated source array.  The
/// out-of-bounds check is independently forced true, so the base query is SAT.
///
/// Before #store-chain-dead-node, AY read cached bit-blast values for the two
/// compound `select` store operands.  Those nodes were not authoritative model
/// leaves, so the fabricated result cells conflicted with definitional array
/// completion and the independent gate degraded this query to `unknown
/// (:reason-unknown incomplete)`.
fn simd_insert_store_chain_query(extra_assertion: &str) -> String {
    format!(
        r"
        (set-logic ALL)
        (declare-datatype i64x2
          ((i64x2_mk (fld_0 (Array (_ BitVec 64) (_ BitVec 64))))))

        (declare-const source_arr (Array (_ BitVec 64) (_ BitVec 64)))
        (assert (= (select source_arr #x0000000000000000) #x000000000000000a))
        (assert (= (select source_arr #x0000000000000001) #x0000000000000014))
        (declare-const source i64x2)
        (assert (= source (i64x2_mk source_arr)))

        (declare-const simd_arr (Array (_ BitVec 64) (_ BitVec 64)))
        (declare-const result i64x2)
        (assert
          (= result
             (i64x2_mk
               (store
                 (store simd_arr
                        #x0000000000000000
                        (select (fld_0 source) #x0000000000000000))
                 #x0000000000000001
                 (select (fld_0 source) #x0000000000000001)))))

        (declare-const ay_violation_simd_insert_0 Bool)
        (assert
          (= ay_violation_simd_insert_0
             (not (bvult #x00000002 #x00000002))))
        (assert ay_violation_simd_insert_0)
        {extra_assertion}
        (check-sat)
        "
    )
}

#[test]
#[ntest::timeout(120_000)]
fn test_trust_simd_insert_constructor_store_of_selects_is_decided() -> Result<()> {
    for (extra, expected, description) in [
        (
            "",
            SolverOutcome::Sat,
            "the forced out-of-bounds violation makes the base query SAT",
        ),
        (
            r"(assert
                 (and
                   (= (select (fld_0 result) #x0000000000000000)
                      #x000000000000000a)
                   (= (select (fld_0 result) #x0000000000000001)
                      #x0000000000000014)))",
            SolverOutcome::Sat,
            "both result lanes must read back the constructor-equated source lanes",
        ),
        (
            r"(assert
                 (not (= (select (fld_0 result) #x0000000000000000)
                         #x000000000000000a)))",
            SolverOutcome::Unsat,
            "ROW at lane zero must refute a contradictory result cell",
        ),
        (
            r"(assert
                 (not (= (select (fld_0 result) #x0000000000000001)
                         #x0000000000000014)))",
            SolverOutcome::Unsat,
            "ROW at lane one must refute a contradictory result cell",
        ),
    ] {
        let outcome = run_executor_smt_with_timeout(&simd_insert_store_chain_query(extra), 20)?;
        assert_eq!(outcome, expected, "{description}; got {outcome:?}");
    }
    Ok(())
}
