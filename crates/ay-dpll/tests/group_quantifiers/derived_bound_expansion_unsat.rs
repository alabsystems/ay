// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! (#withheld-finite-expansion-refutation) A nested-`Vec` premise that is false
//! at one cell, bounded by datatype FIELDS rather than literals.
//!
//! Once the datatype selector fold went live (d06f1074c) the query atoms fold
//! to constants, E-matching has no ground term to instantiate from, and the
//! refutation comes only from the derived-bound finite expansion, whose
//! instances carry no `forall_inst` translation. The mandatory-artifact gate
//! withheld it, so the plain solve answered `unknown` where it answered
//! `unsat` before. The exact finite-expansion UNSAT theorem, replayed from the
//! authored roots alone (#source-derived-unsat-replay), now certifies it; an
//! explicit proof request still fails closed, and the SAT twins never become
//! `unsat`. z3 answers every case as asserted here.

use ntest::timeout;

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};

/// The row's shape at binder/length width 64 (the row's own width).
fn nested_premise(cell: &str, definition: &str, proofs: bool) -> String {
    nested_premise_at(64, cell, definition, proofs)
}

fn nested_premise_at(width: u32, cell: &str, definition: &str, proofs: bool) -> String {
    let value = |cell: &str| {
        format!(
            "(let ((cells ((as const (Array (_ BitVec {width}) (_ BitVec 8))) #x07))) \
               (mkOuter (_ bv3 {width}) \
                 (store ((as const (Array (_ BitVec {width}) Inner)) (mkInner (_ bv0 {width}) cells)) \
                        (_ bv2 {width}) (mkInner (_ bv4 {width}) (store cells (_ bv3 {width}) {cell})))))"
        )
    };
    let definition = definition
        .replace("@VALUE@", &value(cell))
        .replace("@TRUE_VALUE@", &value("#x07"));
    let option = if proofs {
        "(set-option :produce-proofs true)"
    } else {
        ""
    };
    format!(
        "{option} (set-logic ALL) \
         (declare-datatype Inner ((mkInner (fld_len (_ BitVec {width})) \
                                           (fld_data (Array (_ BitVec {width}) (_ BitVec 8)))))) \
         (declare-datatype Outer ((mkOuter (fld_len (_ BitVec {width})) \
                                           (fld_data (Array (_ BitVec {width}) Inner))))) \
         (declare-const fact_outer Outer) \
         (declare-const query_outer Outer) \
         {definition} \
         (assert (forall ((r (_ BitVec {width})) (c (_ BitVec {width}))) \
           (=> (and (bvult r (fld_len fact_outer)) \
                    (bvult c (fld_len (select (fld_data fact_outer) r)))) \
               (= (select (fld_data (select (fld_data fact_outer) r)) c) #x07)))) \
         (assert (= query_outer fact_outer)) \
         (assert (bvult (_ bv2 {width}) (fld_len query_outer))) \
         (assert (bvult (_ bv3 {width}) (fld_len (select (fld_data query_outer) (_ bv2 {width}))))) \
         (assert (distinct (select (fld_data (select (fld_data query_outer) (_ bv2 {width}))) \
                                   (_ bv3 {width})) \
                           #x08)) \
         (check-sat)"
    )
}

const DEFINITION: &str = "(assert (= fact_outer @VALUE@))";

/// The corpus gate's per-row limit: the verdict must arrive within it.
const LIMIT_SECS: u64 = 10;

fn outcome(smt: &str) -> SolverOutcome {
    run_executor_smt_with_timeout(smt, LIMIT_SECS).expect("execution should succeed")
}

#[test]
#[timeout(60000)]
fn a_field_bounded_false_premise_is_unsat_without_proofs() {
    let result = outcome(&nested_premise("#x09", DEFINITION, false));
    assert_eq!(
        result,
        SolverOutcome::Unsat,
        "the premise is false at (2, 3)"
    );
}

#[test]
#[timeout(60000)]
fn a_field_bounded_false_premise_fails_closed_under_proofs() {
    let result = outcome(&nested_premise("#x09", DEFINITION, true));
    assert_eq!(
        result,
        SolverOutcome::Unknown,
        "no translated authored-scope proof exists for this refutation"
    );
}

// The two SAT twins below pin the PRODUCER end to end: the withheld route
// consults the theorem only after the ground solve itself refuted the query,
// which a satisfiable input never does. The theorem's own negative coverage
// (true premise, definition under a disjunction, disjunctive bound, binder
// capture) is in `executor::unsat_cert::source_derived_finite_expansion_tests`.

#[test]
#[timeout(60000)]
fn a_field_bounded_true_premise_is_never_unsat() {
    let result = outcome(&nested_premise("#x07", DEFINITION, false));
    assert_ne!(
        result,
        SolverOutcome::Unsat,
        "every cell holds 7: z3 answers sat"
    );
}

#[test]
#[timeout(60000)]
fn a_definition_under_a_disjunction_is_never_unsat() {
    // Width 8: the same shape decides (`unknown`) in about a second instead of
    // spending the whole 10 s limit at width 64.
    let result = outcome(&nested_premise_at(
        8,
        "#x09",
        "(assert (or (= fact_outer @VALUE@) (= fact_outer @TRUE_VALUE@)))",
        false,
    ));
    assert_ne!(
        result,
        SolverOutcome::Unsat,
        "the second disjunct satisfies the premise: z3 answers sat"
    );
}
