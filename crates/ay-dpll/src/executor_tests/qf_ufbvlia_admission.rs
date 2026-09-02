// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! `QF_UFBVLIA` live-root admission and certificate publication tests.

use crate::{Executor, UnknownReason};
use ay_frontend::parse;

fn execute(input: &str) -> (Executor, Vec<String>) {
    let commands = parse(input).expect("valid SMT-LIB test input");
    let mut executor = Executor::new();
    let output = executor
        .execute_all(&commands)
        .expect("commands must execute");
    (executor, output)
}

#[test]
fn explicit_qf_ufbvlia_flattens_positive_top_level_conjunctions_for_assumptions() {
    let input = r#"
        (set-logic QF_UFBVLIA)
        (declare-const b (_ BitVec 8))
        (declare-const i Int)
        (assert (and (= b #x05) (= i 3)))
        (check-sat-assuming ((= b #x05)))
    "#;
    let (executor, output) = execute(input);

    assert_eq!(output, vec!["sat"]);
    assert_eq!(
        executor.statistics().get_string("solver.logic_category"),
        Some("QfBvLiaIndep")
    );
}

#[test]
fn explicit_qf_ufbvlia_validator_precedes_conversion_bridge() {
    let input = r#"
        (set-logic QF_UFBVLIA)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const b (_ BitVec 8))
        (assert (= (select a #x00) #x01))
        (assert (= (bv2nat b) 5))
        (assert (not (= b #x05)))
        (check-sat)
    "#;
    let (executor, output) = execute(input);

    assert_eq!(output, vec!["unknown"]);
    assert_eq!(
        executor.statistics().get_string("solver.logic_category"),
        Some("Other")
    );
    assert_eq!(
        executor
            .statistics()
            .get_int("smt.bv_lia_bridge.pre_quantifier_runs"),
        Some(0)
    );
}

#[test]
fn explicit_qf_ufbvlia_assumption_validator_precedes_conversion_bridge() {
    let input = r#"
        (set-logic QF_UFBVLIA)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const b (_ BitVec 8))
        (assert (= (select a #x00) #x01))
        (check-sat-assuming ((= (bv2nat b) 5) (not (= b #x05))))
    "#;
    let (executor, output) = execute(input);

    assert_eq!(output, vec!["unknown"]);
    assert_eq!(
        executor.statistics().get_string("solver.logic_category"),
        Some("Other")
    );
}

#[test]
fn explicit_qf_ufbvlia_validator_precedes_quantifier_preprocessing() {
    let cases = [
        (
            "check-sat",
            r#"
                (set-logic QF_UFBVLIA)
                (declare-fun p (Int) Bool)
                (assert (forall ((x Int)) (p x)))
                (check-sat)
            "#,
        ),
        (
            "check-sat-assuming",
            r#"
                (set-logic QF_AUFBVLIA)
                (declare-fun p (Int) Bool)
                (assert (forall ((x Int)) (p x)))
                (check-sat-assuming ((not (p 0))))
            "#,
        ),
        (
            "exact-semantic-presolve",
            r#"
                (set-logic QF_UFBVLIA)
                (assert (forall ((x Int)) false))
                (check-sat)
            "#,
        ),
    ];

    for (name, input) in cases {
        let (executor, output) = execute(input);
        assert_eq!(output, vec!["unknown"], "{name}");
        assert_eq!(
            executor.statistics().get_string("solver.logic_category"),
            Some("Other"),
            "{name}"
        );
    }
}

#[test]
fn explicit_qf_ufbvlia_validator_precedes_ground_folding_fast_paths() {
    let input = r#"
        (set-logic QF_UFBVLIA)
        (declare-const s String)
        (assert (= s "abc"))
        (assert (= (str.len s) 3))
        (check-sat)
    "#;
    let (executor, output) = execute(input);

    assert_eq!(output, vec!["unknown"]);
    assert_eq!(
        executor.statistics().get_string("solver.logic_category"),
        Some("Other")
    );
}

#[test]
fn explicit_qf_ufbvlia_ignores_unused_out_of_slice_declarations() {
    let input = r#"
        (set-logic QF_UFBVLIA)
        (declare-const unused_real Real)
        (declare-const unused_array (Array Int Int))
        (declare-datatype Unused ((unused (field Int))))
        (declare-const b (_ BitVec 8))
        (declare-const i Int)
        (assert (= b #x05))
        (assert (= i 3))
        (check-sat)
    "#;
    let (executor, output) = execute(input);

    assert_eq!(output, vec!["sat"]);
    assert_eq!(
        executor.statistics().get_string("solver.logic_category"),
        Some("QfBvLiaIndep")
    );
}

#[test]
fn unused_mixed_uf_declaration_does_not_fabricate_a_mixed_route() {
    let input = r#"
        (set-logic QF_UFBVLIA)
        (declare-fun unused ((_ BitVec 8)) Int)
        (declare-const b (_ BitVec 8))
        (assert (= b #x05))
        (check-sat)
    "#;
    let (executor, output) = execute(input);

    assert_eq!(output, vec!["sat"]);
    assert_eq!(
        executor.statistics().get_string("solver.logic_category"),
        Some("QfBv")
    );
}

#[test]
fn popped_collection_usage_does_not_poison_the_live_scalar_window() {
    let cases = [
        (
            "set",
            r#"
                (set-logic QF_UFBVLIA)
                (declare-const b (_ BitVec 8))
                (declare-const i Int)
                (push 1)
                (declare-const s (Set Int))
                (assert (= (set.card s) 0))
                (pop 1)
                (assert (= b #x05))
                (assert (= i 3))
                (check-sat)
            "#,
        ),
        (
            "multiset",
            r#"
                (set-logic QF_AUFBVLIA)
                (declare-const b (_ BitVec 8))
                (declare-const i Int)
                (push 1)
                (declare-const m (Multiset Int))
                (assert (= (multiset.count 0 m) 0))
                (pop 1)
                (assert (= b #x05))
                (assert (= i 3))
                (check-sat)
            "#,
        ),
    ];

    for (name, input) in cases {
        let (executor, output) = execute(input);
        assert_eq!(output, vec!["sat"], "{name}");
        assert_eq!(
            executor.statistics().get_string("solver.logic_category"),
            Some("QfBvLiaIndep"),
            "{name}"
        );
    }
}

#[test]
fn qf_aufbvlia_routes_its_array_free_scalar_subset() {
    let input = r#"
        (set-logic QF_AUFBVLIA)
        (declare-const b (_ BitVec 8))
        (declare-const i Int)
        (assert (= b #x05))
        (assert (= i 3))
        (check-sat)
    "#;
    let (executor, output) = execute(input);

    assert_eq!(output, vec!["sat"]);
    assert_eq!(
        executor.statistics().get_string("solver.logic_category"),
        Some("QfBvLiaIndep")
    );
}

#[test]
fn qf_aufbvlia_remains_fail_closed() {
    let input = r#"
        (set-logic QF_AUFBVLIA)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i Int)
        (assert (= (select a #x00) #x01))
        (assert (= i 0))
        (check-sat)
    "#;
    let (executor, output) = execute(input);

    assert_eq!(output, vec!["unknown"]);
    assert_eq!(
        executor.statistics().get_string("solver.logic_category"),
        Some("Other")
    );
}

#[test]
fn qf_ufbvlia_strict_mode_publishes_only_a_trust_free_unsat_proof() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-option :check-proofs-strict true)
        (set-logic QF_UFBVLIA)
        (declare-const b (_ BitVec 8))
        (declare-const i Int)
        (assert (= b #x05))
        (assert (= i 3))
        (assert false)
        (check-sat)
    "#;
    let (executor, output) = execute(input);

    assert_eq!(output, vec!["unsat"]);
    assert!(executor.last_command_unsat_was_strictly_verified());
    let proof = executor.last_proof().expect("strict UNSAT proof");
    let quality = ay_proof::check_proof_strict(proof, executor.terms())
        .expect("published QF_UFBVLIA proof must replay strictly");
    assert!(
        quality.is_complete(),
        "strict proof must be complete: {quality}"
    );
    assert_eq!(quality.trust_count, 0, "strict proof must be trust-free");
    assert_eq!(
        executor.statistics().get_string("solver.logic_category"),
        Some("QfBvLiaIndep")
    );
}

#[test]
fn qf_ufbvlia_strict_mode_withholds_native_only_bv_lia_refutation() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-option :check-proofs-strict true)
        (set-logic QF_UFBVLIA)
        (declare-const result (_ BitVec 16))
        (declare-const x (_ BitVec 16))
        (assert (= x #x9c40))
        (assert (= x result))
        (assert (<= (* (bv2nat x) 2) 65535))
        (check-sat)
    "#;
    let (executor, output) = execute(input);

    assert_eq!(output, vec!["unknown"]);
    assert_eq!(executor.unknown_reason(), Some(UnknownReason::ProofTrusted));
    assert_eq!(
        executor
            .statistics()
            .get_string("solver.bv_lia_bounded_source"),
        Some("unsat")
    );
    assert!(
        executor.last_proof().is_none(),
        "a native-only BV/LIA certificate must not cross the strict Alethe boundary"
    );
}
