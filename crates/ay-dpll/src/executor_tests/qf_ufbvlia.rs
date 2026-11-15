// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Conditional `QF_UFBVLIA` scalar routing and coupling boundary tests.

use crate::Executor;
use ay_core::{ProofStep, TheoryLemmaKind};
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
fn explicit_qf_ufbvlia_routes_linear_array_free_content() {
    let input = r#"
        (set-logic QF_UFBVLIA)
        (declare-const b (_ BitVec 8))
        (declare-const i Int)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (assert (= b #x05))
        (assert (= (f b) #x06))
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
fn explicit_qf_ufbvlia_conversion_routes_to_conservative_bridge() {
    let input = r#"
        (set-logic QF_UFBVLIA)
        (declare-const b (_ BitVec 8))
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (assert (= (bv2nat b) 5))
        (check-sat)
    "#;
    let (executor, output) = execute(input);

    // The bridge may publish SAT only after the ordinary strict and independent
    // model gates validate the concrete BV/Int witness.
    assert_eq!(output, vec!["sat"]);
    assert_eq!(
        executor.statistics().get_string("solver.logic_category"),
        Some("QfBvLia")
    );
}

#[test]
fn explicit_qf_ufbvlia_assumptions_do_not_leak_between_checks() {
    let input = r#"
        (set-logic QF_UFBVLIA)
        (declare-const b (_ BitVec 8))
        (declare-const i Int)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (assert (= b #x05))
        (assert (= (f b) #x06))
        (check-sat-assuming ((= i 3)))
        (check-sat-assuming ((= i 3) (not (= i 3))))
        (check-sat-assuming ((= i 3)))
    "#;
    let (_, output) = execute(input);

    assert_eq!(output, vec!["sat", "unsat", "sat"]);
}

#[test]
fn explicit_qf_ufbvlia_out_of_slice_content_stays_other() {
    let cases = [
        (
            "array",
            r#"
                (set-logic QF_UFBVLIA)
                (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
                (declare-const i Int)
                (assert (= (select a #x00) #x01))
                (assert (= i 0))
                (check-sat)
            "#,
        ),
        (
            "real",
            r#"
                (set-logic QF_UFBVLIA)
                (declare-const r Real)
                (assert (= r 1.0))
                (check-sat)
            "#,
        ),
        (
            "nonlinear",
            r#"
                (set-logic QF_UFBVLIA)
                (declare-const x Int)
                (declare-const y Int)
                (assert (= (* x y) 6))
                (check-sat)
            "#,
        ),
        (
            "datatype",
            r#"
                (set-logic QF_UFBVLIA)
                (declare-datatype Box ((empty) (box (unbox Int))))
                (declare-const b Box)
                (assert (= (unbox b) 1))
                (check-sat)
            "#,
        ),
        (
            "set-operator",
            r#"
                (set-logic QF_UFBVLIA)
                (declare-const s (Set (_ BitVec 8)))
                (assert (not (= (set.card s) 0)))
                (check-sat)
            "#,
        ),
        (
            "rounding-mode",
            r#"
                (set-logic QF_UFBVLIA)
                (declare-const rm RoundingMode)
                (assert (= rm RNE))
                (check-sat)
            "#,
        ),
    ];

    for (name, input) in cases {
        let (executor, output) = execute(input);
        assert_eq!(output, vec!["unknown"], "{name} must stay fenced");
        assert_eq!(
            executor.statistics().get_string("solver.logic_category"),
            Some("Other"),
            "{name} must retain Other dispatch"
        );
    }
}

#[test]
fn explicit_qf_ufbvlia_rejects_live_datatype_carrier_without_member_ops() {
    let input = r#"
        (set-logic QF_UFBVLIA)
        (declare-datatype Box ((empty) (box (unbox Int))))
        (declare-const left Box)
        (declare-const right Box)
        (assert (= left right))
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
fn explicit_qf_ufbvlia_rejects_direct_cross_theory_uf() {
    let input = r#"
        (set-logic QF_UFBVLIA)
        (declare-const b (_ BitVec 2))
        (declare-const i Int)
        (declare-fun p ((_ BitVec 2) Int) Bool)
        (assert (p b i))
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
fn explicit_qf_ufbvlia_rejects_transitive_cross_theory_uf() {
    let input = r#"
        (set-logic QF_UFBVLIA)
        (declare-sort U 0)
        (declare-const b (_ BitVec 2))
        (declare-fun from_bv ((_ BitVec 2)) U)
        (declare-fun to_int (U) Int)
        (assert (= (to_int (from_bv b)) 0))
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
fn named_bv_lia_logics_route_uf_free_mixed_boolean_component_to_bridge() {
    for logic in ["QF_UFBVLIA", "QF_AUFBVLIA"] {
        let input = format!(
            r#"
                (set-logic {logic})
                (declare-const b (_ BitVec 2))
                (declare-const i Int)
                (assert (or (= b #b00) (= i 0)))
                (check-sat)
            "#
        );
        let (executor, output) = execute(&input);

        assert!(
            matches!(output.as_slice(), [answer] if answer == "sat" || answer == "unknown"),
            "{logic} must not publish a false UNSAT"
        );
        assert_eq!(
            executor.statistics().get_string("solver.logic_category"),
            Some("QfBvLia"),
            "{logic}"
        );
    }
}

#[test]
fn explicit_qf_ufbvlia_source_authenticates_mixed_boolean_unsat() {
    let input = r#"
        (set-logic QF_UFBVLIA)
        (declare-const b (_ BitVec 2))
        (declare-const i Int)
        (assert (= b #b01))
        (assert (= i 1))
        (assert (or (= b #b00) (= i 0)))
        (check-sat)
    "#;
    let (executor, output) = execute(input);

    assert_eq!(output, vec!["unsat"]);
    assert_eq!(
        executor
            .statistics()
            .get_string("solver.bv_lia_bounded_source"),
        Some("unsat")
    );
    assert_eq!(
        executor
            .statistics()
            .get_int("smt.bv_lia_bridge.pre_quantifier_runs"),
        Some(1)
    );
    assert!(
        executor.last_command_unsat_was_independently_verified()
            || executor.last_command_unsat_was_strictly_verified(),
        "published UNSAT must consume checked source or strict authority"
    );
}

#[test]
fn explicit_qf_ufbvlia_conversion_does_not_bypass_cross_theory_uf_fence() {
    let input = r#"
        (set-logic QF_UFBVLIA)
        (declare-const b (_ BitVec 2))
        (declare-const i Int)
        (declare-fun p ((_ BitVec 2) Int) Bool)
        (assert (= (bv2nat b) i))
        (assert (p b i))
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
        Some(0),
        "the authored UF fence must run before the bridge"
    );
    assert_eq!(
        executor
            .statistics()
            .get_string("solver.bv_lia_bounded_source"),
        None,
        "a conversion marker must not invoke source authentication past the UF fence"
    );
}

#[test]
fn explicit_qf_ufbvlia_checks_assumption_coupling() {
    let input = r#"
        (set-logic QF_UFBVLIA)
        (declare-const b (_ BitVec 2))
        (declare-const i Int)
        (declare-fun p ((_ BitVec 2) Int) Bool)
        (assert (= b #b00))
        (assert (= i 0))
        (check-sat-assuming ((p b i)))
    "#;
    let (executor, output) = execute(input);

    assert_eq!(output, vec!["unknown"]);
    assert_eq!(
        executor.statistics().get_string("solver.logic_category"),
        Some("Other")
    );
}

#[test]
fn explicit_qf_ufbvlia_source_authenticates_exact_mixed_boolean_assumption() {
    let input = r#"
        (set-logic QF_UFBVLIA)
        (declare-const b (_ BitVec 2))
        (declare-const i Int)
        (assert (= b #b01))
        (assert (= i 1))
        (check-sat-assuming (
            (or (= b #b00) (= i 0))))
        (get-unsat-assumptions)
    "#;
    let (executor, output) = execute(input);

    assert_eq!(output, vec!["unsat", "((or (= b #b00) (= i 0)))"]);
    assert_eq!(
        executor
            .statistics()
            .get_string("solver.bv_lia_bounded_source"),
        Some("unsat")
    );
    assert!(
        executor.last_command_unsat_was_independently_verified()
            || executor.last_command_unsat_was_strictly_verified(),
        "published UNSAT must consume checked source or strict authority"
    );
}

#[test]
fn explicit_qf_ufbvlia_strict_mode_publishes_native_mixed_boolean_refutation() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-option :check-proofs-strict true)
        (set-logic QF_UFBVLIA)
        (declare-const b (_ BitVec 2))
        (declare-const i Int)
        (assert (= b #b01))
        (assert (= i 1))
        (assert (or (= b #b00) (= i 0)))
        (check-sat)
    "#;
    let (executor, output) = execute(input);

    assert_eq!(output, vec!["unsat"]);
    assert_eq!(
        executor
            .statistics()
            .get_string("solver.bv_lia_bounded_source"),
        Some("unsat")
    );
    assert!(executor.last_command_unsat_was_strictly_verified());
    let proof = executor.last_proof().expect("native strict BV/LIA proof");
    let quality = ay_proof::check_proof_strict(proof, executor.terms())
        .expect("native mixed Boolean BV/LIA proof must replay strictly");
    assert!(
        quality.is_complete(),
        "native proof must be complete: {quality}"
    );
    assert_eq!(quality.trust_count, 0);
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::BvLiaTautology,
            ..
        }
    )));
    assert!(
        executor.unsat_proof_has_known_wire_gap(),
        "native admission must not relabel its honest Alethe hole"
    );
}

#[test]
fn explicit_qf_ufbvlia_strict_mode_publishes_native_mixed_boolean_assumption() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-option :check-proofs-strict true)
        (set-logic QF_UFBVLIA)
        (declare-const b (_ BitVec 2))
        (declare-const i Int)
        (assert (= b #b01))
        (assert (= i 1))
        (check-sat-assuming (
            (or (= b #b00) (= i 0))))
        (get-unsat-assumptions)
    "#;
    let (executor, output) = execute(input);

    assert_eq!(output, vec!["unsat", "((or (= b #b00) (= i 0)))"]);
    assert!(executor.last_command_unsat_was_strictly_verified());
    let proof = executor
        .last_proof()
        .expect("native strict assumption proof");
    let quality = ay_proof::check_proof_strict(proof, executor.terms())
        .expect("native BV/LIA assumption proof must replay strictly");
    assert!(quality.is_complete());
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::BvLiaTautology,
            ..
        }
    )));
    assert!(executor.unsat_proof_has_known_wire_gap());
}

#[test]
fn explicit_qf_ufbvlia_joins_base_and_assumption_components() {
    let input = r#"
        (set-logic QF_UFBVLIA)
        (declare-sort U 0)
        (declare-const b (_ BitVec 2))
        (declare-const u U)
        (declare-fun from_bv ((_ BitVec 2)) U)
        (declare-fun to_int (U) Int)
        (assert (= (from_bv b) u))
        (check-sat-assuming ((= (to_int u) 0)))
    "#;
    let (executor, output) = execute(input);

    assert_eq!(output, vec!["unknown"]);
    assert_eq!(
        executor.statistics().get_string("solver.logic_category"),
        Some("Other")
    );
}

/// #ufbvlia-modmonotone. A declared logic name is an UPPER BOUND on the symbols
/// a script may mention, so widening it must never lose a verdict. It did:
/// `QF_LIA` decided this query and `QF_UFBVLIA` — which admits strictly more —
/// answered `unknown (incomplete)`, on a query with no bitvector in it at all.
///
/// The cause was the `has_int_div_mod` row of the closed admission predicate,
/// which fenced a `mod` whether or not a bitvector was live to combine with.
#[test]
fn explicit_qf_ufbvlia_decides_a_bv_free_int_mod_contradiction() {
    let input = r#"
        (set-logic QF_UFBVLIA)
        (declare-fun a () Int)
        (declare-fun k () Int)
        (assert (= k (mod a 4)))
        (assert (<= k 3))
        (assert (>= k 4))
        (check-sat)
    "#;
    let (executor, output) = execute(input);

    assert_eq!(output, vec!["unsat"]);
    assert_eq!(
        executor.statistics().get_string("solver.logic_category"),
        Some("QfLia")
    );
}

/// The SATISFIABLE MUTANT TWIN of the test above: drop the one conjunct that
/// makes it contradictory and the very same routing must answer `sat`. Without
/// this, a fix that admitted the slice by fabricating UNSAT would pass the test
/// above.
#[test]
fn the_bv_free_int_mod_twin_without_the_contradiction_is_sat() {
    let input = r#"
        (set-logic QF_UFBVLIA)
        (declare-fun a () Int)
        (declare-fun k () Int)
        (assert (= k (mod a 4)))
        (assert (<= k 3))
        (check-sat)
    "#;
    let (_, output) = execute(input);

    assert_eq!(output, vec!["sat"], "this query has a model (a = 0, k = 0)");
}

/// The shape Trust's vcgen actually emits for `let i = a & 3; arr[i]` on a
/// `[u8; 4]`: the index bound `i <= 3` beside the masked definition of `i`.
/// `TermStore::mk_bv2nat` rewrites `bv2nat(bvand(int2bv_w(a), 2^k-1))` to
/// `(mod a 2^k)` at interning time, so this arrives BV-free and carrying a
/// `mod` — the exact footprint the fence used to reject.
#[test]
fn explicit_qf_ufbvlia_decides_the_masked_residue_index_bound() {
    let input = r#"
        (set-logic QF_UFBVLIA)
        (declare-fun a () Int)
        (declare-fun k () Int)
        (assert (>= a 0))
        (assert (<= a 18446744073709551615))
        (assert (<= k 3))
        (assert (= k (bv2nat (bvand ((_ int2bv 64) a) ((_ int2bv 64) 3)))))
        (assert (>= k 4))
        (check-sat)
    "#;
    let (_, output) = execute(input);

    assert_eq!(output, vec!["unsat"]);
}

/// Satisfiable mutant twin of the masked-residue query: widen the array from
/// four elements to three (`k <= 2` would be the bound) and the violation
/// `k >= 3` becomes reachable at `a = 3`. Must stay `sat`.
#[test]
fn the_masked_residue_twin_with_a_reachable_violation_is_sat() {
    let input = r#"
        (set-logic QF_UFBVLIA)
        (declare-fun a () Int)
        (declare-fun k () Int)
        (assert (>= a 0))
        (assert (<= a 18446744073709551615))
        (assert (= k (bv2nat (bvand ((_ int2bv 64) a) ((_ int2bv 64) 3)))))
        (assert (>= k 3))
        (check-sat)
    "#;
    let (_, output) = execute(input);

    assert_eq!(
        output,
        vec!["sat"],
        "a = 3 gives k = 3, so the bound is genuinely violable"
    );
}

/// The UNSAFE twin of the relaxation: a `mod` BESIDE A LIVE BITVECTOR is the
/// theory combination this validator exists to fence, and it stays fenced —
/// `unknown`, dispatched as `Other`, never a verdict.
#[test]
fn explicit_qf_ufbvlia_keeps_int_mod_beside_a_live_bitvector_fenced() {
    let input = r#"
        (set-logic QF_UFBVLIA)
        (declare-const b (_ BitVec 8))
        (declare-fun a () Int)
        (declare-fun k () Int)
        (assert (= k (mod a 4)))
        (assert (= b #x05))
        (assert (<= k 3))
        (assert (>= k 4))
        (check-sat)
    "#;
    let (executor, output) = execute(input);

    assert_eq!(
        output,
        vec!["unknown"],
        "BV + div/mod must stay fail-closed"
    );
    assert_eq!(
        executor.statistics().get_string("solver.logic_category"),
        Some("Other")
    );
}
