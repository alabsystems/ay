// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::executor::theories::{
    array_extensionality_witness, deep_array_extensionality_witness, ArrayExtWitnessBinding,
};
use ay_core::{AletheRule, ProofId, Sort};
use ay_frontend::parse;
use ay_proof::check_proof_partial;
use ntest::timeout;
use num_bigint::BigInt;
include!("tests/wire_gap_retry.rs");
include!("tests/authored_scope.rs");
include!("tests/finite_enum.rs");
include!("tests/strict_rebuilds.rs");
include!("tests/row2_rebuilds.rs");
include!("tests/proof_api.rs");
/// The external-codegen GUARDED-division obligation family: `(and (not (= b 0)) (not
/// (= X X)))` with the two encoders of `a - (a / b) * b` coinciding
/// syntactically. The second conjunct alone is the self-equality shape, but the
/// `b ≠ 0` guard puts it under an `and`, so neither the top-level self-equality
/// pass nor the dom-bounds pass matched and the whole (correct) refutation
/// degenerated to the `hole`-rendering rescue.
/// `promote_and_self_eq_contradiction_collapse` must rebuild it into the
/// checkable `and_pos`/`refl` refutation — no `hole`, no `trust`.
#[test]
fn test_and_self_eq_contradiction_promotes_to_checkable_proof() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_BV)
        (declare-const a (_ BitVec 32))
        (declare-const b (_ BitVec 32))
        (assert (and (not (= b (_ bv0 32))) (not (= (bvsub a (bvmul (bvudiv a b) b)) (bvsub a (bvmul (bvudiv a b) b))))))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "unsat");
    let text = &outputs[1];
    // Pin the emitted step sequence: assume, and_pos(1), resolution, refl,
    // resolution. Every rule here is one an external Alethe checker re-derives
    // from the printed text alone.
    let rules: Vec<&str> = text
        .lines()
        .filter_map(|line| line.split(":rule ").nth(1))
        .map(|rest| {
            rest.split_whitespace()
                .next()
                .unwrap_or("")
                .trim_end_matches(')')
        })
        .collect();
    assert_eq!(
        rules,
        vec!["and_pos", "resolution", "refl", "resolution"],
        "guarded self-equality proof must be the and_pos/refl refutation:\n{text}"
    );
    assert!(
        text.contains(":rule and_pos :args (1)"),
        "and_pos must project the SECOND conjunct:\n{text}"
    );
    assert!(
        !text.contains(":rule hole") && !text.contains(":rule trust"),
        "guarded self-equality proof must carry no unproved step:\n{text}"
    );
    let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
    assert!(
        ay_proof::terminal_trust_report(proof).is_trust_free(),
        "guarded self-equality proof must be trust-free"
    );
}

/// A QF_ABV self-equality obligation — the external-codegen memory-image family, whose
/// two sides are byte-identical `select`/`store`/const-array terms. Before the
/// array fragment existed in the faithful rebuilders, `build_bv_pterm` bailed
/// at the first `select`, no collapse promoter could fire, and the refutation
/// degenerated to the `hole`-rendering last resort.
///
/// Also pins the printer: AY stores `((as const (Array I E)) v)` as the
/// internal application `(const-array v)`, which no external checker can even
/// PARSE — emitting it would take the document from `holey` to `invalid`.
#[test]
fn test_array_backed_self_eq_collapse_promotes_to_checkable_proof() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_ABV)
        (declare-const base (_ BitVec 64))
        (declare-const val (_ BitVec 64))
        (declare-const fill (_ BitVec 8))
        (assert (not (= ((_ zero_extend 56) (select (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) fill) (bvadd base (_ bv8 64)) ((_ extract 7 0) val)) base))
                        ((_ zero_extend 56) (select (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) fill) (bvadd base (_ bv8 64)) ((_ extract 7 0) val)) base)))))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "unsat");
    let text = &outputs[1];
    let rules: Vec<&str> = text
        .lines()
        .filter_map(|line| line.split(":rule ").nth(1))
        .map(|rest| {
            rest.split_whitespace()
                .next()
                .unwrap_or("")
                .trim_end_matches(')')
        })
        .collect();
    assert_eq!(
        rules,
        vec!["eq_reflexive", "resolution"],
        "array self-equality proof must be the reflexivity refutation:\n{text}"
    );
    assert!(
        !text.contains(":rule hole") && !text.contains(":rule trust"),
        "array self-equality proof must carry no unproved step:\n{text}"
    );
    assert!(
        text.contains("(select (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) fill)"),
        "the rebuild must keep the RAW select/store and print the SMT-LIB \
         constant-array spelling, never AY's internal `const-array`:\n{text}"
    );
    assert!(
        !text.contains("(const-array"),
        "AY's internal constant-array spelling is unparseable to external \
         checkers and must never reach the wire:\n{text}"
    );
    let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
    assert!(
        ay_proof::terminal_trust_report(proof).is_trust_free(),
        "array self-equality proof must be trust-free"
    );
}

/// Fail-closed print fidelity: a promoter must DECLINE rather than emit a
/// document whose `assume` is not the problem's assertion.
///
/// `(select (store A i v) i)` folds to `v` under read-over-write. The generic
/// override collector rejects a folded spelling keyed on an ATOM, but `v` here
/// is deliberately the composite `(bvadd x y)`, so it retains the authored
/// spelling of the whole read. The raw rebuild legitimately uses that same
/// composite in two unfolded positions (the const-array default and the stored
/// value), and printing it through the override re-spells both as the entire
/// read expression — an `assume` an external checker rejects outright
/// (`invalid`, strictly worse than the honest `hole`, since no rule can run on
/// a premise that is not the problem's). `rebuilt_terms_print_faithfully` must
/// catch this and leave the unproved step in place. Mandatory strict
/// certification must then withhold the UNSAT rather than publish the hole.
#[test]
fn folded_array_read_self_eq_declines_rather_than_misprint_its_assume() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_ABV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (declare-const i (_ BitVec 64))
        (assert (not (= (select (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) (bvadd x y)) i (bvadd x y)) i)
                        (select (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) (bvadd x y)) i (bvadd x y)) i))))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs[0], "unknown",
        "an unfaithful proof must fail closed at publication: {outputs:?}"
    );
    assert_eq!(
        exec.get_reason_unknown(),
        Some(crate::UnknownReason::SelfCheckRejected),
        "strict proof rejection must remain attributable"
    );
    assert!(
        exec.last_proof.is_none(),
        "a rejected proof must not remain publishable"
    );
    assert!(
        exec.take_unsat_certificate().is_none(),
        "a rejected proof must not yield an UNSAT certificate"
    );
    assert!(
        !outputs[1].contains("(assume t0 false)"),
        "never publish an unauthored false premise: {}",
        outputs[1]
    );
}

/// A literal-false assumption carries exact source authority. The retained
/// three-step proof must use literal `false` for both its assumption and
/// `false` rule.
#[test]
fn literal_false_check_sat_assuming_has_exact_source_authority() {
    let commands = parse(
        r#"
            (set-option :produce-proofs true)
            (check-sat-assuming (false))
            (get-proof)
        "#,
    )
    .unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "unsat");
    assert!(exec.unsat_query_has_literal_false_assumption_source());
    assert!(
        outputs[1].contains("(assume t0 false)"),
        "literal-false assumption must remain literal on the wire:\n{}",
        outputs[1]
    );
}

/// Term identity is not source authority: `(not true)` elaborates to the same
/// canonical false term, but it cannot authorize the literal-false proof
/// skeleton because the skeleton's `false` rule would not prove that surface
/// expression. With no faithful promoter, publication must fail closed.
#[test]
fn folded_false_check_sat_assumption_does_not_gain_literal_authority() {
    let commands = parse(
        r#"
            (set-option :produce-proofs true)
            (check-sat-assuming ((not true)))
        "#,
    )
    .unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unknown"]);
    assert!(!exec.unsat_query_has_literal_false_assumption_source());
    assert_eq!(
        exec.get_reason_unknown(),
        Some(crate::UnknownReason::SelfCheckRejected)
    );
    assert!(exec.last_proof.is_none());
    assert!(exec.take_unsat_certificate().is_none());
}

#[test]
fn reachable_false_assume_in_a_noncanonical_proof_is_holed_without_source() {
    let mut exec = Executor::new();
    let false_term = exec.ctx.terms.false_term();
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[false_term]);

    let mut proof = Proof::new();
    let premise = proof.add_assume(false_term, None);
    let not_false = exec.ctx.terms.mk_not_raw(false_term);
    let tautology = proof.add_rule_step(AletheRule::False, vec![not_false], Vec::new(), Vec::new());
    let empty = proof.add_resolution(Vec::new(), false_term, premise, tautology);
    proof.add_resolution(Vec::new(), false_term, empty, tautology);
    assert_eq!(
        proof.steps.len(),
        4,
        "fixture must bypass the old shape test"
    );

    false_source::demote_unattributed_assumed_false(&mut exec, &mut proof);
    assert_eq!(proof.steps.len(), 1);
    assert!(matches!(
        proof.steps[0],
        ProofStep::Step {
            rule: AletheRule::Hole,
            ..
        }
    ));
}

include!("tests/lia_dt.rs");
#[test]
fn test_qf_lia_sorting_network_order_ite_proof_is_strict_checkable() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        (define-fun lo ((x Int) (y Int)) Int (ite (> x y) y x))
        (define-fun hi ((x Int) (y Int)) Int (ite (> x y) x y))
        (assert
          (not
            (let ((a1 (lo a b)) (b1 (hi a b)))
              (let ((b2 (lo b1 c)) (c2 (hi b1 c)))
                (let ((a3 (lo a1 b2)) (b3 (hi a1 b2)))
                  (and (<= a3 b3) (<= b3 c2) (<= a3 c2)))))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    assert_eq!(exec.execute_all(&commands).unwrap(), vec!["unsat"]);
    let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::OrderIteTautology,
                ..
            }
        )),
        "sorting-network proof must use the exact bounded order-ITE theorem"
    );
    assert!(ay_proof::terminal_trust_report(proof).is_trust_free());
    exec.check_proof_strict_with_datatypes(proof)
        .expect("sorting-network proof must pass independent strict replay");
}

include!("tests/bv_identity_collapse.rs");

include!("tests/bv_fp.rs");
include!("tests/dt_nia.rs");
include!("tests/farkas.rs");
mod boolean_closure;
mod trust_closer_array_retag;
mod trust_closer_derived_leaf_head;

include!("tests/pruning.rs");
include!("tests/self_check.rs");
include!("tests/firewall.rs");
include!("tests/array_string.rs");
include!("tests/string_array.rs");
include!("tests/extensionality.rs");
include!("tests/extensionality_folded_pair.rs");
include!("tests/strict_counter.rs");
mod conjunct_eval;
mod source_work;
