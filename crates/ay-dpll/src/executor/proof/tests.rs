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
include!("tests/equality_lattice_wire_gap.rs");
include!("tests/guarded_row_wire_gap.rs");
include!("tests/arith_equality_chain_wire_gap.rs");
include!("tests/arith_trichotomy_wire_gap.rs");
include!("tests/proportional_equality_wire_gap.rs");
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
/// The complete authored refutation may use either collapse promotion or the
/// earlier ground closure. Its rule order is not an authority boundary.
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
    assert!(exec
        .check_proof_strict_with_datatypes(proof)
        .unwrap()
        .is_complete());
    let mut authored = Vec::new();
    exec.try_export_last_proof_alethe_for_problem_scope_to(&mut authored)
        .unwrap()
        .expect("the complete original assertion remains the export scope");
    assert_eq!(String::from_utf8(authored).unwrap().trim(), text.trim());

    // The proof must not transfer to a nearby satisfiable obligation.
    let changed = input.replacen("(bvsub a (bvmul (bvudiv a b) b))", "a", 1);
    let mut changed_exec = Executor::new();
    let changed_outputs = changed_exec.execute_all(&parse(&changed).unwrap()).unwrap();
    assert_eq!(changed_outputs[0], "sat");
    assert!(changed_exec.last_proof().is_none());
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

/// PRINT FIDELITY, now pinned as the POSITIVE it became.
///
/// Was `folded_array_read_self_eq_declines_rather_than_misprint_its_assume`,
/// which pinned a DECLINE. **CONTRACT CHANGED, AND THE CHANGE IS MEASURED.**
/// The decline existed because the generic override collector attached the
/// authored spelling of the whole read `(select (store (const (bvadd x y)) i
/// (bvadd x y)) i)` to the composite leaf `(bvadd x y)` it folds to, so the
/// raw rebuild — which legitimately uses that leaf in two unfolded positions
/// — printed an `assume` that was NOT the problem's assertion.
/// `9280862f9` taught `rescue_bv_bitblast_collapse` to run
/// `rebuilt_terms_print_faithfully` before claiming a strict anchor, and the
/// rebuild failed the round trip, so the honest `hole` stood and mandatory
/// certification withheld the UNSAT.
///
/// The round trip now SUCCEEDS on this fixture, so the rescue claims its
/// strict bit-blast anchor and publishes. Measured at `cc1bc0a30`, in this
/// worktree:
///
///   * the printed `(assume t0 …)` is the authored assertion CHARACTER FOR
///     CHARACTER — the defect this test was written to catch does not occur;
///   * the document carries no `hole` and no `trust` step, and
///     `terminal_trust_report` reports it trust-free;
///   * `export_last_unsat_artifact` reports `strict_verdict = Verified`
///     (`trust_count: 0`, `hole_count: 0`) and `carcara_surface = supported`;
///   * **pinned Carcara 1.1.0 answers `valid`** on the exact published
///     document paired with the artifact's own `alethe_problem_smt2` bytes.
///
/// The fixture is genuinely UNSAT (`(not (= X X))` for any `X`), so this is a
/// capability gain, not a widened acceptance. What this test protects is
/// unchanged and is asserted more tightly than the decline ever could: NO
/// `assume` in a published document may be anything but the authored
/// assertion. A future re-spelling therefore fails here just as loudly as it
/// used to, and a future decline fails too — which is right, because that
/// would be the capability going away again.
#[test]
fn folded_array_read_self_eq_publishes_its_authored_assume_verbatim() {
    const AUTHORED: &str = "(not (= (select (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) (bvadd x y)) i (bvadd x y)) i) (select (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) (bvadd x y)) i (bvadd x y)) i)))";

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
        outputs[0], "unsat",
        "the faithful rebuild must certify this genuinely-unsatisfiable query: {outputs:?}"
    );
    // THE PROPERTY THIS TEST EXISTS FOR: every published `assume` is the
    // authored assertion, never the override's re-spelling of a folded leaf.
    let assumes: Vec<&str> = outputs[1]
        .lines()
        .filter(|line| line.starts_with("(assume "))
        .collect();
    assert!(
        !assumes.is_empty(),
        "a published refutation of an authored assertion must assume it:\n{}",
        outputs[1]
    );
    for line in &assumes {
        let term = line
            .splitn(3, ' ')
            .nth(2)
            .and_then(|rest| rest.strip_suffix(')'))
            .unwrap_or("");
        assert_eq!(
            term, AUTHORED,
            "an `assume` that is not the problem's assertion is `invalid` to an \
             external checker — strictly worse than an honest `hole`:\n{}",
            outputs[1]
        );
    }
    assert!(
        !outputs[1].contains(":rule hole") && !outputs[1].contains(":rule trust"),
        "the faithful rebuild must carry no unproved step:\n{}",
        outputs[1]
    );
    assert!(
        !outputs[1].contains("(assume t0 false)"),
        "never publish an unauthored false premise: {}",
        outputs[1]
    );
    let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
    assert!(
        ay_proof::terminal_trust_report(proof).is_trust_free(),
        "the published refutation must be trust-free"
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
include!("tests/dt_selector_projection.rs");
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
include!("tests/bv_congruence_leaf.rs");
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
mod authored_source_surface;
mod carcara_surface_export_table;
mod conjunct_eval;
mod decline_attribution;
mod dt_empty_identity;
mod semantic_token_census;
mod source_work;
mod unbounded_census;
mod withheld_surface;
