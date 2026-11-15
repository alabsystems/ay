// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! W12 guarded quantifiers at the original-query and public SAT boundaries.
//!
//! Controlled candidates isolate independent checking from search heuristics.
//! The same source formula receives both a valid and an invalid model; neither
//! a quantified proxy assignment nor rewritten source can justify admission.
//!
//! HISTORY 2026-09-12 -> 2026-09-14. The two `..._int_sat_funnel_...` tests had
//! never passed. The measured cause was an ORDERING one, not a missing
//! capability: for `wanted=4` (a genuine witness) `emit_sat_verdict` returned
//! `Unknown`, downgrading at phase `model-validation` with detail "self-check:
//! model could not be independently certified (1 of 3 assertion(s)
//! unverified)". The unverified one was the `exists` — the ground validation
//! pipeline SKIPS quantified assertions
//! (`ValidationStats::skipped_quantifier`), that counted as `incomplete`, and
//! the fail-closed `--self-check` arm degraded `Sat -> Unknown` — while the
//! gate that decides exactly this assertion
//! (`apply_quantified_model_failclosed_gate`) runs LATER in the same funnel.
//! The sibling `guarded_range_int_source_confirms_witness_and_refutes_excluded_endpoint`
//! has been green throughout on the same fixture.
//!
//! FIX (#selfcert-quantified): the `--self-check` completeness ledger now
//! credits a skipped quantified assertion that the INDEPENDENT model checker
//! decides exactly `true` — route (1) of
//! `check_quantified_conjunct_against_model`, its strongest, with no surrogate
//! and no nested solve. Credit is positive-only and per assertion; the
//! quantified gate and the independent gate still run afterwards with unchanged
//! authority, so the change can only stop a premature downgrade, never publish
//! a `sat` a later gate would refuse. The negative controls below pin that:
//! `wanted=5` (refuted) and the opaque-`f` existential (undecidable) must both
//! still come out `Unknown`.

#![cfg(test)]

use ay_frontend::parse;
use ay_lia::LiaModel;
use num_bigint::BigInt;

use super::*;

const BV64_SLICE: &str = r#"
    (set-logic ALL)
    (declare-const len (_ BitVec 64))
    (declare-const edge (_ BitVec 64))
    (declare-const a (Array (_ BitVec 64) (_ BitVec 8)))
    (declare-const b (Array (_ BitVec 64) (_ BitVec 8)))
    (assert (= len (_ bv4 64)))
    (assert (= a
        ((as const (Array (_ BitVec 64) (_ BitVec 8))) (_ bv7 8))))
    (assert (= b (store
        ((as const (Array (_ BitVec 64) (_ BitVec 8))) (_ bv7 8))
        edge (_ bv9 8))))
    (assert (forall ((i (_ BitVec 64)))
        (=> (bvult i len) (= (select a i) (select b i)))))
"#;

const INT_EXISTS: &str = r#"
    (set-logic LIA)
    (declare-const lo Int)
    (declare-const hi Int)
    (declare-const wanted Int)
    (assert (= lo 2))
    (assert (= hi 5))
    (assert (exists ((i Int))
        (and (<= lo i) (< i hi) (= i wanted))))
"#;

/// An existential the independent model checker CANNOT decide: the witness
/// would have to satisfy an uninterpreted `f` that the emitted model does not
/// interpret. Same shape as `INT_EXISTS`, minus the decidability.
const INT_EXISTS_OPAQUE: &str = r#"
    (set-logic ALL)
    (declare-const wanted Int)
    (declare-fun f (Int) Int)
    (assert (= wanted 4))
    (assert (exists ((i Int)) (= (f i) wanted)))
"#;

fn loaded_candidate(source: &str) -> Executor {
    let mut exec = Executor::new();
    let commands = parse(source).expect("valid guarded-quantifier source");
    let outputs = exec
        .execute_all(&commands)
        .expect("load source without solving");
    assert!(
        outputs.is_empty(),
        "candidate fixtures must not run a query"
    );
    // Loading assertions does not start a decision. Use the ordinary public
    // boundary before installing the candidate: it rotates query authority and
    // opens the same shared gate budget as a real check-sat command.
    exec.begin_external_decision_query(false);
    exec
}

fn slice_candidate(edge: u64) -> Executor {
    let mut exec = loaded_candidate(BV64_SLICE);
    let mut model = Model::empty();
    for (name, value) in [("len", 4), ("edge", edge)] {
        let variable = exec.ctx.terms.mk_var(name, Sort::bitvec(64));
        model.completed_values.insert(
            variable,
            EvalValue::BitVec {
                value: BigInt::from(value),
                width: 64,
            },
        );
    }
    exec.last_model = Some(model);
    exec
}

fn existential_candidate(wanted: i64) -> Executor {
    let mut exec = loaded_candidate(INT_EXISTS);
    let mut values = DetHashMap::default();
    for (name, value) in [("lo", 2), ("hi", 5), ("wanted", wanted)] {
        let variable = exec.ctx.terms.mk_var(name, Sort::Int);
        values.insert(variable, BigInt::from(value));
    }
    let mut model = Model::empty();
    model.lia_model = Some(LiaModel { values });
    exec.last_model = Some(model);
    exec
}

fn opaque_existential_candidate() -> Executor {
    let mut exec = loaded_candidate(INT_EXISTS_OPAQUE);
    let mut values = DetHashMap::default();
    let wanted = exec.ctx.terms.mk_var("wanted", Sort::Int);
    values.insert(wanted, BigInt::from(4));
    let mut model = Model::empty();
    model.lia_model = Some(LiaModel { values });
    exec.last_model = Some(model);
    exec
}

fn original_quantifier(exec: &Executor) -> TermId {
    let root = *exec.ctx.assertions.last().expect("quantified source root");
    assert!(matches!(
        exec.ctx.terms.get(root),
        TermData::Forall(..) | TermData::Exists(..)
    ));
    root
}

fn assert_original_check(exec: &mut Executor, expected: bool) {
    let root = original_quantifier(exec);
    let terms_before = exec.ctx.terms.len();
    {
        let model = exec.last_model.as_ref().expect("controlled candidate");
        let view = IndependentModelView::new(exec, model);
        view.ensure_def_index().unwrap();
        let value = ay_model_check::evaluate_term(&exec.ctx.terms, &view, root);
        assert!(
            matches!(&value, EvalOutcome::Value(ModelValue::Bool(actual)) if *actual == expected),
            "the original range body must evaluate exactly: {value:?}"
        );
    }
    let checked = exec.check_quantified_conjunct_against_model(root);
    assert!(matches!(
        (checked, expected),
        (QuantifiedModelCheck::Confirmed, true)
            | (QuantifiedModelCheck::Refuted { clean: true }, false)
    ));
    assert_eq!(
        exec.ctx.terms.len(),
        terms_before,
        "an exact source result must not construct folded bodies or nested probes"
    );
    assert_eq!(original_quantifier(exec), root);
}

#[test]
fn guarded_range_bv64_source_confirms_outside_store_and_refutes_inside_store() {
    // Both candidates satisfy every ground assertion. Only the store's model
    // index changes: 4 is outside [0,4), whereas 3 falsifies its last cell.
    assert_original_check(&mut slice_candidate(4), true);
    assert_original_check(&mut slice_candidate(3), false);
}

#[test]
fn guarded_range_int_source_confirms_witness_and_refutes_excluded_endpoint() {
    // The formula is unchanged; wanted=4 has a witness and wanted=5 does not.
    assert_original_check(&mut existential_candidate(4), true);
    assert_original_check(&mut existential_candidate(5), false);
}

#[test]
fn guarded_range_bv64_confirmation_is_consumed_by_independent_public_gate() {
    let mut exec = slice_candidate(4);
    assert!(matches!(
        exec.confirm_sat_with_independent_gate(),
        GateVerdict::ConfirmedSat
    ));
    assert_eq!(
        exec.apply_quantified_model_failclosed_gate(SolveResult::Sat),
        SolveResult::Sat
    );
    assert_eq!(
        exec.last_statistics
            .get_string("model_check_gate.quantified"),
        Some("confirmed")
    );
    assert!(exec.quantified_model_confirmation.is_some());
    assert_eq!(
        exec.apply_independent_model_gate(SolveResult::Sat),
        SolveResult::Sat
    );
    assert_eq!(
        exec.last_statistics.get_string("model_check_gate.result"),
        Some("confirmed-sat")
    );
    assert!(exec.quantified_model_confirmation.is_none());
}

#[test]
fn guarded_range_bv64_authored_snapshot_cannot_lose_refuted_quantifier() {
    let mut exec = slice_candidate(3);
    let root = original_quantifier(&exec);
    exec.independent_gate_authored_assertions = Some(exec.ctx.assertions.clone());
    assert_eq!(exec.ctx.assertions.pop(), Some(root));
    assert!(matches!(
        exec.confirm_sat_with_independent_gate(),
        GateVerdict::ModelViolates { assertion } if assertion == root
    ));
    assert_eq!(
        exec.apply_quantified_model_failclosed_gate(SolveResult::Sat),
        SolveResult::Unknown
    );
    assert_eq!(
        exec.last_statistics
            .get_string("model_check_gate.quantified"),
        Some("refuted")
    );
    assert!(exec.last_model.is_none());
    assert!(exec.quantified_model_confirmation.is_none());
    assert!(exec.last_sat_certificate.is_none());
}

#[test]
fn guarded_range_int_assumption_is_in_exact_independent_root_window() {
    for (wanted, expected) in [(4, SolveResult::Sat), (5, SolveResult::Unknown)] {
        let mut exec = existential_candidate(wanted);
        let root = original_quantifier(&exec);
        assert_eq!(exec.ctx.assertions.pop(), Some(root));
        let base = exec.ctx.assertions.clone();
        exec.independent_gate_authored_assertions = Some(base.clone());
        exec.last_assumptions = Some(vec![root]);
        assert_eq!(
            exec.independent_gate_query_roots().unwrap(),
            [base.clone(), vec![root]].concat()
        );

        let quantified = exec.apply_quantified_model_failclosed_gate(SolveResult::Sat);
        assert_eq!(quantified, expected);
        assert_eq!(exec.apply_independent_model_gate(quantified), expected);
        assert_eq!(
            exec.ctx.assertions, base,
            "assumptions must remain temporary"
        );
        assert!(exec.quantified_model_confirmation.is_none());
        if expected == SolveResult::Sat {
            assert_eq!(
                exec.last_statistics.get_string("model_check_gate.result"),
                Some("confirmed-sat")
            );
        } else {
            assert!(exec.last_model.is_none());
            assert!(exec.last_sat_certificate.is_none());
        }
    }
}

#[test]
fn guarded_range_int_sat_funnel_mints_only_for_valid_candidate() {
    for (wanted, expected) in [(4, SolveResult::Sat), (5, SolveResult::Unknown)] {
        let mut exec = existential_candidate(wanted);
        exec.set_self_check(true);
        let result = exec
            .emit_sat_verdict(SolveResult::Sat, &[])
            .expect("SAT funnel");
        assert_eq!(
            result,
            expected,
            "wanted={wanted}: the funnel downgraded at phase {:?} with detail {:?}",
            exec.last_statistics.get_string("unknown.phase"),
            exec.last_statistics.get_string("unknown.detail"),
        );
        if expected == SolveResult::Sat {
            assert!(exec.last_sat_certificate.is_some());
            assert!(exec.last_model_validated);
            assert_eq!(
                exec.last_statistics
                    .get_string("model_check_gate.quantified"),
                Some("confirmed")
            );
            assert_eq!(
                exec.last_statistics.get_string("model_check_gate.result"),
                Some("confirmed-sat")
            );
        } else {
            assert!(exec.last_sat_certificate.is_none());
            assert!(exec.last_model.is_none());
            assert!(!exec.last_model_validated);
        }
    }
}

#[test]
fn guarded_range_int_sat_funnel_checks_and_restores_temporary_assumption() {
    for (wanted, expected) in [(4, SolveResult::Sat), (5, SolveResult::Unknown)] {
        let mut exec = existential_candidate(wanted);
        let root = original_quantifier(&exec);
        assert_eq!(exec.ctx.assertions.pop(), Some(root));
        let base = exec.ctx.assertions.clone();
        exec.last_assumptions = Some(vec![root]);
        exec.set_self_check(true);

        let result = exec
            .emit_sat_verdict(SolveResult::Sat, &[root])
            .expect("assumption SAT funnel");
        assert_eq!(
            result,
            expected,
            "wanted={wanted}: the assumption funnel downgraded at phase {:?} \
             with detail {:?}",
            exec.last_statistics.get_string("unknown.phase"),
            exec.last_statistics.get_string("unknown.detail"),
        );
        assert_eq!(exec.ctx.assertions, base);
        assert_eq!(
            exec.last_sat_certificate.is_some(),
            expected == SolveResult::Sat
        );
        if expected == SolveResult::Unknown {
            assert!(exec.last_model.is_none());
            assert!(!exec.last_model_validated);
        }
    }
}

/// The evidence the `--self-check` ledger reads is THREE-VALUED, and each value
/// is earned by an exact independent verdict. This is that function on its own,
/// at all three outcomes.
#[test]
fn guarded_range_int_quantified_skip_evidence_is_exact_and_three_valued() {
    let confirmed = existential_candidate(4);
    let root = original_quantifier(&confirmed);
    assert_eq!(
        confirmed.independent_quantifier_skip_evidence(&[root]),
        QuantifierSkipEvidence::Confirmed(1),
        "wanted=4 has a witness the independent checker finds exactly"
    );

    let refuted = existential_candidate(5);
    let root = original_quantifier(&refuted);
    assert_eq!(
        refuted.independent_quantifier_skip_evidence(&[root]),
        QuantifierSkipEvidence::Refuted(root),
        "wanted=5 is not merely unverified — the emitted model FALSIFIES it"
    );

    let opaque = opaque_existential_candidate();
    let root = original_quantifier(&opaque);
    assert_eq!(
        opaque.independent_quantifier_skip_evidence(&[root]),
        QuantifierSkipEvidence::Indeterminate,
        "an UNDECIDABLE quantified assertion is evidence for neither verdict"
    );
}

/// Negative control for the funnel itself: an undecidable quantified assertion
/// must still take the fail-closed `--self-check` downgrade. If this ever goes
/// green as `Sat`, the ledger has started crediting something other than an
/// exact independent `true`.
#[test]
fn guarded_range_int_sat_funnel_refuses_an_undecidable_quantifier() {
    let mut exec = opaque_existential_candidate();
    exec.set_self_check(true);
    let result = exec
        .emit_sat_verdict(SolveResult::Sat, &[])
        .expect("SAT funnel");
    assert_eq!(
        result,
        SolveResult::Unknown,
        "the funnel reported {result:?} at phase {:?} with detail {:?}",
        exec.last_statistics.get_string("unknown.phase"),
        exec.last_statistics.get_string("unknown.detail"),
    );
    assert!(exec.last_sat_certificate.is_none());
    assert!(!exec.last_model_validated);
}
