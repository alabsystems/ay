// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV-MBQI's symbolic entailment and `discharged-trust` (mutation tests for
//! its `checked_sat_authority_ground_solve` probe).
//!
//! An entailment `G ⊨ ∀x. body` the check establishes mints the full-domain
//! grant the publication gate defers to without re-deciding the universal. On
//! fcdf5b51e its refutation of `G ∧ ¬body[x]` admitted `discharged-trust` at
//! every rigor and the grant was recorded as certified: measured on
//! `∀x:bv32. bv2nat(x) + |c| ≥ 0` (a lone `trust` step), AY published `sat`
//! recorded `deferred-certified-bv-full-domain` under `--rigor strict` too.

#![cfg(test)]

use ay_frontend::parse;

use super::*;
use crate::executor::quantifier_loop::result_mapping::trust_forge::ForgedTrustGuard;
use crate::executor::unsat_cert::ProbeUnsatAuthority;

/// `x = #xffffffff` falsifies the universal under `b < #xffffffff`: not
/// entailed.
const NOT_ENTAILED: &str = "(set-logic ALL)(declare-const b (_ BitVec 32))\
    (assert (bvult b #xffffffff))\
    (assert (forall ((x (_ BitVec 32))) (bvule x b)))";

/// `b < 16 ⊨ ∀x. x < b → x < 16`.
const ENTAILED: &str = "(set-logic ALL)(declare-const b (_ BitVec 32))\
    (assert (bvult b #x00000010))\
    (assert (forall ((x (_ BitVec 32))) (=> (bvult x b) (bvult x #x00000010))))";

fn loaded(source: &str, strict_rigor: bool) -> (Executor, Vec<(String, Sort)>, TermId) {
    let mut exec = Executor::new();
    exec.set_strict_grant_evidence_required(strict_rigor);
    let commands = parse(source).expect("valid source");
    let outputs = exec.execute_all(&commands).expect("load without solving");
    assert!(outputs.is_empty(), "fixtures must not run a query");
    exec.begin_external_decision_query(false);
    let root = *exec.ctx.assertions.last().expect("quantified root");
    let TermData::Forall(vars, body, _) = exec.ctx.terms.get(root) else {
        panic!("the last root is the universal");
    };
    let (vars, body) = (vars.clone(), *body);
    (exec, vars, body)
}

/// `(check, forged)` with every sat-authority probe forged as a
/// `discharged-trust` refutation.
fn forged_check(source: &str, strict_rigor: bool) -> (BvForallCheck, usize) {
    let (mut exec, vars, body) = loaded(source, strict_rigor);
    let guard = ForgedTrustGuard::sat_authority_probes();
    let check = exec.bv_symbolic_entailment_check(&vars, body, LogicCategory::Other);
    (check, guard.forged())
}

/// Under strict rigor a forged `discharged-trust` refutation establishes no
/// entailment, false (where accepting it would be a wrong `sat`) or true.
/// `forged > 0` is the non-vacuity check.
#[test]
fn a_forged_trust_refutation_establishes_no_entailment_under_strict_rigor() {
    for (name, source) in [("not-entailed", NOT_ENTAILED), ("entailed", ENTAILED)] {
        let (check, forged) = forged_check(source, true);
        assert!(forged > 0, "{name}: the check must reach its probe");
        assert!(
            matches!(check, BvForallCheck::Unknown),
            "{name}: a forged trust refutation proved an entailment under --rigor strict"
        );
    }
}

/// At default rigor the class is admitted, as a directly published `unsat` on
/// it is, but never as checked: the entailment carries `DischargedTrust`, so
/// the grant it mints is recorded `deferred-discharged-trust-full-domain`.
#[test]
fn a_forged_trust_refutation_is_carried_as_trust_at_default_rigor() {
    for (name, source) in [("not-entailed", NOT_ENTAILED), ("entailed", ENTAILED)] {
        let (check, forged) = forged_check(source, false);
        assert!(forged > 0, "{name}: the check must reach its probe");
        assert!(
            matches!(
                check,
                BvForallCheck::Holds(ProbeUnsatAuthority::DischargedTrust)
            ),
            "{name}: a trust entailment must carry its class"
        );
    }
}

/// The negative twin: a checked refutation still establishes a true
/// entailment as checked at either rigor, and a false one stays undecided.
#[test]
fn a_checked_refutation_still_establishes_an_entailment() {
    for strict_rigor in [false, true] {
        let (mut exec, vars, body) = loaded(ENTAILED, strict_rigor);
        let check = exec.bv_symbolic_entailment_check(&vars, body, LogicCategory::Other);
        assert!(
            matches!(check, BvForallCheck::Holds(ProbeUnsatAuthority::Checked)),
            "strict={strict_rigor}: b < 16 entails the universal"
        );
        let (mut exec, vars, body) = loaded(NOT_ENTAILED, strict_rigor);
        let check = exec.bv_symbolic_entailment_check(&vars, body, LogicCategory::Other);
        assert!(
            matches!(check, BvForallCheck::Unknown),
            "strict={strict_rigor}: x = #xffffffff falsifies the universal"
        );
    }
}

/// The grant records the class it rests on: a full-domain authority resting on
/// `discharged-trust` is installed and the publication gate records
/// `deferred-discharged-trust-full-domain`, never the certified label.
#[test]
fn the_full_domain_grant_records_a_trust_entailment_as_such() {
    for (admission, label) in [
        (
            ProbeUnsatAuthority::Checked,
            "deferred-certified-bv-full-domain",
        ),
        (
            ProbeUnsatAuthority::DischargedTrust,
            "deferred-discharged-trust-full-domain",
        ),
    ] {
        let (mut exec, _, _) = loaded(ENTAILED, false);
        let roots = exec.independent_gate_query_roots().unwrap();
        exec.last_model = Some(crate::executor::model::Model::empty());
        let evidence =
            CheckedBvFullDomainSatAuthority::for_test(&exec, &roots).resting_on(admission);
        assert!(exec.install_bv_full_domain_sat_authority(evidence));
        assert_eq!(
            exec.apply_quantified_model_failclosed_gate(SolveResult::Sat),
            SolveResult::Sat
        );
        assert_eq!(
            exec.last_statistics
                .get_string("model_check_gate.quantified"),
            Some(label),
            "{admission:?}"
        );
    }
}
