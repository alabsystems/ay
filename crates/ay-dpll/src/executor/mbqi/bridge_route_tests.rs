// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit pins for the W1 bridge route (`AY_DT_CERT_BRIDGE_ROUTE`, SAT-side
//! base-recheck campaign): the `dt_cert_classify_f2_bridge` recognizer and the
//! MANDATORY selector-bridge-premise gate `dt_cert_bridge_claim_check`.
//!
//! These run IN-PROCESS with no env flags and no solving (the classifier and
//! the gate are pure functions of the term store + datatype declarations), so
//! the wrong-selector and free-bridge decline branches are pinned
//! deterministically — the integration-level subprocess tests in
//! `executor_tests::quantifier::dt_model_cert` pin the shadow-withhold and the
//! end-to-end declines, but a wrong-pin base is quantifier-hard (its main
//! solve churns for minutes), so THIS is where its gate branch is pinned.

use super::*;
use ay_frontend::parse;

/// Execute the declares + asserts of `script` and return `(executor,
/// foralls)` where `foralls` is each top-level forall's `(var_names, body)`.
fn setup(script: &str) -> (Executor, Vec<(Vec<String>, TermId)>) {
    let commands = parse(script).expect("parse bridge-route fixture");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("execute fixture");
    let mut foralls = Vec::new();
    for &a in &exec.ctx.assertions.clone() {
        if let TermData::Forall(vars, body, _) = exec.ctx.terms.get(a) {
            let names: Vec<String> = vars.iter().map(|(n, _)| n.clone()).collect();
            foralls.push((names, *body));
        }
    }
    (exec, foralls)
}

const FIXTURE: &str = r#"
    (set-logic ALL)
    (declare-datatypes ((L2 0)) (((C2 (s0 Int) (s1 L2) (s2 L2)) (N2))))
    (declare-fun epg (L2) L2)
    (assert (forall ((a Int) (b L2) (c L2)) (= c (epg (C2 a b c)))))
    (assert (forall ((y L2)) (or (= (epg y) (s2 y)) (not (is-C2 y)))))
"#;

#[test]
fn recognizer_matches_bridge_tautology_shape() {
    let (exec, foralls) = setup(FIXTURE);
    let (names, body) = &foralls[0];
    let claim = exec.dt_cert_classify_f2_bridge(names, *body);
    assert_eq!(
        claim,
        Some(("epg".to_string(), "C2".to_string(), 2)),
        "the W1 recognizer must claim `epg(C2(a,b,c)) = c` as (epg, C2, field 2)"
    );
    // The pin forall is NOT a W1 shape (it is F3's).
    let (pin_names, pin_body) = &foralls[1];
    assert_eq!(exec.dt_cert_classify_f2_bridge(pin_names, *pin_body), None);
}

#[test]
fn recognizer_rejects_native_selector_head() {
    // `s2(C2(a,b,c)) = c` is F2's territory (declared selector head) — the
    // bridge recognizer must NOT claim it.
    let (exec, foralls) = setup(
        r#"
        (set-logic ALL)
        (declare-datatypes ((L2 0)) (((C2 (s0 Int) (s1 L2) (s2 L2)) (N2))))
        (assert (forall ((a Int) (b L2) (c L2)) (= c (s2 (C2 a b c)))))
    "#,
    );
    let (names, body) = &foralls[0];
    // (Elaboration may already fold the native selector-over-constructor to
    // the bare binder; either way the BRIDGE recognizer must not claim it —
    // the declared-selector head is F2's, and a folded `(= c c)` is neither.)
    assert_eq!(exec.dt_cert_classify_f2_bridge(names, *body), None);
}

#[test]
fn premise_gate_passes_on_matching_pin() {
    let (exec, _) = setup(FIXTURE);
    let mut bridge_rewrite: HashMap<String, (String, Sort)> = HashMap::default();
    bridge_rewrite.insert(
        "epg".to_string(),
        ("s2".to_string(), Sort::Uninterpreted("L2".to_string())),
    );
    let checked = exec.dt_cert_bridge_claim_check(&bridge_rewrite, "epg", "C2", 2);
    assert_eq!(checked, Ok("s2".to_string()));
}

#[test]
fn premise_gate_declines_free_bridge() {
    // NO pin in the rewrite map: the bridge is genuinely free — a claim would
    // be a wrong-grant. MUST decline, fail-closed.
    let (exec, _) = setup(FIXTURE);
    let bridge_rewrite: HashMap<String, (String, Sort)> = HashMap::default();
    let checked = exec.dt_cert_bridge_claim_check(&bridge_rewrite, "epg", "C2", 2);
    let err = checked.expect_err("free bridge must decline");
    assert!(
        err.contains("has no in-snapshot selector-bridge pin"),
        "unexpected decline reason: {err}"
    );
}

#[test]
fn premise_gate_declines_wrong_selector_pin() {
    // Pinned to `s1` while the tautology claims field 2 (`s2`): under M' the
    // body would rewrite to `s1(C2(a,b,c)) = c` — NOT a tautology (z3: such a
    // base is UNSAT). MUST decline, fail-closed.
    let (exec, _) = setup(FIXTURE);
    let mut bridge_rewrite: HashMap<String, (String, Sort)> = HashMap::default();
    bridge_rewrite.insert(
        "epg".to_string(),
        ("s1".to_string(), Sort::Uninterpreted("L2".to_string())),
    );
    let checked = exec.dt_cert_bridge_claim_check(&bridge_rewrite, "epg", "C2", 2);
    let err = checked.expect_err("wrong-selector pin must decline");
    assert!(
        err.contains("is pinned to `s1`, not"),
        "unexpected decline reason: {err}"
    );
}

#[test]
fn premise_gate_declines_out_of_range_field_index() {
    let (exec, _) = setup(FIXTURE);
    let mut bridge_rewrite: HashMap<String, (String, Sort)> = HashMap::default();
    bridge_rewrite.insert(
        "epg".to_string(),
        ("s2".to_string(), Sort::Uninterpreted("L2".to_string())),
    );
    assert!(exec
        .dt_cert_bridge_claim_check(&bridge_rewrite, "epg", "C2", 3)
        .is_err());
    // Nullary constructor: no selectors at any index.
    assert!(exec
        .dt_cert_bridge_claim_check(&bridge_rewrite, "epg", "N2", 0)
        .is_err());
}

#[test]
fn precheck_claims_only_with_matching_in_snapshot_pin() {
    // The precheck's W1 leg applies the SAME premise gate, model-free: with
    // the pin present the snapshot is claimable; with the pin absent (or
    // mismatched) it is not. Env-gated: force the flag via a child-free check
    // by setting the var around the call — serial test threads make this safe,
    // and the var is restored either way.
    let (exec, _) = setup(FIXTURE);
    let snapshot = exec.ctx.assertions.clone();
    let (exec_nopin, _) = setup(
        r#"
        (set-logic ALL)
        (declare-datatypes ((L2 0)) (((C2 (s0 Int) (s1 L2) (s2 L2)) (N2))))
        (declare-fun epg (L2) L2)
        (assert (forall ((a Int) (b L2) (c L2)) (= c (epg (C2 a b c)))))
    "#,
    );
    let snapshot_nopin = exec_nopin.ctx.assertions.clone();

    let prev = std::env::var_os("AY_DT_CERT_BRIDGE_ROUTE");
    std::env::set_var("AY_DT_CERT_BRIDGE_ROUTE", "1");
    let claimable_with_pin = exec.dt_cert_snapshot_structurally_claimable(&snapshot);
    let claimable_without_pin = exec_nopin.dt_cert_snapshot_structurally_claimable(&snapshot_nopin);
    match prev {
        Some(v) => std::env::set_var("AY_DT_CERT_BRIDGE_ROUTE", v),
        None => std::env::remove_var("AY_DT_CERT_BRIDGE_ROUTE"),
    }
    assert!(claimable_with_pin, "pinned snapshot must pass the precheck");
    assert!(
        !claimable_without_pin,
        "free-bridge snapshot must fail the precheck"
    );
}

#[test]
fn precheck_flag_off_declines_bridge_shape() {
    // Flag off (removed): the W1 shape stays unclaimable — byte-identical to
    // the pre-route precheck.
    let (exec, _) = setup(FIXTURE);
    let snapshot = exec.ctx.assertions.clone();
    let prev = std::env::var_os("AY_DT_CERT_BRIDGE_ROUTE");
    std::env::remove_var("AY_DT_CERT_BRIDGE_ROUTE");
    let claimable = exec.dt_cert_snapshot_structurally_claimable(&snapshot);
    if let Some(v) = prev {
        std::env::set_var("AY_DT_CERT_BRIDGE_ROUTE", v);
    }
    assert!(
        !claimable,
        "flag-off precheck must decline the bridge tautology shape"
    );
}
