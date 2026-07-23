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
use ay_test_support::env::{lock_env, ScopedEnvVar};

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
    // by setting the var around the call under the workspace env lock; the
    // guard restores the previous value on every exit path.
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

    let _env_lock = lock_env();
    let _route = ScopedEnvVar::set("AY_DT_CERT_BRIDGE_ROUTE", "1");
    let claimable_with_pin = exec.dt_cert_snapshot_structurally_claimable(&snapshot);
    let claimable_without_pin = exec_nopin.dt_cert_snapshot_structurally_claimable(&snapshot_nopin);
    assert!(claimable_with_pin, "pinned snapshot must pass the precheck");
    assert!(
        !claimable_without_pin,
        "free-bridge snapshot must fail the precheck"
    );
}

// ---------------------------------------------------------------------------
// EUF-extraction faithfulness guarantee (SAT-side base-recheck campaign, the
// blocking pin #5). `dt_cert_extraction_faithful` cross-checks the certified
// finite tables against the solver's COMMITTED per-application values. These
// pins run IN-PROCESS over a real committed model (a ground satisfiable base
// solved by `execute_all`), then inject the extraction-infidelity a future
// [[regression-mutref-euf-lia-model]]-class bug would produce and confirm the
// guarantee DECLINES it while a faithful extraction still passes.
// ---------------------------------------------------------------------------

/// A ground (quantifier-free) satisfiable base: `is-Cons c`, `logic_sum(c) = 0`.
/// Solving it leaves `last_model` with logic_sum(c) committed to 0.
const FAITH_BASE: &str = r#"
    (set-logic ALL)
    (declare-datatypes ((List 0)) (((Cons (hd Int) (tl List)) (Nil))))
    (declare-const c List)
    (declare-fun logic_sum (List) Int)
    (assert (is-Cons c))
    (assert (= (logic_sum c) 0))
    (check-sat)
"#;

/// Solve a GROUND satisfiable base ending in `(check-sat)`, returning the
/// executor and its committed model.
fn solve_ground(script: &str) -> (Executor, Model) {
    let commands = parse(script).expect("parse faithfulness fixture");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute fixture");
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("sat"),
        "faithfulness ground base must be sat"
    );
    let model = exec.last_model.clone().expect("committed model after sat");
    (exec, model)
}

/// Locate the `(logic_sum <arg>)` application and its argument in `exec`.
fn find_logic_sum_app(exec: &Executor) -> (TermId, TermId) {
    let mut stack: Vec<TermId> = exec.ctx.assertions.clone();
    let mut seen: HashSet<TermId> = HashSet::default();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match exec.ctx.terms.get(t) {
            TermData::App(sym, args) => {
                if sym.name() == "logic_sum" && args.len() == 1 {
                    return (t, args[0]);
                }
                for &a in args {
                    stack.push(a);
                }
            }
            TermData::Not(i) => stack.push(*i),
            TermData::Ite(a, b, c) => {
                stack.push(*a);
                stack.push(*b);
                stack.push(*c);
            }
            _ => {}
        }
    }
    panic!("logic_sum application not found in assertions");
}

/// Build the certified `logic_sum` finite table + default + codomain the way a
/// faithful-looking extraction would: the cell for `c`'s e-class is the nonneg
/// default 0 (`0 >= 0`, which the F4 cell machinery certifies unconditionally).
#[allow(clippy::type_complexity)]
fn faith_cert_tables(
    key: &str,
) -> (
    HashMap<String, TableCertSort>,
    HashMap<String, HashMap<String, TableCertVal>>,
    HashMap<String, TableCertVal>,
) {
    let mut table: HashMap<String, TableCertVal> = HashMap::default();
    table.insert(
        key.to_string(),
        TableCertVal::Int(num_bigint::BigInt::from(0)),
    );
    let mut tables: HashMap<String, HashMap<String, TableCertVal>> = HashMap::default();
    tables.insert("logic_sum".to_string(), table);
    let mut defaults: HashMap<String, TableCertVal> = HashMap::default();
    defaults.insert(
        "logic_sum".to_string(),
        TableCertVal::Int(num_bigint::BigInt::from(0)),
    );
    let mut table_syms: HashMap<String, TableCertSort> = HashMap::default();
    table_syms.insert("logic_sum".to_string(), TableCertSort::Int);
    (table_syms, tables, defaults)
}

#[test]
fn faithfulness_declines_committed_value_disagreeing_with_certified_cell() {
    // ★ THE ADVERSARIAL ATTACK. logic_sum(c)'s COMMITTED value is negative (-5) —
    // as it would be if it reached the solver only via an EUF equality/congruence
    // chain a buggy extraction then dropped/misassigned — but the certified table
    // cell claims the nonneg default 0. The F4 cell machinery ALONE certifies
    // (0 >= 0); the faithfulness guarantee MUST decline, closing the wrong-SAT
    // hole. Without the guarantee this base would grant → vacuous proof Verified.
    let (mut exec, mut model) = solve_ground(FAITH_BASE);
    let (app, arg) = find_logic_sum_app(&exec);
    let key = exec
        .dt_cert_value_key(&model, arg)
        .expect("resolvable argument e-class");
    let (table_syms, tables, defaults) = faith_cert_tables(&key);
    let bridge_rewrite: HashMap<String, (String, Sort)> = HashMap::default();
    let snapshot = exec.ctx.assertions.clone();

    // The genuine grant is PRESERVED: with the faithful committed value (0) the
    // guarantee passes (committed 0 == certified cell 0).
    assert!(
        exec.dt_cert_extraction_faithful(
            &model,
            &snapshot,
            &table_syms,
            &tables,
            &defaults,
            &bridge_rewrite
        )
        .is_ok(),
        "faithful extraction (committed 0 == cell 0) must pass"
    );

    // Inject the extraction infidelity: pin logic_sum(c)'s COMMITTED value to -5
    // (the func_app_const_terms anchor a dropped-congruence bug would leave)
    // while the certified table cell stays 0.
    let neg5 = exec.ctx.terms.mk_int(num_bigint::BigInt::from(-5));
    model
        .euf_model
        .as_mut()
        .expect("euf model")
        .func_app_const_terms
        .insert(app, neg5);

    let err = exec
        .dt_cert_extraction_faithful(
            &model,
            &snapshot,
            &table_syms,
            &tables,
            &defaults,
            &bridge_rewrite,
        )
        .expect_err("faithfulness must DECLINE the infidel extraction");
    assert!(
        err.contains("disagrees with certified cell"),
        "unexpected decline reason: {err}"
    );
}

#[test]
fn faithfulness_declines_function_table_conflict_flag() {
    // The EUF extraction flags `logic_sum` as a cross-theory function-table
    // conflict (rows that could not be repaired exactly after model combination
    // — the regression-mutref failure mode). Its contract says consumers MUST
    // fail closed; certifying a universal over such a symbol is the wrong-SAT
    // vector. The guarantee MUST decline even though every table cell reads 0.
    let (exec, mut model) = solve_ground(FAITH_BASE);
    let (_, arg) = find_logic_sum_app(&exec);
    let key = exec
        .dt_cert_value_key(&model, arg)
        .expect("resolvable argument e-class");
    let (table_syms, tables, defaults) = faith_cert_tables(&key);
    let bridge_rewrite: HashMap<String, (String, Sort)> = HashMap::default();
    let snapshot = exec.ctx.assertions.clone();

    model
        .euf_model
        .as_mut()
        .expect("euf model")
        .function_table_conflicts
        .insert("logic_sum".to_string());

    let err = exec
        .dt_cert_extraction_faithful(
            &model,
            &snapshot,
            &table_syms,
            &tables,
            &defaults,
            &bridge_rewrite,
        )
        .expect_err("faithfulness must DECLINE a conflict-flagged relied-upon symbol");
    assert!(
        err.contains("flagged inconsistent"),
        "unexpected decline reason: {err}"
    );
}

#[test]
fn faithfulness_declines_ground_application_without_independent_anchor() {
    // A definite F4 cell is not an independent witness: it was produced by the
    // same evaluator/table extraction this gate is checking. If all committed
    // TermId-keyed anchors for a ground application disappear, the guarantee
    // must decline instead of silently trusting that cell.
    let (exec, mut model) = solve_ground(FAITH_BASE);
    let (app, arg) = find_logic_sum_app(&exec);
    let key = exec
        .dt_cert_value_key(&model, arg)
        .expect("resolvable argument e-class");
    let (table_syms, tables, defaults) = faith_cert_tables(&key);
    let bridge_rewrite: HashMap<String, (String, Sort)> = HashMap::default();
    let snapshot = exec.ctx.assertions.clone();

    let euf = model.euf_model.as_mut().expect("euf model");
    euf.func_app_const_terms.remove(&app);
    euf.int_values.remove(&app);
    euf.term_values.remove(&app);

    let err = exec
        .dt_cert_extraction_faithful(
            &model,
            &snapshot,
            &table_syms,
            &tables,
            &defaults,
            &bridge_rewrite,
        )
        .expect_err("faithfulness must DECLINE a ground app with no independent anchor");
    assert!(
        err.contains("no independent committed value"),
        "unexpected decline reason: {err}"
    );
}

#[test]
fn faithfulness_declines_ground_application_without_certified_cell() {
    // Conversely, a committed value cannot certify a table decision that does
    // not exist. Neither a row nor a default means the universal's decision at
    // this e-class is missing, so the grant must fail closed.
    let (exec, model) = solve_ground(FAITH_BASE);
    let (_, arg) = find_logic_sum_app(&exec);
    let key = exec
        .dt_cert_value_key(&model, arg)
        .expect("resolvable argument e-class");
    let (table_syms, mut tables, mut defaults) = faith_cert_tables(&key);
    tables
        .get_mut("logic_sum")
        .expect("logic_sum table")
        .clear();
    defaults.remove("logic_sum");
    let bridge_rewrite: HashMap<String, (String, Sort)> = HashMap::default();
    let snapshot = exec.ctx.assertions.clone();

    let err = exec
        .dt_cert_extraction_faithful(
            &model,
            &snapshot,
            &table_syms,
            &tables,
            &defaults,
            &bridge_rewrite,
        )
        .expect_err("faithfulness must DECLINE a ground app with no certified decision");
    assert!(
        err.contains("no certified row or default"),
        "unexpected decline reason: {err}"
    );
}

#[test]
fn precheck_flag_off_declines_bridge_shape() {
    // Flag off (removed): the W1 shape stays unclaimable — byte-identical to
    // the pre-route precheck.
    let (exec, _) = setup(FIXTURE);
    let snapshot = exec.ctx.assertions.clone();
    let _env_lock = lock_env();
    let _route = ScopedEnvVar::unset("AY_DT_CERT_BRIDGE_ROUTE");
    let claimable = exec.dt_cert_snapshot_structurally_claimable(&snapshot);
    assert!(
        !claimable,
        "flag-off precheck must decline the bridge tautology shape"
    );
}

/// Locate the datatype-sorted `Var(name)` in `exec`'s assertions.
fn find_var(exec: &Executor, name: &str) -> TermId {
    let mut stack: Vec<TermId> = exec.ctx.assertions.clone();
    let mut seen: HashSet<TermId> = HashSet::default();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match exec.ctx.terms.get(t) {
            TermData::Var(n, _) if n == name => return t,
            TermData::App(_, args) => {
                for &a in args {
                    stack.push(a);
                }
            }
            TermData::Not(i) => stack.push(*i),
            TermData::Ite(a, b, c) => {
                stack.push(*a);
                stack.push(*b);
                stack.push(*c);
            }
            _ => {}
        }
    }
    panic!("var `{name}` not found in assertions");
}

#[test]
fn value_key_fails_closed_on_free_carrier_selector_derived_term() {
    // take_some_rest / inc_some_2_list forall-13 (SAT-side base-recheck
    // campaign): the `(&mut u32, &mut List)` tuple carrier routes `logic_sum`'s
    // `List` argument through a FREE, unaxiomatized carrier selector
    // (`logic_...tuple_get_1_placeholder_Tuple2...`) applied to a CONSTRUCTED
    // tuple value. That selector application commits NO model row (the base
    // recheck carries no Tuple2 selector-over-constructor projection axiom and
    // no ground equality pinning it — a verification-consumer premise gap, the
    // `spec_axiom_dropped` class), so the derived `List` term has NO committed
    // datatype e-class. `dt_cert_value_key` MUST fail closed (`None`) — the
    // step-4 "unresolvable e-class key for a table arg" decline — rather than
    // fabricate a key, which would be a wrong-grant.
    //
    // This is precisely why take_some_rest's forall-13 DECLINES while sum_x's
    // forall-5 GRANTS: sum_x's `logic_sum` args bottom out at committed native
    // selectors over committed `List` consts (every arg has a committed
    // e-class); take_some_rest's route through the free carrier selector and
    // bottom out at an uncommitted point. It is NOT resolvable by the W2
    // argument-value congruence completion (`dt_cert_build_uf_value_index`):
    // there is nothing committed to be congruent to. Fail-closed decline is the
    // sound outcome. See memory/sat-side-base-recheck-campaign.md.
    let (mut exec, model) = solve_ground(
        r#"
        (set-logic ALL)
        (declare-datatypes ((List 0)) (((Cons (hd Int) (tl List)) (Nil))))
        (declare-const self List)
        (declare-fun logic_sum (List) Int)
        (assert (is-Cons self))
        (assert (= (logic_sum self) 0))
        (check-sat)
    "#,
    );
    // Positive control (the forall-5 case): a committed `List` const resolves to
    // a datatype e-class.
    let self_tid = find_var(&exec, "self");
    assert!(
        exec.dt_cert_value_key(&model, self_tid).is_some(),
        "a committed List const must resolve to a datatype e-class"
    );
    // Fail-closed (the forall-13 case): a FREE carrier-selector application whose
    // datatype value the model never committed has NO e-class key. (Minted after
    // the solve, so it is committed to nothing — exactly the base-recheck state
    // where the carrier chain is a solver don't-care.)
    let list_sort = exec.ctx.terms.sort(self_tid).clone();
    let carrier_tail = exec.ctx.terms.mk_app(
        Symbol::named("logic_____VERIFICATION_CONSUMER__tuple__get__1__placeholder_Tuple2_carrier"),
        [self_tid],
        list_sort,
    );
    assert_eq!(
        exec.dt_cert_value_key(&model, carrier_tail),
        None,
        "a free carrier-selector-derived List term with no committed e-class must \
         fail closed (the take_some_rest forall-13 decline), never fabricate a key"
    );
}
