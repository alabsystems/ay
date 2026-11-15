// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The independent gate's array and datatype values do not depend on
//! evaluation order, so `(get-model)` prints the values the gate checked
//! (#gate-exact-leaf-memo).
//!
//! `(= u w)` makes each of `u` and `w` the other's definition. Resolving one
//! cuts the cycle at it, so the other falls back to its own model entry. That
//! value used to be cached, so whichever of the two an evaluation reached
//! first decided both: the gate, walking the assertions, checked
//! `u = w = u_M`, while `gate_emit_reconstructions`, walking the declared
//! constants for `(get-model)`, printed `u = w = w_M`. On the QF_AUFBV
//! reproducer `invalid_model_min1` that printed model falsified
//! `(= (select (select m0 x) #x5) (select u #x5))` while the gate said
//! `confirmed-sat`. A datatype alias `(= d1 d2)` did the same through the
//! datatype memo, and an array defined from `(fld d1)` inherited it.

use super::*;
use ay_arrays::ArrayInterpretation;
use ay_frontend::parse;
use ay_model_check::GateVerdict;

/// `u` before `w`, so `(get-model)` reconstructs `u` first.
const DECLARATIONS: &str = "
    (set-logic QF_ABV)
    (declare-const u (Array (_ BitVec 4) (_ BitVec 3)))
    (declare-const w (Array (_ BitVec 4) (_ BitVec 3)))
";
/// Reads `w` first, so the gate resolves `w` before `u`.
const READ_W: &str = "(assert (= (select w #x0) #b100))";
const ALIAS: &str = "(assert (= u w))";
const READ_U: &str = "(assert (= (select u #x5) #b000))";

fn cells(stores: &[(&str, &str)]) -> ArrayInterpretation {
    ArrayInterpretation {
        index_sort: Some(Sort::bitvec(4)),
        element_sort: Some(Sort::bitvec(3)),
        default: Some("#b000".to_string()),
        stores: stores
            .iter()
            .map(|&(index, value)| (index.to_string(), value.to_string()))
            .collect(),
    }
}

fn declared(exec: &Executor, name: &str) -> TermId {
    exec.ctx
        .symbol_iter()
        .find(|(symbol, _)| *symbol == name)
        .and_then(|(_, info)| info.term)
        .unwrap_or_else(|| panic!("`{name}` is declared"))
}

/// Assert `assertions` in order over a sat candidate whose array model holds
/// `u_cells` for `u` and `w_cells` for `w`.
fn candidate(assertions: &[&str], u_cells: &[(&str, &str)], w_cells: &[(&str, &str)]) -> Executor {
    let script = format!("{DECLARATIONS}{}", assertions.concat());
    let commands = parse(&script).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("declarations and assertions execute");
    let (u, w) = (declared(&exec, "u"), declared(&exec, "w"));
    let mut model = empty_model();
    model.array_model = Some(ArrayModel {
        array_values: HashMap::from_iter([(u, cells(u_cells)), (w, cells(w_cells))]),
        ..Default::default()
    });
    model.bv_model = Some(BvModel {
        values: HashMap::default(),
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    exec.last_result = Some(SolveResult::Sat);
    exec.last_model = Some(model);
    exec
}

/// `u_M` satisfies both reads and `w_M` neither: `u = w = u_M` is a model,
/// `u = w = w_M` is not, and the cached cut picked one of the two by order.
const U_M: &[(&str, &str)] = &[("#x0", "#b100")];
const W_M: &[(&str, &str)] = &[("#x5", "#b100")];

/// The gate's verdict on the same candidate must not depend on the order in
/// which the assertions reach it. Before the fix, `w`-first confirmed (with
/// `u = w = u_M`) and `u`-first refuted (with `u = w = w_M`).
#[test]
fn gate_verdict_on_an_inconsistent_alias_does_not_depend_on_assertion_order() {
    for order in [[READ_W, ALIAS, READ_U], [READ_U, ALIAS, READ_W]] {
        let exec = candidate(&order, U_M, W_M);
        let verdict = exec.confirm_sat_with_independent_gate();
        assert!(
            !matches!(verdict, GateVerdict::ConfirmedSat),
            "order {order:?}: the gate confirmed a model `(get-model)` does not print"
        );
    }
}

/// Every top-level read of `u` and `w` is now the same function of the model
/// in every view, so the reconstruction `(get-model)` prints for each is the
/// one the gate evaluates, and `(= u w)` is refuted on those exact values.
/// Which values they are is the cycle-cut rule, pinned here only as the
/// witness of that agreement: `u` resolves through `w` (cut at `u`) to `w_M`,
/// and `w` through `u` to `u_M`, whichever is asked first.
#[test]
fn printed_alias_reconstruction_is_the_value_the_gate_refutes() {
    let exec = candidate(&[READ_W, ALIAS, READ_U], U_M, W_M);
    let alias = exec.ctx.assertions[1];
    assert!(matches!(
        exec.confirm_sat_with_independent_gate(),
        GateVerdict::ModelViolates { assertion } if assertion == alias
    ));
    let model = exec.last_model.as_ref().expect("model installed");
    let printed = exec.gate_emit_reconstructions(model).unwrap();
    let (u, w) = (declared(&exec, "u"), declared(&exec, "w"));
    assert!(
        printed[&u].contains("#x5 #b100") && !printed[&u].contains("#x0 #b100"),
        "u must print w's entry: {}",
        printed[&u]
    );
    assert!(
        printed[&w].contains("#x0 #b100") && !printed[&w].contains("#x5 #b100"),
        "w must print u's entry: {}",
        printed[&w]
    );
}

/// Negative twin: with one entry for both arrays the alias is consistent, the
/// gate confirms in either order, and `(get-model)` prints that entry for both.
#[test]
fn gate_confirms_a_consistent_alias_in_either_order() {
    for order in [[READ_W, ALIAS, READ_U], [READ_U, ALIAS, READ_W]] {
        let exec = candidate(&order, U_M, U_M);
        assert!(
            matches!(
                exec.confirm_sat_with_independent_gate(),
                GateVerdict::ConfirmedSat
            ),
            "order {order:?}: a consistent alias model must confirm"
        );
        let model = exec.last_model.as_ref().expect("model installed");
        let printed = exec.gate_emit_reconstructions(model).unwrap();
        let (u, w) = (declared(&exec, "u"), declared(&exec, "w"));
        assert_eq!(printed[&u], printed[&w]);
    }
}

/// The datatype twin (#gate-exact-leaf-memo). `d1` and `d2` alias each other
/// and `u` is defined from `(fld d1)`; the model commits `(fld d1)` and
/// `(fld d2)` separately.
const DATATYPE_DECLARATIONS: &str = "
    (set-logic ALL)
    (declare-datatypes ((R 0)) (((mk (fld (_ BitVec 3))) (nl))))
    (declare-const d1 R)
    (declare-const d2 R)
    (declare-const u (Array (_ BitVec 4) (_ BitVec 3)))
    (declare-const z (Array (_ BitVec 4) (_ BitVec 3)))
";
const READ_D2: &str = "(assert (= (fld d2) #b001))";
const DATATYPE_ALIAS: &str = "(assert (= d1 d2))";
const DEFINE_U: &str = "(assert (= u (store z #x0 (fld d1))))";
const READ_U0: &str = "(assert (= (select u #x0) #b001))";
const TESTERS: &str = "(assert ((_ is mk) d1))(assert ((_ is mk) d2))";
/// The first order reads `d2` first, so the gate resolves `d2` before `d1`,
/// while `(get-model)` reconstructs `d1` first; the others start from `u`.
const DATATYPE_ORDERS: [[&str; 4]; 3] = [
    [READ_D2, DATATYPE_ALIAS, DEFINE_U, READ_U0],
    [READ_U0, DEFINE_U, DATATYPE_ALIAS, READ_D2],
    [DEFINE_U, READ_U0, DATATYPE_ALIAS, READ_D2],
];

/// A candidate committing `(fld d1) = fld1` and `(fld d2) = fld2`, with the
/// assertions in `order`.
fn datatype_candidate(order: &[&str; 4], fld1: i64, fld2: i64) -> Executor {
    let script = format!("{DATATYPE_DECLARATIONS}{}{TESTERS}", order.concat());
    let commands = parse(&script).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("declarations and assertions execute");
    let (u, z, d1, d2) = (
        declared(&exec, "u"),
        declared(&exec, "z"),
        declared(&exec, "d1"),
        declared(&exec, "d2"),
    );
    let selector = exec
        .ctx
        .constructor_selector_info("mk")
        .and_then(|fields| fields.first().map(|(name, _)| name.clone()))
        .expect("`mk` has one field");
    let mut values = HashMap::default();
    for (owner, field) in [(d1, fld1), (d2, fld2)] {
        let read = exec
            .find_dt_selector_app(&selector, owner)
            .expect("the assertions read the field");
        values.insert(read, BigInt::from(field));
    }
    let mut model = empty_model();
    model.array_model = Some(ArrayModel {
        array_values: HashMap::from_iter([
            (u, cells(&[("#x0", "#b111")])),
            (z, cells(&[("#x3", "#b011")])),
        ]),
        ..Default::default()
    });
    model.bv_model = Some(BvModel {
        values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    exec.last_result = Some(SolveResult::Sat);
    exec.last_model = Some(model);
    exec
}

/// `(fld d1) = #b010` and `(fld d2) = #b001` cannot both hold when `d1 = d2`.
/// The cached cut used to let the gate confirm this candidate while
/// `(get-model)` printed `d1 = d2 = (mk #b010)` and `u[0] = #b010`, which
/// falsifies `(= (fld d2) #b001)` and `(= (select u #x0) #b001)` (z3 rejects).
/// Now `d1` and `d2` are each read the same way everywhere, and the alias is
/// refuted.
#[test]
fn gate_refutes_an_inconsistent_datatype_alias_the_printer_would_expose() {
    for order in &DATATYPE_ORDERS {
        for (fld1, fld2) in [(0b010, 0b001), (0b001, 0b010)] {
            let exec = datatype_candidate(order, fld1, fld2);
            let verdict = exec.confirm_sat_with_independent_gate();
            assert!(
                !matches!(verdict, GateVerdict::ConfirmedSat),
                "order {order:?}, fields {fld1:#b}/{fld2:#b}: the gate confirmed a model \
                 `(get-model)` does not print: {verdict:?}"
            );
        }
    }
}

/// Negative twin: with one committed field value the alias is consistent, the
/// gate confirms, and `(get-model)` prints the value it checked for `d1`,
/// `d2` and `u`.
#[test]
fn gate_confirms_a_consistent_datatype_alias_and_prints_what_it_checked() {
    for order in &DATATYPE_ORDERS {
        let exec = datatype_candidate(order, 0b001, 0b001);
        assert!(
            matches!(
                exec.confirm_sat_with_independent_gate(),
                GateVerdict::ConfirmedSat
            ),
            "order {order:?}: a consistent alias model must confirm"
        );
        let model = exec.last_model.as_ref().expect("model installed");
        let printed = exec.gate_emit_reconstructions(model).unwrap();
        let (u, d1, d2) = (
            declared(&exec, "u"),
            declared(&exec, "d1"),
            declared(&exec, "d2"),
        );
        assert_eq!(printed.get(&d1), printed.get(&d2));
        assert!(
            printed[&u].contains("#x0 #b001"),
            "u must print the cell the gate checked: {}",
            printed[&u]
        );
    }
}
