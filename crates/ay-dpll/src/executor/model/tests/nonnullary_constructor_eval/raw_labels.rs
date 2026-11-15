// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A raw EUF slot holding a bare nullary constructor is an element label, not
//! structure: a constructor application over such a leaf keeps its own class
//! element, so it still equals the other members of its class. A structured
//! raw value is still read (the acceptance path).

use super::*;

fn tree_sort() -> Sort {
    Sort::Uninterpreted("Tree".to_string())
}

/// `(Fork t t)` with `t`'s raw slot `raw`, the application and a variable
/// `v` sharing the class element `@Tree!class`.
fn fork_over_raw_leaf(raw: &str) -> (Executor, Model, TermId, TermId) {
    let mut exec = fixture();
    let leaf = exec.ctx.terms.mk_var("t", tree_sort());
    let fork = exec
        .ctx
        .terms
        .mk_app(Symbol::named("Fork"), vec![leaf, leaf], tree_sort());
    let mate = exec.ctx.terms.mk_var("v", tree_sort());
    let model = raw_model(&[(leaf, raw), (fork, "@Tree!class"), (mate, "@Tree!class")]);
    (exec, model, fork, mate)
}

#[test]
fn nullary_label_leaf_keeps_the_application_in_its_class() {
    let (mut exec, model, fork, mate) = fork_over_raw_leaf("Stop");
    assert_eq!(
        exec.evaluate_term(&model, fork),
        EvalValue::Element("@Tree!class".to_string()),
        "a nullary label supplies no structure"
    );
    let same = exec.ctx.terms.mk_eq(mate, fork);
    assert_eq!(exec.evaluate_term(&model, same), EvalValue::Bool(true));
    assert!(model.dt_ground.is_empty());
    assert!(model.dt_pins.is_empty());
}

#[test]
fn structured_raw_leaf_still_rebuilds_the_application() {
    let (exec, model, fork, _) = fork_over_raw_leaf("(Fork Stop Stop)");
    assert_eq!(
        exec.evaluate_term(&model, fork),
        EvalValue::Element("(Fork (Fork Stop Stop) (Fork Stop Stop))".to_string()),
        "a structured raw value is the leaf's typed constructor value"
    );
}

/// What the decline gives up, and which gate holds it: `p = (MkPair t t)`,
/// `q = (MkPair s s)` and `p = q` over one class element, with `t = Red` and
/// `s = Green`. The constructor reader no longer reads the leaves' labels, as
/// before raw slots were read, so it reads both applications as the class
/// element. The independent gate composes each application from its
/// arguments itself and does not confirm that model; it confirms the same
/// assertions when `p` and `q` carry the structure the applications compose
/// to.
#[test]
fn merged_applications_over_different_labels_fail_the_independent_gate() {
    for (s_label, pair_raw, confirmed) in [
        ("Red", "(MkPair Red Red)", true),
        ("Green", "@Pair!class", false),
    ] {
        let commands = ay_frontend::parse(
            r#"
            (set-logic ALL)
            (declare-datatype Color ((Red) (Green)))
            (declare-datatype Pair ((MkPair (fst Color) (snd Color))))
            (declare-const t Color)
            (declare-const s Color)
            (declare-const p Pair)
            (declare-const q Pair)
            (assert (= p (MkPair t t)))
            (assert (= q (MkPair s s)))
            (assert (= p q))
            "#,
        )
        .expect("valid label fixture");
        let mut exec = Executor::new();
        exec.execute_all(&commands).expect("fixture executes");
        let mut raw = Vec::new();
        for term in exec.ctx.terms.term_ids() {
            match exec.ctx.terms.get(term) {
                TermData::Var(name, _) if name == "t" => raw.push((term, "Red")),
                TermData::Var(name, _) if name == "s" => raw.push((term, s_label)),
                TermData::Var(name, _) if name == "p" || name == "q" => {
                    raw.push((term, pair_raw));
                }
                TermData::App(symbol, _) if symbol.name() == "MkPair" => {
                    raw.push((term, "@Pair!class"));
                }
                _ => {}
            }
        }
        assert_eq!(raw.len(), 6, "t, s, p, q and two applications: {raw:?}");
        exec.last_model = Some(raw_model(&raw));
        let gate = exec.confirm_sat_with_independent_gate();
        assert_eq!(
            matches!(gate, ay_model_check::GateVerdict::ConfirmedSat),
            confirmed,
            "s = {s_label}, p = q = {pair_raw}: {gate:?}"
        );
    }
}
