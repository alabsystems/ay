// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Work bounds and order independence of the exact leaf memo
//! (#gate-exact-leaf-memo).

use ay_arrays::{ArrayInterpretation, ArrayModel};
use ay_bv::BvModel;
use ay_core::kani_compat::DetHashMap;
use ay_core::{Sort, TermId};
use ay_model_check::EvalOutcome;

use super::*;
use crate::executor::model::Model;
use crate::executor::Executor;
use crate::executor_types::SolveResult;

/// An alias chain `(= a_k b_k)`, `(= a_k (store a_{k-1} #x1 (select b_{k-1}
/// #x2)))` over BV arrays. Only `a0` has a model entry, so every other link
/// resolves through its definitions, and each alias is a two-leaf cycle.
fn alias_chain(links: usize) -> Executor {
    let sort = "(Array (_ BitVec 4) (_ BitVec 4))";
    let mut script = format!(
        "(set-logic QF_ABV)(declare-const a0 {sort})(declare-const b0 {sort})(assert (= a0 b0))"
    );
    for k in 1..=links {
        let p = k - 1;
        script.push_str(&format!(
            "(declare-const a{k} {sort})(declare-const b{k} {sort})(assert (= a{k} b{k}))\
             (assert (= a{k} (store a{p} #x1 (select b{p} #x2))))"
        ));
    }
    let commands = ay_frontend::parse(&script).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("declarations and assertions execute");
    let a0 = declared(&exec, "a0");
    let mut model = Model::empty();
    let entry = ArrayInterpretation {
        index_sort: Some(Sort::bitvec(4)),
        element_sort: Some(Sort::bitvec(4)),
        default: Some("#x3".to_string()),
        stores: vec![("#x2".to_string(), "#x7".to_string())],
    };
    model.array_model = Some(ArrayModel {
        array_values: DetHashMap::from_iter([(a0, entry)]),
        ..Default::default()
    });
    model.bv_model = Some(BvModel {
        values: DetHashMap::default(),
        term_to_bits: DetHashMap::default(),
        bool_overrides: DetHashMap::default(),
    });
    exec.last_result = Some(SolveResult::Sat);
    exec.last_model = Some(model);
    exec
}

fn declared(exec: &Executor, name: &str) -> TermId {
    exec.ctx
        .symbol_iter()
        .find(|(symbol, _)| *symbol == name)
        .and_then(|(_, info)| info.term)
        .unwrap_or_else(|| panic!("`{name}` is declared"))
}

fn chain_constants(exec: &Executor, links: usize) -> Vec<TermId> {
    (0..=links)
        .flat_map(|k| [format!("a{k}"), format!("b{k}")])
        .map(|name| declared(exec, &name))
        .collect()
}

/// Read `leaves` in order on one fresh view, as the printer reads the declared
/// constants. Returns each value and the frames the view entered.
fn read_in_order(exec: &Executor, leaves: &[TermId]) -> (Vec<EvalOutcome>, u64) {
    let model = exec.last_model.as_ref().expect("model installed");
    let view = IndependentModelView::new(exec, model);
    view.ensure_def_index().unwrap();
    let values = leaves
        .iter()
        .map(|&leaf| ay_model_check::evaluate_term(&exec.ctx.terms, &view, leaf))
        .collect();
    (values, view.leaf_memo.frames_entered())
}

/// Evaluate every assertion in order on one fresh view, as the gate does.
fn gate_frames(exec: &Executor) -> u64 {
    let model = exec.last_model.as_ref().expect("model installed");
    let view = IndependentModelView::new(exec, model);
    view.ensure_def_index().unwrap();
    for &assertion in &exec.ctx.assertions {
        let _ = ay_model_check::evaluate_term(&exec.ctx.terms, &view, assertion);
    }
    view.leaf_memo.frames_entered()
}

/// Every link of an alias chain is a cycle, so caching only cycle-free
/// resolutions (the rule before #gate-exact-leaf-memo) resolved the chain
/// below a link again on every read: the adversarial `alias_chain_240`
/// (QF_AUFBV) went from 0.21 s to 56 s. The exact memo reuses a resolution
/// wherever the reader's stack cannot change it, so the gate's walk and the
/// printer's walk, in declaration order or in reverse, stay linear.
#[test]
fn alias_chain_resolution_is_linear_in_the_chain() {
    for links in [8, 16, 32, 64] {
        let exec = alias_chain(links);
        let leaves = chain_constants(&exec, links);
        let reversed: Vec<TermId> = leaves.iter().rev().copied().collect();
        let bound = 12 * links as u64 + 12;
        let gate = gate_frames(&exec);
        let (_, forward) = read_in_order(&exec, &leaves);
        let (_, backward) = read_in_order(&exec, &reversed);
        for (walk, frames) in [("gate", gate), ("forward", forward), ("reverse", backward)] {
            assert!(
                frames <= bound,
                "{links} links: the {walk} walk entered {frames} frames (bound {bound})"
            );
        }
    }
}

/// Order independence on the same chain: every constant reads the same value
/// whether the printer walks the declarations forward or in reverse, so the
/// values cannot depend on what an earlier read memoized.
#[test]
fn alias_chain_values_do_not_depend_on_read_order() {
    let links = 24;
    let exec = alias_chain(links);
    let leaves = chain_constants(&exec, links);
    let reversed: Vec<TermId> = leaves.iter().rev().copied().collect();
    let (forward, _) = read_in_order(&exec, &leaves);
    let (mut backward, _) = read_in_order(&exec, &reversed);
    backward.reverse();
    for ((leaf, f), b) in leaves.iter().zip(&forward).zip(&backward) {
        assert_eq!(
            format!("{f:?}"),
            format!("{b:?}"),
            "{} reads differently by order",
            exec.format_term(*leaf)
        );
    }
    assert!(
        forward
            .iter()
            .all(|value| matches!(value, EvalOutcome::Value(_))),
        "every link resolves: {forward:?}"
    );
}
