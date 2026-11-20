// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The AUTHORED-CONJUNCT lane over a root whose TEXT is tree-sized
//! (DR-PROOF-RENDER-BUDGET-20261118).
//!
//! MEASURED on CHC-COMP 2026 LRA-Lin `oral_messages` (`ec4cd5b8abaf3a98`):
//! DAR's proof-backed interpolation reached this lane with a `let`-shared
//! authored root of 4,659 DAG nodes and 1.03e14 tree nodes; Guard 5 printed it
//! as a tree into one `String` and the run died of a 5 GB memout ~4 s in. The
//! fixtures below are the same shape over an uninterpreted `f`:
//! `a_{i+1} = (f a_i a_i)`, a DAG of `depth + 1` nodes and a tree of
//! `2^(depth+1) - 1`.
//!
//! * depth 22 (~25 MB of text): small enough for the tree-size precheck, too
//!   big for one bounded renderability check, which DECLINES it — the
//!   unbounded check rendered it and planned the fragment;
//! * depth 64 (1.8e19 tree nodes): declined by the precheck in O(DAG), before
//!   any fragment is built or rendered;
//! * depth 3: the two-sided control, planned exactly as before.

use ay_core::{AletheRule, ProofStep, Symbol, TermData, TermId};

use super::tests::{leaf_proof, premiseless_unit_trust_leaves, rerun, shape, solve};
use crate::Executor;

/// `(and b0 (= a_depth c))`, authored as a `let` chain, made unsat by a
/// contradiction over a variable the root does not mention.
fn doubling_problem(depth: usize) -> String {
    let mut root = String::new();
    let mut close = String::new();
    for i in 1..=depth {
        let previous = if i == 1 {
            "x".to_string()
        } else {
            format!("a{}", i - 1)
        };
        root.push_str(&format!("(let ((a{i} (f {previous} {previous}))) "));
        close.push(')');
    }
    root.push_str(&format!("(and b0 (= a{depth} c))"));
    root.push_str(&close);
    format!(
        "(set-logic QF_UF)\n\
         (declare-sort U 0)\n\
         (declare-fun f (U U) U)\n\
         (declare-fun x () U)\n\
         (declare-fun c () U)\n\
         (declare-fun b0 () Bool)\n\
         (declare-fun zz () Bool)\n\
         (assert {root})\n\
         (assert zz)\n\
         (assert (not zz))\n\
         (check-sat)\n"
    )
}

/// The authored root (the only `and` in the strict scope) and its second
/// conjunct, the equality over the deep chain.
fn root_and_deep_conjunct(exec: &Executor) -> (TermId, TermId) {
    exec.complete_problem_assertions_for_strict_proof()
        .into_iter()
        .find_map(|term| match exec.ctx.terms.get(term) {
            TermData::App(Symbol::Named(name), args) if name == "and" && args.len() == 2 => args
                .iter()
                .copied()
                .find(|&child| !matches!(exec.ctx.terms.get(child), TermData::Var(..)))
                .map(|deep| (term, deep)),
            _ => None,
        })
        .expect("the authored root is in the strict scope")
}

/// Run the lane on a COMPLETE REFUTATION whose one premiseless `trust` leaf is
/// the deep conjunct; returns the planned count and whether the proof changed.
fn run_on_deep_conjunct(depth: usize) -> (usize, bool, Executor, TermId) {
    let mut exec = solve(&doubling_problem(depth));
    let (root, atom) = root_and_deep_conjunct(&exec);
    let mut proof = leaf_proof(&mut exec, atom, Vec::new(), Vec::new());
    assert_eq!(premiseless_unit_trust_leaves(&proof), 1);
    let before = shape(&proof);
    let planned = rerun(&mut exec, &mut proof);
    (planned, shape(&proof) != before, exec, root)
}

#[test]
fn a_shallow_chain_root_is_still_derived() {
    let (planned, changed, _, _) = run_on_deep_conjunct(3);
    assert_eq!(planned, 1, "the two-sided control must still be derived");
    assert!(changed);
}

#[test]
fn a_root_too_big_for_one_render_check_plans_no_fragment() {
    let (planned, changed, exec, root) = run_on_deep_conjunct(22);
    // The precheck admits it (its text is under one check's budget), so the
    // decline is the BOUNDED render's, not the precheck's.
    let bytes = super::printed_tree_bytes_lower_bound(
        &exec.ctx.terms,
        root,
        None,
        ay_proof::DERIVATION_RENDER_WORK_BUDGET,
        &mut Default::default(),
    );
    assert!(
        bytes <= ay_proof::DERIVATION_RENDER_WORK_BUDGET,
        "bound {bytes}"
    );
    assert!(bytes > 16 << 20, "the fixture must be big: bound {bytes}");
    assert_eq!(planned, 0, "the fragment cannot render within one check");
    assert!(!changed, "a declined leaf keeps the proof byte-identical");
}

#[test]
fn a_tree_blowup_root_is_declined_by_the_precheck_in_dag_time() {
    let started = std::time::Instant::now();
    let (planned, changed, exec, root) = run_on_deep_conjunct(64);
    assert_eq!(planned, 0);
    assert!(!changed);
    let mut memo = Default::default();
    let bytes = super::printed_tree_bytes_lower_bound(
        &exec.ctx.terms,
        root,
        None,
        ay_proof::DERIVATION_RENDER_WORK_BUDGET,
        &mut memo,
    );
    assert_eq!(
        bytes,
        ay_proof::DERIVATION_RENDER_WORK_BUDGET + 1,
        "saturates"
    );
    assert!(memo.len() < 256, "one entry per DAG node: {}", memo.len());
    // Generous: the solve plus a DAG walk. The unbounded check would need
    // 1e20 bytes.
    assert!(started.elapsed().as_secs() < 120, "{:?}", started.elapsed());
}

#[test]
fn the_lower_bound_is_exact_on_override_free_applications() {
    // `(f a b)` over single-byte leaves prints exactly `(` + `f` + 2 spaces +
    // `)` + its arguments, which is the bound's own arithmetic; the printer
    // agrees byte for byte.
    let exec = solve(&doubling_problem(5));
    let (_, atom) = root_and_deep_conjunct(&exec);
    let TermData::App(_, args) = exec.ctx.terms.get(atom) else {
        panic!("an equality");
    };
    let chain = args
        .iter()
        .copied()
        .find(
            |&arg| matches!(exec.ctx.terms.get(arg), TermData::App(_, inner) if !inner.is_empty()),
        )
        .expect("the chain side of the equality");
    let printed = ay_proof::format_term_alethe(&exec.ctx.terms, chain);
    let bound = super::printed_tree_bytes_lower_bound(
        &exec.ctx.terms,
        chain,
        None,
        u64::MAX - 1,
        &mut Default::default(),
    );
    assert_eq!(bound, printed.len() as u64, "{printed}");
}

/// One `let`-shared doubling-chain root with TWO deep conjuncts, and a small
/// second root, `(and b1 b2)`.
fn two_deep_conjuncts_problem(depth: usize) -> String {
    let mut root = String::new();
    let mut close = String::new();
    for i in 1..=depth {
        let previous = if i == 1 {
            "x".to_string()
        } else {
            format!("a{}", i - 1)
        };
        root.push_str(&format!("(let ((a{i} (f {previous} {previous}))) "));
        close.push(')');
    }
    root.push_str(&format!("(and b0 (= a{depth} c) (= a{depth} d))"));
    root.push_str(&close);
    format!(
        "(set-logic QF_UF)\n\
         (declare-sort U 0)\n\
         (declare-fun f (U U) U)\n\
         (declare-fun x () U)\n\
         (declare-fun c () U)\n\
         (declare-fun d () U)\n\
         (declare-fun b0 () Bool)\n\
         (declare-fun b1 () Bool)\n\
         (declare-fun b2 () Bool)\n\
         (declare-fun zz () Bool)\n\
         (assert {root})\n\
         (assert (and b1 b2))\n\
         (assert zz)\n\
         (assert (not zz))\n\
         (check-sat)\n"
    )
}

fn premiseless_trust(atom: TermId) -> ProofStep {
    ProofStep::Step {
        rule: AletheRule::Trust,
        clause: vec![atom],
        premises: Vec::new(),
        args: Vec::new(),
    }
}

#[test]
fn a_root_out_of_budget_once_is_not_rendered_again_for_its_other_leaves() {
    // Depth 21: the root prints the ~12 MB chain twice, so the tree-size
    // precheck admits it and the decline is Guard 5's (asserted below).
    let mut exec = solve(&two_deep_conjuncts_problem(21));
    let roots = exec.complete_problem_assertions_for_strict_proof();
    let and_args = |exec: &Executor, arity: usize| -> Vec<TermId> {
        roots
            .iter()
            .find_map(|&term| match exec.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args)
                    if name == "and" && args.len() == arity =>
                {
                    Some(args.clone())
                }
                _ => None,
            })
            .expect("authored root in the strict scope")
    };
    let deep: Vec<TermId> = and_args(&exec, 3)
        .into_iter()
        .filter(|&child| !matches!(exec.ctx.terms.get(child), TermData::Var(..)))
        .collect();
    assert_eq!(deep.len(), 2);
    let deep_root = roots
        .iter()
        .copied()
        .find(|&term| matches!(exec.ctx.terms.get(term), TermData::App(_, args) if args.len() == 3))
        .expect("the deep root");
    let bound = super::printed_tree_bytes_lower_bound(
        &exec.ctx.terms,
        deep_root,
        None,
        ay_proof::DERIVATION_RENDER_WORK_BUDGET,
        &mut Default::default(),
    );
    assert!(
        bound <= ay_proof::DERIVATION_RENDER_WORK_BUDGET,
        "the precheck must admit the root: bound {bound}"
    );
    let small = and_args(&exec, 2)[1];
    let mut proof = ay_core::Proof::new();
    for atom in [deep[0], deep[1], small] {
        proof.steps.push(premiseless_trust(atom));
    }
    super::super::check::RENDER_CHECKS.with(|checks| checks.set(0));
    let _ = rerun(&mut exec, &mut proof);
    // One check for the first deep leaf (out of budget), NONE for its
    // sibling, one for the small root's leaf: the memo is per root.
    assert_eq!(
        super::super::check::RENDER_CHECKS.with(std::cell::Cell::get),
        2
    );
    assert!(
        proof.steps[..2].iter().all(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::Trust,
                ..
            }
        )),
        "both deep leaves keep their trust steps"
    );
}
