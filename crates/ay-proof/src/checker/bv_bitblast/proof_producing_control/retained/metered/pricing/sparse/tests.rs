// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::checker::bv_bitblast::{
    array_finite::SmallIndexReads,
    producer_limits::counted_limits_until,
    proof_producing_control::{lower_clause_once, Route},
};
use std::time::Duration;

fn proof() -> BvExprProofLimits {
    counted_limits_until(Instant::now() + Duration::from_secs(60))
}
fn fixture(width: u32) -> (TermStore, TermId) {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::bitvec(64), Sort::bitvec(width));
    let array = terms.mk_var("sparse", sort.clone());
    let at = terms.mk_var("write", Sort::bitvec(64));
    let key = terms.mk_var("read", Sort::bitvec(64));
    let value = terms.mk_var("value", Sort::bitvec(width));
    let stored = terms.mk_app(Symbol::named("store"), [array, at, value], sort);
    let read = terms.mk_app(Symbol::named("select"), [stored, key], Sort::bitvec(width));
    let root = terms.mk_app(Symbol::named("="), [read, read], Sort::Bool);
    (terms, root)
}
fn cost(terms: &TermStore, root: TermId) -> Option<Cost> {
    plan(terms, &[root], &proof(), &mut |_, _| true).unwrap()
}

#[test]
fn sparse_entry_refusal_is_terminal_before_source_allocation_or_work() {
    let (terms, root) = fixture(8);
    let before = terms.entries_snapshot();
    let mut calls = 0;
    assert!(matches!(
        plan(&terms, &[root], &proof(), &mut |_, _| {
            calls += 1;
            false
        }),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert_eq!(calls, 1);
    assert_eq!(terms.entries_snapshot(), before);
}

#[test]
fn every_sparse_planner_checkpoint_refusal_is_terminal_without_retry() {
    let (terms, root) = fixture(8);
    let mut total = 0;
    assert!(plan(&terms, &[root], &proof(), &mut |_, _| {
        total += 1;
        true
    })
    .unwrap()
    .is_some());
    for stop in 1..=total {
        let mut calls = 0;
        assert!(matches!(
            plan(&terms, &[root], &proof(), &mut |_, _| {
                calls += 1;
                calls != stop
            }),
            Err(ProofCheckError::ResourceLimit)
        ));
        assert_eq!(calls, stop);
    }
}

#[test]
fn sparse_shared_read_store_operand_and_root_multiplicity_increase_prepaid_cost() {
    let (mut terms, root) = fixture(8);
    let one = cost(&terms, root).unwrap();
    let many = plan(&terms, &[root, root], &proof(), &mut |_, _| true)
        .unwrap()
        .unwrap();
    assert!(many.work > one.work);
    assert!(many.name_work > one.name_work);
    let repeated = terms.mk_app(Symbol::named("and"), [root; 8], Sort::Bool);
    assert!(cost(&terms, repeated).unwrap().work > one.work);
}

fn footprint(expr: &BvExpr) -> (usize, usize) {
    let mut pending = vec![expr];
    let (mut nodes, mut names) = (0, 0);
    while let Some(expr) = pending.pop() {
        nodes += 1;
        match expr {
            BvExpr::Leaf { name, .. } => {
                assert!(name.len() <= 42);
                names += name.len();
            }
            BvExpr::Const { .. } => {}
            BvExpr::Not(a) | BvExpr::SignExt(a, _) => pending.push(a),
            BvExpr::Add(a, b)
            | BvExpr::Sub(a, b)
            | BvExpr::And(a, b)
            | BvExpr::Or(a, b)
            | BvExpr::Xor(a, b)
            | BvExpr::Eq(a, b)
            | BvExpr::Ult(a, b) => {
                pending.push(a);
                pending.push(b);
            }
            _ => panic!("unexpected sparse-subset output"),
        }
    }
    (nodes, names)
}

#[test]
fn sparse_unknown_address_mux_and_generated_name_bound_cover_actual_native_output() {
    for width in [1, 8, 128] {
        let (terms, root) = fixture(width);
        let proof = proof();
        let cost = cost(&terms, root).unwrap();
        let (lowered, _) = lower_clause_once(
            &terms,
            &[root],
            proof.resolution.deadline.unwrap(),
            Route::default(),
            None,
            &mut || true,
            SmallIndexReads::CompleteDomain,
        );
        let (nodes, names) = footprint(&lowered.unwrap().disjunction);
        assert!(nodes < 30); // each width>1 read has14 nodes, equality29
        assert!(16 * names <= cost.name_work);
    }
}

#[test]
fn sparse_bool_constant_array_fill_and_all_overwritten_values_are_checked() {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::bitvec(64), Sort::Bool);
    let key = terms.mk_bitvec(0.into(), 64);
    let fill = terms.true_term();
    let base = terms.mk_app(Symbol::named("const-array"), [fill], sort.clone());
    let store = terms.mk_app(Symbol::named("store"), [base, key, fill], sort);
    let read = terms.mk_app(Symbol::named("select"), [store, key], Sort::Bool);
    let root = terms.mk_app(Symbol::named("="), [read, fill], Sort::Bool);
    assert!(cost(&terms, root).is_some());
    let mut entries = terms.entries_snapshot();
    entries[base.index()].0 = TermData::App(Symbol::named("const-array"), vec![key]);
    let malformed = TermStore::from_entries(entries, None, None, terms.var_counter());
    assert!(cost(&malformed, root).is_none());
}

#[test]
fn sparse_missing_cycle_wrong_types_and_unsupported_heads_keep_old_eligibility() {
    let (terms, root) = fixture(8);
    for mode in 0..4 {
        let mut entries = terms.entries_snapshot();
        entries[root.index()].0 = match mode {
            0 => TermData::Not(root),
            1 => TermData::Not(TermId::SENTINEL),
            2 => TermData::App(Symbol::named("="), vec![root, terms.true_term()]),
            _ => TermData::App(Symbol::indexed("extract", vec![1, 0]), vec![root]),
        };
        if mode == 2 {
            entries[root.index()].1 = Sort::bitvec(8);
        }
        let malformed = TermStore::from_entries(entries, None, None, terms.var_counter());
        assert!(cost(&malformed, root).is_none());
    }
}

#[test]
fn sparse_ite_small_or_nested_array_sorts_are_not_discounted() {
    let (mut terms, root) = fixture(8);
    let ite = terms.mk_ite_raw(terms.true_term(), root, root);
    assert!(cost(&terms, ite).is_none());
    for sort in [
        Sort::array(Sort::bitvec(8), Sort::bitvec(8)),
        Sort::array(Sort::bitvec(64), Sort::array(Sort::Bool, Sort::Bool)),
    ] {
        let mut entries = terms.entries_snapshot();
        for (_, actual) in &mut entries {
            if matches!(actual, Sort::Array(_)) {
                *actual = sort.clone();
            }
        }
        let unsupported = TermStore::from_entries(entries, None, None, terms.var_counter());
        assert!(cost(&unsupported, root).is_none());
    }
}

mod ge;

#[test]
fn sparse_store_address_depth_occurrence_and_original_name_caps_are_retained() {
    let (mut terms, root) = fixture(8);
    let mut low = proof();
    low.max_leaf_name_bytes = 0;
    assert!(plan(&terms, &[root], &low, &mut |_, _| true)
        .unwrap()
        .is_none());
    low = proof();
    low.max_expr_occurrences = 1;
    assert!(plan(&terms, &[root], &low, &mut |_, _| true)
        .unwrap()
        .is_none());
    let mut deep = root;
    for _ in 0..crate::checker::bv_bitblast::MAX_PROOF_PRODUCING_EXPR_DEPTH {
        deep = terms.mk_not_raw(deep);
    }
    assert!(cost(&terms, deep).is_none());
    let sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
    let mut array = terms.mk_var("long-chain", sort.clone());
    let at = terms.mk_bitvec(0.into(), 64);
    let value = terms.mk_bitvec(0.into(), 8);
    for _ in 0..65 {
        array = terms.mk_app(Symbol::named("store"), [array, at, value], sort.clone());
    }
    let selected = terms.mk_app(Symbol::named("select"), [array, at], Sort::bitvec(8));
    let eq = terms.mk_app(Symbol::named("="), [selected, selected], Sort::Bool);
    assert!(cost(&terms, eq).is_none());
    let array = terms.mk_var("address-chain", sort);
    let mut key = at;
    for _ in 0..17 {
        key = terms.mk_app(Symbol::named("bvadd"), [key, at], Sort::bitvec(64));
    }
    let selected = terms.mk_app(Symbol::named("select"), [array, key], Sort::bitvec(8));
    let eq = terms.mk_app(Symbol::named("="), [selected, selected], Sort::Bool);
    assert!(cost(&terms, eq).is_none());
}

#[test]
fn scalar_n_recurrence_covers_unrolled_occurrences_and_raw_repeated_pushes() {
    let mut nodes = HashMap::new();
    let atom = bounds::node(Operation::Atom, &[], &nodes).unwrap();
    nodes.insert(
        TermId(0),
        Node {
            references: 1,
            result: Some(atom),
        },
    );
    let repeated = bounds::node(Operation::Balanced, &[TermId(0); 128], &nodes).unwrap();
    assert_eq!(repeated.nodes, 255);
    assert!(repeated.nodes > 128); // source node plus raw children
    let empty = bounds::node(Operation::Balanced, &[], &nodes).unwrap();
    assert_eq!(empty.nodes, 1);
    let singleton = bounds::node(Operation::Balanced, &[TermId(0)], &nodes).unwrap();
    assert_eq!(singleton.nodes, 2); // original lowering erases source AND/OR
}

#[test]
fn sparse_checked_overflow_and_opaque_user_names_do_not_issue_extra_grants() {
    let (terms, root) = fixture(8);
    let cost = cost(&terms, root).unwrap();
    let mut huge = proof();
    huge.max_leaf_name_bytes = usize::MAX;
    assert!(plan(&terms, &[root], &huge, &mut |_, _| true)
        .unwrap()
        .is_none());
    let mut entries = terms.entries_snapshot();
    for (term, _) in &mut entries {
        if let TermData::Var(name, _) = term {
            *name = "opaque".repeat(1024);
        }
    }
    let borrowed = TermStore::from_entries(entries, None, None, terms.var_counter());
    assert_eq!(
        plan(&borrowed, &[root], &proof(), &mut |_, _| true).unwrap(),
        Some(cost)
    );
}
