// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::{ChcOp, ClauseBody, HornClause};
use std::time::Duration;

mod budget;
mod wide_copies;

fn control(token: &CancellationToken) -> SourceControl<'_> {
    SourceControl::new(Instant::now() + Duration::from_secs(60), token)
}

fn binder(name: &str, width: u32) -> ChcVar {
    ChcVar::new(name, ChcSort::BitVec(width))
}

fn pair(left: ChcExpr, right: ChcExpr) -> ChcExpr {
    ChcExpr::Op(ChcOp::Eq, vec![Arc::new(left), Arc::new(right)])
}

#[test]
fn simultaneous_replacements_can_reference_other_binders_without_being_rewritten() {
    let i = binder("i", 8);
    let j = binder("j", 8);
    let i_value = ChcExpr::var(i.clone());
    let j_value = ChcExpr::var(j.clone());
    let zero = ChcExpr::BitVec(0, 8);
    let matrix = pair(i_value.clone(), j_value.clone());
    let token = CancellationToken::new();
    let live = control(&token);
    let result = simultaneous(&matrix, &[(&i, &j_value), (&j, &zero)], &live).unwrap();
    assert_eq!(result, pair(j_value.clone(), zero));
    let compound = ChcExpr::Op(
        ChcOp::BvAdd,
        vec![Arc::new(j_value), Arc::new(ChcExpr::BitVec(1, 8))],
    );
    assert_eq!(
        simultaneous(&matrix, &[(&i, &compound), (&j, &i_value)], &live).unwrap(),
        pair(compound, i_value),
    );
    let left = ChcExpr::var(i.clone());
    let right = ChcExpr::var(j.clone());
    assert_eq!(
        simultaneous(&matrix, &[(&i, &right), (&j, &left)], &live).unwrap(),
        pair(right, left)
    );
    assert!(simultaneous(&matrix, &[(&i, &ChcExpr::BitVec(0, 16))], &live).is_none());
    assert!(simultaneous(
        &matrix,
        &[(&i, &ChcExpr::BitVec(0, 8)), (&i, &ChcExpr::BitVec(1, 8))],
        &live
    )
    .is_none());
}

#[test]
fn cartesian_instances_include_off_diagonals_and_keep_input_order_and_duplicates() {
    let i = binder("i", 8);
    let j = binder("j", 8);
    let premise = UniversalPremise::with_binders(
        vec![i.clone(), j.clone()],
        pair(ChcExpr::var(i), ChcExpr::var(j)),
    )
    .unwrap();
    let terms = [
        ChcExpr::BitVec(2, 8),
        ChcExpr::BitVec(1, 8),
        ChcExpr::BitVec(2, 8),
    ];
    let token = CancellationToken::new();
    let live = control(&token);
    let output = instances(&[premise], &terms, &live).unwrap();
    let expected: Vec<_> = terms
        .iter()
        .flat_map(|left| {
            terms
                .iter()
                .map(move |right| pair(left.clone(), right.clone()))
        })
        .collect();
    assert_eq!(output, expected);
    assert_eq!(output.len(), 9);
    assert_eq!(output[1], pair(terms[0].clone(), terms[1].clone()));
    assert_eq!(output[3], pair(terms[1].clone(), terms[0].clone()));
}

#[test]
fn each_binder_uses_its_own_sort_domain_and_singletons_keep_legacy_order() {
    let i = binder("i", 8);
    let j = binder("j", 16);
    let matrix = ChcExpr::and(
        pair(ChcExpr::var(i.clone()), ChcExpr::BitVec(7, 8)),
        pair(ChcExpr::var(j.clone()), ChcExpr::BitVec(9, 16)),
    );
    let premise = UniversalPremise::with_binders(vec![i.clone(), j], matrix).unwrap();
    let terms = [
        ChcExpr::BitVec(3, 8),
        ChcExpr::BitVec(4, 8),
        ChcExpr::BitVec(5, 16),
    ];
    let token = CancellationToken::new();
    let live = control(&token);
    assert_eq!(
        instances(&[premise.clone()], &terms, &live).unwrap().len(),
        2
    );
    assert_eq!(
        instances(&[premise], &terms[..2], &live).unwrap(),
        [] as [ChcExpr; 0]
    );
    let singleton = UniversalPremise::new(i.clone(), pair(ChcExpr::var(i), ChcExpr::BitVec(7, 8)));
    assert_eq!(
        instances(&[singleton], &terms, &live).unwrap(),
        vec![
            pair(terms[0].clone(), ChcExpr::BitVec(7, 8)),
            pair(terms[1].clone(), ChcExpr::BitVec(7, 8))
        ]
    );
}

#[test]
fn free_variable_and_fresh_name_censuses_cover_all_group_binders() {
    let i = binder("i", 8);
    let j = binder("__gpi0", 8);
    let free = binder("free", 8);
    let premise = UniversalPremise::with_binders(
        vec![i.clone(), j.clone()],
        pair(ChcExpr::var(i.clone()), ChcExpr::var(free.clone())),
    )
    .unwrap();
    let clause = HornClause::query(ClauseBody::empty());
    let token = CancellationToken::new();
    let live = control(&token);
    assert_eq!(
        clause_variables(&clause, &[premise.clone()], &live).unwrap(),
        vec![free.clone()]
    );
    let mut reserved = FxHashSet::default();
    reserve_names(&[premise.clone()], &mut reserved, &live).unwrap();
    for name in [&i.name, &j.name, &free.name] {
        assert!(reserved.contains(name));
    }
    assert_eq!(
        binder_list(&premise, Some(&live)).unwrap(),
        "(i (_ BitVec 8)) (__gpi0 (_ BitVec 8))"
    );
}

#[test]
fn cartesian_resource_refusal_discards_the_whole_prefix_and_remains_stopped() {
    let binders: Vec<_> = (0..8)
        .map(|index| binder(&format!("b{index}"), 8))
        .collect();
    let explosive = UniversalPremise::with_binders(binders, ChcExpr::Bool(true)).unwrap();
    let prefix = UniversalPremise::new(binder("p", 8), ChcExpr::Bool(true));
    let terms: Vec<_> = (0..8).map(|value| ChcExpr::BitVec(value, 8)).collect();
    let token = CancellationToken::new();
    let stopped = control(&token);
    assert!(instances(&[prefix.clone(), explosive], &terms, &stopped).is_none());
    assert!(stopped.stopped.get());
    assert!(instances(&[prefix.clone()], &terms, &stopped).is_none());
    let fresh = control(&token);
    assert_eq!(instances(&[prefix], &terms, &fresh).unwrap().len(), 8);
}

#[test]
fn cancellation_refusal_cannot_be_revived_by_reset() {
    let premise =
        UniversalPremise::with_binders(vec![binder("i", 8), binder("j", 8)], ChcExpr::Bool(true))
            .unwrap();
    let token = CancellationToken::new();
    let stopped = control(&token);
    token.cancel();
    assert!(instances(&[premise.clone()], &[ChcExpr::BitVec(0, 8)], &stopped).is_none());
    token.reset();
    assert!(instances(&[premise.clone()], &[ChcExpr::BitVec(0, 8)], &stopped).is_none());
    assert_eq!(
        instances(&[premise], &[ChcExpr::BitVec(0, 8)], &control(&token))
            .unwrap()
            .len(),
        1
    );
}
