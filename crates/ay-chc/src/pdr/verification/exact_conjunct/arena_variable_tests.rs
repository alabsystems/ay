// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{ChcSort, ChcVar};
use ay_core::resource::{ChildSpec, Guard, NodeLabel};
use std::sync::Arc;

fn variable(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::Var(ChcVar::new(name, sort))
}

fn repeated_variables() -> ChcExpr {
    let name = "v".repeat(200);
    ChcExpr::Op(
        ChcOp::And,
        (0..256)
            .map(|_| Arc::new(variable(&name, ChcSort::Bool)))
            .collect(),
    )
}

#[test]
fn repeated_variable_sources_share_a_canonical_node_within_the_original_allowance() {
    let source = repeated_variables();
    let guard = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(130_000)));
    let _entered = guard.enter();
    let mut owner = Owner::capture().unwrap();
    let mut arena = Arena::new();
    let root = arena
        .read(&source, 0, &mut owner)
        .expect("bounded repeated names");
    let Key::Op(ChcOp::And, children) = &arena.node(root).key else {
        panic!("original conjunction");
    };
    assert_eq!(children.len(), 256);
    assert!(children.iter().all(|child| *child == children[0]));
    assert!(
        guard.ticks() > 100_000,
        "all repeated source names are still read and charged"
    );
    assert!(guard.poll().is_none());
}

#[test]
fn canonical_variable_hits_still_reject_a_different_complete_sort() {
    let first = variable("same", ChcSort::Bool);
    let other = variable("same", ChcSort::BitVec(8));
    let mut owner = Owner::capture().unwrap();
    let mut arena = Arena::new();
    let id = arena.read(&first, 0, &mut owner).unwrap();
    assert!(matches!(arena.node(id).key, Key::Var("same", _)));
    assert_eq!(arena.read(&other, 0, &mut owner), Err(Error::InvalidSource));
}

#[test]
fn a_colliding_name_bucket_never_substitutes_its_other_full_key() {
    let first = variable("first", ChcSort::Bool);
    let second = variable("second", ChcSort::Bool);
    let second_again = variable("second", ChcSort::Bool);
    let mut owner = Owner::capture().unwrap();
    let mut arena = Arena::new();
    let first_id = arena.read(&first, 0, &mut owner).unwrap();
    let mut hash = DefaultHasher::new();
    "second".hash(&mut hash);
    // Place a different full key in the requested bucket, exactly the state
    // a hash collision presents. The production lookup must compare names.
    let first_sort = arena.node(first_id).sort;
    arena
        .names
        .insert(hash.finish(), vec![("first", first_sort, first_id)]);
    let second_id = arena.read(&second, 0, &mut owner).unwrap();
    assert_ne!(second_id, first_id);
    assert_eq!(arena.read(&second_again, 0, &mut owner), Ok(second_id));
}

#[test]
fn reused_variables_do_not_renew_a_short_original_owner() {
    let source = repeated_variables();
    let generous = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(200_000)));
    let entered = generous.enter();
    let mut owner = Owner::capture().unwrap();
    Arena::new().read(&source, 0, &mut owner).unwrap();
    let used = generous.ticks();
    drop(entered);

    let short = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(used - 1)));
    let entered = short.enter();
    let mut owner = Owner::capture().unwrap();
    let mut arena = Arena::new();
    assert_eq!(arena.read(&source, 0, &mut owner), Err(Error::Resource));
    drop(entered);
    let replacement =
        Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(200_000)));
    let _entered = replacement.enter();
    assert_eq!(arena.read(&source, 0, &mut owner), Err(Error::Resource));
    assert_eq!(replacement.ticks(), 0);
}

#[test]
fn unique_variables_use_one_complete_name_admission_each() {
    let prefix = "v".repeat(200);
    let source = ChcExpr::Op(
        ChcOp::And,
        (0..256)
            .map(|index| Arc::new(variable(&format!("{prefix}_{index}"), ChcSort::Bool)))
            .collect(),
    );
    let guard = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(80_000)));
    let _entered = guard.enter();
    let mut owner = Owner::capture().unwrap();
    let mut arena = Arena::new();
    let root = arena
        .read(&source, 0, &mut owner)
        .expect("bounded unique names");
    let Key::Op(ChcOp::And, children) = &arena.node(root).key else {
        panic!("original conjunction");
    };
    assert_eq!(children.len(), 256);
    let distinct: std::collections::HashSet<_> = children.iter().copied().collect();
    assert_eq!(distinct.len(), 256, "different full names never alias");
    assert!(
        guard.ticks() > 50_000,
        "every source name is still read and charged"
    );
    assert!(guard.poll().is_none());
}

#[test]
fn first_variable_allocation_cannot_publish_through_any_original_work_cut() {
    let source = variable(&"first".repeat(40), ChcSort::Bool);
    let generous = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(10_000)));
    let entered = generous.enter();
    let mut owner = Owner::capture().unwrap();
    Arena::new().read(&source, 0, &mut owner).unwrap();
    let used = generous.ticks();
    assert!(used > 1);
    drop(entered);

    for allowance in 1..used {
        let short =
            Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(allowance)));
        let entered = short.enter();
        let mut owner = Owner::capture().unwrap();
        let mut arena = Arena::new();
        assert_eq!(arena.read(&source, 0, &mut owner), Err(Error::Resource));
        drop(entered);
        let replacement =
            Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(10_000)));
        let _entered = replacement.enter();
        assert_eq!(arena.read(&source, 0, &mut owner), Err(Error::Resource));
        assert_eq!(replacement.ticks(), 0);
    }
}
