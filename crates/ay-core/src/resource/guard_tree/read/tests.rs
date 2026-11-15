// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::resource::ChildSpec;

#[test]
fn charging_relation_includes_clones_and_shared_counter_views() {
    let guard = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(100)));
    let mut first = guard.clone();
    let mut second = guard.clone();
    first.set_rlimit(Some(20));
    second.set_rlimit(Some(30));
    for (left, right) in [(&guard, &first), (&first, &guard), (&first, &second)] {
        assert!(left.charges_against(right));
        assert!(right.charges_against(left));
    }
    assert!(first.tick(7).is_ok());
    assert_eq!((guard.ticks(), first.ticks(), second.ticks()), (7, 7, 7));
}

#[test]
fn full_ancestry_settles_once_but_cancel_only_is_independent() {
    let parent = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(100)));
    {
        let child = parent.child(ChildSpec::new(NodeLabel::Search).with_rlimit(Some(40)));
        let leaf = child.child(ChildSpec::new(NodeLabel::Grant).with_rlimit(Some(10)));
        assert!(leaf.charges_against(&parent));
        assert!(leaf.charges_against(&child));
        assert!(!parent.charges_against(&leaf));
        assert!(leaf.tick(3).is_ok());
        assert_eq!(parent.ticks(), 0, "live grant, not immediate spend");
    }
    assert_eq!(
        parent.ticks(),
        3,
        "one settlement, not a second direct tick"
    );
    let separate = parent.child(
        ChildSpec::new(NodeLabel::Certify)
            .cancel_only()
            .with_rlimit(Some(20)),
    );
    let leaf = separate.child(ChildSpec::new(NodeLabel::Grant).with_rlimit(Some(5)));
    assert!(!separate.charges_against(&parent));
    assert!(!leaf.charges_against(&parent));
    assert!(leaf.charges_against(&separate));
}

#[test]
fn unrelated_guards_and_later_tight_ancestor_views_are_not_covered() {
    let parent = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(100)));
    let child = parent.child(ChildSpec::new(NodeLabel::Search).with_rlimit(Some(50)));
    let mut tight = parent.clone();
    tight.set_rlimit(Some(10));
    assert!(child.charges_against(&parent));
    assert!(!child.charges_against(&tight));
    let unrelated = Guard::new();
    assert!(!child.charges_against(&unrelated));
    assert!(!unrelated.charges_against(&child));
    assert!(child.tick(11).is_ok());
    assert_eq!(tight.ticks(), 0, "child work is still held by its grant");
    assert_eq!(
        tight.poll(),
        None,
        "live child spend has not settled into this view"
    );
    assert_eq!(tight.tick(1), Err(crate::resource::Exhausted::Rlimit));
}
