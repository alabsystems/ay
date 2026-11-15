// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::resource::{ChildSpec, Guard, NodeLabel};

fn guard(limit: u64) -> Guard {
    Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(limit)))
}

#[test]
fn later_caller_guard_is_debited_and_scope_replacement_cannot_hide_it() {
    let original = Owner::capture().expect("original unbounded owner");
    let caller = guard(10);
    let mut scope = Some(caller.enter());
    let mut callback = || {
        drop(scope.take());
        true
    };
    let mut continued = original.with_progress(&mut callback);
    assert_eq!(continued.admit(7, 0), Ok(()));
    assert_eq!(caller.ticks(), 7);
    assert_eq!(continued.admit(4, 0), Err(Error::Resource));
    assert_eq!(original.retained().poll(), Err(Error::Resource));
}

#[test]
fn shared_counter_views_are_debited_once_and_both_caps_stay_live() {
    let original = guard(100);
    let scope = original.enter();
    let owner = Owner::capture().expect("original");
    drop(scope);
    let mut view = original.clone();
    view.set_rlimit(Some(10));
    let _scope = view.enter();
    let mut open = || true;
    let mut continued = owner.with_progress(&mut open);
    assert_eq!(continued.admit(7, 0), Ok(()));
    assert_eq!((original.ticks(), view.ticks()), (7, 7));
    assert_eq!(continued.admit(4, 0), Err(Error::Resource));
}

#[test]
fn full_child_settles_once_but_cancel_only_debits_both_allowances() {
    for cancel_only in [false, true] {
        let parent = guard(100);
        let scope = parent.enter();
        let owner = Owner::capture().expect("parent");
        drop(scope);
        let spec = ChildSpec::new(NodeLabel::Certify).with_rlimit(Some(40));
        let child = parent.child(if cancel_only {
            spec.cancel_only()
        } else {
            spec
        });
        {
            let _scope = child.enter();
            let mut open = || true;
            let mut continued = owner.with_progress(&mut open);
            assert_eq!(continued.admit(7, 0), Ok(()));
            assert_eq!(child.ticks(), 7);
            assert_eq!(parent.ticks(), if cancel_only { 7 } else { 0 });
        }
        drop(child);
        assert_eq!(parent.ticks(), 7);
    }
}

#[test]
fn later_sibling_view_cannot_be_covered_through_skipped_parent() {
    let parent = guard(100);
    let scope = parent.enter();
    let owner = Owner::capture().expect("parent").into_retained();
    drop(scope);
    let child = parent.child(ChildSpec::new(NodeLabel::Search).with_rlimit(Some(40)));
    let scope = child.enter();
    let retained = owner.owner();
    drop(scope);
    let mut view = parent.clone();
    view.set_rlimit(Some(10));
    let _scope = view.enter();
    let mut open = || true;
    let mut continued = retained.with_progress(&mut open);
    assert_eq!(continued.admit(7, 0), Ok(()));
    assert_eq!((parent.ticks(), child.ticks(), view.ticks()), (7, 7, 7));
    assert_eq!(continued.admit(4, 0), Err(Error::Resource));
    assert_eq!(owner.owner().poll(), Err(Error::Resource));
}
