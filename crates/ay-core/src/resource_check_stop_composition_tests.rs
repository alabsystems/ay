// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::resource::{ChildSpec, DeadlineSource, Guard, NodeLabel};
use crate::time::Instant;
use std::sync::atomic::{AtomicBool, Ordering};

#[test]
fn explicit_callback_and_tree_stop_cannot_hide_each_other() {
    let tree_flag = Arc::new(AtomicBool::new(false));
    let owner_flag = Arc::new(AtomicBool::new(false));
    let owner_poll = Arc::clone(&owner_flag);
    let original: CheckStop = Arc::new(move || owner_poll.load(Ordering::SeqCst));
    let _owner = enter_check_stop(Arc::clone(&original));
    let check =
        Guard::root_child(ChildSpec::new(NodeLabel::Check).with_external(Arc::clone(&tree_flag)));
    let _scope = check.enter();
    assert!(Arc::ptr_eq(
        &current_check_stop().unwrap().unwrap(),
        &original
    ));
    assert!(!check_stop_requested());
    owner_flag.store(true, Ordering::SeqCst);
    assert!(check_stop_requested());
    owner_flag.store(false, Ordering::SeqCst);
    tree_flag.store(true, Ordering::SeqCst);
    assert!(check_stop_requested());
    tree_flag.store(false, Ordering::SeqCst);
    assert!(
        !check_stop_requested(),
        "the live poll does not latch a stop"
    );
}

#[test]
fn nested_explicit_callbacks_restore_the_exact_original() {
    let original: CheckStop = Arc::new(|| false);
    let outer = enter_check_stop(Arc::clone(&original));
    let check = Guard::new();
    let _tree = check.enter();
    {
        let _inner = enter_check_stop(Arc::new(|| true));
        assert!(check_stop_requested());
    }
    assert!(!check_stop_requested());
    assert!(Arc::ptr_eq(
        &current_check_stop().unwrap().unwrap(),
        &original
    ));
    drop(outer);
    assert!(current_check_stop().unwrap().is_none());
}

#[test]
fn certification_skips_search_deadline_but_not_an_explicit_owner() {
    let search = Guard::root_child(
        ChildSpec::new(NodeLabel::Search).with_deadline(DeadlineSource::Fixed(Instant::now())),
    );
    let _search = search.enter();
    assert!(check_stop_requested());
    let certification = search.child(ChildSpec::new(NodeLabel::Certify).cancel_only());
    let _certification = certification.enter();
    assert!(!check_stop_requested());
    assert!(current_check_stop().unwrap().is_none());
    let _explicit_owner = enter_check_stop(Arc::new(|| true));
    assert!(check_stop_requested(), "an explicit owner is never renewed");
}

#[test]
fn a_shared_guard_view_keeps_the_original_external_cancel_handle() {
    let flag = Arc::new(AtomicBool::new(false));
    let mut original = Guard::new();
    original.set_cancel(Some(Arc::clone(&flag)));
    let mut view = original.clone();
    view.set_rlimit(Some(10));
    assert!(Arc::ptr_eq(original.cancel_flag().unwrap(), &flag));
    assert!(Arc::ptr_eq(view.cancel_flag().unwrap(), &flag));
    assert_eq!(view.tick(1), Ok(()));
    assert_eq!(original.ticks(), 1);
    flag.store(true, Ordering::SeqCst);
    assert_eq!(
        view.exhausted(),
        Some(crate::resource::Exhausted::Cancelled)
    );
}
