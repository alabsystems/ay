// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::SmtContext;

#[test]
fn later_memory_cap_survives_callback_removing_ambient_scope() {
    let original = Owner::capture().expect("original owner");
    let mut scope = Some(SmtContext::scoped_thread_term_memory_budget(Some(64)));
    let mut callback = || {
        drop(scope.take());
        true
    };
    let mut continued = original.with_progress(&mut callback);
    assert_eq!(continued.admit(1, 32), Ok(()));
    assert_eq!(SmtContext::current_thread_term_memory_budget(), None);
    assert_eq!(continued.admit(1, 33), Err(Error::Resource));
    assert_eq!(original.retained().poll(), Err(Error::Resource));
}

#[test]
fn exact_captured_memory_is_accepted_without_new_credit() {
    let original = Owner::capture().expect("original owner");
    let mut scope = Some(SmtContext::scoped_thread_term_memory_budget(Some(64)));
    let mut callback = || {
        drop(scope.take());
        true
    };
    let mut continued = original.with_progress(&mut callback);
    assert_eq!(continued.admit(1, 32), Ok(()));
    assert_eq!(continued.admit(1, 32), Ok(()));
    assert_eq!(continued.admitted_storage_for_test(), 64);
    assert_eq!(continued.admit(0, 1), Err(Error::Resource));
}

#[test]
fn retained_handle_captures_memory_before_scope_ends_and_keeps_it_when_recarried() {
    let original = Owner::capture().expect("original owner").into_retained();
    let scope = SmtContext::scoped_thread_term_memory_budget(Some(64));
    let continued = original.owner();
    drop(scope);
    let recarried = continued.into_retained();
    let mut continued = recarried.owner();
    {
        let _installed = continued.enter();
        assert_eq!(SmtContext::current_thread_term_memory_budget(), Some(64));
    }
    assert_eq!(continued.admit(1, 64), Ok(()));
    assert_eq!(continued.retained().admit(1, 1), Err(Error::Resource));
    assert_eq!(original.owner().poll(), Err(Error::Resource));
}

#[test]
fn earlier_original_memory_limit_cannot_be_widened_by_new_caller() {
    let scope = SmtContext::scoped_thread_term_memory_budget(Some(32));
    let original = Owner::capture().expect("original 32-byte owner");
    drop(scope);
    let _larger = SmtContext::scoped_thread_term_memory_budget(Some(64));
    let mut open = || true;
    let mut continued = original.with_progress(&mut open);
    assert_eq!(continued.admit(1, 32), Ok(()));
    assert_eq!(continued.admit(1, 1), Err(Error::Resource));
}
