// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]
use super::*;
use ay_core::debug_channel::misc_cli_flags_with;
use std::sync::OnceLock;

#[test]
fn cached_selected_emission_target_refuses_even_when_current_flags_are_inactive() {
    let _scope = ay_core::misc_test_override::set(misc_cli_flags_with(|flags| {
        flags.ab_triage_clause = None
    }));
    let target = OnceLock::new();
    target.set(Some(vec![1, -2])).unwrap();
    assert!(!counted_triage_inactive(&target));
    assert_eq!(target.get(), Some(&Some(vec![1, -2])));
}

#[test]
fn unselected_capture_initializes_only_none_and_never_replaces_an_existing_cache() {
    let _scope = ay_core::misc_test_override::set(misc_cli_flags_with(|flags| {
        flags.ab_triage_clause = None
    }));
    let target = OnceLock::new();
    assert!(counted_triage_inactive(&target));
    assert_eq!(target.get(), Some(&None));
    let _selected = ay_core::misc_test_override::set(misc_cli_flags_with(|flags| {
        flags.ab_triage_clause = Some("1,-2".to_owned())
    }));
    assert!(
        counted_triage_inactive(&target),
        "same cached ordinary selection"
    );
    assert_eq!(target.get(), Some(&None));
}

#[test]
fn unresolved_selected_target_refuses_without_parsing_or_populating_cache() {
    let _scope = ay_core::misc_test_override::set(misc_cli_flags_with(|flags| {
        flags.ab_triage_clause = Some("1,-2".to_owned())
    }));
    let target = OnceLock::new();
    assert!(!counted_triage_inactive(&target));
    assert!(target.get().is_none());
}
