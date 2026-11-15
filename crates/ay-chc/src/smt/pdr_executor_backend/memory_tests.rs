// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::resource_observation::{ResourceRefusal, ScopedResourceObservation};

#[test]
fn inherited_persistent_cap_is_latched_before_reset_and_cannot_be_raised() {
    let observation = ScopedResourceObservation::install();
    let _cap = super::super::SmtContext::scoped_thread_term_memory_budget(Some(1));
    let mut backend = PdrExecutorBackend::new();
    assert_eq!(backend.exec.term_memory_limit(), Some(1));
    assert!(!backend.resources_open());
    backend.reset();
    backend.set_term_memory_limit(Some(usize::MAX));
    assert!(!backend.resources_open());
    assert_eq!(backend.exec.term_memory_limit(), Some(1));
    assert_eq!(observation.first(), Some(ResourceRefusal::Memory));
}

#[test]
fn warm_persistent_context_tightens_to_new_ambient_owner() {
    let mut backend = PdrExecutorBackend::new();
    backend.set_term_memory_limit(Some(usize::MAX));
    {
        let _cap = super::super::SmtContext::scoped_thread_term_memory_budget(Some(1));
        assert!(!backend.resources_open());
        assert_eq!(backend.exec.term_memory_limit(), Some(1));
    }
    backend.reset();
    assert!(!backend.resources_open());
    assert_eq!(backend.exec.term_memory_limit(), Some(1));
}
