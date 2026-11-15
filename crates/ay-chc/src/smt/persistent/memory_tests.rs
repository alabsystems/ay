// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::resource_observation::{ResourceRefusal, ScopedResourceObservation};

#[test]
fn cached_array_executor_cannot_accept_or_reset_past_inherited_cap() {
    let observation = ScopedResourceObservation::install();
    let mut context = PersistentExecutorSmtContext::new();
    let _cap = SmtContext::scoped_thread_term_memory_budget(Some(1));
    assert!(!context.ensure_background(&ChcExpr::Bool(true), Duration::from_secs(20)));
    assert_eq!(context.backend.exec.term_memory_limit(), Some(1));
    context.reset_backend();
    assert!(matches!(
        context.check_query(
            &ChcExpr::Bool(true),
            &FxHashMap::default(),
            Duration::from_secs(20),
        ),
        SmtResult::Unknown
    ));
    assert_eq!(context.backend.exec.term_memory_limit(), Some(1));
    assert_eq!(observation.first(), Some(ResourceRefusal::Memory));
}
