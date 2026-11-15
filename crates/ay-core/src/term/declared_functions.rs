// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! User declarations whose core identity is not their surface spelling.
//!
//! The declaring layer gives a `declare-fun` / `declare-const` a private core
//! identity (`__ay_overload_N`) when its surface spelling cannot be used: a
//! re-declaration after `pop` with a new signature, or a name a builtin owns
//! (`abs`, `div`, ...). Such a name looks internal, and a consumer that
//! classifies symbols by spelling reads `__ay*` as interpreted; it is in fact
//! an uninterpreted symbol, and this registry says so by provenance.
//!
//! Membership is exact: the declaring layer registers each private identity
//! it mints for a user declaration, and nothing else (datatype members and
//! definitions are not declarations). Like `constructor_fields`, the set is
//! append-only for the store's lifetime and keyed by NAME, so it survives
//! `rollback_to` and `mark_and_compact`; identities are never reused.

use super::TermStore;

impl TermStore {
    /// Record that `identity` is the core identity of a user declaration
    /// (an uninterpreted symbol whatever its spelling).
    pub fn register_declared_function(&mut self, identity: &str) {
        if !self.declared_functions.contains(identity) {
            self.declared_functions.insert(identity.to_string());
            self.bump_checker_visible_metadata_generation();
        }
    }

    /// Whether `identity` was registered by
    /// [`Self::register_declared_function`].
    #[must_use]
    pub fn is_declared_function(&self, identity: &str) -> bool {
        self.declared_functions.contains(identity)
    }

    /// Borrow the exact user-function identities that must remain opaque to
    /// builtin readers. Callers copying them must admit each owning string.
    pub fn declared_function_identities(&self) -> impl ExactSizeIterator<Item = &str> {
        self.declared_functions.iter().map(String::as_str)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn declared_identities_are_exact_and_survive_clone() {
        let mut store = TermStore::new();
        let generation = store.checker_visible_metadata_generation();
        assert!(!store.is_declared_function("__ay_overload_0"));
        store.register_declared_function("__ay_overload_0");
        assert_eq!(store.checker_visible_metadata_generation(), generation + 1);
        store.register_declared_function("__ay_overload_0");
        assert_eq!(store.checker_visible_metadata_generation(), generation + 1);
        assert!(store.is_declared_function("__ay_overload_0"));
        assert!(!store.is_declared_function("__ay_overload_1"));
        let cloned = store.clone();
        assert!(cloned.is_declared_function("__ay_overload_0"));
    }
}
