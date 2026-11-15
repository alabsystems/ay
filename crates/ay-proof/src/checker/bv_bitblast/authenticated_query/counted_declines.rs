// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Counted exhaustions of the authentication lanes, remembered per lowered
//! query, so one query never pays the same counted exhaustion twice.
//!
//! The Bool/BV lane and the atom-leaf lane lower a pure Bool/BV query to the
//! very same expression, and certification runs one after the other: each paid
//! the whole counted envelope for the identical SAT problem. What is repeated
//! here is only an exhaustion of the COUNTED caps that ended before the lane's
//! deadline (the caller's solve deadline or the hang guard); a stop is never
//! recorded. Repeating it can only DECLINE the lane, which is never an
//! authentication, so a spurious hit could cost availability and nothing
//! else. The key is the query's fingerprint (a hash of its full structural
//! form) with the counted envelope's identity; the table lives on this thread
//! and holds [`MAX_REMEMBERED`] entries.

use std::cell::RefCell;
use std::hash::Hasher;

use super::super::producer_limits::strict_producer_envelope_id;
use crate::{BvExpr, BvExprExportError};

const MAX_REMEMBERED: usize = 64;

/// The counted envelope's identity and the lowered query's fingerprint.
pub(super) type Key = (u64, u64);

thread_local! {
    static DECLINES: RefCell<Vec<(Key, BvExprExportError)>> = const { RefCell::new(Vec::new()) };
}

#[cfg(test)]
thread_local! {
    /// Exports actually run on this thread, so a test can prove a repeated
    /// exhaustion did not run the producer again.
    pub(super) static EXPORTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(super) fn note_export() {
    EXPORTS.with(|exports| exports.set(exports.get() + 1));
}

#[cfg(not(test))]
pub(super) fn note_export() {}

struct HashWriter<'a>(&'a mut std::collections::hash_map::DefaultHasher);

impl std::fmt::Write for HashWriter<'_> {
    fn write_str(&mut self, text: &str) -> std::fmt::Result {
        self.0.write(text.as_bytes());
        Ok(())
    }
}

/// Key `query` under the lanes' counted envelope. `Debug` spells the whole
/// expression tree, leaf names included; it is streamed into the hash, never
/// materialized.
pub(super) fn key(query: &BvExpr) -> Key {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    let _ = std::fmt::write(&mut HashWriter(&mut hasher), format_args!("{query:?}"));
    (strict_producer_envelope_id(), hasher.finish())
}

pub(super) fn remembered(key: Key) -> Option<BvExprExportError> {
    DECLINES.with(|declines| {
        declines
            .borrow()
            .iter()
            .find(|(seen, _)| *seen == key)
            .map(|(_, error)| error.clone())
    })
}

/// Record a counted exhaustion. The caller has established that it ended
/// before the lane's deadline.
pub(super) fn remember(key: Key, error: &BvExprExportError) {
    DECLINES.with(|declines| {
        let mut declines = declines.borrow_mut();
        if declines.len() >= MAX_REMEMBERED {
            declines.remove(0);
        }
        declines.push((key, error.clone()));
    });
}
