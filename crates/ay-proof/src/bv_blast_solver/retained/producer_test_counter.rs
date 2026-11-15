// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Test-only census at the common expression proof-producer entry. Search
//! grants of zero do not establish absence of a call: root propagation or a
//! lucky phase can produce a refutation without a counted CDCL conflict.

use std::cell::Cell;

thread_local! {
    static CALLS: Cell<usize> = const { Cell::new(0) };
}

pub(crate) fn record() {
    CALLS.with(|calls| calls.set(calls.get().checked_add(1).expect("test counter overflow")));
}

pub(crate) fn count() -> usize {
    CALLS.with(Cell::get)
}
