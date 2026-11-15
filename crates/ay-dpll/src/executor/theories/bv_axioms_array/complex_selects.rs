// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Membership from the existing complete select/store collector.

use super::TermId;

/// Every valid store below a collected store is itself collected, including
/// stores beneath generic/indexed Apps, Not and ITE. Its own tuple therefore
/// contributes every intermediate base the old suffix walk would discover.
/// No term lookup, chain walk or additional membership is necessary here.
pub(super) fn store_arrays(
    stores: &[(TermId, TermId, TermId, TermId)],
) -> impl Iterator<Item = TermId> + '_ {
    stores.iter().flat_map(|&(store, base, _, _)| [store, base])
}

#[cfg(test)]
mod tests;
