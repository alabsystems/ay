// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Read-only accounting of arbitrary existing producer data, not permission to
//! construct it. Snapshot copy prices are charged as work before hashing or
//! comparison; no copy or new storage grant is involved.
use super::*;

fn inspect(
    owner: &dyn TermConstructionAdmission,
    visit: impl FnOnce(
        &mut dyn FnMut(usize, usize) -> bool,
    ) -> std::result::Result<(), crate::term::TermSnapshotError>,
) -> Result<()> {
    let result = visit(&mut |work, bytes| {
        let Some(total) = work.checked_add(bytes) else {
            storage::work(owner);
            return false;
        };
        owner.admit(total, 0).is_ok()
    });
    owner.check()?;
    result.map_err(|_| storage::work(owner))
}

pub(super) fn entry(
    term: &TermData,
    sort: &Sort,
    owner: &dyn TermConstructionAdmission,
) -> Result<()> {
    inspect(owner, |progress| {
        crate::term::snapshot::meter_entry(term, sort, progress)
    })
}

pub(super) fn sort_equal(
    left: &Sort,
    right: &Sort,
    owner: &dyn TermConstructionAdmission,
) -> Result<bool> {
    inspect(owner, |progress| {
        crate::term::snapshot::meter_sort(left, 0, progress)?;
        crate::term::snapshot::meter_sort(right, 0, progress)
    })?;
    Ok(left == right)
}
