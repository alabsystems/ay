// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fallible, caller-admitted bootstrap for the existing DRUP checker.

use super::{DenseArrays, DenseRefusal, DratChecker, Stats, INITIAL_HASH_CAPACITY, MAX_DENSE_VARS};
use rustc_hash::FxHashMap;
use std::collections::TryReserveError;
use std::mem::size_of;

pub(super) enum CheckMode {
    Drup,
    Rat,
}

/// No checker is returned when any bootstrap operation is refused.
#[derive(Debug, thiserror::Error)]
pub enum CheckerConstructionError<E> {
    /// The caller's exact admission error, without replacing its authority.
    #[error("checker bootstrap admission refused")]
    Admission(E),
    /// The requested dense universe exceeds the existing supported envelope.
    #[error("checker universe {requested} exceeds {maximum} variables")]
    VariableLimit { requested: usize, maximum: usize },
    /// A logical allocation or work size cannot be represented.
    #[error("checker bootstrap size overflow")]
    SizeOverflow,
    /// An actual fallible vector reservation failed.
    #[error("checker bootstrap allocation refused: {0}")]
    Allocation(#[source] TryReserveError),
}

impl DratChecker {
    /// Construct the ordinary DRUP checker under a borrowed original admission.
    ///
    /// This admits all six dense buffers AND the initial hash buckets before
    /// fallible reservation. Logical bytes are requested elements times their
    /// size, not allocator capacity or RSS. Work counts one bootstrap step,
    /// one per reservation, and one per bounded initialization chunk plus two
    /// per initialized slot (initialization and conservative later cleanup).
    /// Chunking polls the SAME callback during large fills; it adds no grant.
    /// The final poll follows assembly. A refusal drops all partial buffers.
    ///
    /// The callback is borrowed, so this API does not drop opaque captures
    /// after its final poll. Its caller owns sticky refusal/unwind handling
    /// and must fence any later cleanup. Later insertion/RUP work is NOT
    /// instrumented by this constructor. Ordinary `new` remains compatible.
    pub fn try_new_drup_with_admission<E>(
        num_vars: usize,
        admit: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<Self, CheckerConstructionError<E>> {
        construct(num_vars, admit, &mut Reservations::default())
    }

    pub(super) fn from_arrays(
        num_vars: usize,
        dense: DenseArrays,
        hash_buckets: Vec<Vec<usize>>,
        mode: CheckMode,
        dense_refusal: Option<DenseRefusal>,
    ) -> Self {
        Self {
            num_vars,
            assigns: dense.assigns,
            trail: Vec::new(),
            propagate_cursor: 0,
            watches: dense.watches,
            occ_lists: dense.occ_lists,
            clauses: Vec::new(),
            free_clause_slots: Vec::new(),
            hash_buckets,
            live_clauses: 0,
            inconsistent: false,
            authority_tainted: false,
            dense_refusal,
            #[cfg(test)]
            reservations_before_refusal: None,
            bulk_verify_started: false,
            stats: Stats::default(),
            check_rat: matches!(mode, CheckMode::Rat),
            marks: dense.marks,
            reasons: dense.reasons,
            bcp_conflict_cidx: None,
            conflict_marked: dense.conflict_marked,
            conflict_marked_dirty: Vec::new(),
            scratch_resolvent: Vec::new(),
            clause_match_counts: FxHashMap::default(),
            clause_match_consumed: Vec::new(),
            core_first: false,
            prep: false,
            simplify_buf: Vec::new(),
        }
    }
}

fn construct<E>(
    num_vars: usize,
    admit: &mut impl FnMut(usize, usize) -> Result<(), E>,
    reservations: &mut Reservations,
) -> Result<DratChecker, CheckerConstructionError<E>> {
    use CheckerConstructionError as Error;
    admit(1, 0).map_err(Error::Admission)?;
    if num_vars > MAX_DENSE_VARS {
        return Err(Error::VariableLimit {
            requested: num_vars,
            maximum: MAX_DENSE_VARS,
        });
    }
    let literals = num_vars.checked_mul(2).ok_or(Error::SizeOverflow)?;
    let dense = DenseArrays {
        assigns: reservations.filled(None, num_vars, admit)?,
        watches: reservations.filled(Vec::new(), literals, admit)?,
        occ_lists: reservations.filled(Vec::new(), literals, admit)?,
        marks: reservations.filled(false, literals, admit)?,
        reasons: reservations.filled(None, num_vars, admit)?,
        conflict_marked: reservations.filled(false, num_vars, admit)?,
    };
    let buckets = reservations.filled(Vec::new(), INITIAL_HASH_CAPACITY, admit)?;
    let checker = DratChecker::from_arrays(num_vars, dense, buckets, CheckMode::Drup, None);
    admit(0, 0).map_err(Error::Admission)?;
    Ok(checker)
}

/// Fault injection is local to one test construction, never global or ambient.
#[derive(Default)]
struct Reservations {
    #[cfg(test)]
    before_failure: Option<usize>,
    #[cfg(test)]
    attempts: usize,
}

impl Reservations {
    fn filled<T: Clone, E>(
        &mut self,
        element: T,
        len: usize,
        admit: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<Vec<T>, CheckerConstructionError<E>> {
        use CheckerConstructionError as Error;
        let bytes = len.checked_mul(size_of::<T>()).ok_or(Error::SizeOverflow)?;
        admit(1, bytes).map_err(Error::Admission)?;
        let mut values = Vec::new();
        self.reserve(&mut values, len).map_err(Error::Allocation)?;
        // All T here are scalars or EMPTY Vec headers: clone never allocates.
        // The already-paid cleanup allowance covers partial-fill destruction.
        while values.len() < len {
            let count = (len - values.len()).min(1024);
            admit(2 * count + 1, 0).map_err(Error::Admission)?;
            values.extend(std::iter::repeat_n(element.clone(), count));
        }
        Ok(values)
    }

    fn reserve<T>(&mut self, values: &mut Vec<T>, len: usize) -> Result<(), TryReserveError> {
        #[cfg(test)]
        {
            self.attempts += 1;
            if let Some(remaining) = self.before_failure.as_mut() {
                if *remaining == 0 {
                    // A real, deterministic capacity failure; no giant alloc.
                    return values.try_reserve_exact(usize::MAX);
                }
                *remaining -= 1;
            }
        }
        values.try_reserve_exact(len)
    }
}

#[cfg(test)]
mod tests;
