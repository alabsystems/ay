// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Charge the sort stored in a syntactic function-application key. Debug
//! spelling, Hash and comparisons see a name and a content-addressed handle at
//! a datatype occurrence. The source and value typecheckers separately account
//! for visiting actual constructors and selectors.

use super::{GroundSourceSurfaceCache, GroundSourceSurfaceError, GroundValidationControl};
use crate::{ChcDtConstructors, ChcSort};

impl GroundSourceSurfaceCache<'_> {
    pub(super) fn reserve_nested_sort_identity(
        &mut self,
        sort: &ChcSort,
        memberships: usize,
        control: &mut GroundValidationControl<'_>,
    ) -> Result<usize, GroundSourceSurfaceError> {
        if memberships == 0 {
            return Ok(0);
        }
        // The preceding reserve_source_sort has guarded every sort depth and
        // metadata node. This walk follows only what a nested identity spells.
        let exhausted = GroundSourceSurfaceError::SourceWorkLimitExceeded;
        let mut pending = vec![sort];
        let mut total = 0usize;
        while let Some(sort) = pending.pop() {
            control.poll()?;
            let (name, fixed) = match sort {
                ChcSort::Datatype { name, constructors } => {
                    let id = constructors.id();
                    if let Some(previous) = self.identity_datatypes.get(&id) {
                        // Ord breaks a real digest collision by visiting both
                        // definitions. A reference-only bound cannot admit it.
                        if !ChcDtConstructors::ptr_eq(previous, constructors) {
                            return Err(exhausted);
                        }
                    } else {
                        self.charge(128)?;
                        self.identity_datatypes
                            .try_reserve(1)
                            .map_err(|_| exhausted)?;
                        self.identity_datatypes.insert(id, constructors.clone());
                    }
                    (name.as_str(), 160usize)
                }
                ChcSort::Uninterpreted(name) => (name.as_str(), 32),
                ChcSort::Array(key, value) => {
                    pending.push(key);
                    pending.push(value);
                    ("", 32)
                }
                ChcSort::Bool | ChcSort::Int | ChcSort::Real | ChcSort::BitVec(_) => ("", 32),
            };
            // At most ten Debug bytes per input byte (Unicode escapes), plus
            // the variant's delimiters, decimal width or fixed 64-digit ID.
            let work = name
                .len()
                .checked_mul(10)
                .and_then(|n| n.checked_add(fixed))
                .and_then(|n| n.checked_mul(memberships))
                .ok_or(exhausted)?;
            self.charge(work)?;
            total = total.checked_add(work).ok_or(exhausted)?;
        }
        Ok(total)
    }
}

#[cfg(test)]
mod tests;
