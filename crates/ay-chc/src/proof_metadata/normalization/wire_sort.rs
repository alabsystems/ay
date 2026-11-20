// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Sort the same full canonical keys under the artifact reader's remaining work grant.
//! The shared stable merge sort charges scratch storage, moves and bounded prefix
//! comparisons before use. Unique constructor lists remain keyed by fixed-size IDs.

use super::{input_identity_with_control, ordered, prepared, ChcProblem, Progress};
use ay_core::original_query::{QueryError, StopReason};
use prepared::Control;
use std::cmp::Ordering;

#[derive(Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct Key<'a>(pub(super) &'a str, pub(super) &'a str, pub(super) usize);

impl<'a> Key<'a> {
    pub(super) fn text(s: &'a str) -> Self {
        Self(s, "", 0)
    }
}

pub(crate) struct WireSort<'a> {
    pub(crate) remaining: &'a mut usize,
    pub(crate) progress: &'a mut dyn FnMut() -> bool,
}

impl Control for WireSort<'_> {
    fn offer(&mut self, work: usize, storage: usize) -> Result<(), QueryError> {
        self.poll()?;
        *self.remaining = self
            .remaining
            .checked_sub(work)
            .and_then(|left| left.checked_sub(storage))
            .ok_or(QueryError::Exhausted)?;
        Ok(())
    }

    fn exhausted(&mut self) -> QueryError {
        QueryError::Exhausted
    }
}

impl Progress for WireSort<'_> {
    type Error = QueryError;

    fn poll(&mut self) -> Result<(), Self::Error> {
        if (self.progress)() {
            Ok(())
        } else {
            Err(QueryError::Interrupted(StopReason::Cancelled))
        }
    }

    fn sort<T>(&mut self, rows: &mut [T], key: impl Fn(&T) -> Key<'_>) -> Result<(), QueryError> {
        let count = rows.len();
        if count < 2 {
            return self.poll();
        }
        let order = prepared::order::indices(count, self, |left, right, this| {
            let a = key(&rows[left]);
            let b = key(&rows[right]);
            let first = prepared::order::compare(a.0.as_bytes(), b.0.as_bytes(), this)?;
            if first != Ordering::Equal {
                return Ok(first);
            }
            let second = prepared::order::compare(a.1.as_bytes(), b.1.as_bytes(), this)?;
            Ok(second.then_with(|| a.2.cmp(&b.2)))
        })?;
        // Convert destination -> source to source -> destination, then apply each
        // disjoint cycle in place. Payload strings remain in their original buffers.
        let mut dest = Vec::new();
        prepared::bytes::reserve(&mut dest, count, self)?;
        self.offer(
            count
                .checked_mul(std::mem::size_of::<usize>() * 3)
                .ok_or(QueryError::Exhausted)?,
            0,
        )?;
        dest.resize(count, 0);
        for (to, from) in order.into_iter().enumerate() {
            dest[from] = to;
        }
        for i in 0..count {
            while dest[i] != i {
                self.offer(
                    4 * std::mem::size_of::<usize>() + 3 * std::mem::size_of::<T>(),
                    0,
                )?;
                let j = dest[i];
                rows.swap(i, j);
                dest.swap(i, j);
            }
        }
        self.poll()
    }
}

impl WireSort<'_> {
    pub(crate) fn normalized(
        &mut self,
        p: &ChcProblem,
    ) -> Result<(&'static str, String), QueryError> {
        input_identity_with_control(p, self)
    }

    pub(crate) fn ordered(&mut self, p: &ChcProblem) -> Result<String, QueryError> {
        ordered::hash(p, self)
    }
}
