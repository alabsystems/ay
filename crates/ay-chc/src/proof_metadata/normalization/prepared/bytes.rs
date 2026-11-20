// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Requested-capacity, copy and eventual logical disposal offers before reserve.

use super::{Control, QueryError};
use std::mem::size_of;

pub(super) struct Bytes(pub(super) Vec<u8>);

pub(in super::super) fn reserve<T, C: Control>(
    values: &mut Vec<T>,
    additional: usize,
    control: &mut C,
) -> Result<(), QueryError> {
    // Six field reads/tests and up to ten checked size/header operations.
    control.offer(16, 0)?;
    let needed = values
        .len()
        .checked_add(additional)
        .ok_or_else(|| control.exhausted())?;
    if needed <= values.capacity() {
        return Ok(());
    }
    let capacity = values
        .capacity()
        .checked_mul(2)
        .ok_or_else(|| control.exhausted())?
        .max(needed);
    let requested = capacity
        .checked_mul(size_of::<T>())
        .ok_or_else(|| control.exhausted())?;
    let old = values
        .len()
        .checked_mul(size_of::<T>())
        .ok_or_else(|| control.exhausted())?;
    let work = requested
        .checked_mul(2)
        .and_then(|x| x.checked_add(old))
        .and_then(|x| x.checked_add(size_of::<Vec<T>>()))
        .ok_or_else(|| control.exhausted())?;
    // Old initialized payload may be moved; requested payload + header disposal
    // are prepaid cumulatively. Allocator bookkeeping/spare capacity is not RSS.
    control.offer(work, requested)?;
    values
        .try_reserve_exact(capacity - values.len())
        .map_err(|_| control.exhausted())
}

pub(super) fn push<T, C: Control>(
    values: &mut Vec<T>,
    control: &mut C,
    value: impl FnOnce() -> T,
) -> Result<(), QueryError> {
    reserve(values, 1, control)?;
    // Fixed internal constructors run only after record construction, insertion
    // and eventual header disposal have been paid; this is not a public callback.
    let work = size_of::<T>()
        .checked_mul(3)
        .ok_or_else(|| control.exhausted())?;
    control.offer(work, 0)?;
    values.push(value());
    Ok(())
}

impl Bytes {
    pub(super) fn new<C: Control>(control: &mut C) -> Result<Self, QueryError> {
        // At most twelve fixed header transports from creation through the
        // visitor/result/row/carrier paths; sixteen includes eventual disposal.
        control.offer(16 * size_of::<Self>(), 0)?;
        Ok(Self(Vec::new()))
    }

    pub(super) fn append<C: Control>(
        &mut self,
        bytes: &[u8],
        control: &mut C,
    ) -> Result<(), QueryError> {
        reserve(&mut self.0, bytes.len(), control)?;
        let mut at = 0usize;
        while at < bytes.len() {
            control.offer(4, 0)?;
            let end = at.saturating_add(128).min(bytes.len());
            control.offer(2 * (end - at), 0)?;
            self.0.extend_from_slice(&bytes[at..end]);
            at = end;
        }
        Ok(())
    }

    pub(super) fn text<C: Control>(
        &mut self,
        text: &str,
        control: &mut C,
    ) -> Result<(), QueryError> {
        self.append(text.as_bytes(), control)
    }

    pub(super) fn finish<C: Control>(self, control: &mut C) -> Result<String, QueryError> {
        // Generated spelling preserves UTF-8, but the safe conversion checks it.
        control.offer(self.0.len(), 0)?;
        String::from_utf8(self.0)
            .map_err(|_| QueryError::Invalid("canonical spelling is not UTF-8"))
    }
}
