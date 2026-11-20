// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bottom-up stable mergesort of fixed-size indices (Knuth, TAOCP vol.3, §5.2.4).
//! Byte comparisons are offered in bounded chunks, not an opaque String::cmp.

use super::{bytes, Control, QueryError};
use std::cmp::Ordering;

pub(in super::super) fn compare<C: Control>(
    a: &[u8],
    b: &[u8],
    control: &mut C,
) -> Result<Ordering, QueryError> {
    let mut at = 0usize;
    while at < a.len().min(b.len()) {
        control.offer(4, 0)?;
        let end = at.saturating_add(128).min(a.len()).min(b.len());
        control.offer(2 * (end - at), 0)?;
        let comparison = a[at..end].cmp(&b[at..end]);
        if comparison != Ordering::Equal {
            return Ok(comparison);
        }
        at = end;
    }
    control.offer(1, 0)?;
    Ok(a.len().cmp(&b.len()))
}

pub(in super::super) fn indices<C: Control>(
    count: usize,
    control: &mut C,
    mut compare: impl FnMut(usize, usize, &mut C) -> Result<Ordering, QueryError>,
) -> Result<Vec<usize>, QueryError> {
    control.offer(4 * std::mem::size_of::<Vec<usize>>(), 0)?;
    let mut order = Vec::new();
    let mut scratch = Vec::new();
    bytes::reserve(&mut order, count, control)?;
    bytes::reserve(&mut scratch, count, control)?;
    for index in 0..count {
        bytes::push(&mut order, control, || index)?;
        bytes::push(&mut scratch, control, || 0)?;
    }
    let mut width = 1usize;
    while width < count {
        control.offer(4, 0)?;
        let mut start = 0usize;
        while start < count {
            control.offer(8, 0)?;
            let middle = start.saturating_add(width).min(count);
            let end = middle.saturating_add(width).min(count);
            merge(
                &order,
                &mut scratch,
                start,
                middle,
                end,
                control,
                &mut compare,
            )?;
            start = end;
        }
        control.offer(3 * std::mem::size_of::<Vec<usize>>(), 0)?;
        std::mem::swap(&mut order, &mut scratch);
        width = width.checked_mul(2).ok_or_else(|| control.exhausted())?;
    }
    Ok(order)
}

fn merge<C: Control>(
    order: &[usize],
    scratch: &mut [usize],
    start: usize,
    middle: usize,
    end: usize,
    control: &mut C,
    compare: &mut impl FnMut(usize, usize, &mut C) -> Result<Ordering, QueryError>,
) -> Result<(), QueryError> {
    let (mut left, mut right) = (start, middle);
    for output in start..end {
        control.offer(8 + 4 * std::mem::size_of::<usize>(), 0)?;
        let take_left = left < middle
            && (right == end || compare(order[left], order[right], control)? != Ordering::Greater);
        scratch[output] = if take_left {
            let value = order[left];
            left += 1;
            value
        } else {
            let value = order[right];
            right += 1;
            value
        };
    }
    Ok(())
}
