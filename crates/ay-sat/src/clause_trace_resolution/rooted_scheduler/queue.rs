// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Fixed-capacity binary min-heap. Explicit operations keep comparisons,
/// relocations and writes inside the conversion meter, with no hidden growth.
pub(super) fn push(
    heap: &mut Vec<usize>,
    position: usize,
    bound: usize,
    meter: &mut ConversionMeter<'_>,
) -> Result<(), ResolutionValidationError> {
    let requested = checked_resource_add(
        heap.len(),
        1,
        ResolutionValidationResource::AssignmentScratch,
    )?;
    enforce_resource(
        ResolutionValidationResource::AssignmentScratch,
        requested,
        bound.min(heap.capacity()),
    )?;
    meter.charge(1)?;
    heap.push(position);
    let mut index = heap.len() - 1;
    while index > 0 {
        meter.charge(1)?;
        let parent = (index - 1) / 2;
        if heap[parent] <= heap[index] {
            break;
        }
        meter.charge(2)?;
        heap.swap(parent, index);
        index = parent;
    }
    Ok(())
}

pub(super) fn pop(
    heap: &mut Vec<usize>,
    meter: &mut ConversionMeter<'_>,
) -> Result<Option<usize>, ResolutionValidationError> {
    meter.charge(1)?;
    if heap.is_empty() {
        return Ok(None);
    }
    let first = heap[0];
    // swap_remove(0) is constant-time and never reallocates.
    meter.charge(2)?;
    heap.swap_remove(0);
    let mut index = 0;
    while index < heap.len() / 2 {
        meter.charge(1)?;
        let left = index * 2 + 1;
        let right = left + 1;
        let child = if right < heap.len() && heap[right] < heap[left] {
            right
        } else {
            left
        };
        meter.charge(1)?;
        if heap[index] <= heap[child] {
            break;
        }
        meter.charge(2)?;
        heap.swap(index, child);
        index = child;
    }
    Ok(Some(first))
}
