// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `clause_trace_resolution.rs` to retain private item paths.

fn reserve_exact<T>(
    values: &mut Vec<T>,
    count: usize,
    resource: ResolutionValidationResource,
    meter: &mut ConversionMeter<'_>,
) -> Result<(), ResolutionValidationError> {
    // Poll only around a reservation big enough to be worth interrupting.
    //
    // `check_controls` reads the process footprint, which is a `task_info`
    // Mach RPC. These two polls were unconditional, so every reservation --
    // and the dominant caller reserves ONE CLAUSE, ~2.5 literals -- paid for
    // two syscalls to guard an allocation that costs far less than they do.
    //
    // Cancellation is not weakened: `ConversionMeter::charge` already polls on
    // every `CONTROL_POLL_INTERVAL` work boundary, which is the rate this
    // module's own constant declares ("Long conversion loops poll external
    // controls at least this often"). A reservation at or above that size is
    // the only one that can outrun that rate, and it still polls.
    let poll = count >= CONTROL_POLL_INTERVAL;
    if poll {
        meter.check_controls()?;
    }
    values
        .try_reserve_exact(count)
        .map_err(|_| ResolutionValidationError::AllocationFailed { resource })?;
    if poll {
        meter.check_controls()?;
    }
    Ok(())
}

fn copy_slice_bounded<T: Copy>(
    values: &[T],
    resource: ResolutionValidationResource,
    meter: &mut ConversionMeter<'_>,
) -> Result<Vec<T>, ResolutionValidationError> {
    let mut copy = Vec::new();
    reserve_exact(&mut copy, values.len(), resource, meter)?;
    // `charge` carries the poll. It calls `check_controls` whenever the work
    // counter crosses a `CONTROL_POLL_INTERVAL` boundary, so for a FULL chunk
    // (`chunk.len() == CONTROL_POLL_INTERVAL`) the poll rate here is exactly
    // what the removed explicit call gave -- one per chunk -- while a short
    // slice no longer buys a `task_info` syscall per clause to copy a handful
    // of literals. The trailing poll is likewise subsumed: it could only
    // observe a stop that the next `charge` in the enclosing conversion loop
    // observes anyway.
    for chunk in values.chunks(CONTROL_POLL_INTERVAL) {
        meter.charge(chunk.len())?;
        copy.extend_from_slice(chunk);
    }
    Ok(copy)
}
