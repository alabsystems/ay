// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Typed cancellation for borrowed, synchronous proof emission.

use std::io;

#[derive(Debug, thiserror::Error)]
#[error("bounded proof emission cancelled")]
struct EmissionCancelled;

pub(crate) fn is_bounded_emission_cancelled(error: &io::Error) -> bool {
    error
        .get_ref()
        .is_some_and(|inner| inner.is::<EmissionCancelled>())
}

pub(crate) fn bounded_emission_cancelled() -> io::Error {
    // Interrupted is deliberately not used: Write::write_all retries it.
    io::Error::other(EmissionCancelled)
}
