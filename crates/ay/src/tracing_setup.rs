// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tracing subscriber initialization for AY.
//!
//! When `--verbose` is passed, installs a `tracing-subscriber` that writes
//! human-readable output to stderr.  When tracing is off (the default), no
//! subscriber is installed and the per-call-site cost is a single relaxed
//! atomic load (~1 ns).

use tracing_subscriber::{fmt, prelude::*, EnvFilter, Registry};

/// Install the global tracing subscriber.
///
/// Must be called exactly once, before any solver work begins.
/// When `verbose` is false this is a no-op: no subscriber is installed and
/// every `tracing::info!()` call compiles down to a single relaxed atomic
/// load.
pub(crate) fn setup_tracing(verbose: bool) {
    if !verbose {
        return; // Zero cost: no subscriber installed
    }

    // Default filter: info-level for ay crates, warn for everything else.
    // The user can override via `RUST_LOG` env var.
    let filter = EnvFilter::try_from_default_env()
        .unwrap_or_else(|_| EnvFilter::new("ay_chc=info,ay_sat=info,ay=info"));

    Registry::default()
        .with(filter)
        .with(
            fmt::layer()
                .with_target(true)
                .with_writer(std::io::stderr)
                .compact(),
        )
        .init();
}
