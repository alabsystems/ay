// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Monotonic-clock shim (re-export of [`ay_sys::time`]).
//!
//! On native targets `Instant` is exactly `std::time::Instant`, so host codegen
//! is byte-identical. On `wasm32-unknown-unknown` it is `ay-sys`'s host-clock
//! shim. The implementation lives in `ay-sys` because it needs an `unsafe` FFI
//! call and `ay-core` is `#![forbid(unsafe_code)]`; this module simply re-exports
//! it so the rest of the workspace can write `ay_core::time::Instant`.

pub use ay_sys::time::Instant;
