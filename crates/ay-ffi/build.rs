// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Build script: embeds build provenance into ay-ffi.
//!
//! This keeps the FFI version surface aligned with the stamped build identity
//! exposed by the CLI and other consumers. What the stamp claims, and what it
//! watches, is `build_support/provenance.rs`.

#[path = "../../build_support/provenance.rs"]
mod provenance;

fn main() {
    provenance::emit_build_provenance();
}
