// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Build script: embeds build provenance into ay-dpll.
//!
//! This keeps the executor's SMT-LIB `get-info :version` surface aligned with
//! the CLI build provenance contract without requiring the outer `ay` crate.
//! What the stamp claims, and what it watches, is `build_support/provenance.rs`.

#[path = "../../build_support/provenance.rs"]
mod provenance;

fn main() {
    provenance::emit_build_provenance();
}
