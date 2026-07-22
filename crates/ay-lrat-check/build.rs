// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

include!("../../build_support/exact_provenance.rs");

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=../../build_support/exact_provenance.rs");
    validate_exact_binary_provenance_env();
}
