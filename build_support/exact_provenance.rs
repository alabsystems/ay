// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::env as exact_provenance_env;

/// Validate the compile-time tokens used by the exact binary provenance JSON.
///
/// The endpoint deliberately has a byte-exact schema. Restricting both values
/// to the helper's content-identity alphabet makes direct JSON interpolation
/// unambiguous and prevents hostile build environments from injecting JSON or
/// terminal control bytes.
fn validate_exact_binary_provenance_env() {
    for name in ["AY_TEST_SOURCE_IDENTITY", "AY_TEST_BUILD_IDENTITY"] {
        println!("cargo:rerun-if-env-changed={name}");
        let Some(value) = exact_provenance_env::var_os(name) else {
            continue;
        };
        let value = value
            .into_string()
            .unwrap_or_else(|_| panic!("{name} must be valid UTF-8 exact-provenance text"));
        assert!(
            !value.is_empty()
                && value
                    .bytes()
                    .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-'),
            "{name} must be a non-empty ASCII alphanumeric/hyphen exact-provenance token"
        );
    }
}
