// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for `ay::api` and `ay::prelude` helper utility parity (#6589).
//!
//! Verifies that the helper slice (`VERSION`, panic helpers, `cached_env_flag!`)
//! is accessible through both the explicit-import (`ay::api`) and glob-import
//! (`ay::prelude`) consumer surfaces.

// ---- Packet C: api helper parity ----

#[test]
fn test_api_exports_helper_facade() {
    // VERSION is accessible and non-empty
    let v: &str = ay::api::VERSION;
    assert!(!v.is_empty(), "VERSION must be non-empty");

    // panic_payload_to_string converts &str payloads
    let s =
        ay::api::panic_payload_to_string(&("test payload" as &str) as &(dyn std::any::Any + Send));
    assert_eq!(s, "test payload");

    // panic_payload_to_string converts String payloads
    let s = ay::api::panic_payload_to_string(
        &String::from("owned payload") as &(dyn std::any::Any + Send)
    );
    assert_eq!(s, "owned payload");

    // is_ay_panic_reason is callable
    assert!(ay::api::is_ay_panic_reason("BUG: something broke"));
    assert!(!ay::api::is_ay_panic_reason("user error"));

    // catch_ay_panics can wrap a non-panicking closure
    let result: Result<i32, String> = ay::api::catch_ay_panics(|| Ok(42), Err);
    assert_eq!(result, Ok(42));

    // cached_env_flag! can be imported from api and expanded
    ay::api::cached_env_flag!(test_env_flag_6589, "AY_TEST_ENV_FLAG_6589");
    let _ = test_env_flag_6589();
}

// ---- Packet C: prelude helper parity ----

#[test]
fn test_prelude_exports_helper_facade() {
    use ay::prelude::*;

    // VERSION is accessible and non-empty
    let v: &str = VERSION;
    assert!(!v.is_empty(), "VERSION must be non-empty");

    // panic_payload_to_string converts &str payloads
    let s = panic_payload_to_string(&("test payload" as &str) as &(dyn std::any::Any + Send));
    assert_eq!(s, "test payload");

    // panic_payload_to_string converts String payloads
    let s = panic_payload_to_string(&String::from("owned payload") as &(dyn std::any::Any + Send));
    assert_eq!(s, "owned payload");

    // is_ay_panic_reason is callable
    assert!(is_ay_panic_reason("BUG: something broke"));
    assert!(!is_ay_panic_reason("user error"));

    // catch_ay_panics can wrap a non-panicking closure
    // Note: prelude::* imports ay::Result which shadows std::result::Result,
    // so we use the fully qualified path here.
    let result: std::result::Result<i32, String> = catch_ay_panics(|| Ok(42), Err);
    assert_eq!(result, Ok(42));

    // cached_env_flag! can be imported from prelude and expanded
    cached_env_flag!(test_prelude_flag_6589, "AY_TEST_PRELUDE_FLAG_6589");
    let _ = test_prelude_flag_6589();
}
