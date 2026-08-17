// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT-LIB Parser Fuzz Target
//!
//! This fuzz target ensures the SMT-LIB parser doesn't panic or exhibit
//! undefined behavior on arbitrary input. The parser should gracefully
//! handle malformed input and return appropriate errors.

#![no_main]
#![forbid(unsafe_code)]

use ay_frontend::parse;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    // Try to interpret bytes as UTF-8 string
    if let Ok(input) = std::str::from_utf8(data) {
        // Parser should never panic - it should return Result
        let _ = parse(input);
    }
    // Non-UTF8 data is ignored (parser expects string input)
});
