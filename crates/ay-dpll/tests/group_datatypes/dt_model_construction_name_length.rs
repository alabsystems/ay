// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! A datatype's name does not decide whether its model can be built.
//!
//! The fixture is a bounded (BMC) query model-checker-consumer exports for a harness over
//! `[Option<u8>; 2]`, with the datatype named by its definition path
//! (`std_option_Option_u8`). It is satisfiable. Its first candidate model
//! fails the model gate, and the answer then rests on total datatype model
//! construction, whose opaque-collection preflight charged its quadratic pair
//! envelope in identifier bytes: 785 selector and constructor pairs fit at the
//! longest spelling's 19-byte weight and were refused at 20. Renaming the
//! datatype from `Option_u8` (9 bytes) to `OptionX_u8` (10) turned `sat` into
//! `unknown`; every longer name stayed `unknown`. The pair envelope counts
//! pairs and the byte-weighted cost goes to the work envelope
//! (`dt_construct_budget.rs`, `finish`).

const QUERY: &str = include_str!("../fixtures/dt_option_refjoin_bmc_query.smt2");
const EXPORTED_NAME: &str = "std_option_Option_u8";

#[test]
fn satisfiable_query_is_sat_at_every_datatype_name_length() {
    let long = "q".repeat(40);
    for name in ["Option_u8", "OptionX_u8", EXPORTED_NAME, long.as_str()] {
        let smt = QUERY.replace(EXPORTED_NAME, name);
        let output = crate::common::solve_authored_vec(&smt);
        assert_eq!(
            output.first().map(String::as_str),
            Some("sat"),
            "datatype named `{name}` ({} bytes): {output:?}",
            name.len()
        );
    }
}
