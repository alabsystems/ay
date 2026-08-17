// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact census for dynamic Alethe rule placeholders found by wire coverage.

use std::collections::{BTreeMap, BTreeSet};

pub(super) fn assert_expected(placeholders: &BTreeMap<String, BTreeSet<String>>) {
    let actual = placeholders
        .iter()
        .map(|(name, sites)| (name.as_str(), sites.len()))
        .collect::<BTreeMap<_, _>>();
    // `UNPROVED_STEP_RULE` is a CONSTANT, not a computed rule name: every
    // expansion prints the one checker-implemented unproved marker. The scanner
    // cannot resolve constants, so it reports the identifier as if it were a
    // dynamic placeholder. `b83b2fa1d refactor(proof): isolate eq-transitive
    // surface guards` extracted `alethe_printer_eq_transitive.rs` and spelled
    // the name as an inline format placeholder instead of a substituted value —
    // the emitted wire text is byte-identical, only the spelling moved.
    //
    // The exemption is pinned to the constant's VALUE so it cannot become a
    // hiding place: if the constant is ever redefined to some rule name carcara
    // does not implement, this fails here rather than shipping an unknown rule.
    assert_eq!(
        ay_core::UNPROVED_STEP_RULE,
        "hole",
        "the const-substituted placeholder exempted below must remain the \
         checker-implemented unproved marker"
    );
    let expected = BTreeMap::from([
        ("", 1),
        ("UNPROVED_STEP_RULE", 1),
        ("blast_rule", 1),
        ("rule_name", 2),
        ("simplify_rule", 1),
        ("wire", 2),
        ("wire_rule", 1),
    ]);
    assert_eq!(
        actual, expected,
        "unaccounted dynamic :rule placeholder; connect its producer to the wire-rule inventory"
    );
}
