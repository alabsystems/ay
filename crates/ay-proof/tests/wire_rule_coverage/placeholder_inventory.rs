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
    // the emitted wire text is byte-identical, only the spelling moved. Three
    // positional `{}` sites likewise print this exact constant: the two fresh
    // definitional lowerings `format_fresh_def_bound` / `format_fresh_def_eq`,
    // which have no Alethe rule to claim, and the promoted-LIA evaluation
    // fallback taken when the ground formatter declines. The remaining
    // positional site prints the already-inventoried promoted Farkas rule.
    //
    // The two `rule` sites are bounded selectors: `sko_forall`/`sko_ex` after
    // strict Skolem-step validation, and the shared promoted Farkas wire rule.
    // The unsigned-comparison duality site similarly selects its two rules
    // from the fixed decoder table. The counts below make every such producer
    // addition fail closed until this census and the candidate inventory are
    // reviewed together.
    //
    // `blast_rule` and `simplify_rule` each have TWO sites, and both pairs are
    // fed by the SAME production table: `decode_idempotent_bv_gate`, whose arms
    // this test reads field-by-field. The second pair is the zero-test duality's
    // gate bridge (`alethe_printer/bv_ult_zero.rs`), which lowers the very same
    // `(bvand v v)` / `(bvor v v)` collapse. It previously spliced its rule
    // names out of a connective fragment (`:rule bitblast_{conn}` and `:rule
    // {conn}_simplify`); that spelling put a name the checker cannot resolve
    // (`bitblast_`) into the literal inventory while hiding the real names from
    // it, so the site now carries complete rule names from the shared table.
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
        ("", 4),
        ("UNPROVED_STEP_RULE", 1),
        ("blast_rule", 2),
        ("non_strict_rule", 1),
        ("rule", 2),
        ("rule_name", 2),
        ("simplify_rule", 2),
        ("strict_rule", 1),
        ("wire", 2),
        ("wire_rule", 1),
    ]);
    assert_eq!(
        actual, expected,
        "unaccounted dynamic :rule placeholder; connect its producer to the wire-rule inventory"
    );
}
