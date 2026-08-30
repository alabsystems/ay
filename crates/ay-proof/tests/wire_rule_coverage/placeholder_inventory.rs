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
    // fallback taken when the ground formatter declines. The fourth
    // positional site prints the already-inventoried promoted Farkas rule.
    //
    // The FIFTH positional site is NOT a constant. `707ac89b43 proof(bv):
    // certify bounded E5 shift contradictions` added
    // `alethe_printer/bv_mul_zero/shift_monotonicity.rs`, which prints one
    // Alethe step per Tseitin clause of its Boolean circuit and takes each
    // step's rule from `CnfStep::rule`. That name set is closed and
    // enumerable: `CnfStep` has one private constructor,
    // `BoolCircuit::add_clause`, called only from `BoolCircuit::build_cnf`,
    // whose arms spell exactly ten `&'static str` rules -- `true`, `false`,
    // `and_pos`, `and_neg`, `or_pos`, `or_neg`, `equiv_pos1`, `equiv_pos2`,
    // `equiv_neg1`, `equiv_neg2`. Bumping this count on its own would have
    // been a rubber stamp, so `dynamic_printer_rule_candidates` now reads
    // those ten literals straight out of that production table and feeds them
    // to the external probe. carcara 1.1.0 (git 9a352ee) implements all ten,
    // and the probe -- not this comment -- is what re-proves that every run.
    //
    // The two `rule` sites are bounded selectors: `sko_forall`/`sko_ex` after
    // strict Skolem-step validation, and the shared promoted Farkas wire rule.
    // The unsigned-comparison duality site similarly selects its two rules
    // from the fixed decoder table. The counts below make every such producer
    // addition fail closed until this census and the candidate inventory are
    // reviewed together.
    //
    // The `rule` count stays at TWO even though `707ac89b43` looked like it
    // added a third. That commit also put its test module INLINE in
    // `shift_monotonicity.rs`, and a filename suffix (`*_tests.rs`) is the
    // ONLY exclusion this scan has for test code. The inline module therefore
    // entered the scan as production and contributed both a phantom `:rule
    // {rule}` site (a loop over eight expected names) and -- worse -- a
    // literal `:rule trust` taken from a NEGATIVE assertion. `trust` is the
    // fallback AY deliberately refuses to emit (#8821) and is a name the
    // installed carcara answers `unknown rule` for, so accepting the site
    // would have failed the external probe over a rule AY never writes. Those
    // tests now live in `shift_monotonicity_tests.rs`, beside the sibling
    // `bv_mul_zero_tests.rs`, so the scan sees only what the printer emits.
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
        ("", 5),
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
