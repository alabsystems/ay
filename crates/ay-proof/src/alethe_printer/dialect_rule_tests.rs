// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Every Clean-only spelling names the consumer rule that admits it.
//!
//! The rule is stated once, in Clean (its `third-party/carcara/DOWNSTREAM.md`;
//! [`CleanOnlySpelling::consumer_rule`] says where a key's entry is not there
//! yet); AY names it by key and Clean's agreement test checks that the key is
//! a rule its checker implements. A
//! spelling with no key, or a key outside the three forms DOWNSTREAM.md names
//! its rules by, would be a reliance nobody can check.

use super::CleanOnlySpelling;

/// The variants, named by an exhaustive match: `#[non_exhaustive]` does not
/// bind inside this crate, so a new variant does not compile here until it is
/// named, and once named it must be listed in [`CleanOnlySpelling::ALL`].
fn named(spelling: CleanOnlySpelling) -> CleanOnlySpelling {
    match spelling {
        CleanOnlySpelling::SignFilledAshrOvershift
        | CleanOnlySpelling::ZeroExtendAsConcat
        | CleanOnlySpelling::FixedDivider
        | CleanOnlySpelling::DatatypeSelectorProject
        | CleanOnlySpelling::BvOffsetEqualitySimplify
        | CleanOnlySpelling::BvOffsetSpinesV1
        | CleanOnlySpelling::BvReconstructV1 => spelling,
    }
}

#[test]
fn every_clean_only_spelling_is_listed_with_its_consumer_rule() {
    let named_variants = [
        named(CleanOnlySpelling::SignFilledAshrOvershift),
        named(CleanOnlySpelling::ZeroExtendAsConcat),
        named(CleanOnlySpelling::FixedDivider),
        named(CleanOnlySpelling::DatatypeSelectorProject),
        named(CleanOnlySpelling::BvOffsetEqualitySimplify),
        named(CleanOnlySpelling::BvOffsetSpinesV1),
        named(CleanOnlySpelling::BvReconstructV1),
    ];
    assert_eq!(CleanOnlySpelling::ALL, &named_variants[..]);
    let mut keys = Vec::new();
    for &spelling in CleanOnlySpelling::ALL {
        let key = spelling.consumer_rule();
        let well_formed = match key.split_once(':') {
            Some(("dialect", option)) => {
                let (stem, version) = option.rsplit_once("_v").unwrap_or((option, ""));
                !stem.is_empty()
                    && stem.bytes().all(|b| b.is_ascii_lowercase() || b == b'_')
                    && (version.is_empty()
                        || (!version.starts_with('0')
                            && version.bytes().all(|b| b.is_ascii_digit())))
            }
            Some(("fix", row)) => row.parse::<u32>().is_ok_and(|row| row > 0),
            Some(("extension", row)) => row
                .strip_prefix('C')
                .is_some_and(|row| row.parse::<u32>().is_ok_and(|row| row > 0)),
            _ => false,
        };
        assert!(well_formed, "{spelling:?}: {key}");
        assert!(!keys.contains(&key), "{spelling:?} repeats the key {key}");
        keys.push(key);
    }
}

#[test]
fn a_dialect_spelling_names_its_rule_in_the_disclosure_and_has_conformance_problems() {
    for &spelling in CleanOnlySpelling::ALL {
        let key = spelling.consumer_rule();
        if key.starts_with("dialect:") {
            let line = format!("{} {}", spelling.describe(), spelling.pinned_dialect_note());
            assert!(line.contains(key), "{spelling:?}: {line}");
            let problems = spelling.conformance_problems();
            assert!(!problems.is_empty(), "{spelling:?}");
            for problem in problems {
                assert!(
                    problem.starts_with("(set-logic ") && problem.ends_with("(check-sat)\n"),
                    "{problem}"
                );
            }
        }
    }
}
