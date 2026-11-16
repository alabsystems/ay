// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn exact_z3_510_parameter_database_is_closed() {
    let globals = PARAMETER_DETAILS
        .iter()
        .filter(|(name, _)| !name.contains('.'))
        .count();
    assert_eq!(globals, 25);
    assert_eq!(MODULE_TEXT.len(), 22);
    assert_eq!(MODULE_MARKDOWN.len(), 23);
    assert_eq!(PARAMETER_DETAILS.len(), 688);
    assert_eq!(PARAMETER_DETAILS.len() - globals, 663);
    assert_eq!(NULL_DEFAULT_PARAMETERS.len(), 15);
}

#[test]
fn maps_are_sorted_and_profiles_are_in_bounds() {
    for entries in [
        MODULE_TEXT,
        MODULE_MARKDOWN,
        MODULE_LEGAL_PARAMETERS,
        PARAMETER_DETAILS,
    ] {
        assert!(entries.windows(2).all(|pair| pair[0].0 < pair[1].0));
        assert!(entries
            .iter()
            .all(|(_, profile)| (*profile as usize) < OUTPUT_PROFILES.len()));
    }
    assert!(OUTPUT_PROFILES
        .iter()
        // `OUTPUT_PROFILES` is `&[&[u16]]`, so `.iter()` yields
        // `&&[u16]` — a double reference, which is not
        // `IntoIterator`, so `.flatten()` does not compile.
        .copied()
        .flatten()
        .all(|line| (*line as usize) < OUTPUT_LINES.len()));
    assert!(OLD_GLOBAL_PARAMETERS
        .windows(2)
        .all(|pair| pair[0] < pair[1]));
}

#[test]
fn z3_parameter_normalization_matches_source() {
    assert_eq!(
        normalize_parameter(":SMT.RANDOM-SEED"),
        ("smt".to_string(), "random_seed".to_string())
    );
    assert_eq!(
        normalize_parameter("well-sorted-check"),
        (String::new(), "well_sorted_check".to_string())
    );
}
