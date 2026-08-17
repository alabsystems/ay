// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Surface-pair filtering for proof syntax restoration.

use ay_core::TermId;

pub(super) const MAX_OVERRIDE_PAIRS: usize = 8_192;
pub(super) const MAX_OVERRIDE_SOURCE_SCAN: usize = 100_000;

/// Retain only pairs backed by a parsed source assertion.
///
/// Native internal probes and retention-off contexts can keep canonical roots
/// while deliberately dropping the parsed stack. Truncating those unmatched
/// pairs reproduces the former `zip(parsed_assertions)` behavior: canonical
/// rendering remains authoritative and the later assume-authorization and
/// demotion checks still run. Rejecting the entire refutation here would turn
/// otherwise valid MaxSMT, optimization, and Pareto boundary proofs unknown.
pub(super) fn retain_available_surface_pairs(
    pairs: &mut Vec<(TermId, usize)>,
    parsed_assertion_count: usize,
) {
    pairs.retain(|(_, index)| *index < parsed_assertion_count);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unavailable_surface_pairs_are_dropped_without_reordering() {
        let mut pairs = vec![
            (TermId::new(10), 0),
            (TermId::new(11), 2),
            (TermId::new(12), 1),
        ];

        retain_available_surface_pairs(&mut pairs, 2);

        assert_eq!(pairs, vec![(TermId::new(10), 0), (TermId::new(12), 1)]);
    }
}
