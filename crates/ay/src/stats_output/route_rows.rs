// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The curated block's `quantified routes` group.

/// Key prefixes of the quantified decision routes (QSAT game, nested-CEGQI
/// LRA lane, equality QE).
const ROUTE_PREFIXES: [&str; 3] = ["qsat.", "qlra.", "eq_qe."];

/// The `(":key", value)` rows of the quantified routes, in key order.
///
/// The routes record what they decided and why they declined in `extra`
/// under [`ROUTE_PREFIXES`]. Like the certificate rows these are absent on
/// runs the routes never touched, so the group prints exactly the keys
/// present and nothing else: the full block prints every `extra` key, so
/// this stays a strict selection of it. Before this group a census run with
/// `-st` could not see a route's verdict, its publication refusal or a parked
/// certificate at all, only under `--stats-full`.
pub(super) fn quantified_route_rows(stats: &ay_dpll::Statistics) -> Vec<(String, String)> {
    stats
        .extra
        .iter()
        .filter(|(key, _)| ROUTE_PREFIXES.iter().any(|prefix| key.starts_with(prefix)))
        .map(|(key, value)| (format!(":{key}"), value.to_string()))
        .collect()
}
