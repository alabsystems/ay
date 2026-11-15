// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The quantified-route statistics (`qsat.*`, `qlra.*`, `eq_qe.*`) of one
//! public solve, carried across the resets of its internal passes.

use super::super::Executor;
use crate::executor_types::Statistics;

/// Key prefixes of the quantified-route statistics carried across the
/// internal passes of one public solve.
const ROUTE_STAT_PREFIXES: [&str; 3] = ["qsat.", "qlra.", "eq_qe."];

fn is_route_stat(key: &str) -> bool {
    ROUTE_STAT_PREFIXES
        .iter()
        .any(|prefix| key.starts_with(prefix))
}

impl Executor {
    /// Close the carry: the next reset starts a fresh scope that carries
    /// nothing from before it (`cegar_refine_solve` brackets each check-sat's
    /// internal passes with this, and `begin_public_solve` clears it too).
    pub(in crate::executor) fn reset_route_statistics_carry(&mut self) {
        self.qsat_route.route_stats.clear();
        self.qsat_route.route_stats_live = false;
    }

    /// Carry the quantified-route statistics across an internal re-solve's
    /// reset (`prepare_check_sat_internal_state`), which replaced
    /// `last_statistics` with a fresh block and handed the discarded one in as
    /// `previous`.
    ///
    /// Only the QSAT route restored its keys (from its memo); the nested lane
    /// restored `qlra.*` only when a retry re-entered it, and the equality-QE
    /// lane never did. A deep-QE or trace-armed retry that reached a deadline,
    /// or took a path that does not re-enter the lanes, therefore published
    /// `--stats` without saying what the lanes had done (`qlra.cert
    /// "expansion-deferred"`, `eq_qe.gate`). Every later pass's own writes
    /// still win: the carried values are reinserted BEFORE the pass runs.
    /// Statistics only; no decision reads these keys.
    pub(in crate::executor) fn carry_route_statistics(&mut self, previous: &Statistics) {
        if self.qsat_route.route_stats_live {
            for (key, value) in &previous.extra {
                if !is_route_stat(key) {
                    continue;
                }
                match self
                    .qsat_route
                    .route_stats
                    .iter_mut()
                    .find(|(carried, _)| carried == key)
                {
                    Some((_, carried)) => *carried = value.clone(),
                    None => self
                        .qsat_route
                        .route_stats
                        .push((key.clone(), value.clone())),
                }
            }
        }
        self.qsat_route.route_stats_live = true;
        for (key, value) in &self.qsat_route.route_stats {
            self.last_statistics
                .extra
                .insert(key.clone(), value.clone());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::executor::Executor;
    use crate::executor_types::StatValue;

    fn with(entries: &[(&str, StatValue)]) -> Statistics {
        let mut stats = Statistics::default();
        for (key, value) in entries {
            stats.extra.insert((*key).to_string(), value.clone());
        }
        stats
    }

    /// An internal re-solve's reset keeps every earlier pass's route keys
    /// of THIS public solve (later writes win), carries nothing else, and
    /// never carries the previous public solve's keys into the next one.
    #[test]
    fn route_statistics_survive_resets_within_one_public_solve_only() {
        let mut exec = Executor::new();
        let label = |s: &str| StatValue::String(s.to_string());

        // First pass of a public solve: what it discards is the previous
        // solve's block, never carried.
        exec.qsat_route.begin_public_solve();
        exec.carry_route_statistics(&with(&[("qlra.cert", label("stale"))]));
        assert_eq!(exec.last_statistics.get_string("qlra.cert"), None);

        // A retry's reset discards the first pass's block: its route keys
        // (and only those) come back.
        exec.last_statistics = Statistics::default();
        exec.carry_route_statistics(&with(&[
            ("qlra.cert", label("expansion-deferred")),
            ("eq_qe.gate", label("refused")),
            ("qsat.verdict", label("unsat")),
            ("cert.decisions", StatValue::Int(1)),
        ]));
        let stats = &exec.last_statistics;
        assert_eq!(stats.get_string("qlra.cert"), Some("expansion-deferred"));
        assert_eq!(stats.get_string("eq_qe.gate"), Some("refused"));
        assert_eq!(stats.get_string("qsat.verdict"), Some("unsat"));
        assert_eq!(stats.get_int("cert.decisions"), None);

        // A later pass overwrote a key: its value wins on the next reset.
        let mut second = exec.last_statistics.clone();
        second
            .extra
            .insert("qlra.cert".to_string(), label("expansion-installed"));
        exec.last_statistics = Statistics::default();
        exec.carry_route_statistics(&second);
        assert_eq!(
            exec.last_statistics.get_string("qlra.cert"),
            Some("expansion-installed")
        );
        assert_eq!(
            exec.last_statistics.get_string("eq_qe.gate"),
            Some("refused")
        );

        // A closed carry scope (the end of one `cegar_refine_solve`) carries
        // nothing into the next check-sat, public or not.
        exec.reset_route_statistics_carry();
        exec.last_statistics = Statistics::default();
        exec.carry_route_statistics(&second);
        assert_eq!(exec.last_statistics.get_string("qlra.cert"), None);
        exec.last_statistics = Statistics::default();
        exec.carry_route_statistics(&second);
        assert_eq!(
            exec.last_statistics.get_string("qlra.cert"),
            Some("expansion-installed"),
            "a second reset inside the new scope carries its first pass"
        );

        // The next public solve starts clean.
        exec.qsat_route.begin_public_solve();
        exec.last_statistics = Statistics::default();
        exec.carry_route_statistics(&second);
        assert_eq!(exec.last_statistics.get_string("qlra.cert"), None);
        assert_eq!(exec.last_statistics.get_string("eq_qe.gate"), None);
    }
}
