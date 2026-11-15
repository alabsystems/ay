// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--sat-veripb-hints` statistics: proof additions by technique, those written
//! without hints (`red`, the steps the official check pays most for), hint
//! fallbacks by reason, and the derived-clause counters.

use super::veripb_hints::HINT_FAIL_KEYS;
use super::*;
use crate::diagnostic_trace::DiagnosticPass;
use std::collections::HashMap;

/// Call sites reported by `red_site_profile`.
const RED_SITES_REPORTED: usize = 16;

impl Solver {
    /// Count a proof addition written by the technique now running.
    #[inline]
    pub(super) fn note_proof_add(&mut self) {
        let code = Self::diagnostic_pass_code(self.cold.diagnostic_pass) as usize;
        self.cold.veripb_hints.adds_by_pass[code] += 1;
    }

    /// Count an addition written without hints (`red` on VeriPB) by the pass
    /// that wrote it and, with hints on, by the technique's call site (the
    /// proof-add funnels are `#[track_caller]` down to here).
    #[inline]
    #[track_caller]
    pub(super) fn note_unhinted_add(&mut self) {
        let code = Self::diagnostic_pass_code(self.cold.diagnostic_pass) as usize;
        self.cold.veripb_hints.derived.red_by_pass[code] += 1;
        if self.veripb_hints_active() {
            let at = std::panic::Location::caller();
            *self
                .cold
                .veripb_hints
                .red_sites
                .entry((at.file(), at.line()))
                .or_default() += 1;
        }
    }

    /// Proof additions by the pass that wrote them, keyed `sat.proof_adds_<pass>`,
    /// those written without hints, `sat.proof_red_<pass>`, and the RUP-probe
    /// walks that failed, `sat.veripb_probe_fail_<reason>`.
    pub fn proof_add_profile(&self) -> Vec<(String, u64)> {
        let st = &self.cold.veripb_hints;
        DiagnosticPass::BY_CODE
            .iter()
            .zip(st.adds_by_pass)
            .map(|(pass, count)| (format!("sat.proof_adds_{}", pass.as_str()), count))
            .chain(
                DiagnosticPass::BY_CODE
                    .iter()
                    .zip(st.derived.red_by_pass)
                    .map(|(pass, count)| (format!("sat.proof_red_{}", pass.as_str()), count)),
            )
            .chain(self.red_site_profile())
            .chain(
                HINT_FAIL_KEYS
                    .iter()
                    .zip(st.probe_fail_counts)
                    .filter(|&(_, count)| count > 0)
                    .map(|(key, count)| (key.replace("hint_fail", "probe_fail"), count)),
            )
            .collect()
    }

    /// The call sites that wrote the most `red` steps, keyed
    /// `sat.proof_red_at_<dir>/<file>:<line>`, and those whose RUP-probe
    /// walks failed most, `sat.veripb_probe_fail_at_<dir>/<file>:<line>`.
    fn red_site_profile(&self) -> Vec<(String, u64)> {
        let st = &self.cold.veripb_hints;
        top_sites("sat.proof_red_at_", &st.red_sites)
            .into_iter()
            .chain(top_sites("sat.veripb_probe_fail_at_", &st.probe_fail_sites))
            .collect()
    }

    /// Fallbacks by reason, and jump reasons resolved, keyed by stat name.
    pub fn veripb_hint_fail_profile(&self) -> Vec<(&'static str, u64)> {
        let mut profile: Vec<(&'static str, u64)> = HINT_FAIL_KEYS
            .iter()
            .zip(self.cold.veripb_hints.fail_counts)
            .map(|(name, count)| (*name, count))
            .collect();
        profile.push((
            "sat.veripb_hint_jumps_resolved",
            self.cold.veripb_hints.jumps_resolved,
        ));
        profile.push((
            "sat.veripb_hint_walk_visited",
            self.cold.veripb_hints.walk_visited,
        ));
        profile.push(("sat.veripb_hint_walk_ids", self.cold.veripb_hints.walk_ids));
        profile.push((
            "sat.veripb_hint_walk_units",
            self.cold.veripb_hints.walk_units,
        ));
        profile.push((
            "sat.veripb_hint_walk_ms",
            self.cold.veripb_hints.walk_ns / 1_000_000,
        ));
        profile.push((
            "sat.veripb_derived_hinted",
            self.cold.veripb_hints.derived.hinted,
        ));
        profile.push((
            "sat.veripb_derived_plain",
            self.cold.veripb_hints.derived.plain,
        ));
        profile.push((
            "sat.veripb_fresh_collections",
            self.proof_manager
                .as_ref()
                .map_or(0, |manager| manager.output().veripb_fresh_collections()),
        ));
        profile.push((
            "sat.veripb_anchored_reds",
            self.proof_manager
                .as_ref()
                .map_or(0, |manager| manager.output().veripb_anchored_reds()),
        ));
        profile
    }

    /// (learned clauses written with hints, written without after a failed
    /// walk, level-0 units written to make a hint possible).
    pub fn veripb_hint_profile(&self) -> (u64, u64, u64) {
        let st = &self.cold.veripb_hints;
        (st.hinted, st.fallbacks, st.units_written)
    }
}

/// The `RED_SITES_REPORTED` most frequent call sites of `sites`, keyed
/// `<prefix><dir>/<file>:<line>` (the directory too: several passes live in a
/// `mod.rs`).
fn top_sites(prefix: &str, sites: &HashMap<(&'static str, u32), u64>) -> Vec<(String, u64)> {
    let mut sites: Vec<_> = sites.iter().collect();
    sites.sort_unstable_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
    sites
        .into_iter()
        .take(RED_SITES_REPORTED)
        .map(|(&(file, line), &count)| {
            let file = file.rsplitn(3, '/').take(2).collect::<Vec<_>>();
            let file = file.iter().rev().copied().collect::<Vec<_>>().join("/");
            (format!("{prefix}{file}:{line}"), count)
        })
        .collect()
}
