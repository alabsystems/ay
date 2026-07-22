// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Statistics tracking for clause-level IC3 (#8211).

/// Statistics for the IC3 solver.
#[derive(Debug, Clone, Default)]
pub(crate) struct Ic3Stats {
    /// Number of SAT solver calls
    pub(crate) sat_calls: u64,
    /// Number of cubes blocked across all frames
    pub(crate) cubes_blocked: u64,
    /// Number of MIC generalization attempts
    pub(crate) generalizations: u64,
    /// Total literals dropped by MIC generalization
    pub(crate) literals_dropped: u64,
    /// Number of clauses propagated forward
    pub(crate) clauses_propagated: u64,
    /// Number of frames created
    pub(crate) frames_created: u64,
    /// Number of proof obligations processed
    pub(crate) obligations_processed: u64,
    /// Number of counterexample traces generated
    pub(crate) cex_traces: u64,
    /// UNSAT core shrinks performed
    pub(crate) core_shrinks: u64,
    /// CTG (Counterexample-To-Generalization) attempts that successfully
    /// blocked a predecessor and enabled an otherwise-impossible literal drop.
    pub(crate) ctg_successes: u64,
    /// Number of independent-consecution cross-checks performed (every reduced
    /// cube on small systems is re-verified on a fresh, independent solver).
    pub(crate) cross_check_calls: u64,
    /// Generalized cubes rejected by the independent-consecution cross-check
    /// (fell back to the un-generalized cube). A nonzero value indicates the
    /// soundness backstop caught a false-UNSAT from the incremental solver.
    pub(crate) cross_check_rejections: u64,
    /// Domain BCP skip count (watchers skipped due to non-domain variables, #8430)
    pub(crate) domain_bcp_skips: u64,
    /// Domain BCP call count (#8430)
    pub(crate) domain_bcp_calls: u64,
}

impl std::fmt::Display for Ic3Stats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "IC3 stats: sat_calls={}, blocked={}, gen={}, lit_drop={}, prop={}, frames={}, obligs={}, domain_bcp(calls={}, skips={})",
            self.sat_calls,
            self.cubes_blocked,
            self.generalizations,
            self.literals_dropped,
            self.clauses_propagated,
            self.frames_created,
            self.obligations_processed,
            self.domain_bcp_calls,
            self.domain_bcp_skips,
        )
    }
}
