// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof conclusion: final validation after all proof steps are processed.
//!
//! CaDiCaL lratchecker.cpp:569-587 (basic conclude checks) + :797-811
//! (report_status finalization coverage check).
//!
//! Extracted from checker/mod.rs for the 500-line limit.

use std::io::Write;

use super::types::{ConcludeFailure, ConcludeResult};
use super::LratChecker;

impl LratChecker {
    /// Check whether an empty clause derivation was encountered.
    pub fn derived_empty_clause(&self) -> bool {
        self.has_empty_clause
    }

    /// Conclude the proof as UNSAT. Checks: (0) not already concluded,
    /// (1) steps were processed, (2) no step failures, (3) empty clause derived,
    /// (4) finalization coverage (if finalize_clause() was used).
    ///
    /// Failures are checked before empty clause: when a step failure prevents
    /// the empty clause from being derived, `StepFailures` is the root cause.
    /// CaDiCaL avoids this via fatal abort on first error (lratchecker.cpp
    /// fatal_message_end); in ay's non-aborting design, the ordering matters.
    ///
    /// CaDiCaL lratchecker.cpp:569-587 (basic checks) + :797-811 (report_status).
    pub fn conclude_unsat(&mut self) -> ConcludeResult {
        if self.concluded {
            let _ = writeln!(
                std::io::stderr(),
                "LRAT conclude_unsat: already concluded (double-conclusion)"
            );
            return ConcludeResult::Failed(ConcludeFailure::AlreadyConcluded);
        }
        self.concluded = true;
        if self.stats.derived == 0 {
            let _ = writeln!(
                std::io::stderr(),
                "LRAT conclude_unsat: no derivation steps processed"
            );
            return ConcludeResult::Failed(ConcludeFailure::NoStepsProcessed);
        }
        if self.stats.failures > 0 {
            let _ = writeln!(
                std::io::stderr(),
                "LRAT conclude_unsat: {} derivation step(s) failed",
                self.stats.failures
            );
            return ConcludeResult::Failed(ConcludeFailure::StepFailures);
        }
        if !self.has_empty_clause {
            let _ = writeln!(
                std::io::stderr(),
                "LRAT conclude_unsat: empty clause not derived"
            );
            return ConcludeResult::Failed(ConcludeFailure::NoEmptyClause);
        }
        // Finalization coverage check (CaDiCaL lratchecker.cpp:797-811).
        // Only enforced when finalize_clause() has been called at least once.
        // This preserves backward compatibility: callers that don't use
        // finalization still pass. When finalization is used, every original
        // clause must be either deleted or finalized.
        if self.stats.finalized > 0 {
            // Use deleted_originals (not total deleted) for coverage check.
            // Derived-clause deletions must NOT count toward original coverage.
            // CaDiCaL lratchecker.cpp:797-811 tracks originals separately.
            let accounted = self.stats.finalized + self.stats.deleted_originals;
            if accounted != self.stats.originals {
                let _ = writeln!(
                    std::io::stderr(),
                    "LRAT conclude_unsat: finalization check failed: \
                     {} originals but {} finalized + {} deleted_originals = {} accounted",
                    self.stats.originals,
                    self.stats.finalized,
                    self.stats.deleted_originals,
                    accounted,
                );
                return ConcludeResult::Failed(ConcludeFailure::IncompleteCoverage {
                    originals: self.stats.originals,
                    finalized: self.stats.finalized,
                    deleted_originals: self.stats.deleted_originals,
                });
            }
        }
        ConcludeResult::Verified
    }

    /// Format verification statistics as a diagnostic string.
    pub fn stats_summary(&self) -> String {
        format!(
            "original={} derived={} deleted={} deleted_originals={} \
             weakened={} restored={} finalized={} failures={} \
             rup={} resolution_ok={} resolution_mismatch={} rat={} blocked={} \
             compactions={}",
            self.stats.originals,
            self.stats.derived,
            self.stats.deleted,
            self.stats.deleted_originals,
            self.stats.weakened,
            self.stats.restored,
            self.stats.finalized,
            self.stats.failures,
            self.stats.rup_ok,
            self.stats.resolution_ok,
            self.stats.resolution_mismatch,
            self.stats.rat_ok,
            self.stats.blocked_ok,
            self.stats.compactions,
        )
    }
}
