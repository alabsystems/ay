// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The capability ledger: every automatic capability decision, recorded.
//!
//! # Why this exists (batch B0 of the batteries-included migration)
//!
//! AY reads ~900 `AY_*` environment flags; 460 are set by nothing, so the
//! capabilities behind them only ran if a human typed them — and competition
//! runs type none. Worse, nothing reported *which* capabilities engaged, so
//! three fixes in a row shipped unverifiable (see
//! the development design notes §0 and the per-route outcome
//! records in `symmetry/stats.rs`, the pattern this generalises).
//!
//! The target architecture: capabilities are ON by default, disabling and
//! special options are CLI flags, tuning is decided by the engine from
//! instance features, and stale env vars are deleted. This module is the
//! instrumentation layer that makes each step of that migration verifiable:
//! one [`CapabilityDecision`] per capability *considered* — a capability that
//! declined must say so, which is the exact lesson of
//! `SymmetrySkipReason::NoGenerators`.

#[cfg(test)]
use std::mem::size_of;

/// A single automatic capability decision, recorded so `--stats` can show it.
///
/// The shape is copied from `SymmetryStats::routes`
/// (`symmetry/stats.rs`) because that is the one telemetry surface in this
/// tree that already survived a reachability audit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CapabilityDecision {
    /// Stable kebab-case capability id, e.g. `"bve"`.
    pub capability: &'static str,
    /// What the engine chose.
    pub state: CapabilityState,
    /// Which layer decided. Never guessed.
    pub source: DecisionSource,
    /// The signal that produced it, already formatted for printing,
    /// e.g. `"variant=Default"` or `"num_vars=723104 > 200000"`.
    pub because: String,
}

/// The chosen state of a capability.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CapabilityState {
    /// Capability is enabled.
    On,
    /// Capability is disabled.
    Off,
    /// A tuning value was chosen.
    Value(u64),
    /// Considered and declined, with the reason.
    Skipped(&'static str),
}

/// Which layer produced a decision.
///
/// Precedence (highest first): `Cli` > `EnvShim` > `Auto` > `Default` —
/// the same contract `ay-milp`'s `tune.rs` documents as
/// `caller > explicit env > policy > compiled default`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DecisionSource {
    /// `--disable <t>` / `--<knob> <v>`: the operator asked.
    Cli,
    /// The engine read the instance and chose.
    Auto,
    /// No signal applied; the compiled default stands.
    Default,
    /// The value came from an `AY_*` env var. B34: the A/B kill-switch
    /// family is extinct (those decisions are `Cli` now); what remains is
    /// the OFFICIAL submission wrapper's IPC contract
    /// (`AY_SAT_MAIN_ENABLE_STARTUP_PHASE_INIT`, `AY_SAT_AI_CLASS`, ...)
    /// plus the still-open value knobs — `any_env_shim` reports those.
    EnvShim(&'static str),
}

impl CapabilityState {
    /// Short printable form for `--stats`.
    #[must_use]
    pub fn label(&self) -> String {
        match self {
            Self::On => "on".to_string(),
            Self::Off => "off".to_string(),
            Self::Value(v) => format!("value={v}"),
            Self::Skipped(why) => format!("skipped({why})"),
        }
    }
}

impl DecisionSource {
    /// Short printable form for `--stats`.
    #[must_use]
    pub fn label(&self) -> String {
        match self {
            Self::Cli => "cli".to_string(),
            Self::Auto => "auto".to_string(),
            Self::Default => "default".to_string(),
            Self::EnvShim(name) => format!("env:{name}"),
        }
    }
}

/// Append-only record of every capability decision for one solve.
///
/// One entry per capability *considered*, not per capability enabled.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CapabilityLedger {
    entries: Vec<CapabilityDecision>,
}

impl CapabilityLedger {
    /// Record a decision. Append-only: later routes cannot erase earlier
    /// entries — the single-overwritten-slot failure this replaces.
    pub fn record(&mut self, d: CapabilityDecision) {
        self.entries.push(d);
    }

    /// Replace one decision in the frozen startup plan without changing its
    /// position or the one-entry-per-capability schema.
    ///
    /// This is used by frontend layers (notably CLI `--disable`) that resolve
    /// after the variant plan is built but before solving starts. Missing or
    /// duplicate capability ids are programmer errors: silently inserting or
    /// choosing one would make startup provenance ambiguous.
    pub(crate) fn replace_startup_decision(&mut self, replacement: CapabilityDecision) {
        let mut matches = self
            .entries
            .iter_mut()
            .filter(|entry| entry.capability == replacement.capability);
        let Some(entry) = matches.next() else {
            panic!(
                "startup capability ledger has no entry for {}",
                replacement.capability
            );
        };
        assert!(
            matches.next().is_none(),
            "startup capability ledger has duplicate entries for {}",
            replacement.capability
        );
        *entry = replacement;
    }

    /// All decisions, in the order they were taken.
    #[must_use]
    pub fn entries(&self) -> &[CapabilityDecision] {
        &self.entries
    }

    /// True iff any decision still came from an env shim — the assertion
    /// that backs the final "env is gone" migration test.
    #[must_use]
    pub fn any_env_shim(&self) -> bool {
        self.entries
            .iter()
            .any(|e| matches!(e.source, DecisionSource::EnvShim(_)))
    }

    /// Retained heap owned by the ledger, including spare vector/string capacity.
    #[cfg(test)]
    pub(crate) fn heap_bytes(&self) -> usize {
        self.entries.capacity() * size_of::<CapabilityDecision>()
            + self
                .entries
                .iter()
                .map(|entry| entry.because.capacity())
                .sum::<usize>()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn heap_bytes_counts_vector_and_reason_string_capacity() {
        let mut reason = String::with_capacity(73);
        reason.push_str("adaptive-instance-profile");
        let mut ledger = CapabilityLedger::default();
        ledger.record(CapabilityDecision {
            capability: "bve",
            state: CapabilityState::On,
            source: DecisionSource::Auto,
            because: reason,
        });

        let vector_bytes = ledger.entries.capacity() * size_of::<CapabilityDecision>();
        let string_bytes = ledger
            .entries
            .iter()
            .map(|entry| entry.because.capacity())
            .sum::<usize>();
        assert!(vector_bytes > 0, "fixture must allocate the entry vector");
        assert!(
            string_bytes >= 73,
            "fixture must retain reason-string slack"
        );
        assert_eq!(ledger.heap_bytes(), vector_bytes + string_bytes);
    }

    #[test]
    fn ledger_is_append_only_and_reports_env_shims() {
        let mut ledger = CapabilityLedger::default();
        assert!(!ledger.any_env_shim());
        ledger.record(CapabilityDecision {
            capability: "bve",
            state: CapabilityState::On,
            source: DecisionSource::Default,
            because: "variant=Default".to_string(),
        });
        ledger.record(CapabilityDecision {
            capability: "xor-max-clauses",
            state: CapabilityState::Value(1 << 20),
            source: DecisionSource::EnvShim("AY_XOR_ALLOW_LARGE"),
            because: "shim".to_string(),
        });
        assert_eq!(ledger.entries().len(), 2);
        assert!(ledger.any_env_shim());
        assert_eq!(ledger.entries()[0].state.label(), "on");
        assert_eq!(ledger.entries()[1].source.label(), "env:AY_XOR_ALLOW_LARGE");
    }

    #[test]
    fn replace_startup_decision_preserves_length_order_and_exact_value() {
        let mut ledger = CapabilityLedger::default();
        for capability in ["bve", "probe"] {
            ledger.record(CapabilityDecision {
                capability,
                state: CapabilityState::On,
                source: DecisionSource::Default,
                because: "compiled profile".to_string(),
            });
        }
        ledger.replace_startup_decision(CapabilityDecision {
            capability: "bve",
            state: CapabilityState::Off,
            source: DecisionSource::Cli,
            because: "--disable bve".to_string(),
        });

        assert_eq!(ledger.entries().len(), 2);
        assert_eq!(ledger.entries()[0].capability, "bve");
        assert_eq!(ledger.entries()[0].state, CapabilityState::Off);
        assert_eq!(ledger.entries()[0].source, DecisionSource::Cli);
        assert_eq!(ledger.entries()[0].because, "--disable bve");
        assert_eq!(ledger.entries()[1].capability, "probe");
    }
}
