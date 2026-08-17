// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Deterministic admission for self-contained quantified SAT certificates.

use super::{Executor, UnknownReason};

impl Executor {
    /// Whether a fail-closed quantifier `Unknown` should still consult the
    /// self-contained SAT certificates (const-interp / finite-table /
    /// default-row / valid-closed-sentence).
    ///
    /// #cert-consult-determinism: the reason label a truncated quantifier loop
    /// records is LOAD-DEPENDENT. A nested tight sub-deadline installed on the
    /// shared `solve_deadline` cell (e.g. the CEGQI disambiguation 300 ms
    /// per-universal refutation legs in `disambiguate_cegqi_unsat`) transiently
    /// expiring records `UnknownReason::Timeout` via the deadline origin — even
    /// though the ENCLOSING solve is healthy: its own deadline is NOT expired
    /// and no interrupt is pending. On identical inputs a contended machine
    /// therefore stamps `Timeout` where an idle machine stamps a
    /// `Quantifier*Incomplete` label, and the old gate — which admitted only the
    /// incompleteness labels — then SKIPPED the deterministic certificate and
    /// flipped a satisfiable problem's verdict from `sat` to `unknown` under
    /// load (the finite_table_cert nested-quantifier flake).
    ///
    /// Fix: decide the consult on a DETERMINISTIC condition rather than the
    /// wall-clock-derived label. Admit the quantifier-incompleteness labels
    /// unconditionally, and admit a `Timeout` label ONLY while the enclosing
    /// solve is genuinely live (`external_stop_reason().is_none()` — neither the
    /// real deadline expired nor an interrupt pending). A genuinely
    /// deadline-expired / interrupted solve still declines here, and each
    /// certificate independently re-checks `external_stop_reason()` at entry, so
    /// a truly stopped solve never performs certificate work.
    ///
    /// SOUNDNESS: every admitted certificate is GRANT-ONLY and SELF-CONTAINED —
    /// it re-verifies each assertion under an explicitly constructed model (or a
    /// checked-UNSAT refutation) and can only upgrade a fail-closed `Unknown` to
    /// `Sat`. Widening the gate can never touch an `Unsat`, mint an unchecked
    /// `Sat`, or alter a genuine external stop; it only removes the load
    /// dependence.
    pub(super) fn quantifier_sat_cert_consult_admitted(&self) -> bool {
        match self.last_unknown_reason {
            Some(
                UnknownReason::QuantifierCegqiIncomplete
                | UnknownReason::QuantifierUnhandled
                | UnknownReason::QuantifierRoundLimit
                | UnknownReason::QuantifierEmatchingExistsIncomplete,
            ) => true,
            // Load artifact only: a real timeout leaves the deadline expired /
            // interrupt set, which `external_stop_reason` reports and which the
            // certificates' own entry guards also decline.
            Some(UnknownReason::Timeout) => self.external_stop_reason().is_none(),
            // #cert-consult-determinism, second half. The MBQI-UNSAFE PARTIAL
            // QUANTIFIER guard is a QUANTIFIER incompleteness — a binder over
            // Array/FP/Seq/RegLan that E-matching alone cannot decide — but it
            // records the generic `Incomplete` label whenever a UF-completion
            // candidate was attempted first, and `QuantifierUnhandled` when it
            // was not. Same situation, two labels, and only one of them reached
            // the certificates. Read the structural marker instead:
            // `unsafe_partial_quantifier_unknown` is set by exactly one call
            // site (`record_unsafe_partial_unknown`) and cleared at the top of
            // every classification, so it cannot be inherited from a prior
            // solve. `forall s. 0 <= seq_len(s)` — satisfiable by
            // `seq_len := λs. 0`, and the const-interp certificate's own
            // documented example — was answered `unknown` for exactly this
            // reason.
            //
            // SOUNDNESS: unchanged. Every certificate this admits is grant-only
            // and self-contained: it constructs an interpretation, re-verifies
            // EVERY assertion of the snapshot under it, and can only upgrade a
            // fail-closed `Unknown` to `Sat`. It never touches an `Unsat`, never
            // publishes an unchecked `Sat`, and re-checks `external_stop_reason`
            // at its own entry.
            // The `external_stop_reason` conjunct mirrors the `Timeout` arm: a
            // genuinely stopped solve declines here rather than spending its
            // remaining moments on certificate work.
            _ => self.unsafe_partial_quantifier_unknown && self.external_stop_reason().is_none(),
        }
    }
}
