// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The publication wire-gap screen for native SOS steps.
//!
//! A native `NraSos` certificate is strict-checked by AY, but acceptance by
//! AY's own checker never authorizes an Alethe publication. The printer lowers
//! a strict-checked certificate into pinned-checker steps; this screen asks the
//! printer itself, over the same override channel the exporter uses, so the
//! two cannot disagree. Whatever the lowering declines keeps its wire gap and
//! prints an honest `hole`.

use ay_core::kani_compat::DetHashMap;
use ay_core::{ProofStep, TermId};

use super::super::super::Executor;

impl Executor {
    /// `true` unless `step` is a native SOS step the printer lowers to checked
    /// Alethe under `term_overrides`.
    pub(super) fn sos_wire_gap(
        &self,
        step: &ProofStep,
        term_overrides: Option<&DetHashMap<TermId, String>>,
    ) -> bool {
        let ProofStep::NraSos {
            clause,
            certificate,
        } = step
        else {
            return true;
        };
        !ay_proof::nra_sos_lowering_supported(&self.ctx.terms, clause, certificate, term_overrides)
    }
}
