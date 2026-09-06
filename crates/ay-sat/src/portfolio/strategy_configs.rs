// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Focused portfolio strategy configurations.

use super::SolverConfig;

/// Configuration with all optional inprocessing disabled.
pub(super) fn conservative_config() -> SolverConfig {
    SolverConfig {
        features: crate::InprocessingFeatureProfile {
            preprocess: true,
            walk: true,
            warmup: true,
            shrink: true,
            hbr: false,
            vivify: false,
            subsume: false,
            probe: false,
            bve: false,
            bce: false,
            condition: false,
            decompose: false,
            factor: false,
            sbva: false,
            transred: false,
            htr: false,
            gate: false,
            congruence: false,
            sweep: false,
            backbone: false,
            symmetry: false,
            reorder: false,
            cce: false,
        },
        glucose_restarts: false,
        chrono_enabled: false,
        seed: 3,
        ..Default::default()
    }
}

/// Configuration emphasizing subsumption, probing, and HBR.
pub(super) fn probe_focused_config() -> SolverConfig {
    SolverConfig {
        features: crate::InprocessingFeatureProfile {
            preprocess: true,
            walk: true,
            warmup: true,
            shrink: true,
            hbr: true,
            vivify: false,
            subsume: true,
            probe: true,
            bve: false,
            bce: false,
            condition: false,
            decompose: false,
            factor: false,
            sbva: false,
            transred: false,
            htr: false,
            gate: false,
            congruence: false,
            sweep: false,
            backbone: true,
            symmetry: false,
            reorder: true,
            cce: false,
        },
        initial_phase: Some(false),
        seed: 4,
        ..Default::default()
    }
}

/// Configuration emphasizing elimination, gates, and conditioning.
pub(super) fn bve_focused_config() -> SolverConfig {
    SolverConfig {
        features: crate::InprocessingFeatureProfile {
            preprocess: true,
            walk: true,
            warmup: true,
            shrink: true,
            hbr: false,
            vivify: false,
            subsume: true,
            probe: false,
            bve: true,
            bce: true,
            condition: true,
            decompose: false,
            factor: true,
            sbva: true,
            transred: false,
            htr: false,
            gate: true,
            congruence: false,
            sweep: false,
            backbone: false,
            symmetry: false,
            reorder: true,
            // CCE is DISABLED here deliberately: BVE + CCE together drop
            // constraints. On minandmaxor128 (officially UNSAT, CaDiCaL proves
            // it in 231 s) this config reaches a satisfying assignment of the
            // internal formula in 8.4 s; the finalize gate catches it and
            // demotes to UNKNOWN, so no wrong answer escapes, but that gate is
            // the only barrier. Isolation: `bve` alone clean, `bve,bce` clean,
            // `bve,cce` produces the phantom model — reproduced byte-identically
            // on sudoku-N30-11, so it is deterministic, not a race. Re-enable
            // only once covered-clause reconstruction (or CCE's occurrence
            // handling after BVE elimination) is fixed AND a regression fixture
            // exists. CCE also measured as converting 0 of 6 instances, so this
            // costs nothing.
            cce: false,
        },
        initial_phase: Some(true),
        seed: 5,
        ..Default::default()
    }
}
