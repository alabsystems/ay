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
            cce: true,
        },
        initial_phase: Some(true),
        seed: 5,
        ..Default::default()
    }
}
