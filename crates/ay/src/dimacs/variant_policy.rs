// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Typed proof and startup posture for DIMACS variant selection.

/// Proof posture relevant to SAT variant selection.
#[derive(Clone, Copy)]
enum DimacsProofPosture {
    NoProof,
    Drat,
    InternalLrat,
    LratOutput,
}

impl DimacsProofPosture {
    fn from_proof(proof: &ProofConfig) -> Self {
        match proof.format {
            // VeriPB is a clause-stream surface with no LRAT hint channel, so
            // it takes the DRAT posture: same transform permissions, same
            // variant routing.
            ProofFormat::Drat | ProofFormat::Veripb => Self::Drat,
            ProofFormat::Lrat => Self::LratOutput,
            ProofFormat::Alethe | ProofFormat::Lean4 => Self::InternalLrat,
        }
    }

    const fn variant_proof_mode(self) -> VariantProofMode {
        match self {
            Self::NoProof => VariantProofMode::Disabled,
            Self::Drat => VariantProofMode::Drat,
            Self::InternalLrat | Self::LratOutput => VariantProofMode::Lrat,
        }
    }

    const fn lrat_output(self) -> bool {
        matches!(self, Self::LratOutput)
    }
}

#[derive(Clone, Copy)]
enum OfficialMainRoute {
    Regular,
    Other,
}

#[derive(Clone, Copy)]
enum StartupPhaseInit {
    Default,
    Explicit,
}

/// Typed route identity used by the lower-level policy tests and selector.
#[derive(Clone, Copy)]
struct DimacsRouteContext {
    official_main: OfficialMainRoute,
    startup_phase_init: StartupPhaseInit,
}

impl DimacsRouteContext {
    const fn new(official_main: OfficialMainRoute, startup_phase_init: StartupPhaseInit) -> Self {
        Self {
            official_main,
            startup_phase_init,
        }
    }
}
