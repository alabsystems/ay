// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fail-closed native theory-bound propagation dispatch contract.

use ay_core::{NativeTheoryPropagationBackend, NativeTheoryPropagationProfile, TheorySolver};

use super::TheoryExtension;
use crate::DpllEagerStats;

/// Internal control plane for native theory-bound propagation.
///
/// The default is intentionally disabled. Enabling this enum in tests only
/// exercises the eligibility contract; production construction does not opt in.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(test), allow(dead_code))]
pub(super) enum NativeTheoryPropagationControl {
    Disabled,
    EnabledForEligibleProfiles,
}

/// DPLL-side native propagation eligibility decision.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum NativeTheoryPropagationDispatch {
    DisabledByControl,
    UnsupportedTheory,
    NoTheoryAtoms,
    NoCompiledVars,
    NoNativeVars,
    PartialNativeCoverage,
    NonSmallAtomFallback,
    Eligible,
}

impl NativeTheoryPropagationDispatch {
    pub(super) fn evaluate(
        profile: NativeTheoryPropagationProfile,
        theory_atom_count: usize,
        control: NativeTheoryPropagationControl,
    ) -> Self {
        if matches!(control, NativeTheoryPropagationControl::Disabled) {
            return Self::DisabledByControl;
        }
        if theory_atom_count == 0 {
            return Self::NoTheoryAtoms;
        }

        let NativeTheoryPropagationProfile::BoundPropagation {
            backend,
            compiled_vars,
            native_vars,
            total_atoms,
            small_atoms,
        } = profile
        else {
            return Self::UnsupportedTheory;
        };

        if !matches!(
            backend,
            NativeTheoryPropagationBackend::ExternalCodegenBackend
        ) {
            return Self::UnsupportedTheory;
        }
        if compiled_vars == 0 || total_atoms == 0 {
            return Self::NoCompiledVars;
        }
        if native_vars == 0 {
            return Self::NoNativeVars;
        }
        if small_atoms != total_atoms {
            return Self::NonSmallAtomFallback;
        }
        if native_vars != compiled_vars {
            return Self::PartialNativeCoverage;
        }

        Self::Eligible
    }

    pub(super) fn record(self, stats: &mut DpllEagerStats) {
        match self {
            Self::DisabledByControl => stats.native_theory_prop_disabled += 1,
            Self::Eligible => stats.native_theory_prop_eligible += 1,
            Self::UnsupportedTheory
            | Self::NoTheoryAtoms
            | Self::NoCompiledVars
            | Self::NoNativeVars
            | Self::PartialNativeCoverage
            | Self::NonSmallAtomFallback => stats.native_theory_prop_unsupported += 1,
        }
    }
}

impl<T: TheorySolver> TheoryExtension<'_, T> {
    #[cfg(test)]
    pub(super) fn build_native_theory_propagation_dispatch(
        &self,
        control: NativeTheoryPropagationControl,
    ) -> NativeTheoryPropagationDispatch {
        NativeTheoryPropagationDispatch::evaluate(
            self.theory.native_theory_propagation_profile(),
            self.theory_atoms.len(),
            control,
        )
    }

    #[cfg(test)]
    pub(super) fn recompute_native_theory_propagation_dispatch_for_test(
        &mut self,
        control: NativeTheoryPropagationControl,
    ) {
        self.native_theory_propagation_dispatch =
            self.build_native_theory_propagation_dispatch(control);
    }
}
