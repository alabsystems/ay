// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Typed carrier and profile lowering for exact structural reductions.

use crate::tune::{Knob, Profile, Setting};

use super::super::EngineEconomics;

impl EngineEconomics {
    /// Opt in to exact implied-free equality aggregation.
    #[must_use]
    pub fn with_affine_agg(mut self, enabled: bool) -> Self {
        self.affine_agg = Some(enabled);
        self
    }
}

pub(super) fn extend_reduction_profile(opts: &EngineEconomics, mut profile: Profile) -> Profile {
    if let Some(enabled) = opts.struct_elim {
        profile = profile.with(Knob::StructElim, Setting::Flag(enabled));
    }
    if let Some(enabled) = opts.affine_agg {
        profile = profile.with(Knob::AffineAgg, Setting::Flag(enabled));
    }
    profile
}
