// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Typed carriers for dual-simplex engine lanes.

use crate::tune::{Knob, Profile, Setting};

use super::{EngineConfigError, EngineEconomics};

impl EngineEconomics {
    /// Dual-walk anatomy tracing (diagnostic). Default off.
    #[must_use]
    pub fn with_dual_anatomy(mut self, enabled: bool) -> Self {
        self.dual_anatomy = Some(enabled);
        self
    }

    /// Pivot count after which the warm walk re-verifies the factorization.
    #[must_use]
    pub fn with_verify_after(mut self, pivots: usize) -> Self {
        self.verify_after = Some(pivots);
        self
    }

    /// Fused one-pass ratio test. Default on; off restores the two-pass baseline.
    #[must_use]
    pub fn with_fused_rt(mut self, enabled: bool) -> Self {
        self.fused_rt = Some(enabled);
        self
    }

    /// Incremental ratio-test eligibility bitmask. Default on.
    #[must_use]
    pub fn with_rt_kind(mut self, enabled: bool) -> Self {
        self.rt_kind = Some(enabled);
        self
    }

    /// Per-iteration ratio-test profiler (diagnostic). Default off.
    #[must_use]
    pub fn with_iter_profile(mut self, enabled: bool) -> Self {
        self.iter_profile = Some(enabled);
        self
    }

    /// Bare-u64 ratio-test compare key. Default on.
    #[must_use]
    pub fn with_rt_bits_key(mut self, enabled: bool) -> Self {
        self.rt_bits_key = Some(enabled);
        self
    }

    /// Wide set-partition bloom-cap relaxation. Default on.
    #[must_use]
    pub fn with_wide_bloom(mut self, enabled: bool) -> Self {
        self.wide_bloom = Some(enabled);
        self
    }

    /// Cross-solve eta reuse. Default on.
    #[must_use]
    pub fn with_eta_reuse(mut self, enabled: bool) -> Self {
        self.eta_reuse = Some(enabled);
        self
    }

    /// Devex pricing. Default on.
    #[must_use]
    pub fn with_devex(mut self, enabled: bool) -> Self {
        self.devex = Some(enabled);
        self
    }

    /// Cold dual-simplex start on wide-and-tall LPs. Default on.
    #[must_use]
    pub fn with_cold_dual(mut self, enabled: bool) -> Self {
        self.cold_dual = Some(enabled);
        self
    }

    /// Triangular equality crash on big cold LPs. Default on.
    #[must_use]
    pub fn with_tri_crash(mut self, enabled: bool) -> Self {
        self.tri_crash = Some(enabled);
        self
    }

    /// Chained-devex mode: `0` | `1` | `2` (the measured default).
    ///
    /// # Errors
    ///
    /// [`EngineConfigError`] unless `mode <= 2`.
    /// Chain-shape structural class gate. Default on.
    #[must_use]
    pub fn with_chain_shape(mut self, enabled: bool) -> Self {
        self.chain_shape = Some(enabled);
        self
    }

    /// Chain-verdict-driven refactorize peel preorder. Default on.
    #[must_use]
    pub fn with_chain_preorder(mut self, enabled: bool) -> Self {
        self.chain_preorder = Some(enabled);
        self
    }

    /// BUMP-LU base factor inside `refactorize`. Default on.
    #[must_use]
    pub fn with_bump_lu(mut self, enabled: bool) -> Self {
        self.bump_lu = Some(enabled);
        self
    }

    /// Dual-bypass mode: `0` never, `1` adaptive (the default), `2` force.
    pub fn with_dual_bypass(mut self, mode: usize) -> Result<Self, EngineConfigError> {
        if mode > 2 {
            return Err(EngineConfigError::OutOfRange {
                knob: Knob::DualBypassMode.label(),
                value: mode as f64,
                low: 0.0,
                high: 2.0,
            });
        }
        self.dual_bypass = Some(mode);
        Ok(self)
    }

    /// Eager-perturb mode: `0` off, `1` armed-on-stall (the default), `2` all
    /// cold walks.
    pub fn with_eager_perturb(mut self, mode: usize) -> Result<Self, EngineConfigError> {
        if mode > 2 {
            return Err(EngineConfigError::OutOfRange {
                knob: Knob::EagerPerturbMode.label(),
                value: mode as f64,
                low: 0.0,
                high: 2.0,
            });
        }
        self.eager_perturb = Some(mode);
        Ok(self)
    }

    pub fn with_chain_devex(mut self, mode: usize) -> Result<Self, EngineConfigError> {
        if mode > 2 {
            return Err(EngineConfigError::OutOfRange {
                knob: Knob::ChainDevex.label(),
                value: mode as f64,
                low: 0.0,
                high: 2.0,
            });
        }
        self.chain_devex = Some(mode);
        Ok(self)
    }

    /// Objective-cutoff early stop in the warm dual walk. Default on.
    #[must_use]
    pub fn with_cutoff_stop(mut self, enabled: bool) -> Self {
        self.cutoff_stop = Some(enabled);
        self
    }

    /// Warm-solve LU engine on wide-tall `plain_cold` instances. Default on.
    #[must_use]
    pub fn with_node_lu(mut self, enabled: bool) -> Self {
        self.node_lu = Some(enabled);
        self
    }

    /// Tall LU gate. Default on.
    #[must_use]
    pub fn with_tall_lu(mut self, enabled: bool) -> Self {
        self.tall_lu = Some(enabled);
        self
    }

    /// Dual churn band. Default on.
    #[must_use]
    pub fn with_dual_churn_band(mut self, enabled: bool) -> Self {
        self.dual_churn_band = Some(enabled);
        self
    }

    /// Override the dual bloom cap.
    #[must_use]
    pub fn with_dual_bloom_cap(mut self, cap: usize) -> Self {
        self.dual_bloom_cap = Some(cap);
        self
    }

    pub(super) fn extend_dual_simplex_profile(&self, mut profile: Profile) -> Profile {
        for (knob, value) in [
            (Knob::DualAnatomy, self.dual_anatomy.map(Setting::Flag)),
            (Knob::VerifyAfter, self.verify_after.map(Setting::Count)),
            (Knob::NoFusedRt, self.fused_rt.map(|v| Setting::Flag(!v))),
            (Knob::NoRtKind, self.rt_kind.map(|v| Setting::Flag(!v))),
            (Knob::IterProfile, self.iter_profile.map(Setting::Flag)),
            (
                Knob::NoRtBitsKey,
                self.rt_bits_key.map(|v| Setting::Flag(!v)),
            ),
            (
                Knob::NoWideBloom,
                self.wide_bloom.map(|v| Setting::Flag(!v)),
            ),
            (Knob::NoEtaReuse, self.eta_reuse.map(|v| Setting::Flag(!v))),
            (Knob::NoDevex, self.devex.map(|v| Setting::Flag(!v))),
            (Knob::NoColdDual, self.cold_dual.map(|v| Setting::Flag(!v))),
            (Knob::NoTriCrash, self.tri_crash.map(|v| Setting::Flag(!v))),
            (Knob::ChainDevex, self.chain_devex.map(Setting::Count)),
            (
                Knob::NoChainShape,
                self.chain_shape.map(|v| Setting::Flag(!v)),
            ),
            (
                Knob::NoChainPreorder,
                self.chain_preorder.map(|v| Setting::Flag(!v)),
            ),
            (Knob::NoBumpLu, self.bump_lu.map(|v| Setting::Flag(!v))),
            (Knob::FullPricing, self.full_pricing.map(Setting::Flag)),
            (Knob::DualBypassMode, self.dual_bypass.map(Setting::Count)),
            (
                Knob::EagerPerturbMode,
                self.eager_perturb.map(Setting::Count),
            ),
            (Knob::NoCutoff, self.cutoff_stop.map(|v| Setting::Flag(!v))),
            (Knob::NoNodeLu, self.node_lu.map(|v| Setting::Flag(!v))),
            (Knob::NoTallLu, self.tall_lu.map(|v| Setting::Flag(!v))),
            (
                Knob::NoDualChurnBand,
                self.dual_churn_band.map(|v| Setting::Flag(!v)),
            ),
            (Knob::DualBloomCap, self.dual_bloom_cap.map(Setting::Count)),
        ] {
            if let Some(value) = value {
                profile = profile.with(knob, value);
            }
        }
        profile
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn typed_engine_switches_reach_the_profile_with_one_inversion() {
        let b11 = EngineEconomics::default()
            .with_vub(false)
            .with_mir_genint(false)
            .with_sep_screen(false)
            .with_ft_fast(false)
            .with_ftran_fast(false)
            .with_ftran_nz_fast(false)
            .with_countsort(false)
            .with_coef_tighten(false)
            .with_orbitope(false)
            .with_ft_growth_tol(1e-12)
            .expect("finite positive tolerance");
        let active = crate::tune::activate_caller(b11.profile());
        for knob in [
            Knob::NoVub,
            Knob::NoMirGenint,
            Knob::NoSepScreen,
            Knob::NoFtFast,
            Knob::NoFtranFast,
            Knob::NoFtranNzFast,
            Knob::NoCountsort,
            Knob::NoCoefTighten,
            Knob::NoOrbitope,
        ] {
            assert!(crate::tune::on(knob), "{knob:?}");
        }
        assert_eq!(crate::tune::real_opt(Knob::FtGrowthTol), Some(1e-12));
        drop(active);

        let b12 = EngineEconomics::default()
            .with_dual_anatomy(true)
            .with_verify_after(7)
            .with_fused_rt(false)
            .with_rt_kind(false)
            .with_iter_profile(true)
            .with_rt_bits_key(false)
            .with_wide_bloom(false)
            .with_eta_reuse(false)
            .with_devex(false)
            .with_cold_dual(false)
            .with_tri_crash(false)
            .with_chain_devex(1)
            .expect("mode 1 is in domain")
            .with_cutoff_stop(false)
            .with_node_lu(false)
            .with_tall_lu(false)
            .with_dual_churn_band(false)
            .with_dual_bloom_cap(9);
        let _active = crate::tune::activate_caller(b12.profile());
        for knob in [
            Knob::DualAnatomy,
            Knob::IterProfile,
            Knob::NoFusedRt,
            Knob::NoRtKind,
            Knob::NoRtBitsKey,
            Knob::NoWideBloom,
            Knob::NoEtaReuse,
            Knob::NoDevex,
            Knob::NoColdDual,
            Knob::NoTriCrash,
            Knob::NoCutoff,
            Knob::NoNodeLu,
            Knob::NoTallLu,
            Knob::NoDualChurnBand,
        ] {
            assert!(crate::tune::on(knob), "{knob:?}");
        }
        assert_eq!(crate::tune::count_opt(Knob::VerifyAfter), Some(7));
        assert_eq!(crate::tune::count_opt(Knob::ChainDevex), Some(1));
        assert_eq!(crate::tune::count_opt(Knob::DualBloomCap), Some(9));
        assert!(EngineEconomics::default().with_chain_devex(3).is_err());
        for knob in [Knob::NoVub, Knob::FtGrowthTol] {
            assert_eq!(knob.env(), None, "{knob:?} must have no env spelling");
        }
    }
}
