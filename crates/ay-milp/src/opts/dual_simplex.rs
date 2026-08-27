// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Typed carriers for dual-simplex engine lanes.

use crate::tune::{Knob, Profile, Setting};

use super::{EngineConfigError, EngineEconomics};

/// Whether the tall-covering cold-dual rescue is available to a solve.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TallColdDualMode {
    /// Keep the rescue available (the compiled default).
    Enabled,
    /// Disable the rescue for this solve.
    Disabled,
}

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

    /// The configured eager-perturb mode, if the caller set one.
    ///
    /// Read directly rather than through [`crate::tune`] by the all-continuous
    /// float-first lane (`session::continuous_float_first_eager`), which runs
    /// OUTSIDE any `tune::activate_caller` frame — that lane never installs a
    /// caller profile, so `tune::count_opt` there reports the compiled default
    /// no matter what the operator passed, and `--eager-perturb-mode 0` would
    /// have been a silent no-op as a kill switch.
    pub(crate) fn eager_perturb_mode(&self) -> Option<usize> {
        self.eager_perturb
    }

    /// PRIMAL Harris two-pass ratio test: `0` off (the shipped single-pass
    /// test, byte-for-byte), `1` two-pass largest-pivot selection inside a
    /// feasibility-tolerance band, `2` that plus the bounded positive step
    /// floor.
    ///
    /// The band is the textbook anti-degeneracy device: pass one computes the
    /// minimum ratio against every basic bound RELAXED outward by that
    /// variable's own feasibility tolerance, and pass two picks, among the rows
    /// whose TRUE ratio is inside that relaxed minimum, the one with the
    /// largest pivot element. Mode `2` additionally refuses a zero-length step
    /// when the band admits a positive one — never further than the relaxed
    /// minimum, so no basic variable leaves its box by more than its own
    /// feasibility tolerance.
    pub fn with_harris_rt(mut self, mode: usize) -> Result<Self, EngineConfigError> {
        if mode > 2 {
            return Err(EngineConfigError::OutOfRange {
                knob: Knob::HarrisRt.label(),
                value: mode as f64,
                low: 0.0,
                high: 2.0,
            });
        }
        self.harris_rt = Some(mode);
        Ok(self)
    }

    /// The float advice lane. Default on; `--no-float` forces every solve down
    /// the exact rational rim.
    ///
    /// This is the A/B switch the float lane's speedup is measured with, and
    /// the kill switch if it ever misbehaves. It had no carrier at all before
    /// this: `Knob::NoFloat` was read by `session::float_lane_enabled` and
    /// written by nothing, so `--no-float` parsed as an unknown bare switch and
    /// changed nothing — a prior measurement that believed it had turned the
    /// float lane off had in fact measured the float lane.
    #[must_use]
    pub fn with_float_lane(mut self, enabled: bool) -> Self {
        self.float_lane = Some(enabled);
        self
    }

    /// The configured float-lane setting, if the caller set one.
    ///
    /// Read directly rather than only through [`crate::tune`] for the same
    /// reason as [`Self::eager_perturb_mode`] above: the all-continuous lane
    /// runs OUTSIDE any `tune::activate_caller` frame, so `tune::caller_flag`
    /// there reports the compiled default whatever the operator passed — and
    /// the all-continuous covering class is precisely what this switch exists
    /// to A/B. See `session::float_lane_enabled`.
    pub(crate) fn float_lane(&self) -> Option<bool> {
        self.float_lane
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

    /// Cold dual-simplex start on TALL covering LPs (`m >= TALL_LU_ROWS`,
    /// `n < m` — the metro / correlation-clustering set-cover shape). Default
    /// on; see `FloatLp::tall_cold_dual`.
    #[must_use]
    pub fn with_tall_cold_dual(mut self, mode: TallColdDualMode) -> Self {
        self.tall_cold_dual = Some(matches!(mode, TallColdDualMode::Enabled));
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
            (Knob::DualBypassMode, self.dual_bypass.map(Setting::Count)),
            (
                Knob::EagerPerturbMode,
                self.eager_perturb.map(Setting::Count),
            ),
            (Knob::HarrisRt, self.harris_rt.map(Setting::Count)),
            (Knob::NoFloat, self.float_lane.map(|v| Setting::Flag(!v))),
            (Knob::NoCutoff, self.cutoff_stop.map(|v| Setting::Flag(!v))),
            (Knob::NoNodeLu, self.node_lu.map(|v| Setting::Flag(!v))),
            (Knob::NoTallLu, self.tall_lu.map(|v| Setting::Flag(!v))),
            (
                Knob::NoTallColdDual,
                self.tall_cold_dual.map(|v| Setting::Flag(!v)),
            ),
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
            .with_tall_cold_dual(TallColdDualMode::Disabled)
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
            Knob::NoTallColdDual,
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

    /// `--no-float` HAS A CARRIER, ON BOTH ROUTES.
    ///
    /// `Knob::NoFloat` used to be read by `session::float_lane_enabled` and
    /// written by nothing at all, so `--no-float` parsed as an unrecognised
    /// bare switch and changed no behaviour — and a prior "no-float"
    /// measurement measured the float path. This pins BOTH halves of the
    /// repair, because either half alone leaves the flag dead on one lane:
    /// the `tune` profile entry (branch-and-bound, which installs a caller
    /// frame) and the direct typed getter (the all-continuous lane, which does
    /// not).
    #[test]
    fn the_no_float_switch_reaches_both_the_profile_and_the_typed_getter() {
        assert_eq!(
            EngineEconomics::default().float_lane(),
            None,
            "unset by default, so the compiled default still decides"
        );

        let off = EngineEconomics::default().with_float_lane(false);
        assert_eq!(off.float_lane(), Some(false));
        let active = crate::tune::activate_caller(off.profile());
        assert!(
            crate::tune::on(Knob::NoFloat),
            "--no-float must reach the tune layer for the branch-and-bound lane"
        );
        drop(active);

        let on = EngineEconomics::default().with_float_lane(true);
        assert_eq!(on.float_lane(), Some(true));
        let _active = crate::tune::activate_caller(on.profile());
        assert!(
            !crate::tune::on(Knob::NoFloat),
            "the switch must be honoured in both directions"
        );
    }
}
