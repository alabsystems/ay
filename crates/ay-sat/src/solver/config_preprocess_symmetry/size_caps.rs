// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clause caps for the orbitope and aux-free SR routes, and the
//! `--sat-symmetry-large-caps` switch that raises them: lever 2 of
//! competition/proof-posture-parity/PLAN-next-sat-levers.md at 9598c4206 (2026-09-14). The
//! switch is ON by default since 2026-09-17; `false` restores the old caps.

use super::ladder_collapse::LADDER_COLLAPSE_MAX_TOTAL_BINARIES;
use super::{ORBITOPE_MAX_CLAUSES, SYMMETRY_DETECTOR_MAX_CLAUSES};
use crate::symmetry::orbitope::OrbitopeLimits;

/// The clause cap of both routes under `--sat-symmetry-large-caps true`. The
/// orbitope cap also gates the ladder-collapse pre-pass.
///
/// In the 2026 band both routes skipped latin_square_10.15 (13,500 vars,
/// 4,611,150 clauses) on size alone. The default caps bound detection cost: on
/// that instance the switch costs about 130 s of preprocessing that cannot be
/// interrupted, most of it the orbitope column ordering (stage 0, 2026-09-15).
/// The IR caps do not move: an aux-free miss still reapplies them.
const SYMMETRY_LARGE_MAX_CLAUSES: usize = 8_000_000;

/// `--sat-symmetry-large-caps`, ON by default since 2026-09-17: on the A/B of
/// competition/proof-posture-parity at 9598c4206 it solved latin_square_10.15 (3 of 3, and at
/// 1500 s) and lost nothing, and the three instances it slowed still solve at
/// 1500 s. Read per call, not cached: the symmetry pass runs once per solve,
/// and tests scope the switch.
fn large_caps() -> bool {
    ay_core::sat_ab_switches()
        .symmetry_large_caps
        .unwrap_or(true)
}

/// The orbitope route's clause cap.
pub(super) fn orbitope_max_clauses() -> usize {
    if large_caps() {
        SYMMETRY_LARGE_MAX_CLAUSES
    } else {
        ORBITOPE_MAX_CLAUSES
    }
}

/// The aux-free SR route's clause cap. A route that may reach the IR finder
/// keeps `SYMMETRY_IR_MAX_CLAUSES` under either setting.
pub(super) fn symmetry_detector_max_clauses() -> usize {
    if large_caps() {
        SYMMETRY_LARGE_MAX_CLAUSES
    } else {
        SYMMETRY_DETECTOR_MAX_CLAUSES
    }
}

/// The orbitope detector's limits. Its own clause limit (1M by default) sits
/// below the route's 2M cap, so a formula between the two reaches the detector
/// and finds nothing. Under the switch it admits everything the route admits:
/// the route's cap plus what ladder collapse may add before detection.
pub(super) fn orbitope_limits() -> OrbitopeLimits {
    let mut limits = OrbitopeLimits::default();
    if large_caps() {
        limits.max_clauses = SYMMETRY_LARGE_MAX_CLAUSES + LADDER_COLLAPSE_MAX_TOTAL_BINARIES;
    }
    limits
}

#[cfg(test)]
mod tests {
    use super::*;

    /// latin_square_10.15, snw_16_9_CCSpre and snw_16_9_Encpre, header counts.
    const BAND_TARGET_CLAUSES: [usize; 3] = [4_611_150, 2_799_064, 1_641_152];

    /// `(orbitope route, aux-free SR route, orbitope detector)` clause caps
    /// with the switch scoped to `switch`.
    fn caps_under(switch: Option<bool>) -> (usize, usize, usize) {
        let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
            symmetry_large_caps: switch,
            ..Default::default()
        });
        let detector = orbitope_limits().max_clauses;
        (
            orbitope_max_clauses(),
            symmetry_detector_max_clauses(),
            detector,
        )
    }

    #[test]
    fn the_raised_caps_are_the_default_and_false_restores_the_old_ones() {
        assert_eq!(caps_under(None), (8_000_000, 8_000_000, 9_000_000));
        assert_eq!(caps_under(Some(true)), (8_000_000, 8_000_000, 9_000_000));
        assert_eq!(caps_under(Some(false)), (2_000_000, 1_000_000, 1_000_000));
    }

    #[test]
    fn the_switch_moves_only_the_detector_clause_limit() {
        let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
            symmetry_large_caps: Some(true),
            ..Default::default()
        });
        // Exhaustive, so a field added later has to be considered here.
        let OrbitopeLimits {
            max_clauses: _,
            max_verified_rows,
            min_rows,
            min_cols,
        } = orbitope_limits();
        let shipped = OrbitopeLimits::default();
        assert_eq!(max_verified_rows, shipped.max_verified_rows);
        assert_eq!(min_rows, shipped.min_rows);
        assert_eq!(min_cols, shipped.min_cols);
    }

    #[test]
    fn the_band_targets_fit_the_raised_clause_caps_only_under_the_switch() {
        let (orbitope_off, route_off, detector_off) = caps_under(Some(false));
        let (orbitope_on, route_on, detector_on) = caps_under(Some(true));
        for clauses in BAND_TARGET_CLAUSES {
            assert!(clauses > route_off && clauses > detector_off, "{clauses}");
            assert!(
                clauses <= orbitope_on.min(route_on).min(detector_on),
                "{clauses}"
            );
        }
        // snw_16_9_Encpre fits the orbitope route's cap already, but not the
        // detector's own limit, so the route ran and found nothing.
        assert!(BAND_TARGET_CLAUSES[..2].iter().all(|&c| c > orbitope_off));
        assert!(BAND_TARGET_CLAUSES[2] <= orbitope_off);
    }

    /// An aux-free miss on `solver` must skip as `TooLarge` at the IR fallback,
    /// leaving the formula alone, whatever the switch says.
    fn assert_ir_fallback_skips(num_vars: usize, clauses: &[[(usize, bool); 2]]) {
        use crate::solver::Solver;
        use crate::{Literal, Variable};
        for switch in [Some(false), Some(true)] {
            let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
                no_orbitope: true,
                composite_symmetry: true,
                symmetry_large_caps: switch,
                ..Default::default()
            });
            let mut solver = Solver::new(num_vars);
            solver.set_symmetry_oneshot(true);
            for clause in clauses {
                let lits = clause.iter().map(|&(var, positive)| {
                    let var = Variable(var as u32);
                    if positive {
                        Literal::positive(var)
                    } else {
                        Literal::negative(var)
                    }
                });
                assert!(solver.add_clause(lits.collect()));
            }
            let before = solver.arena.active_clause_count();
            assert_eq!(solver.preprocess_symmetry(), (false, false), "{switch:?}");
            assert_eq!(solver.arena.active_clause_count(), before, "{switch:?}");
            assert_eq!(
                solver.cold.symmetry_stats.last_skipped_reason,
                Some(crate::symmetry::SymmetrySkipReason::TooLarge),
                "{switch:?}"
            );
        }
    }

    #[test]
    fn the_ir_variable_cap_holds_under_the_switch() {
        // One variable above SYMMETRY_MAX_VARS (4,096).
        assert_ir_fallback_skips(4_097, &[[(0, true), (1, true)], [(0, false), (1, false)]]);
    }

    #[test]
    fn the_ir_clause_cap_holds_under_the_switch() {
        // One clause above SYMMETRY_IR_MAX_CLAUSES (20,000) at the variable cap:
        // distinct positive binaries, which no aux-free family recognizes.
        let clauses: Vec<[(usize, bool); 2]> = (1..=5)
            .flat_map(|offset| (0..4_096 - offset).map(move |i| [(i, true), (i + offset, true)]))
            .take(20_001)
            .collect();
        assert_ir_fallback_skips(4_096, &clauses);
    }
}
