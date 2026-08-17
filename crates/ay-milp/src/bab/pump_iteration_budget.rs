// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// THE SAME CEILING, IN THE ENGINE'S OWN UNIT: cumulative simplex ITERATIONS spent by the root
/// pump's restart loop, as a multiple of the ROOT LP's iteration count.
///
/// WHY A SECOND CAP AT ALL. `pump_window` is denominated in WALL CLOCK, so the number of
/// iterations the pump actually spends is non-deterministic BY CONSTRUCTION — a busy box buys
/// fewer restarts than an idle one, and the restarts choose the seed, and the seed chooses the
/// tree. That is the same defect `stats::solve_work` was introduced to fix for strong branching.
///
/// WHY IT BINDS WHERE THE WALL CAP DOES NOT. `pump_window`'s work term is
/// `PUMP_WORK_MULT x root_lp`, but it is `max`-ed against `PUMP_FLOOR_SECS` (0.25s) — and on a
/// small model the FLOOR, not the multiple, is what is granted. Measured on the corpus
/// (`--iter-ledger`, 1 thread, limit 60), pump iterations as a multiple of the root LP's:
///
/// ```text
///   binding on the work term      floored, i.e. UNBOUNDED in model units
///   qiu       3.92                mod010    7.97   p0201    9.82   blend2  11.2
///   air03     3.91                mas76    18.1    misc07  52.9    dcmulti 53.9
///   qnet1     4.62                flugpl   56.2    gt2     72.9
///   khb05250  4.47                gen       6.71
/// ```
///
/// So `6.0` is set exactly where the corpus splits: above every instance whose pump the WALL cap
/// already prices in model units (qiu, the one instance whose root heuristics measurably pay, is
/// 3.92 and stays untouched), below every instance where the 0.25s floor was handing out ten to
/// seventy root-LP-equivalents of lottery.
///
/// THE CAP CAN NEVER STARVE THE PUMP'S FIRST ATTEMPT, and that is the property that keeps the
/// DIVE alive rather than replacing it: the gate is evaluated at the TOP of each restart, so
/// attempt 0 always runs in full whatever the cap says. When the cap then stops the loop with
/// nothing landed, `seed` is `None` and the dive runs on the wall the pump did not spend —
/// which is the whole point (`--heur-share 0` kills the pump AND the dive together).
const PUMP_ITER_MULT: f64 = 6.0;

/// The pump's iteration ceiling for this model, or `None` when the cap is off.
/// `with_pump_iter_cap(false)` is the kill switch (the pre-cap arm, byte-for-byte);
/// `with_pump_iter_mult` pins the multiple for a sweep.
pub(super) fn pump_iter_cap(root_lp_iters: u64) -> Option<u64> {
    if crate::tune::caller_flag(crate::tune::Knob::NoPumpIterCap) == Some(true) {
        return None;
    }
    let mult = crate::tune::real_opt(crate::tune::Knob::PumpIterMult)
        .filter(|v| v.is_finite() && *v >= 0.0)
        .unwrap_or(PUMP_ITER_MULT);
    #[expect(
        clippy::cast_precision_loss,
        clippy::cast_possible_truncation,
        clippy::cast_sign_loss,
        reason = "finite nonnegative products intentionally use Rust's saturating float-to-int cast"
    )]
    Some((root_lp_iters as f64 * mult) as u64)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn mult_profile(v: f64) -> crate::tune::Profile {
        crate::tune::Profile::EMPTY.with(
            crate::tune::Knob::PumpIterMult,
            crate::tune::Setting::Real(v),
        )
    }

    /// The pump's WORK-denominated ceiling: denominated in the root LP's own iteration
    /// count, switchable inside one process (a `OnceLock` here would make an A/B sweep
    /// measure the same arm twice), and hardened against out-of-domain knob values.
    #[test]
    fn pump_iter_cap_is_root_lp_denominated_and_switchable() {
        // (1) Denominated in the ROOT LP, not in a constant: a model whose root LP costs
        //     ten times as many iterations earns ten times the pump allowance.
        assert_eq!(pump_iter_cap(633), Some(3798));
        assert_eq!(pump_iter_cap(6330), Some(37980));
        // A degenerate zero-iteration root LP yields a zero budget — which cannot starve
        // the pump, because the gate is read at the TOP of each restart and attempt 0
        // therefore always runs. That invariant lives at the call site, not here.
        assert_eq!(pump_iter_cap(0), Some(0));

        // (2) The kill switch removes the ceiling outright (the pre-cap arm).
        {
            let _off = crate::tune::activate_caller(crate::tune::Profile::EMPTY.with(
                crate::tune::Knob::NoPumpIterCap,
                crate::tune::Setting::Flag(true),
            ));
            assert_eq!(pump_iter_cap(633), None);
        }
        // ... and switching it back on inside the SAME process must take effect.
        assert_eq!(pump_iter_cap(633), Some(3798));

        // (3) The multiple is pinnable for a sweep, in both directions.
        {
            let _m = crate::tune::activate_caller(mult_profile(3.0));
            assert_eq!(pump_iter_cap(633), Some(1899));
        }
        {
            let _m = crate::tune::activate_caller(mult_profile(0.0));
            assert_eq!(pump_iter_cap(633), Some(0));
        }
        assert_eq!(pump_iter_cap(633), Some(3798));

        // (4) Out-of-domain values fall back to the default policy rather than
        //     producing a nonsense (or saturating-negative) budget.
        for invalid in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY, -1.0] {
            let _m = crate::tune::activate_caller(mult_profile(invalid));
            assert_eq!(
                pump_iter_cap(633),
                Some(3798),
                "{invalid:?} must fall back to the default multiple"
            );
        }
    }
}
