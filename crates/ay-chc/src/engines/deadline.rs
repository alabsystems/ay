// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Capture the outer clock before `ScopedSolveDeadline` replaces its binding.

use crate::PdrConfig;
use ay_core::time::Instant;

pub(super) fn for_config(config: &PdrConfig) -> Option<Instant> {
    for_config_at(config, Instant::now())
}

fn for_config_at(config: &PdrConfig, now: Instant) -> Option<Instant> {
    [
        config.solve_timeout.map(|timeout| now + timeout),
        crate::smt::current_thread_solve_deadline(),
        crate::smt::deadline::current_smt_deadline(),
    ]
    .into_iter()
    .flatten()
    .min()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn absent_config_timeout_preserves_absent_or_existing_clock() {
        let config = PdrConfig::default();
        assert_eq!(config.solve_timeout, None);
        assert_eq!(for_config(&config), None);
        let now = Instant::now();
        let deadline = now + Duration::from_secs(30);
        {
            let _solve = crate::smt::ScopedSolveDeadline::new(Some(deadline));
            assert_eq!(for_config_at(&config, now), Some(deadline));
        }
        assert_eq!(for_config_at(&config, now), None);
    }

    #[test]
    fn every_clock_can_be_the_minimum_and_scopes_restore_exactly() {
        let now = Instant::now();
        for (requested, solve, smt) in [(10, 20, 30), (30, 10, 20), (20, 30, 10)] {
            let config = PdrConfig {
                solve_timeout: Some(Duration::from_secs(requested)),
                ..PdrConfig::default()
            };
            let solve = now + Duration::from_secs(solve);
            let smt = now + Duration::from_secs(smt);
            {
                let _solve = crate::smt::ScopedSolveDeadline::new(Some(solve));
                let _smt = crate::smt::ScopedSmtDeadline::install_until(smt);
                let selected = for_config_at(&config, now);
                assert_eq!(selected, Some(now + Duration::from_secs(10)));
                {
                    let _child = crate::smt::ScopedSolveDeadline::new(selected);
                    assert_eq!(crate::smt::current_thread_solve_deadline(), selected);
                }
                assert_eq!(crate::smt::current_thread_solve_deadline(), Some(solve));
                assert_eq!(crate::smt::deadline::current_smt_deadline(), Some(smt));
            }
            assert_eq!(crate::smt::current_thread_solve_deadline(), None);
            assert_eq!(crate::smt::deadline::current_smt_deadline(), None);
        }
    }

    #[test]
    fn expired_ambient_clock_is_not_replaced_by_absent_or_later_request() {
        let now = Instant::now();
        let expired = now - Duration::from_secs(1);
        for timeout in [None, Some(Duration::from_secs(30))] {
            let config = PdrConfig {
                solve_timeout: timeout,
                ..PdrConfig::default()
            };
            {
                let _solve = crate::smt::ScopedSolveDeadline::new(Some(expired));
                assert_eq!(for_config_at(&config, now), Some(expired));
            }
            {
                let _smt = crate::smt::ScopedSmtDeadline::install_until(expired);
                assert_eq!(for_config_at(&config, now), Some(expired));
            }
        }
    }

    #[test]
    fn zero_requested_budget_remains_expired_with_later_ambient_clocks() {
        let now = Instant::now();
        let later = now + Duration::from_secs(30);
        let _solve = crate::smt::ScopedSolveDeadline::new(Some(later));
        let _smt = crate::smt::ScopedSmtDeadline::install_until(later);
        let config = PdrConfig {
            solve_timeout: Some(Duration::ZERO),
            ..PdrConfig::default()
        };
        assert_eq!(for_config_at(&config, now), Some(now));
    }
}
