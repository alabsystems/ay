// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fixtures for original preclosed owner boundaries.

use super::*;

#[derive(Clone, Copy)]
pub(super) enum ClosedOwner {
    Caller,
    OuterLane,
    SolveDeadline,
    SmtDeadline,
    Memory,
}

pub(super) const CLOSED_OWNERS: [ClosedOwner; 5] = [
    ClosedOwner::Caller,
    ClosedOwner::OuterLane,
    ClosedOwner::SolveDeadline,
    ClosedOwner::SmtDeadline,
    ClosedOwner::Memory,
];

pub(super) fn with_closed_owner(
    portfolio: &AdaptivePortfolio,
    owner: ClosedOwner,
    run: impl FnOnce(),
) {
    match owner {
        ClosedOwner::Caller => {
            portfolio.cancellation_token.cancel();
            run();
        }
        ClosedOwner::OuterLane => {
            let token = CancellationToken::new();
            token.cancel();
            let _lane = crate::smt::ScopedLaneCancellation::install(token, None);
            run();
        }
        ClosedOwner::SolveDeadline => {
            let _solve = crate::smt::ScopedSolveDeadline::new(Some(Instant::now()));
            run();
        }
        ClosedOwner::SmtDeadline => {
            let _smt = crate::smt::ScopedSmtDeadline::install_until(Instant::now());
            run();
        }
        ClosedOwner::Memory => {
            let group =
                ay_sys::MemoryGroup::new(1024 * 1024, usize::MAX, Arc::new(AtomicBool::new(false)));
            let _group = ay_sys::enter_memory_group(group);
            ay_sys::charge_current_for_testing(2 * 1024 * 1024);
            assert!(ay_sys::current_memory_group_soft_tripped());
            run();
        }
    }
}
