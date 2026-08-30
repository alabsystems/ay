// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Per-route deadlines for a chain of interruptible certificate routes.
//!
//! THE DEFECT THIS EXISTS TO CLOSE. The OPT-LIN certificate routes are tried as
//! a `route_a.or_else(route_b).or_else(route_c)` chain, and every route in that
//! chain used to be handed the SAME `should_stop` closure — one shared deadline
//! for the whole chain. So the first route could consume all of it and the ones
//! behind it measured nothing. That is not a hypothesis; it was measured. On the
//! nine PB25 OPT-LIN instances AY solves to optimum but does not certify
//! (census/delivery-merged.tsv, 2026-08-28, 60 s budget):
//!
//! ```text
//!   evencolouring_..._nvert_071   compact=70381ms  auxfree=0ms  pb_native=0ms
//!   single-obj-f47-DC_Side1       compact=    4ms  auxfree=64529ms  pb_native=0ms
//! ```
//!
//! In both rows the route that was never reached is the one that CAN certify
//! the instance: given a deadline of its own, `bounds_pb_native` closed
//! evencolouring in 27.2 s and f47 in 7.5 s. Six of the nine misses were closed
//! that way and every one of the six was closed by the LAST route in the chain.
//!
//! WHAT THIS DOES. Each route gets an equal share of what is LEFT at the moment
//! it starts: route `i` of `n` remaining gets `remaining / n`. Time an earlier
//! route did not use therefore rolls forward to the later ones automatically
//! (an instant structural decline costs the chain nothing), while no route can
//! take more than its share and starve the rest.
//!
//! WHY THIS CANNOT PRODUCE A WRONG CERTIFICATE. The per-route deadline enters
//! ONLY as an extra disjunct in the `should_stop` predicate the route already
//! consults. Every emitter is fail-closed on interruption: it returns `None`,
//! never a truncated or unsound proof. So the strongest thing this scheduler can
//! do to any single route is make it decline EARLIER — it can convert a proof
//! into no-proof, never no-proof into a proof, and never one proof into another.
//! Certificates only ever appear because a route that previously got zero time
//! now runs at all, and whatever it emits is checked by the pinned VeriPB
//! checker exactly as before.

use std::time::Instant;

/// Splits a certification budget across the interruptible routes of a chain so
/// that a route cannot be starved by the ones scheduled before it.
///
/// `deadline` is the absolute end of the certification stage (`None` = no
/// budget at all, which keeps today's uncapped behaviour). `routes` is how many
/// interruptible routes the chain will run through this scheduler; passing a
/// number larger than the calls actually made only makes the early slices
/// smaller, never unsound.
pub struct CertRouteBudget<'a> {
    deadline: Option<Instant>,
    routes_left: u32,
    outer_stop: &'a dyn Fn() -> bool,
}

impl<'a> CertRouteBudget<'a> {
    /// `outer_stop` is the caller's own cancellation predicate (termination
    /// flag, overall timeout, memory guard). It always wins: a route stops when
    /// EITHER its own slice expires or the caller says stop.
    pub fn new(deadline: Option<Instant>, routes: u32, outer_stop: &'a dyn Fn() -> bool) -> Self {
        Self {
            deadline,
            routes_left: routes,
            outer_stop,
        }
    }

    /// Runs one interruptible route against a deadline of its own.
    ///
    /// The route is handed a `should_stop` that fires on the caller's predicate
    /// OR on this route's slice, and its `Option<String>` result is returned
    /// unchanged. Consumes one route's worth of the remaining budget whether or
    /// not the route used it, so the accounting cannot drift.
    ///
    /// `label` names the rung in `--cert-debug` output. That trace is the only
    /// way to answer "did this rung actually get time?" from a shipped binary,
    /// and the question is not rhetorical: the defect this type exists to close
    /// was invisible to code review — `deadline - elapsed` reads as correct
    /// right up to the moment you notice `elapsed` is already the whole budget.
    pub fn run<F>(&mut self, label: &str, route: F) -> Option<String>
    where
        F: FnOnce(&dyn Fn() -> bool) -> Option<String>,
    {
        let share_of = self.routes_left.max(1);
        self.routes_left = self.routes_left.saturating_sub(1);

        let outer_stop = self.outer_stop;
        if outer_stop() {
            trace(label, None, 0, "skipped(caller-stop)");
            return None;
        }
        let now = Instant::now();
        let slice = self
            .deadline
            .map(|end| end.saturating_duration_since(now) / share_of);
        let route_deadline = slice.map(|s| now + s);
        let should_stop =
            move || outer_stop() || route_deadline.is_some_and(|rd| Instant::now() >= rd);
        let out = route(&should_stop);
        trace(
            label,
            slice,
            now.elapsed().as_millis(),
            if out.is_some() { "proof" } else { "none" },
        );
        out
    }
}

/// One `--cert-debug` line per rung: the slice it was GRANTED and the time it
/// actually SPENT. Both numbers are needed — a rung that spent 0 ms because it
/// declined structurally and a rung that spent 0 ms because it was handed 0 ms
/// are the same observation until the slice is printed next to it.
fn trace(label: &str, slice: Option<std::time::Duration>, elapsed_ms: u128, outcome: &str) {
    if !ay_core::misc_cli_flags().cert_debug {
        return;
    }
    match slice {
        Some(slice) => eprintln!(
            "c [cert/budget] {label} slice={}ms elapsed={elapsed_ms}ms -> {outcome}",
            slice.as_millis()
        ),
        None => {
            eprintln!("c [cert/budget] {label} slice=unbounded elapsed={elapsed_ms}ms -> {outcome}")
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    // The timing assertions below run at SECOND scale on purpose. This box is
    // shared and has been observed at 1-minute load 80-148; a 200 ms nominal
    // slice with a 250 ms tolerance is a flake waiting to happen, while a 1 s
    // slice with a 1.4 s tolerance still fails loudly if a route eats the whole
    // chain (3 s) and passes under any scheduling delay short of that.
    #[test]
    fn each_route_gets_an_equal_share_and_a_later_route_still_runs() {
        let never = || false;
        let start = Instant::now();
        let mut budget = CertRouteBudget::new(Some(start + Duration::from_secs(3)), 3, &never);

        // Route 1 burns its whole slice (~1s) and declines.
        let mut r1_ran = false;
        let out = budget.run("r1", |stop| {
            r1_ran = true;
            while !stop() {
                std::hint::spin_loop();
            }
            None
        });
        assert!(out.is_none());
        assert!(r1_ran);
        let after_r1 = start.elapsed();
        assert!(
            after_r1 >= Duration::from_millis(700) && after_r1 < Duration::from_millis(2400),
            "route 1 took its share, not the chain's: {after_r1:?}"
        );

        // Route 2 is the one production used to starve. It must still get time.
        let out = budget.run("r2", |stop| {
            assert!(!stop(), "route 2 was starved by route 1");
            Some("proof".to_string())
        });
        assert_eq!(out.as_deref(), Some("proof"));
    }

    #[test]
    fn unused_time_rolls_forward_to_the_last_route() {
        let never = || false;
        let start = Instant::now();
        let mut budget = CertRouteBudget::new(Some(start + Duration::from_secs(2)), 2, &never);

        // An instant structural decline costs the chain nothing.
        assert!(budget.run("r1", |_| None).is_none());

        // The last route's slice is what is LEFT divided by one, i.e. nearly
        // the whole 2 s -- so a 500 ms route inside it must not be interrupted.
        let seen_deadline_ok = budget.run("r2", |stop| {
            std::thread::sleep(Duration::from_millis(500));
            if stop() {
                None
            } else {
                Some("proof".to_string())
            }
        });
        assert_eq!(
            seen_deadline_ok.as_deref(),
            Some("proof"),
            "the last route should inherit the time the first did not spend"
        );
    }

    #[test]
    fn no_deadline_means_no_cap() {
        let never = || false;
        let mut budget = CertRouteBudget::new(None, 3, &never);
        let out = budget.run("r1", |stop| {
            assert!(!stop());
            std::thread::sleep(Duration::from_millis(20));
            assert!(!stop(), "an unbounded chain must stay unbounded");
            Some("proof".to_string())
        });
        assert_eq!(out.as_deref(), Some("proof"));
    }

    #[test]
    fn the_callers_predicate_always_wins() {
        let always = || true;
        let mut budget = CertRouteBudget::new(None, 3, &always);
        let mut ran = false;
        let out = budget.run("r1", |_| {
            ran = true;
            Some("proof".to_string())
        });
        assert!(out.is_none());
        assert!(!ran, "a cancelled chain must not run its routes at all");
    }
}
