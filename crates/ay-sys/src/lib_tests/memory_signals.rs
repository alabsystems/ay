// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::{memory_signals_exceed, memory_signals_exceed_with};
use std::cell::{Cell, RefCell};

fn observed_signals(threshold: usize, signals: [usize; 3]) -> (bool, Vec<&'static str>) {
    let calls = RefCell::new(Vec::new());
    let exceeded = memory_signals_exceed_with(
        threshold,
        || {
            calls.borrow_mut().push("footprint");
            signals[0]
        },
        || {
            calls.borrow_mut().push("live");
            signals[1]
        },
        || {
            calls.borrow_mut().push("rss");
            signals[2]
        },
    );
    (exceeded, calls.into_inner())
}

#[test]
fn lazy_advisory_acquires_only_policy_required_signals_in_order() {
    let cases = [
        ([949, usize::MAX, usize::MAX], false, 1),
        ([950, usize::MAX, usize::MAX], false, 1),
        ([951, 0, 0], true, 1),
        ([0, 951, 0], true, 2),
        ([0, 950, 951], true, 3),
        ([0, 949, 950], false, 3),
        ([0, 0, 951], true, 3),
        ([0, 0, 0], false, 3),
    ];
    let order = ["footprint", "live", "rss"];
    for (signals, expected, count) in cases {
        let (actual, calls) = observed_signals(950, signals);
        assert_eq!(actual, expected, "signals={signals:?}");
        assert_eq!(calls, order[..count], "signals={signals:?}");
    }
}

#[test]
fn lazy_advisory_matches_unchanged_pure_policy_at_all_boundaries() {
    let values = [0, 1, 94, 95, 96, usize::MAX - 1, usize::MAX];
    for threshold in values {
        for footprint in values {
            for live in values {
                for rss in values {
                    let signals = [footprint, live, rss];
                    let (actual, calls) = observed_signals(threshold, signals);
                    assert_eq!(
                        actual,
                        memory_signals_exceed(threshold, footprint, live, rss),
                        "threshold={threshold}, signals={signals:?}",
                    );
                    let count = if footprint > 0 {
                        1
                    } else if live > threshold {
                        2
                    } else {
                        3
                    };
                    assert_eq!(calls, ["footprint", "live", "rss"][..count]);
                }
            }
        }
    }
}

#[test]
fn lazy_advisory_reads_fresh_footprint_after_both_clear_and_exceeded_polls() {
    let readings = [949, 950, 951, 0, 1];
    let expected = [false, false, true, true, false];
    let footprint_calls = Cell::new(0);
    let live_calls = Cell::new(0);
    let rss_calls = Cell::new(0);
    for expected in expected {
        let actual = memory_signals_exceed_with(
            950,
            || {
                let index = footprint_calls.get();
                footprint_calls.set(index + 1);
                readings[index]
            },
            || {
                live_calls.set(live_calls.get() + 1);
                951
            },
            || {
                rss_calls.set(rss_calls.get() + 1);
                usize::MAX
            },
        );
        assert_eq!(actual, expected);
    }
    assert_eq!(footprint_calls.get(), readings.len());
    assert_eq!(live_calls.get(), 1);
    assert_eq!(rss_calls.get(), 0);
}

#[test]
fn lazy_advisory_accepts_once_only_providers_without_calling_unused_fallbacks() {
    let footprint = Box::new(950);
    assert!(!memory_signals_exceed_with(
        950,
        move || {
            let value = *footprint;
            drop(footprint);
            value
        },
        || panic!("positive footprint must skip live bytes"),
        || panic!("positive footprint must skip RSS"),
    ));
    assert!(memory_signals_exceed_with(
        950,
        || 0,
        || 951,
        || panic!("live-byte breach must skip RSS"),
    ));
}
