// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for the MemoryPressure observer.

use super::*;

fn mock_mp(rss: usize, budget: usize) -> (MemoryPressure, std::sync::Arc<MockSource>) {
    let src = std::sync::Arc::new(MockSource::new(rss, budget));
    // Clone the Arc for ownership inside Box<dyn MemorySource>.
    let src_for_box = MockSource::new(rss, budget);
    let mp = MemoryPressure::with_source(Box::new(src_for_box));
    (mp, src)
}

// ---------------------------------------------------------------------------
// classify_raw: pure band classification (no hysteresis state)
// ---------------------------------------------------------------------------

#[test]
fn classify_raw_low_pressure_is_green() {
    let t = BandThresholds::default();
    // 100 MB / 10 GB = 1%
    assert_eq!(
        classify_raw(100 * 1024 * 1024, 10 * 1024 * 1024 * 1024, t, Band::Green),
        Band::Green
    );
}

#[test]
fn classify_raw_50_percent_enters_yellow() {
    let t = BandThresholds::default();
    // 5 GB / 10 GB = 50%
    assert_eq!(
        classify_raw(
            5 * 1024 * 1024 * 1024,
            10 * 1024 * 1024 * 1024,
            t,
            Band::Green
        ),
        Band::Yellow
    );
}

#[test]
fn classify_raw_70_percent_enters_orange() {
    let t = BandThresholds::default();
    // 7 GB / 10 GB = 70%
    assert_eq!(
        classify_raw(
            7 * 1024 * 1024 * 1024,
            10 * 1024 * 1024 * 1024,
            t,
            Band::Green
        ),
        Band::Orange
    );
}

#[test]
fn classify_raw_85_percent_enters_red() {
    let t = BandThresholds::default();
    // 8.5 GB / 10 GB = 85%
    let rss = 85 * 1024 * 1024 * 1024 / 10; // 8.5 GB in bytes
    assert_eq!(
        classify_raw(rss, 10 * 1024 * 1024 * 1024, t, Band::Green),
        Band::Red
    );
}

#[test]
fn classify_raw_99_percent_is_red() {
    let t = BandThresholds::default();
    assert_eq!(classify_raw(99, 100, t, Band::Green), Band::Red);
}

#[test]
fn classify_raw_zero_rss_holds_previous_orange_red() {
    // No signal (rss=0) must not drop us out of a pre-existing high band.
    let t = BandThresholds::default();
    assert_eq!(classify_raw(0, 1024, t, Band::Orange), Band::Orange);
    assert_eq!(classify_raw(0, 1024, t, Band::Red), Band::Red);
    // But green/yellow with no signal stays Green (conservative).
    assert_eq!(classify_raw(0, 1024, t, Band::Green), Band::Green);
    assert_eq!(classify_raw(0, 1024, t, Band::Yellow), Band::Green);
}

#[test]
fn classify_raw_usize_max_budget_is_unmeasured() {
    // Budget = usize::MAX = "no OS figure available" → treat as Green even
    // at high RSS (we can't compute a fraction meaningfully).
    let t = BandThresholds::default();
    assert_eq!(
        classify_raw(100 * 1024 * 1024 * 1024, usize::MAX, t, Band::Green),
        Band::Green
    );
}

// ---------------------------------------------------------------------------
// Hysteresis
// ---------------------------------------------------------------------------

#[test]
fn hysteresis_no_flap_on_small_oscillation_at_yellow_boundary() {
    let t = BandThresholds::default();
    // Enter yellow at 50%.
    let band = classify_raw(500, 1000, t, Band::Green);
    assert_eq!(band, Band::Yellow);
    // Dip to 48% — with 5% hysteresis we should STAY in Yellow (exit at 45%).
    let band = classify_raw(480, 1000, t, band);
    assert_eq!(band, Band::Yellow, "48% should stay yellow (exit at 45%)");
    // Dip to 46% — still above 45% exit.
    let band = classify_raw(460, 1000, t, band);
    assert_eq!(band, Band::Yellow);
    // Drop to 44% — now below exit, should go Green.
    let band = classify_raw(440, 1000, t, band);
    assert_eq!(band, Band::Green);
}

#[test]
fn hysteresis_no_flap_at_orange_boundary() {
    let t = BandThresholds::default();
    // Enter orange at 70%.
    let band = classify_raw(700, 1000, t, Band::Yellow);
    assert_eq!(band, Band::Orange);
    // Dip to 66% — exit threshold is 65%, should stay Orange.
    let band = classify_raw(660, 1000, t, band);
    assert_eq!(band, Band::Orange);
    // Drop to 64% — below exit.
    let band = classify_raw(640, 1000, t, band);
    assert_eq!(band, Band::Yellow);
}

#[test]
fn hysteresis_red_holds_until_80_percent() {
    let t = BandThresholds::default();
    // Enter Red at 85%.
    let band = classify_raw(850, 1000, t, Band::Orange);
    assert_eq!(band, Band::Red);
    // Drop to 82% — exit is 80%, stay Red.
    let band = classify_raw(820, 1000, t, band);
    assert_eq!(band, Band::Red);
    // Drop to 79% — now Orange (still >= 70% orange_enter).
    let band = classify_raw(790, 1000, t, band);
    assert_eq!(band, Band::Orange);
}

#[test]
fn hysteresis_big_drop_skips_multiple_bands() {
    let t = BandThresholds::default();
    // From Red down to 10% — drop all the way to Green in one step.
    let band = classify_raw(100, 1000, t, Band::Red);
    assert_eq!(band, Band::Green);
}

// ---------------------------------------------------------------------------
// MemoryPressure lifecycle
// ---------------------------------------------------------------------------

#[test]
fn new_starts_at_green() {
    let mp = MemoryPressure::new();
    assert_eq!(mp.current_band(), Band::Green);
}

#[test]
fn sample_updates_band_with_mock_source() {
    let src = Box::new(MockSource::new(100, 1000));
    let mut mp = MemoryPressure::with_source(src);
    assert_eq!(mp.sample(), Band::Green);
    assert_eq!(mp.sample_count(), 1);
    assert_eq!(mp.red_samples(), 0);
}

#[test]
fn sample_transitions_green_yellow_orange_red() {
    let shared = std::sync::Arc::new(MockSource::new(100, 1000));
    struct ArcSource(std::sync::Arc<MockSource>);
    impl MemorySource for ArcSource {
        fn rss_bytes(&self) -> usize {
            self.0.rss_bytes()
        }
        fn budget_bytes(&self) -> usize {
            self.0.budget_bytes()
        }
    }
    let mut mp = MemoryPressure::with_source(Box::new(ArcSource(shared.clone())));

    assert_eq!(mp.sample(), Band::Green);

    shared.set_rss(500); // 50%
    assert_eq!(mp.sample(), Band::Yellow);

    shared.set_rss(700); // 70%
    assert_eq!(mp.sample(), Band::Orange);

    shared.set_rss(850); // 85%
    assert_eq!(mp.sample(), Band::Red);
    assert!(mp.red_samples() >= 1);
}

#[test]
fn observer_receives_band_changes_only() {
    struct Recorder(Vec<(Band, Band)>);
    impl PressureObserver for Recorder {
        fn on_band_change(&mut self, old: Band, new: Band) {
            self.0.push((old, new));
        }
    }

    let shared = std::sync::Arc::new(MockSource::new(100, 1000));
    struct ArcSource(std::sync::Arc<MockSource>);
    impl MemorySource for ArcSource {
        fn rss_bytes(&self) -> usize {
            self.0.rss_bytes()
        }
        fn budget_bytes(&self) -> usize {
            self.0.budget_bytes()
        }
    }
    let mut mp = MemoryPressure::with_source(Box::new(ArcSource(shared.clone())));
    let mut rec = Recorder(Vec::new());

    mp.sample_with(&mut rec); // Green → Green, no callback
    assert_eq!(rec.0.len(), 0);

    shared.set_rss(500);
    mp.sample_with(&mut rec); // Green → Yellow
    assert_eq!(rec.0, vec![(Band::Green, Band::Yellow)]);

    // Small dip inside hysteresis band — no callback.
    shared.set_rss(480);
    mp.sample_with(&mut rec);
    assert_eq!(rec.0.len(), 1);

    shared.set_rss(700);
    mp.sample_with(&mut rec); // Yellow → Orange
    assert_eq!(
        rec.0,
        vec![(Band::Green, Band::Yellow), (Band::Yellow, Band::Orange),]
    );
}

#[test]
fn unit_observer_impl_is_noop() {
    // Sanity: PressureObserver for () doesn't panic.
    let mut unit: () = ();
    unit.on_band_change(Band::Green, Band::Red);
}

// ---------------------------------------------------------------------------
// Red-band abort payload
// ---------------------------------------------------------------------------

#[test]
fn red_abort_reason_captures_last_sample() {
    let shared = std::sync::Arc::new(MockSource::new(900, 1000));
    struct ArcSource(std::sync::Arc<MockSource>);
    impl MemorySource for ArcSource {
        fn rss_bytes(&self) -> usize {
            self.0.rss_bytes()
        }
        fn budget_bytes(&self) -> usize {
            self.0.budget_bytes()
        }
    }
    let mut mp = MemoryPressure::with_source(Box::new(ArcSource(shared)));
    let band = mp.sample();
    assert_eq!(band, Band::Red);

    let reason = mp.red_abort_reason();
    match reason {
        UnknownReason::MemoryPressure {
            rss_bytes,
            budget_bytes,
        } => {
            assert_eq!(rss_bytes, 900);
            assert_eq!(budget_bytes, 1000);
        }
    }
}

#[test]
fn unknown_reason_display_and_kind() {
    let r = UnknownReason::MemoryPressure {
        rss_bytes: 123,
        budget_bytes: 456,
    };
    assert_eq!(r.kind_str(), "memory_pressure");
    assert!(format!("{r}").contains("rss=123"));
    assert!(format!("{r}").contains("budget=456"));
}

// ---------------------------------------------------------------------------
// Band helpers
// ---------------------------------------------------------------------------

#[test]
fn band_ordering_reflects_severity() {
    assert!(Band::Green < Band::Yellow);
    assert!(Band::Yellow < Band::Orange);
    assert!(Band::Orange < Band::Red);
}

#[test]
fn band_as_str_is_stable() {
    assert_eq!(Band::Green.as_str(), "green");
    assert_eq!(Band::Yellow.as_str(), "yellow");
    assert_eq!(Band::Orange.as_str(), "orange");
    assert_eq!(Band::Red.as_str(), "red");
}

#[test]
fn band_is_red_helper() {
    assert!(!Band::Green.is_red());
    assert!(!Band::Yellow.is_red());
    assert!(!Band::Orange.is_red());
    assert!(Band::Red.is_red());
}

// ---------------------------------------------------------------------------
// SystemSource sanity (production path — real RSS read)
// ---------------------------------------------------------------------------

#[test]
fn system_source_rss_is_non_negative() {
    let src = SystemSource;
    let _ = src.rss_bytes(); // may be 0 on unsupported platforms
    let _ = src.budget_bytes();
}

#[test]
fn default_memory_pressure_samples_successfully() {
    let mut mp = MemoryPressure::default();
    // Sampling must not panic regardless of OS signal availability.
    let band = mp.sample();
    // On a running test process, the band is almost certainly Green, but we
    // only assert "some valid Band was returned and state updated".
    let _ = band;
    assert_eq!(mp.sample_count(), 1);
}

// Suppress the unused `mock_mp` helper warning by using it once.
#[test]
fn _mock_mp_helper_is_callable() {
    let (mp, src) = mock_mp(0, 1000);
    let _ = (mp.current_band(), src.rss_bytes());
}
