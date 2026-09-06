// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Build provenance helpers for the ay CLI.

use std::sync::OnceLock;
use std::time::Duration;

pub(crate) struct BuildInfo {
    pub(crate) version: &'static str,
    pub(crate) increment: &'static str,
    pub(crate) commit: &'static str,
    pub(crate) datetime_utc: &'static str,
    pub(crate) stamp: &'static str,
}

pub(crate) const BUILD_INFO: BuildInfo = BuildInfo {
    version: env!("CARGO_PKG_VERSION"),
    increment: env!("AY_BUILD_INCREMENT"),
    commit: env!("AY_BUILD_COMMIT"),
    datetime_utc: env!("AY_BUILD_DATETIME_UTC"),
    stamp: env!("AY_BUILD_STAMP"),
};

pub(crate) const CLAP_VERSION: &str = env!("AY_BUILD_STAMP");
pub(crate) const CLAP_LONG_VERSION: &str = concat!(
    env!("AY_BUILD_STAMP"),
    "\n",
    "build.version=",
    env!("CARGO_PKG_VERSION"),
    "\n",
    "build.increment=",
    env!("AY_BUILD_INCREMENT"),
    "\n",
    "build.commit=",
    env!("AY_BUILD_COMMIT"),
    "\n",
    "build.datetime_utc=",
    env!("AY_BUILD_DATETIME_UTC"),
    "\n",
    "build.stamp=",
    env!("AY_BUILD_STAMP"),
);

pub(crate) fn exact_provenance_json() -> String {
    let source_identity = option_env!("AY_TEST_SOURCE_IDENTITY").unwrap_or("unbound");
    let build_identity = option_env!("AY_TEST_BUILD_IDENTITY").unwrap_or("unbound");
    format!(
        "{{\"schema\":\"ay-exact-binary-provenance-v1\",\"source_identity\":\"{source_identity}\",\"build_identity\":\"{build_identity}\"}}"
    )
}

pub(crate) enum SessionOutcome {
    ExitCode(i32),
    Signal(i32),
    LaunchError,
}

/// Verbosity of the `c ay.session.*` provenance markers on stderr.
///
/// The build stamp already concatenates version, increment, commit, and
/// datetime, so [`SessionLog::Compact`] — the default — states it once per run
/// and nothing is lost: `build.stamp=` still greps, and every field remains
/// recoverable from that one token. [`SessionLog::Full`] restores the
/// historical spelling byte-for-byte for audit and competition transcripts,
/// which is why any competition signal forces it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SessionLog {
    /// No session markers at all (`AY_SESSION_LOG=off`; `-q` suppresses too).
    Off,
    /// One `build.stamp=` on start, outcome and timing on end. Default.
    Compact,
    /// Every `build.*` field on both markers — the audit form.
    Full,
}

/// Resolve the session-marker verbosity once per process.
///
/// Precedence: an explicit `AY_SESSION_LOG` value wins, because an operator who
/// names a level means it; otherwise a competition signal forces `full`, since
/// those transcripts are the archived evidence a claim is later audited
/// against. An unrecognized value falls back to the default rather than
/// aborting a solve over a typo in an env var.
pub(crate) fn session_log() -> SessionLog {
    static LEVEL: OnceLock<SessionLog> = OnceLock::new();
    *LEVEL.get_or_init(|| {
        match std::env::var("AY_SESSION_LOG")
            .ok()
            .map(|value| value.trim().to_ascii_lowercase())
            .as_deref()
        {
            Some("off" | "none" | "0") => SessionLog::Off,
            Some("full" | "verbose") => SessionLog::Full,
            Some("compact" | "1") => SessionLog::Compact,
            _ if super::competition_mode::competition_env_active() => SessionLog::Full,
            _ => SessionLog::Compact,
        }
    })
}

pub(crate) fn session_start_marker() -> String {
    session_start_marker_at(session_log())
}

/// The start marker at an explicit verbosity — the formatting half of
/// [`session_start_marker`], split out so it is testable without racing the
/// process-wide `AY_SESSION_LOG` latch.
fn session_start_marker_at(level: SessionLog) -> String {
    match level {
        SessionLog::Full => format!(
            "c ay.session.start build.version={} build.increment={} build.commit={} build.datetime_utc={} build.stamp={}",
            BUILD_INFO.version,
            BUILD_INFO.increment,
            BUILD_INFO.commit,
            BUILD_INFO.datetime_utc,
            BUILD_INFO.stamp
        ),
        // The stamp is `version+build.increment.commit@datetime`: one field,
        // all four values, still greppable as `build.stamp=`.
        SessionLog::Off | SessionLog::Compact => {
            format!("c ay.session.start build.stamp={}", BUILD_INFO.stamp)
        }
    }
}

pub(crate) fn session_end_marker(outcome: SessionOutcome, elapsed: Duration) -> String {
    session_end_marker_at(session_log(), outcome, elapsed)
}

/// The end marker at an explicit verbosity. See [`session_start_marker_at`].
fn session_end_marker_at(level: SessionLog, outcome: SessionOutcome, elapsed: Duration) -> String {
    let wall_time_ms = elapsed.as_millis();
    let outcome_field = match outcome {
        SessionOutcome::ExitCode(code) => format!("exit.code={code}"),
        SessionOutcome::Signal(signal) => format!("exit.signal={signal}"),
        SessionOutcome::LaunchError => "exit.error=launch-failed".to_string(),
    };
    match level {
        SessionLog::Full => format!(
            "c ay.session.end build.increment={} build.stamp={} {outcome_field} wall_time_ms={wall_time_ms}",
            BUILD_INFO.increment, BUILD_INFO.stamp
        ),
        // The start marker already carried the stamp this run; repeating it
        // here bought nothing. `build.increment` stays because it is the field
        // harness logs correlate runs by.
        SessionLog::Off | SessionLog::Compact => format!(
            "c ay.session.end {outcome_field} wall_time_ms={wall_time_ms} build.increment={}",
            BUILD_INFO.increment
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The whole point of the compact form: one build token per run, not two on
    /// the start line and a third on the end line.
    #[test]
    fn compact_start_marker_states_the_stamp_exactly_once() {
        let marker = session_start_marker_at(SessionLog::Compact);
        assert_eq!(marker.matches("build.stamp=").count(), 1, "{marker}");
        assert_eq!(marker.matches(BUILD_INFO.stamp).count(), 1, "{marker}");
        for redundant in [
            "build.version=",
            "build.increment=",
            "build.commit=",
            "build.datetime_utc=",
        ] {
            assert!(
                !marker.contains(redundant),
                "{redundant} survives in {marker}"
            );
        }
    }

    /// Every field the compact form drops is recoverable from the stamp it
    /// keeps, which is what makes the compaction lossless rather than merely
    /// shorter.
    #[test]
    fn the_stamp_still_carries_every_dropped_field() {
        let stamp = BUILD_INFO.stamp;
        for field in [
            BUILD_INFO.version,
            BUILD_INFO.increment,
            BUILD_INFO.commit,
            BUILD_INFO.datetime_utc,
        ] {
            assert!(
                stamp.contains(field),
                "{field} is not recoverable from {stamp}"
            );
        }
    }

    #[test]
    fn compact_end_marker_carries_outcome_and_increment_but_not_the_stamp() {
        let marker = session_end_marker_at(
            SessionLog::Compact,
            SessionOutcome::ExitCode(0),
            Duration::from_millis(76),
        );
        assert_eq!(
            marker,
            format!(
                "c ay.session.end exit.code=0 wall_time_ms=76 build.increment={}",
                BUILD_INFO.increment
            )
        );
        assert!(!marker.contains("build.stamp="), "{marker}");
    }

    /// `AY_SESSION_LOG=full` is the audit escape hatch, so its bytes must stay
    /// the historical ones — field for field, in the historical order.
    #[test]
    fn full_markers_keep_the_historical_spelling() {
        assert_eq!(
            session_start_marker_at(SessionLog::Full),
            format!(
                "c ay.session.start build.version={} build.increment={} build.commit={} build.datetime_utc={} build.stamp={}",
                BUILD_INFO.version,
                BUILD_INFO.increment,
                BUILD_INFO.commit,
                BUILD_INFO.datetime_utc,
                BUILD_INFO.stamp
            )
        );
        assert_eq!(
            session_end_marker_at(
                SessionLog::Full,
                SessionOutcome::ExitCode(0),
                Duration::from_millis(76)
            ),
            format!(
                "c ay.session.end build.increment={} build.stamp={} exit.code=0 wall_time_ms=76",
                BUILD_INFO.increment, BUILD_INFO.stamp
            )
        );
    }

    /// A crash or a failed launch must still be distinguishable in the compact
    /// form — compaction drops repetition, never outcome.
    #[test]
    fn compact_end_marker_distinguishes_every_outcome() {
        let at = |outcome| session_end_marker_at(SessionLog::Compact, outcome, Duration::ZERO);
        assert!(at(SessionOutcome::ExitCode(3)).contains("exit.code=3"));
        assert!(at(SessionOutcome::Signal(9)).contains("exit.signal=9"));
        assert!(at(SessionOutcome::LaunchError).contains("exit.error=launch-failed"));
    }
}
