// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Build provenance helpers for the ay CLI.

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

pub(crate) fn session_start_marker() -> String {
    format!(
        "c ay.session.start build.version={} build.increment={} build.commit={} build.datetime_utc={} build.stamp={}",
        BUILD_INFO.version,
        BUILD_INFO.increment,
        BUILD_INFO.commit,
        BUILD_INFO.datetime_utc,
        BUILD_INFO.stamp
    )
}

pub(crate) fn session_end_marker(outcome: SessionOutcome, elapsed: Duration) -> String {
    let wall_time_ms = elapsed.as_millis();
    match outcome {
        SessionOutcome::ExitCode(code) => format!(
            "c ay.session.end build.increment={} build.stamp={} exit.code={code} wall_time_ms={wall_time_ms}",
            BUILD_INFO.increment, BUILD_INFO.stamp
        ),
        SessionOutcome::Signal(signal) => format!(
            "c ay.session.end build.increment={} build.stamp={} exit.signal={signal} wall_time_ms={wall_time_ms}",
            BUILD_INFO.increment, BUILD_INFO.stamp
        ),
        SessionOutcome::LaunchError => format!(
            "c ay.session.end build.increment={} build.stamp={} exit.error=launch-failed wall_time_ms={wall_time_ms}",
            BUILD_INFO.increment, BUILD_INFO.stamp
        ),
    }
}
