// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Command-line probe dials for the FRB SLS measurement harness.

pub(super) const USAGE: &str =
    "usage: frb_sls_probe <file.opb> [secs] [seed] [noise] [mode=full|core] \
     [--core-cdcl] [--csp-nocoord] [--clique-restart N] [--csp-maxmoves N] \
     [--csp-stag N] [--csp-kick N] [--probsat-cb X] [--maxflips-per-n N]";

// B14: probe dials moved off `AY_*` env vars onto example CLI flags, read
// directly at their sites (no param threading in a measurement harness).
pub(super) fn flag(name: &str) -> bool {
    std::env::args().any(|argument| argument == name)
}

pub(super) fn val<T: std::str::FromStr>(name: &str) -> Option<T> {
    let mut args = std::env::args();
    while let Some(argument) = args.next() {
        if argument == name {
            return args.next().and_then(|value| value.parse().ok());
        }
        if let Some(value) = argument
            .strip_prefix(name)
            .and_then(|rest| rest.strip_prefix('='))
        {
            return value.parse().ok();
        }
    }
    None
}
