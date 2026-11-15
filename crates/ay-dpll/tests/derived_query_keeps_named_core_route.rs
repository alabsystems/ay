// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! The certification funnel's fresh-executor re-solves (`Executor::
//! new_derived_query_executor`) must keep the session's `:produce-unsat-cores`
//! so the named-to-assumption redirect stays available to the nested solve.
//!
//! `freevar_takesome_manual_d1` (the `demand_probes` green probe, a DT+UF+LIA
//! named-core query, z3: unsat) decides through the named-core route in
//! ~1.7 s at release and needs ~31 s through the plain route. A first cut of
//! the derived-query context cleared core tracking to skip the minimizer,
//! which dropped the redirect with it: the step-(4) corroboration then ran
//! the plain route, hit the 15 s wall, and a green probe published
//! `unknown`. Only the deletion minimizer is suppressed on a derived query.

use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use std::time::{Duration, Instant};

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

const PROBE_WALL: Duration = Duration::from_secs(15);

#[test]
#[timeout(300_000)]
fn dt_uf_lia_named_core_probe_stays_unsat_through_the_corroborating_re_solve() {
    let commands = parse(include_str!(
        "fixtures/dt_uf_lia_freevar_takesome_named_core.smt2"
    ))
    .expect("fixture parses");
    let mut executor = Executor::new();
    executor.set_interrupt(Arc::new(AtomicBool::new(false)));
    executor.set_timeout(Some(PROBE_WALL));
    let started = Instant::now();
    let outputs = executor.execute_all(&commands).expect("script executes");
    let elapsed = started.elapsed();
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("unsat"),
        "the probe must stay unsat (reason {:?}) after {elapsed:?}",
        executor.unknown_reason()
    );
    if !cfg!(debug_assertions) {
        assert!(
            elapsed < PROBE_WALL,
            "the verdict must arrive inside the probe wall, took {elapsed:?}"
        );
    }
}
