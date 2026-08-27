// Copyright 2026 Andrew Yates
//! THE DETECTOR FOR A DEFECT THAT COST THE CAMPAIGN ITS HEADLINE NUMBER.
//!
//! `bab::diag_float_lp` and `session::diag_shipped_float_lp` used to print
//! `wall={:.3}s`. That field is what `scripts/milp_w0.py` DIVIDES by a
//! reference solver's full-precision time. At three decimals every LP ay
//! answered in under a millisecond printed `wall=0.000s`, the quotient was
//! exactly `0.0`, and the summariser's `have = [r for r in rows if
//! r.get("ratio")]` dropped it as FALSY. The deleted rows were, by
//! construction, the ones where ay was FASTEST: 42 of 154 on the recorded W0
//! run, and the recorded "112 measurable" denominator was set by this bug and
//! not by any reference-solver skip.
//!
//! Measured effect on the recorded corpus: the published `8.2x` geomean
//! (re-derived here as 8.1574x from the development design notes) is
//! inflated 2.08-2.15x by this filter alone. The corrected ay/Gurobi LP gap is
//! ~3.2-3.4x on today's engine.
//!
//! WHY THIS FILE EXISTS AT ALL: an independent audit showed that reverting
//! `.6` back to `.3` passed all 1,446 crate tests and all four manual gates
//! **silently** — no test referenced either diag lane, and none of the gates
//! sets `AY_LP_ONLY` or invokes `diag`, so the changed code is not reachable
//! from any of them. A fix whose revert nothing detects is a fix with a
//! shelf life. These tests are that detector.
//!
//! # STILL AT THREE DECIMALS, DELIBERATELY NOT CHANGED HERE
//!
//! The same pattern survives on the SHIPPED result lines, and an audit flagged
//! it as a live hazard of this exact class:
//!   * `crates/ay-milp/src/bin/ay-milp.rs:314, 546` — `{dt:.3}` on the human
//!     result line, and `:646` — `"time":{dt:.3}` in the JSON output, which is
//!     precisely the shape a harness divides.
//!   * `crates/ay-milp/examples/mps_solve.rs:513, 532, 546, 550, 551` — the
//!     same field on every terminal status.
//! These are NOT fixed here on purpose: they are the shipped output contract,
//! and widening them is a consumer-compatibility decision (anything parsing
//! `status obj time nodes` by column, plus the JSON schema) rather than a
//! defect fix. What is recorded, so the next reader does not have to
//! rediscover it: `scripts/milp_w0.py`'s `run_ay` times these with its OWN
//! `time.monotonic()` and does not parse `dt`, and 0 of 154 archival ay times
//! in the development design notes are exactly 3-decimal — so this hazard has
//! NOT contaminated any recorded number. It is latent, not active. If a future
//! harness ever divides one of these fields, fix the format first.

use ay_milp::{Model, Sense, SolveOpts};
use std::time::Duration;

/// A trivial continuous LP: `max x`, `0 <= x <= 1`, one row. It solves in far
/// under a millisecond, which is exactly the regime the defect erased.
fn tiny_lp() -> Model {
    let mut m = Model::new();
    let x = m.add_col(0.0, 1.0);
    m.set_objective(&[(x, 1.0)], Sense::Maximize);
    m.add_row(f64::NEG_INFINITY, 1.0, &[(x, 1.0)]);
    m
}

/// Pull `wall=<value>s` out of a diag line.
fn wall_field(line: &str) -> &str {
    line.split("wall=")
        .nth(1)
        .expect("diag line must carry a wall= field")
        .split('s')
        .next()
        .expect("wall= must be terminated by 's'")
}

/// The load-bearing property, stated as the CONSUMER sees it: a sub-millisecond
/// solve must not print a wall that reads as zero, because downstream that
/// becomes a falsy ratio and the row is deleted from the geomean.
///
/// Note this asserts on RESOLUTION, not on a duration — the wall itself is
/// wildly load-coupled and would be a flaky pin. What is pinned is the number
/// of decimals, which is a property of the format string alone.
#[test]
fn a_sub_millisecond_diag_wall_is_not_printed_as_zero() {
    for (name, line) in [
        ("diag_float_lp", ay_milp::diag_float_lp(&tiny_lp(), 5.0)),
        (
            "diag_shipped_float_lp",
            ay_milp::diag_shipped_float_lp(&tiny_lp(), 5.0, &SolveOpts::new()),
        ),
    ] {
        let wall = wall_field(&line);
        let decimals = wall.split('.').nth(1).map_or(0, str::len);
        assert!(
            decimals >= 6,
            "{name}: wall={wall} carries {decimals} decimals; a harness that divides this by a \
             reference time turns any sub-millisecond solve into a falsy 0.0 and DELETES the row. \
             Full line: {line}"
        );
        // The direct statement of the defect: this LP is far faster than a
        // millisecond, so at 3 decimals this assertion is what fails first.
        assert_ne!(
            wall.parse::<f64>().expect("wall must parse"),
            0.0,
            "{name}: a solve that completed printed wall=0, which is the exact value the \
             summariser drops as falsy. Full line: {line}"
        );
    }
}

/// The scaled-units clause must travel ON the line, for the same reason the
/// scaffold and relaxation banners do: a separate header does not survive being
/// pasted into a report. On a model whose reader scale is 1 it must stay silent
/// — a diagnostic that cries wolf on every model teaches readers to skip it.
#[test]
fn the_units_clause_is_silent_when_there_is_no_scale_to_warn_about() {
    let line = ay_milp::diag_float_lp(&tiny_lp(), 5.0);
    assert!(
        !line.contains("[UNITS:"),
        "unit-scale 1 must not emit a UNITS clause: {line}"
    );
}

/// The shipped lane must keep saying, on the line, that an integer model's
/// answer is a RELAXATION bound and not that model's optimum.
#[test]
fn an_integer_model_still_gets_the_relaxation_banner() {
    let mut m = Model::new();
    let x = m.add_int_col(0.0, 1.0);
    m.set_objective(&[(x, 1.0)], Sense::Maximize);
    m.add_row(f64::NEG_INFINITY, 1.0, &[(x, 1.0)]);
    let line = ay_milp::diag_shipped_float_lp(
        &m,
        5.0,
        &SolveOpts::new().with_time_limit(Duration::from_secs(5)),
    );
    assert!(
        line.contains("RELAXATION-NOT-MODEL"),
        "an integral model's shipped-lp line must name itself a relaxation bound: {line}"
    );
}

/// The scaffold banner must keep naming what the lane does NOT do. This is the
/// text that stops a `Stopped` from a one-cold-walk diagnostic being quoted as
/// solver behaviour — the artifact that sent an entire research round chasing a
/// numerically-lost walk the shipped solver never had.
#[test]
fn the_scaffold_still_announces_that_it_is_not_the_solver() {
    let line = ay_milp::diag_float_lp(&tiny_lp(), 5.0);
    assert!(
        line.contains("SCAFFOLD-NOT-SOLVER"),
        "diag_float_lp must self-label: {line}"
    );
}
