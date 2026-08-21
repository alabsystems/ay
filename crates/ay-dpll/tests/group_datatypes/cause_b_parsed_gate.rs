// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! #cause-b-parsed-gate — a correct refutation must not be discarded just
//! because the session dropped the parsed-assertion prefix.
//!
//! The CLI calls `set_retain_parsed_assertions(false)` in `--z3-mode`,
//! `--no-proof` and competition mode (`ay/src/run.rs:7969` and `:8582`,
//! #rss-vs-z3: the parsed-AST clone was ~190 MB of a 318 MB peak). Since
//! `66538b006f` the strict UNSAT certificate is MANDATORY, and
//! `apply_input_syntax_rewrites_to_proof` used to return early on an empty
//! parsed prefix — switching off not only the COSMETIC surface-syntax
//! overrides (which do need the parsed ASTs) but also the ASSUMPTION-AUTHORITY
//! passes (which do not: they reason over canonical `TermId`s). Foreign leaves
//! stayed `Assume`, strict certification reported `UnauthorizedAssumption`, and
//! that error is NOT trust-eligible in `unsat_cert.rs` — so
//! `discharge_trust_steps_for_certification`, the funnel's own rescue, was
//! never reached and the answer published as `unknown`.
//!
//! Because the defect is retention-OFF only, the default (retaining) mode that
//! `cargo test` exercises could not see it: the test below runs BOTH
//! configurations, and the retention-ON row is the control that passed before
//! the fix too.
//!
//! The input combines both producers of unauthorized leaves — authored
//! bool-ITEs (`rewrite_assertion_bool_ites` replaces `(ite C T E)` in place with
//! `(and (=> C T) (=> (not C) E))`, which `FlattenAnd` then splits, so the
//! frozen obligation still holds only the original `ite`) and the DT lazy
//! lane's appended selector/tester axioms, which no rewrite provenance can ever
//! authorize.
//!
//! It is also the end-to-end pin for #cause-b-narrow-split: the retention-off
//! path deliberately does NOT run
//! `derive_conjunct_assumptions_from_problem_roots` (the measured cause of all
//! 12 out-of-division losses), so this file also proves the demotion passes
//! alone are sufficient to restore the verdict.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;
use std::path::Path;

/// Solve `path` with the parsed-assertion prefix retained or dropped — the
/// latter is the configuration the CLI uses for `--z3-mode` / `--no-proof` /
/// competition mode.
fn solve_with_retention(path: &Path, retain_parsed: bool) -> String {
    let smt = std::fs::read_to_string(path)
        .unwrap_or_else(|err| panic!("failed reading {}: {err}", path.display()));
    let commands =
        parse(&smt).unwrap_or_else(|err| panic!("parse error in {}: {err}", path.display()));
    let mut executor = Executor::new();
    executor.set_retain_parsed_assertions(retain_parsed);
    let outputs = executor
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution error on {}: {err}", path.display()));
    outputs
        .into_iter()
        .find(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
        .unwrap_or_else(|| "unknown".to_string())
        .trim()
        .to_string()
}

/// Reduced, self-contained repro: authored bool-ITEs (the rewrite producer)
/// over a datatype whose lazy lane appends selector axioms (the lane producer).
#[test]
#[timeout(120_000)]
fn dt_bool_ite_refutation_survives_without_parsed_retention() {
    let path = crate::common::workspace_path(
        "benchmarks/smt/regression/cause_b_parsed_gate_dt_bool_ite.smt2",
    );
    assert!(
        path.is_file(),
        "missing tracked regression input: {}",
        path.display()
    );

    // Control: retention ON. This passed before the gate split too — it is here
    // to prove the defect was configuration-specific, not a solving regression.
    assert_eq!(
        solve_with_retention(&path, true),
        "unsat",
        "control (parsed prefix RETAINED) must be unsat"
    );

    // The regression: retention OFF. Before the gate split this published
    // `unknown` — "computed UNSAT rejected by mandatory strict certification:
    // step tN assumes term tM outside the supplied problem obligation".
    assert_eq!(
        solve_with_retention(&path, false),
        "unsat",
        "#cause-b-parsed-gate REGRESSION: AY computed the refutation and then \
         discarded it because the assumption-authority passes were gated off with \
         the parsed-assertion prefix. The answer must not depend on whether the \
         session retains parsed ASTs."
    );
}
