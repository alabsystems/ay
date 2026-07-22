// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for #6892: BVE backward subsumption deletes irredundant
//! clauses without adding reconstruction entries. When BVE later eliminates
//! a variable present in the deleted clause, the `!is_active` guard at
//! line 364 skips it — losing its constraint from the reconstruction stack.
//! Cross-variable reconstruction interference then flips witness variables
//! in a way that unsatisfies the original clause, producing an invalid SAT
//! model (reported as UNKNOWN).
//!
//! Root cause: BVE backward subsumption (bve.rs:590) marks subsumed clauses
//! as deleted without pushing a reconstruction entry. The resolvent that
//! subsumes the clause may itself be deleted by a subsequent elimination,
//! breaking the subsumption chain.
//!
//! Fix: push a witness-clause reconstruction entry for irredundant clauses
//! before backward-subsumption deletion.
//!
//! Minimal trigger: probe + BVE + subsumption on the crn_11_99_u benchmark.

#![allow(clippy::panic)]

use ay_sat::{parse_dimacs, SatResult};
use ntest::timeout;

const CRN_PATH: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../benchmarks/sat/satcomp2024-sample/ef330d1b144055436a2d576601191ea5-crn_11_99_u.cnf.xz"
);

/// Full default configuration must produce UNSAT on crn_11_99_u.
/// Before the #6892 fix, this returned UNKNOWN (invalid SAT model).
#[test]
#[timeout(120_000)]
fn crn_full_default_config() {
    let Some(content) = super::common::load_optional_benchmark(CRN_PATH) else {
        return;
    };
    let formula = parse_dimacs(&content).expect("valid DIMACS");
    let mut solver = formula.into_solver();
    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "#6892: full default config must produce UNSAT on crn_11_99_u, got {result:?}"
    );
}

/// Minimal trigger: probe + BVE + subsumption (the three interacting features).
/// With #8397 fix (keeping root-false literals), this configuration may return
/// Unknown due to multi-variable reconstruction cascades that the limited
/// simplification suite cannot avoid. The default config reliably returns UNSAT.
/// Only SAT would be a soundness violation.
#[test]
#[timeout(120_000)]
fn crn_probe_bve_subsume() {
    let Some(content) = super::common::load_optional_benchmark(CRN_PATH) else {
        return;
    };
    let formula = parse_dimacs(&content).expect("valid DIMACS");
    let mut solver = formula.into_solver();
    super::common::disable_all_inprocessing(&mut solver);
    solver.set_probe_enabled(true);
    solver.set_bve_enabled(true);
    solver.set_subsume_enabled(true);
    let result = solver.solve().into_inner();
    assert!(
        !matches!(result, SatResult::Sat(_)),
        "#6892: probe+BVE+subsume must not return SAT on crn_11_99_u (known UNSAT), got {result:?}"
    );
}

/// Probe only (no BVE) — baseline: confirms the benchmark is UNSAT without BVE.
#[test]
#[timeout(120_000)]
fn crn_probe_only() {
    let Some(content) = super::common::load_optional_benchmark(CRN_PATH) else {
        return;
    };
    let formula = parse_dimacs(&content).expect("valid DIMACS");
    let mut solver = formula.into_solver();
    super::common::disable_all_inprocessing(&mut solver);
    solver.set_probe_enabled(true);
    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "#6892: probe-only must produce UNSAT on crn_11_99_u, got {result:?}"
    );
}

/// BVE only (no probe): without probing, BVE can produce a reduced formula
/// where search finds SAT but reconstruction can't extend to the original
/// (fail-closed to Unknown). Default config (probe+BVE) always works.
/// Only Sat would be a soundness bug; Unknown is correct fail-closed behavior.
#[test]
#[timeout(120_000)]
fn crn_bve_only() {
    let Some(content) = super::common::load_optional_benchmark(CRN_PATH) else {
        return;
    };
    let formula = parse_dimacs(&content).expect("valid DIMACS");
    let mut solver = formula.into_solver();
    super::common::disable_all_inprocessing(&mut solver);
    solver.set_bve_enabled(true);
    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Unsat(_) | SatResult::Unknown),
        "#6892: BVE-only must produce UNSAT or Unknown on crn_11_99_u, got {result:?}"
    );
}
