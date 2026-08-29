// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! `check-sat-assuming` isolation on the FP lane (#fp-incremental-subsystem).
//!
//! An assumption must constrain ONLY the query it was given to. This file exists
//! because the FP route reaches that guarantee differently from every other lane,
//! and because grep shows the existing `check-sat-assuming` tests
//! (`sat_chokepoint_repros`, `sat_chokepoint_conformance`,
//! `unsat_chokepoint_conformance`) contain no FP at all — so the FP assumption
//! path had zero coverage.
//!
//! `solve_fp_with_scoped_assumptions` (`executor/check_sat_assuming.rs`) does not
//! hand assumptions to the SAT solver as assumption literals. It MERGES them into
//! `ctx.assertions`, runs the ordinary FP pipeline, and restores the vector
//! afterwards. That is sound today for a second reason as well: `solve_fp` builds
//! a fresh `FpSolver` and a fresh `SatSolver` every call, so nothing an assumption
//! caused can outlive the query.
//!
//! Both of those reasons must keep holding. If the FP lane becomes incremental
//! (`FP_INCREMENTAL_SUBSYSTEM_DESIGN.md`), merged assumptions would be encoded and
//! ACTIVATED into the persistent solver, and restoring `ctx.assertions` would not
//! undo that — the assumption would silently constrain every later query. The
//! design classifies these as "must NOT be installed at all": they belong in
//! `Solver::solve_with_assumptions`, never in the clause database.
//!
//! ⚠ NOT MUTATION-VERIFIED, AND HERE IS WHY — read before trusting them.
//!
//! This program's standard is that a barrier which cannot be made to fail is not
//! a barrier. These two do not meet it, and the honest reason is that the channel
//! they guard DOES NOT EXIST YET. I tried two mutations of today's code:
//!
//!   1. skip `self.ctx.assertions = original_assertions` entirely;
//!   2. restore it and then append the assumptions permanently.
//!
//! BOTH left the tests passing, because the executor rebuilds `ctx.assertions`
//! from the scope stack on each command — so `ctx.assertions` is not the leak
//! channel, and mutating it cannot simulate the hazard. The hazard is an
//! assumption ACTIVATED INTO A PERSISTENT SAT SOLVER, and there is no persistent
//! FP solver to corrupt.
//!
//! Contrast `fp_to_ubv_congruence_survives_a_push_8870_incremental`, which IS
//! mutation-verified: the site-list mechanism it guards exists today, so emptying
//! the prior-site list breaks it exactly as designed.
//!
//! UPDATE — `IncrementalFpState` HAS NOW LANDED, the promised re-verification was
//! done, and the prediction above was WRONG. What actually happened:
//!
//! Mutating the persistent lane's assertion activation from scoped `add_clause`
//! to `add_clause_global` — literally "the assertion survives its scope" — leaves
//! both tests PASSING. The statistics say why: running the first fixture through
//! the CLI emits no `fp-incremental` counter at all. **The persistent lane does
//! not engage for the `check-sat-assuming` route.**
//!
//! That is the DESIGNED behaviour, not an oversight: design bucket 3a says
//! assumption literals must never enter the clause database, and the lane
//! correctly leaves that route on the stateless path. So these canaries still
//! cannot be broken by mutating the lane — because the lane is not in their path.
//!
//! Their value changed rather than vanished. They are now standing EVIDENCE that
//! the assumption route stays outside persistence: if a later change routes
//! `check-sat-assuming` through the persistent lane without moving assumptions to
//! `Solver::solve_with_assumptions`, the leak they describe becomes reachable and
//! they become discriminating. Until then they remain INVARIANT ASSERTIONS, not
//! proven guards, and this file keeps saying so.
//!
//! The verified guards for persistence are the lane's own controls `nc1`-`nc6`;
//! an independent review confirmed the activation-to-global mutation is killed by
//! five of six.

mod common;

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn verdicts(script: &str) -> Vec<String> {
    let commands = parse(script).expect("script should parse");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("script should execute")
        .into_iter()
        .filter(|o| matches!(o.as_str(), "sat" | "unsat" | "unknown"))
        .collect()
}

/// Two MUTUALLY CONTRADICTORY assumptions, asked in sequence, must both be `sat`.
///
/// `x` is a normal Float16. Assuming `x < 0` is satisfiable; so is assuming
/// `x > 0`. They cannot both hold at once, so if the first assumption survived
/// into the second query the second would be `unsat` — which is precisely the
/// signature of an assumption that leaked into persistent state.
#[test]
#[timeout(30_000)]
fn an_fp_assumption_does_not_constrain_the_next_query() {
    let out = verdicts(
        r#"
        (set-logic QF_BVFP)
        (declare-const x (_ FloatingPoint 5 11))
        (assert (fp.isNormal x))
        (check-sat-assuming ((fp.lt x ((_ to_fp 5 11) RNE 0.0))))
        (check-sat-assuming ((fp.gt x ((_ to_fp 5 11) RNE 0.0))))
        (check-sat)
        "#,
    );

    assert_eq!(out.len(), 3, "expected three verdicts, got {out:?}");
    assert_eq!(
        out[0], "sat",
        "a normal Float16 can be negative; if this is not `sat` the fixture is \
         broken and the rest proves nothing"
    );
    assert_eq!(
        out[1], "sat",
        "a normal Float16 can be positive. `unsat` here means the FIRST \
         assumption (x < 0) was still constraining the solver — an assumption \
         leaked out of its query"
    );
    assert_eq!(
        out[2], "sat",
        "with no assumption at all the base problem is satisfiable. `unsat` means \
         one or both assumptions leaked into the unconstrained query"
    );
}

/// An assumption that makes a query UNSAT must not poison the base problem.
///
/// The base is satisfiable; assuming `x` is both normal and NaN is not. The
/// following plain `check-sat` must still be `sat`. A stateful lane that
/// activated the contradictory assumption permanently would answer `unsat` here
/// forever after.
#[test]
#[timeout(30_000)]
fn an_unsat_fp_assumption_does_not_poison_later_queries() {
    let out = verdicts(
        r#"
        (set-logic QF_BVFP)
        (declare-const x (_ FloatingPoint 5 11))
        (assert (fp.isNormal x))
        (check-sat-assuming ((fp.isNaN x)))
        (check-sat)
        (check-sat-assuming ((fp.isNormal x)))
        "#,
    );

    assert_eq!(out.len(), 3, "expected three verdicts, got {out:?}");
    assert_eq!(
        out[0], "unsat",
        "a value cannot be both normal and NaN; if this is not `unsat` the \
         assumption is not reaching the solver and the test proves nothing"
    );
    assert_eq!(
        out[1], "sat",
        "the base problem alone is satisfiable. `unsat` means the contradictory \
         assumption was activated permanently instead of scoped to its query"
    );
    assert_eq!(
        out[2], "sat",
        "re-asserting what the base already says is satisfiable"
    );
}
