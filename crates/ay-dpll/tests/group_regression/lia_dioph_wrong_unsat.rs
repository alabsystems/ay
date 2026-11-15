// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! D2, D3 and A-UFA-g6-div0 of the 2026-09-23 differential hunt, end to end
//! through the executor in both postures.
//!
//! - D2 (`sat_lia_dioph_fold_cache_*`): Diophantine caches built on a folded
//!   branch-and-bound pin outlived the pop of the pin (`ay-lia/src/dioph_cache.rs`).
//! - D3 (`sat_lia_dioph_expansion_cap_*`): the 100-pop substitution expansion
//!   cap returned a partial sum whose GCD gave a false modulus
//!   (`ay-lia/src/dioph/expansion.rs`).
//! - `sat_lia_modular_unique_window_*`: a modular unique-value conflict that
//!   cited only the true-valued asserted literals (`ay-lia/src/modular_bounds.rs`).
//! - `sat_uflia_shared_modular_window_branch`: a modular conflict whose bound
//!   window rests on a shared EUF equality must cite that equality's reason,
//!   or refuting the `a = b` branch also discards the satisfiable `a = c` one
//!   (`ay-lia/src/modular_bounds.rs`, `modular_cached_conflict_reasons`).
//! - A-UFA-g6-div0 (`unsat_uflia_div0_reconfirm_*`): the certification
//!   re-solve compacted an arena whose zero-divisor variable names spell term
//!   ids, and the nested solve decoded a stale one (a panic).
//!
//! The files live in `benchmarks/smt/wrong-verdict/` and are rows of
//! `scripts/z3_parity_reproducers.sh`. For the satisfiable files `unknown` is
//! a completeness loss, reported but not wrong; `unsat` is the regression.

use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn solve(input: &str, shed_proof_cycle: bool) -> String {
    let commands = parse(input).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = Executor::new();
    exec.set_competition_mode(shed_proof_cycle);
    if !shed_proof_cycle {
        // Match the CLI's synthesized-default proof posture. Without this,
        // certification regressions can pass without running the guard at all.
        exec.set_best_effort_produce_proofs(1_000_000);
    }
    exec.set_timeout(Some(Duration::from_secs(30)));
    exec.set_memory_limit(Some(8 << 30));
    let outputs = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}"));
    assert_ne!(
        exec.get_reason_unknown(),
        Some(ay_dpll::UnknownReason::InternalError),
        "an internal solver error is not an admissible Unknown"
    );
    outputs.last().cloned().unwrap_or_default()
}

macro_rules! never_unsat {
    ($test:ident, $file:literal) => {
        #[test]
        #[timeout(180_000)]
        fn $test() {
            let input = include_str!(concat!(
                "../../../../benchmarks/smt/wrong-verdict/",
                $file,
                ".smt2"
            ));
            for shed in [false, true] {
                let verdict = solve(input, shed);
                assert!(
                    matches!(verdict.as_str(), "sat" | "unknown"),
                    "{} (shed_proof_cycle={shed}) is satisfiable (z3 5.1.0: sat), got {verdict:?}",
                    $file
                );
            }
        }
    };
}

never_unsat!(
    d2_fold_cache_fib_k06_01_is_never_unsat,
    "sat_lia_dioph_fold_cache_fib_k06_01"
);
never_unsat!(
    d3_expansion_cap_pbig_21_00085_is_never_unsat,
    "sat_lia_dioph_expansion_cap_pbig_21_00085"
);
never_unsat!(
    d3_expansion_cap_big_11_00375_is_never_unsat,
    "sat_lia_dioph_expansion_cap_big_11_00375"
);
// Found by this repair's measurement: a modular conflict that dropped the
// negated atoms its bound window rested on (not in the ledger of main
// 6818b5d067, where this file answered `sat`/`unknown`).
never_unsat!(
    modular_unique_window_puniq_31_00276_is_never_unsat,
    "sat_lia_modular_unique_window_puniq_31_00276"
);

#[test]
#[timeout(180_000)]
fn g6_div0_reconfirm_does_not_abort() {
    let input = include_str!(
        "../../../../benchmarks/smt/wrong-verdict/unsat_uflia_div0_reconfirm_g6_100000.smt2"
    );
    for shed in [false, true] {
        let commands = parse(input).unwrap_or_else(|err| panic!("parse failed: {err}"));
        let mut exec = Executor::new();
        exec.set_competition_mode(shed);
        if !shed {
            exec.set_best_effort_produce_proofs(1_000_000);
        }
        exec.set_timeout(Some(Duration::from_secs(30)));
        exec.set_memory_limit(Some(8 << 30));
        let result =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| exec.execute_all(&commands)));
        let outputs = result
            .unwrap_or_else(|_| panic!("g6_100000 (shed_proof_cycle={shed}) panicked"))
            .unwrap_or_else(|err| panic!("execution failed: {err}"));
        assert_ne!(
            exec.get_reason_unknown(),
            Some(ay_dpll::UnknownReason::InternalError),
            "g6_100000 (shed_proof_cycle={shed}) masked an internal solver error"
        );
        let verdict = outputs.last().cloned().unwrap_or_default();
        assert!(
            matches!(verdict.as_str(), "unsat" | "unknown"),
            "g6_100000 (shed_proof_cycle={shed}) is unsatisfiable (z3 5.1.0: unsat), got {verdict:?}"
        );
    }
}

/// Shared EUF equality can create a modularly inconsistent LRA window.
/// Refuting that branch must not discard the other, satisfiable branch.
#[test]
#[timeout(180_000)]
fn shared_modular_window_keeps_the_other_branch_sat() {
    let input = include_str!(
        "../../../../benchmarks/smt/wrong-verdict/sat_uflia_shared_modular_window_branch.smt2"
    );
    let commands = parse(input).unwrap_or_else(|err| panic!("parse failed: {err}"));
    for shed in [false, true] {
        let mut exec = Executor::new();
        exec.set_competition_mode(shed);
        exec.set_timeout(Some(Duration::from_secs(10)));
        exec.set_memory_limit(Some(8 << 30));
        let outputs = exec
            .execute_all(&commands)
            .unwrap_or_else(|err| panic!("execution failed: {err}"));
        assert_eq!(
            outputs,
            ["unsat", "sat", "sat", "sat"],
            "the alternate branch has y=38, f(a)=f(c)=154, f(b)=151; \
             shed_proof_cycle={shed}"
        );
    }
}
