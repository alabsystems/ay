// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The differential gate's uf-arith `g6_100000/g6_100167` (QF_UFLIA, unsat),
//! end to end through the executor in both postures.
//!
//! The only failure of main's full-budget differential gate on 243d322e31 and
//! b288f5e6f5: the default posture PANICKED during UNSAT certification
//! (`index out of bounds: the len is 77 but the index is 80` at
//! `TermStore::mk_eq_depth_mode <- mod_div_elim::eliminate_int_mod_div_impl
//! <- ... <- discharge_trust_steps_for_certification`), which the CLI
//! publishes as `unknown` / "internal solver error".
//!
//! The forged-UNSAT guard re-solves the authored problem on a cloned context
//! whose arena it compacts. Compaction relabels every held `TermId` but not
//! the digits of `__ay_zerodiv_div_{dividend}`, a name `mod_div_elim` parses
//! back into a `TermId`; the nested solve decoded the stale index. The
//! A-UFA-g6-div0 fix (fbb541002a) vetoed this in the step-(4) reconfirm
//! caller only, and the forged guard's arena rebuild (80fe296b26) arrived
//! without it. Every ay-dpll caller now reaches the compaction through
//! `compact_derived_arena`, which applies the veto.
//!
//! A panic propagates out of `execute_all` and fails this test at the site
//! that fired. `unsat` is the verdict (z3 5.1.0 agrees, and the witness file's
//! header derives it by hand); an honest `unknown` would be a completeness
//! loss, `sat` or an abort the regression.

use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

const G6_100167: &str =
    include_str!("../../../../benchmarks/smt/abort/unsat_uflia_div0_forged_guard_g6_100167.smt2");

#[test]
#[timeout(180_000)]
fn g6_100167_forged_guard_certification_does_not_abort() {
    for shed_proof_cycle in [false, true] {
        let commands = parse(G6_100167).unwrap_or_else(|err| panic!("parse failed: {err}"));
        let mut exec = Executor::new();
        exec.set_competition_mode(shed_proof_cycle);
        exec.set_timeout(Some(Duration::from_secs(30)));
        exec.set_memory_limit(Some(8 << 30));
        let outputs = exec
            .execute_all(&commands)
            .unwrap_or_else(|err| panic!("execution failed: {err}"));
        let verdict = outputs
            .iter()
            .rev()
            .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
            .cloned()
            .unwrap_or_default();
        assert!(
            verdict == "unsat" || verdict == "unknown",
            "g6_100167 (shed_proof_cycle={shed_proof_cycle}) is unsatisfiable \
             (z3 5.1.0: unsat); AY answered {verdict:?}"
        );
    }
}
