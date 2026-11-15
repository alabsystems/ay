// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LNH symmetry breaking published WRONG `unsat` in both postures (found
//! 2026-10-02 by the E13 audit; reproduced on main `4ebd66a925`).
//! `lnh_symmetry::find_domain` accepted compound terms (`(f a_i)`, `(hd l_i)`,
//! `(top (left s_i))`) and nullary datatype constructors as interchangeable
//! domain elements; the least-index and lex-leader clauses then excluded real
//! models. z3 5.1.0 answers `sat` on every fixture, and AY answers `sat` with
//! the pass off. The default posture admitted the wrong `unsat` as
//! `discharged-trust`: its one hole was the bogus symmetry fact, and the
//! corroborating re-solve ran the same pass.
//!
//! Every pin states only what the defect denied: never `unsat`. Each runs in
//! the default posture and in the proof-free competition posture.

use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn solve(src: &str, competition: bool) -> Vec<String> {
    let commands = parse(src).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = Executor::new();
    exec.set_competition_mode(competition);
    exec.set_timeout(Some(Duration::from_secs(20)));
    exec.set_memory_limit(Some(8 << 30));
    exec.execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}"))
}

fn assert_never_unsat(name: &str, src: &str) {
    for competition in [false, true] {
        let outputs = solve(src, competition);
        assert!(
            !outputs.iter().any(|line| line == "unsat"),
            "{name} (competition={competition}): z3 5.1.0 answers sat; AY must never answer unsat: {outputs:?}"
        );
    }
}

macro_rules! fixture {
    ($test:ident, $file:literal) => {
        #[test]
        #[timeout(120_000)]
        fn $test() {
            assert_never_unsat(
                $file,
                include_str!(concat!("lnh_wrong_unsat_fixtures/", $file)),
            );
        }
    };
}

fixture!(lnh_compound_domain_dt, "l01_lnh_compound_domain.smt2");
fixture!(
    lnh_compound_domain_pure_uf,
    "l02_lnh_compound_domain_uf.smt2"
);
fixture!(lnh_lex_leader_compound, "l03_lnh_lexleader_compound.smt2");
fixture!(
    lnh_least_index_list_domain,
    "l04_lnh_leastidx_list_domain.smt2"
);
fixture!(lnh_blocksworld_shape, "l06_lnh_blocksworld_shape.smt2");
