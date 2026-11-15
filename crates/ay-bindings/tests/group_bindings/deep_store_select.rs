// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! R22's deep-store/read shape through the actual in-process bindings path.
//! Run these crash-sensitive controls in an isolated, resource-guarded test
//! process. They are decision/stack regressions, not consumer certification or
//! proof-cost measurements. The solver timeout does not bound preparation.

#![cfg(feature = "direct")]

use ay_bindings::execute_direct::{execute_typed_with_details, ExecuteTypedResult};
use ay_bindings::{AYProgram, Expr, Sort};

#[derive(Clone, Copy, Debug)]
enum Case {
    Contradiction,
    SatisfiableNeighbor,
}

fn run(case: Case) {
    std::thread::Builder::new()
        .name(format!("deep-store-{case:?}"))
        .stack_size(2 * 1024 * 1024)
        .spawn(move || {
            eprintln!("deep-store {case:?}: construct");
            let mut array = Expr::const_array(Sort::bitvec(64), Expr::bitvec_const(0, 32));
            for index in 0..16_384u32 {
                array = array.store(Expr::bitvec_const(index, 64), Expr::bitvec_const(index, 32));
            }
            // Read near the BOTTOM of the chain, not the latest write. Expr's
            // typed builder retains this Select/Store tree until translation.
            let read = array.select(Expr::bitvec_const(5, 64));
            let comparison = match case {
                Case::Contradiction => 5,
                Case::SatisfiableNeighbor => 6,
            };
            let mut program = AYProgram::qf_aufbv();
            program.set_option("timeout", "30000");
            program.assert(read.ne(Expr::bitvec_const(comparison, 32)));
            program.check_sat();
            eprintln!("deep-store {case:?}: execute_direct");
            let details = execute_typed_with_details(&program).unwrap();
            assert!(
                details.fallback.is_none(),
                "unexpected fallback: {details:?}"
            );
            assert!(
                details.degradation.is_none(),
                "degraded result: {details:?}"
            );
            assert!(details.solve_details.is_some());
            match (&details.result, case) {
                (ExecuteTypedResult::Verified, Case::Contradiction)
                | (ExecuteTypedResult::Counterexample(_), Case::SatisfiableNeighbor) => {}
                _ => panic!("wrong deep-store decision for {case:?}: {details:?}"),
            }
            eprintln!("deep-store {case:?}: cleanup");
            drop(details);
            drop(program);
            eprintln!("deep-store {case:?}: complete");
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn deep_bv_store_read_contradiction_completes_on_two_mib_thread() {
    run(Case::Contradiction);
}

#[test]
fn deep_bv_store_read_sat_neighbor_completes_on_two_mib_thread() {
    run(Case::SatisfiableNeighbor);
}
