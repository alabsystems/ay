// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Exercise public emission and serialized replay, including the IR Bool carrier.
use ay_dpll::{ApiSolver as Solver, ApiSort as Sort, Logic};
use num_bigint::BigInt;

#[test]
fn wide_bitvector_queries_emit_serialized_zero_trust_refutations() {
    let mut checked_queries = 0;
    for width in [64u32, 65, 96, 127, 128] {
        for literal in [
            (BigInt::from(1) << width) - 1,
            (BigInt::from(1) << (width - 1)) + 5,
            -(BigInt::from(1) << (width - 1)),
        ] {
            let mut solver = Solver::new(Logic::QfBv);
            solver.set_produce_proofs(true);
            let x = solver
                .try_declare_const("wide_input", Sort::bitvec(width))
                .unwrap();
            let literal = solver.try_bv_const_bigint(&literal, width).unwrap();
            let changed = solver.try_bvxor(x, literal).unwrap();
            let mask = solver.try_bv_const_u64(15, width).unwrap();
            let low = solver.try_bvand(changed, mask).unwrap();
            let bound = solver.try_bv_const_u64(16, width).unwrap();
            let within = solver.try_bvult(low, bound).unwrap();
            let one = solver.try_bv_const_u64(1, 1).unwrap();
            let zero = solver.try_bv_const_u64(0, 1).unwrap();
            let carrier = solver.try_ite(within, one, zero).unwrap();
            let holds = solver.try_eq(carrier, one).unwrap();
            let negated = solver.try_not(holds).unwrap();
            let goal = solver.try_render_term_canonical(negated).unwrap();
            assert!(
                !matches!(goal.trim(), "true" | "false"),
                "width {width}: vacuous goal {goal}"
            );
            solver.try_assert_term(negated).unwrap();
            assert!(solver.try_check_sat().unwrap().is_unsat(), "width {width}");
            let bundle = solver
                .export_last_unsat_bundle()
                .expect("public proof bundle");
            let bytes = serde_json::to_vec(&bundle).unwrap();
            let copied: ay_proof::SerializableProofBundle = serde_json::from_slice(&bytes).unwrap();
            let checked = ay_proof::re_check_bundle_strict(&copied)
                .unwrap_or_else(|error| panic!("width {width}: {error:?}"));
            assert_eq!(checked.quality.trust_count, 0);
            assert!(checked.quality.is_complete());
            assert_ne!(checked.assume_terms, [] as [ay_dpll::api::TermId; 0]);
            checked_queries += 1;
        }
    }
    assert_eq!(checked_queries, 15);
}
