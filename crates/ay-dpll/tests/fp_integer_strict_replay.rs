// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Public proof-producing FP saturation queries, including offline bundle replay.
use ay_dpll::{ApiSolver as Solver, ApiSort as Sort, Logic};

#[test]
fn saturating_fp_integer_queries_replay_without_trust() {
    let sources = [
        (5, 11, [0x7e00, 0x7c00, 0xfc00, 0x3f00, 0xbf00]),
        (
            8,
            24,
            [
                0x7fc0_0000,
                0x7f80_0000,
                0xff80_0000,
                0x3fe0_0000,
                0xbfe0_0000,
            ],
        ),
        (
            11,
            53,
            [
                0x7ff8_0000_0000_0000,
                0x7ff0_0000_0000_0000,
                0xfff0_0000_0000_0000,
                0x3ffc_0000_0000_0000,
                0xbffc_0000_0000_0000,
            ],
        ),
    ];
    let native = [f64::NAN, f64::INFINITY, f64::NEG_INFINITY, 1.75, -1.75];
    for (eb, sb, bits) in sources {
        for (bits, native) in bits.into_iter().zip(native) {
            for signed in [false, true] {
                let mut solver = Solver::new(Logic::QfFp);
                solver.set_produce_proofs(true);
                let literal = solver.try_fp_const_from_bits(bits, eb, sb).unwrap();
                let x = solver
                    .try_declare_const("x", Sort::FloatingPoint(eb, sb))
                    .unwrap();
                let pin = solver.try_eq(x, literal).unwrap();
                solver.try_assert_term(pin).unwrap();
                let rne = solver.try_fp_rounding_mode("RNE").unwrap();
                let wide = solver.try_fp_to_fp(rne, x, 11, 53).unwrap();
                let nan = solver.try_fp_is_nan(wide).unwrap();
                let zero = solver.try_bv_const_u64(0, 32).unwrap();
                let minimum = solver
                    .try_bv_const_u64(if signed { 0x8000_0000 } else { 0 }, 32)
                    .unwrap();
                let maximum = solver
                    .try_bv_const_u64(if signed { 0x7fff_ffff } else { 0xffff_ffff }, 32)
                    .unwrap();
                let lower = solver
                    .try_fp_const_from_bits(if signed { 0xc1e0_0000_0000_0000 } else { 0 }, 11, 53)
                    .unwrap();
                let upper = solver
                    .try_fp_const_from_bits(
                        if signed {
                            0x41e0_0000_0000_0000
                        } else {
                            0x41f0_0000_0000_0000
                        },
                        11,
                        53,
                    )
                    .unwrap();
                let low = solver.try_fp_lt(wide, lower).unwrap();
                let high = solver.try_fp_ge(wide, upper).unwrap();
                let rtz = solver.try_fp_rounding_mode("RTZ").unwrap();
                let converted = if signed {
                    solver.try_fp_to_sbv(rtz, wide, 32).unwrap()
                } else {
                    solver.try_fp_to_ubv(rtz, wide, 32).unwrap()
                };
                let clamped_high = solver.try_ite(high, maximum, converted).unwrap();
                let clamped = solver.try_ite(low, minimum, clamped_high).unwrap();
                let result = solver.try_ite(nan, zero, clamped).unwrap();
                let expected = if signed {
                    (native as i32) as u32
                } else {
                    native as u32
                };
                let expected = solver.try_bv_const_u64(u64::from(expected), 32).unwrap();
                let eq = solver.try_eq(result, expected).unwrap();
                let wrong = solver.try_not(eq).unwrap();
                solver.try_assert_term(wrong).unwrap();
                assert!(
                    solver.try_check_sat().unwrap().is_unsat(),
                    "({eb},{sb}) {native:?}, signed={signed}"
                );
                let bundle = solver.export_last_unsat_bundle().expect("proof bundle");
                let bytes = serde_json::to_vec(&bundle).unwrap();
                let copied: ay_proof::SerializableProofBundle =
                    serde_json::from_slice(&bytes).unwrap();
                let checked = ay_proof::re_check_bundle_strict(&copied).expect("offline replay");
                assert_eq!(checked.quality.trust_count, 0);
                assert!(!checked.assume_terms.is_empty());
            }
        }
    }
}
