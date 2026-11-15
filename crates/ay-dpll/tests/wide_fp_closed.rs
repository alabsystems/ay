// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Public simplify retains exact fields and the original checked obligation;
//! the simplified result must never replace its proof premises.

use ay_dpll::api::{Logic, Solver, SolverConfig};
use num_bigint::BigInt;
use num_traits::One;

#[test]
fn public_wide_pins_keep_original_scope_with_repeated_definitions() {
    let input =
        include_str!("../../ay-model-check/tests/fixtures/wide-fp-remainder-odd-unsat.smt2");
    for (inconsistent, repetitions) in [
        (true, 128),
        (true, 1),
        (false, 1),
        (true, 2),
        (false, 2),
        (false, 128),
    ] {
        let mut script = input.replace("(check-sat)", "");
        if !inconsistent {
            script = script.replace("(_ +zero 8 200)", "((_ to_fp 8 200) RNE (- 1))");
        }
        let definition = script
            .lines()
            .find(|line| line.starts_with("(assert "))
            .unwrap()
            .to_owned();
        for _ in 1..repetitions {
            script.push('\n');
            script.push_str(&definition);
        }
        let config = SolverConfig::default()
            .with_timeout(std::time::Duration::from_secs(5))
            .with_memory_limit(256 * 1024 * 1024);
        let mut solver = Solver::try_new_with_config(Logic::QfFp, config).unwrap();
        solver.set_produce_proofs(true);
        solver.parse_smtlib2(&script).unwrap();
        let authored = solver.assertions();
        let result = solver.check_sat();
        if inconsistent {
            assert!(
                result.is_unsat(),
                "repetitions={repetitions}: {result:?}; {:?}; {:?}; {:?}",
                solver.unknown_reason(),
                solver.executor_error(),
                solver.reason_unknown_smtlib()
            );
            let bundle = solver.export_last_unsat_bundle().unwrap();
            assert!(ay_proof::re_check_bundle_strict(&bundle)
                .unwrap()
                .quality
                .is_complete());
            let mut unpinned = bundle;
            // The remainder claim alone is satisfiable. The original pin
            // premises cannot disappear from a claimed UNSAT obligation.
            unpinned.obligation_assertions = vec![authored[2].id()];
            assert!(ay_proof::re_check_bundle_strict(&unpinned).is_err());
        } else {
            assert!(result.is_sat(), "{result:?}; {:?}", solver.unknown_reason());
        }
        assert_eq!(solver.assertions(), authored);
    }
}

#[test]
fn wide_closed_public_simplify_retains_the_high_fraction_bit() {
    for sb in [66, 130, 256] {
        let mut solver = Solver::new(Logic::QfFp);
        let one_and_half = (BigInt::one() << (sb - 1)) | (BigInt::one() << (sb - 2));
        let x = solver
            .try_fp_const_from_bits_bigint(&one_and_half, 2, sb)
            .unwrap();
        let rm = solver.try_fp_rounding_mode("RNE").unwrap();
        let sum = solver.try_fp_add(rm, x, x).unwrap();
        let result = solver.simplify(sum);
        let decoded = solver
            .fp_numeral_decode(result)
            .expect("closed IEEE numeral");
        // Public introspection must retain the full declared field width.
        assert_eq!(decoded.eb, 2);
        assert_eq!(decoded.sb, sb);
        let bits = solver.try_fp_to_ieee_bv(result).unwrap();
        let bits = solver.simplify(bits);
        let expected = (BigInt::from(2) << (sb - 1)) | (BigInt::one() << (sb - 2));
        let expected = solver.try_bv_const_bigint(&expected, sb + 2).unwrap();
        assert_eq!(bits, expected);
    }
}

#[test]
fn wide_closed_oracle_fixture_keeps_original_checked_proof_obligation() {
    let config = SolverConfig::default()
        .with_timeout(std::time::Duration::from_secs(5))
        .with_memory_limit(256 * 1024 * 1024);
    let mut solver = Solver::try_new_with_config(Logic::QfFp, config).unwrap();
    solver.set_produce_proofs(true);
    let input = include_str!("../../ay-theories/fp/tests/wide_precision.smt2");
    // Parsing the command does not execute check-sat through this API.
    solver.parse_smtlib2(input).unwrap();
    let authored = solver.assertions();
    assert_eq!(authored.len(), 1);
    let folded = solver.simplify(authored[0]);
    assert_eq!(folded, solver.bool_const(false));
    assert_eq!(
        solver.assertions(),
        authored,
        "simplify must retain authored roots"
    );
    // The independent ground kernel now supports these 66/130-bit formats.
    // Check the ORIGINAL obligation, including its wide rounded arithmetic,
    // rather than freezing the old refusal or accepting an assumed `false`.
    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "{result:?}; {:?}",
        solver.unknown_reason()
    );
    assert_eq!(solver.assertions(), authored);
    // Native checking is independent of textual Alethe export. The pinned
    // external reader has no FloatingPoint sort grammar; do not turn that
    // honest transport refusal into a requirement to publish an artifact.
    let bundle = solver.export_last_unsat_bundle().unwrap();
    assert_eq!(
        bundle.obligation_assertions,
        authored.iter().map(|term| term.id()).collect::<Vec<_>>()
    );
    assert!(ay_proof::re_check_bundle_strict(&bundle)
        .unwrap()
        .quality
        .is_complete());
    let mut retargeted = bundle;
    retargeted.obligation_assertions = vec![folded.id()];
    assert!(
        ay_proof::re_check_bundle_strict(&retargeted).is_err(),
        "a simplified false cannot replace the proof's original assumption"
    );
}
