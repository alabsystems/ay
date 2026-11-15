// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Public binary128 integration: a complete asserted FP witness, not just a
//! Boolean solve followed by data-only decoding of a wide literal.

use super::*;
use num_rational::BigRational;

const BITS: u128 = 0x3fff_8000_0000_0000_0000_0000_0000_0001;
const FRACTION: u128 = (1u128 << 111) + 1;

#[derive(Clone, Copy, Debug)]
enum Spelling {
    Constructor,
    Reinterpret,
}

fn fp_literal(solver: &mut Solver, spelling: Spelling, bits: u128) -> Term {
    match spelling {
        Spelling::Constructor => {
            let sign = solver
                .try_bv_const_bigint(&BigInt::from(bits >> 127), 1)
                .unwrap();
            let exponent = solver
                .try_bv_const_bigint(&BigInt::from((bits >> 112) & 0x7fff), 15)
                .unwrap();
            let fraction = solver
                .try_bv_const_bigint(&BigInt::from(bits & ((1u128 << 112) - 1)), 112)
                .unwrap();
            solver
                .try_fp_from_bvs(sign, exponent, fraction, 15, 113)
                .unwrap()
        }
        Spelling::Reinterpret => {
            let source = solver
                .try_bv_const_bigint(&BigInt::from(bits), 128)
                .unwrap();
            solver.try_bv_to_fp_reinterpret(source, 15, 113).unwrap()
        }
    }
}

fn assert_quad(value: &ModelValue, exponent: u64, fraction: u128) {
    assert!(
        matches!(value, ModelValue::FloatingPointWide { .. }),
        "exact quad field representation: {value:?}"
    );
    assert_eq!(
        value.try_fp_wide().unwrap(),
        (false, exponent, fraction, 15, 113)
    );
    assert_eq!(
        value.as_fp_wide(),
        Some((false, exponent, fraction, 15, 113))
    );
    assert!(
        value.as_fp().is_none(),
        "this fraction cannot be narrowed to u64"
    );
    assert!(matches!(
        value.try_fp(),
        Err(SolverError::ModelValueMismatch { .. })
    ));
}

fn assert_bits(value: &ModelValue, expected: u128) {
    assert_eq!(
        value,
        &ModelValue::BitVec {
            value: BigInt::from(expected),
            width: 128
        }
    );
}

fn assert_confirmed(solver: &mut Solver) {
    let details = solver.check_sat_with_details();
    assert_eq!(
        details.result,
        SolveResult::Sat,
        "full FP query: {details:?}"
    );
    assert!(
        details.verification.sat_model_validated,
        "the original FP assertions must be validated"
    );
    assert!(solver.try_get_model_for_consumer().is_ok());
}

fn assert_parsed_named_witness(spelling: Spelling) {
    let literal = match spelling {
        Spelling::Constructor => format!("(fp #b0 #b011111111111111 #x{FRACTION:028x})"),
        Spelling::Reinterpret => format!("((_ to_fp 15 113) #x{BITS:032x})"),
    };
    let mut solver = Solver::new(Logic::QfBvfp);
    solver
        .parse_smtlib2(&format!(
            "(declare-const quad_x (_ FloatingPoint 15 113))
             (assert (= quad_x {literal}))
             (assert (fp.isNormal quad_x))
             (assert (= (fp.to_ieee_bv quad_x) #x{BITS:032x}))"
        ))
        .unwrap();
    assert_confirmed(&mut solver);
    let values = solver.try_get_named_values(&["quad_x", "quad_x"]).unwrap();
    assert_eq!(values.len(), 2);
    for value in &values {
        assert_quad(value, 0x3fff, FRACTION);
    }
    assert_eq!(values[0], values[1]);
    let accepted = solver.try_get_model_for_consumer().unwrap();
    assert_quad(
        &accepted.model().value_by_name("quad_x").unwrap(),
        0x3fff,
        FRACTION,
    );
    assert!(solver.try_get_named_values(&["quad_x", "missing"]).is_err());
    solver.parse_smtlib2("(assert false)").unwrap();
    assert!(solver.try_get_named_values(&["quad_x"]).is_err());
}

fn assert_fresh_post_sat_literal_reads() {
    let mut solver = Solver::new(Logic::QfBvfp);
    // This is only a fresh-read control. The separately asserted FP witnesses
    // above provide solve authority; a Boolean-only SAT is not counted as that.
    let truth = solver.bool_const(true);
    solver.assert_term(truth);
    assert_confirmed(&mut solver);
    let constructor = fp_literal(&mut solver, Spelling::Constructor, BITS);
    let reinterpret = fp_literal(&mut solver, Spelling::Reinterpret, BITS);
    let constructor_bits = solver.try_fp_to_ieee_bv(constructor).unwrap();
    let reinterpret_bits = solver.try_fp_to_ieee_bv(reinterpret).unwrap();
    let values = solver
        .try_get_values(&[constructor, reinterpret, constructor_bits, reinterpret_bits])
        .unwrap();
    assert_eq!(values.len(), 4);
    for value in &values[..2] {
        assert_quad(value, 0x3fff, FRACTION);
    }
    for value in &values[2..] {
        assert_bits(value, BITS);
    }
}

#[test]
fn binary128_full_witness_constructor_and_bitcast_getters_are_exact() {
    for spelling in [Spelling::Constructor, Spelling::Reinterpret] {
        let mut solver = Solver::new(Logic::QfBvfp);
        let x = solver.declare_const("quad_x", Sort::FloatingPoint(15, 113));
        let literal = fp_literal(&mut solver, spelling, BITS);
        let equality = solver.eq(x, literal);
        solver.assert_term(equality);
        let normal = solver.try_fp_is_normal(x).unwrap();
        solver.assert_term(normal);
        let ieee = solver.try_fp_to_ieee_bv(x).unwrap();
        let expected = solver
            .try_bv_const_bigint(&BigInt::from(BITS), 128)
            .unwrap();
        let exact_bits = solver.eq(ieee, expected);
        solver.assert_term(exact_bits);
        assert_confirmed(&mut solver);

        // The opposite spelling is requested after the full FP solve. Both
        // getters must preserve all 112 fraction bits, including the last bit.
        let opposite = match spelling {
            Spelling::Constructor => Spelling::Reinterpret,
            Spelling::Reinterpret => Spelling::Constructor,
        };
        let other = fp_literal(&mut solver, opposite, BITS);
        let other_ieee = solver.try_fp_to_ieee_bv(other).unwrap();
        let to_real = solver.try_fp_to_real(x).unwrap();
        let actual = solver
            .try_get_values(&[x, literal, other, ieee, other_ieee, to_real])
            .unwrap();
        assert_eq!(actual.len(), 6);
        for value in &actual[..3] {
            assert_quad(value, 0x3fff, FRACTION);
        }
        for value in &actual[3..5] {
            assert_bits(value, BITS);
        }
        assert_eq!(
            actual[5],
            ModelValue::Real(BigRational::new(
                BigInt::from(3) * (BigInt::from(1) << 111usize) + 1,
                BigInt::from(1) << 112usize,
            ))
        );
        assert_quad(&solver.try_get_value(x).unwrap(), 0x3fff, FRACTION);
        let accepted = solver.try_get_model_for_consumer().unwrap();
        assert_quad(accepted.model().fp_val("quad_x").unwrap(), 0x3fff, FRACTION);
        let model_map = solver.try_get_model_map().unwrap();
        assert_quad(&model_map["quad_x"], 0x3fff, FRACTION);
        assert_quad(
            &accepted.model().value_by_name("quad_x").unwrap(),
            0x3fff,
            FRACTION,
        );
        // Source-name requests deliberately exclude native builder aliases.
        // Exercise their positive path on the same fully constrained witness
        // in a separate parsed solver, without inventing declaration authority.
        assert!(matches!(
            solver.try_get_named_values(&["quad_x"]),
            Err(SolverError::InvalidArgument { .. })
        ));
        assert_parsed_named_witness(spelling);
    }
    assert_fresh_post_sat_literal_reads();
}

#[test]
fn binary128_exact_ieee_roundtrip_refutation_is_unsat() {
    for spelling in [Spelling::Constructor, Spelling::Reinterpret] {
        let mut solver = Solver::new(Logic::QfBvfp);
        let x = solver.declare_const("quad_x", Sort::FloatingPoint(15, 113));
        let literal = fp_literal(&mut solver, spelling, BITS);
        let equality = solver.eq(x, literal);
        solver.assert_term(equality);
        let roundtrip = solver.try_fp_to_ieee_bv(x).unwrap();
        let expected = solver
            .try_bv_const_bigint(&BigInt::from(BITS), 128)
            .unwrap();
        let exact = solver.eq(roundtrip, expected);
        let wrong = solver.not(exact);
        solver.assert_term(wrong);
        assert_eq!(solver.check_sat(), SolveResult::unsat());
        assert!(solver.try_get_value(x).is_err());
        assert!(solver.try_get_model_for_consumer().is_err());
    }
}

#[test]
fn binary128_rounded_division_returns_a_validated_exact_witness() {
    // 1/3 has biased exponent 0x3ffd and stored fraction floor(2^112/3).
    // The remainder is 1/3 ulp: RNE rounds down, RTP rounds up by one bit.
    let floor = ((1u128 << 112) - 1) / 3;
    for (mode, fraction) in [("RNE", floor), ("RTP", floor + 1)] {
        let mut solver = Solver::new(Logic::QfBvfp);
        let one = fp_literal(&mut solver, Spelling::Constructor, 0x3fffu128 << 112);
        let three = fp_literal(
            &mut solver,
            Spelling::Constructor,
            (0x4000u128 << 112) | (1u128 << 111),
        );
        let rounding = solver.try_fp_rounding_mode(mode).unwrap();
        let division = solver.try_fp_div(rounding, one, three).unwrap();
        let result = solver.declare_const("quad_result", Sort::FloatingPoint(15, 113));
        let equality = solver.eq(result, division);
        solver.assert_term(equality);
        let normal = solver.try_fp_is_normal(result).unwrap();
        solver.assert_term(normal);
        assert_confirmed(&mut solver);

        let ieee = solver.try_fp_to_ieee_bv(result).unwrap();
        let actual = solver.try_get_values(&[result, division, ieee]).unwrap();
        assert_eq!(actual.len(), 3);
        assert_quad(&actual[0], 0x3ffd, fraction);
        assert_quad(&actual[1], 0x3ffd, fraction);
        assert_bits(&actual[2], (0x3ffdu128 << 112) | fraction);
        let accepted = solver.try_get_model_for_consumer().unwrap();
        assert_quad(
            accepted.model().fp_val("quad_result").unwrap(),
            0x3ffd,
            fraction,
        );
    }
}

#[test]
fn malformed_fields_refuse_and_representable_custom_model_data_can_solve() {
    let mut solver = Solver::new(Logic::QfBvfp);
    let sign = solver.try_bv_const_bigint(&BigInt::from(0), 1).unwrap();
    let exponent = solver
        .try_bv_const_bigint(&BigInt::from(0x3fff), 15)
        .unwrap();
    let fraction = solver
        .try_bv_const_bigint(&BigInt::from(FRACTION), 112)
        .unwrap();
    for (bad_sign, bad_exponent, bad_fraction) in [
        (
            solver.try_bv_const_bigint(&BigInt::from(0), 2).unwrap(),
            exponent,
            fraction,
        ),
        (
            sign,
            solver.try_bv_const_bigint(&BigInt::from(0), 16).unwrap(),
            fraction,
        ),
        (
            sign,
            exponent,
            solver.try_bv_const_bigint(&BigInt::from(0), 113).unwrap(),
        ),
    ] {
        assert!(matches!(
            solver.try_fp_from_bvs(bad_sign, bad_exponent, bad_fraction, 15, 113),
            Err(SolverError::InvalidArgument { .. })
        ));
    }
    let narrow = solver.try_bv_const_bigint(&BigInt::from(0), 127).unwrap();
    assert!(matches!(
        solver.try_bv_to_fp_reinterpret(narrow, 15, 113),
        Err(SolverError::InvalidArgument { .. })
    ));
    assert!(matches!(
        solver.try_fp_from_bvs(sign, exponent, fraction, 0, 113),
        Err(SolverError::InvalidArgument { .. })
    ));

    let sort = Sort::FloatingPoint(15, 113);
    let valid = "(fp #b0 #b011111111111111 #x8000000000000000000000000001)";
    let decoded = ModelValue::decode_typed_literals(&[(valid, &sort)]).unwrap();
    assert_quad(&decoded[0], 0x3fff, FRACTION);
    for bad in [
        "(fp #b00 #b011111111111111 #x8000000000000000000000000001)",
        "(fp #b0 #b0011111111111111 #x8000000000000000000000000001)",
        "(fp #b0 #b011111111111111 #x18000000000000000000000000001)",
        "(_ +zero 15 114)",
    ] {
        assert!(ModelValue::decode_typed_literals(&[(bad, &sort)]).is_err());
    }

    // All 128 stored fraction bits fit the checked concrete model carrier.
    let representation_only = Sort::FloatingPoint(15, 129);
    let text = "(fp #b0 #b011111111111111 #xffffffffffffffffffffffffffffffff)";
    let decoded = ModelValue::decode_typed_literals(&[(text, &representation_only)]).unwrap();
    assert_eq!(
        decoded[0].try_fp_wide().unwrap(),
        (false, 0x3fff, u128::MAX, 15, 129)
    );
    let _unused = solver.declare_const("represented_neighbor", representation_only);
    assert_eq!(solver.check_sat(), SolveResult::Sat);
    assert!(solver.try_get_model_for_consumer().is_ok());
}
