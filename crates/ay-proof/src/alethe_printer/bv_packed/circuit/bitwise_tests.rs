// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::tests::{certificate, original, TestResult};
use super::*;

fn problem(width: u32, value: &str, expected: &str) -> String {
    format!(
        "(set-logic QF_BV)
        (declare-const a (_ BitVec {width}))
        (declare-const b (_ BitVec {width}))
        (declare-const wrong (_ BitVec {width}))
        (assert (not (= {value} {expected}))) (check-sat)"
    )
}

#[test]
fn checked_bitwise_reductions_preserve_constants_repeated_bits_and_source_values() -> TestResult {
    for width in [1, 9, 64, 128] {
        let zero = format!("(_ bv0 {width})");
        let ones = (num_bigint::BigInt::from(1) << width) - 1;
        let ones = format!("(_ bv{ones} {width})");
        for (name, op, rhs, expected) in [
            ("or-zero", "bvor", zero.as_str(), "a"),
            ("and-ones", "bvand", ones.as_str(), "a"),
            ("or-repeat", "bvor", "a", "a"),
            ("and-repeat", "bvand", "a", "a"),
            ("or-ones", "bvor", ones.as_str(), ones.as_str()),
            ("and-zero", "bvand", zero.as_str(), zero.as_str()),
        ] {
            let value = format!("({op} a {rhs})");
            certificate(
                &format!("bitwise-reduction-{name}-{width}"),
                &problem(width, &value, expected),
            )?;
            let (context, _, negative) = original(&problem(width, &value, "wrong"))?;
            assert!(AlethePrinter::new(&context.terms)
                .format_bv_circuit_refutation(ProofId(7), &[negative])
                .is_none());
        }
    }
    Ok(())
}

#[test]
fn nonconstant_bitwise_relations_keep_their_cnf_derivations() -> TestResult {
    for width in [1, 9, 64, 128] {
        for (outer, inner) in [("bvor", "bvand"), ("bvand", "bvor")] {
            let value = format!("({outer} a ({inner} a b))");
            certificate(
                &format!("bitwise-absorption-{outer}-{width}"),
                &problem(width, &value, "a"),
            )?;
            let (context, _, negative) = original(&problem(width, &value, "b"))?;
            assert!(AlethePrinter::new(&context.terms)
                .format_bv_circuit_refutation(ProofId(7), &[negative])
                .is_none());
        }
    }
    Ok(())
}
