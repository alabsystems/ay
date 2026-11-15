// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn interchange_to_fp_matches_indices_and_complete_bitstring_width() {
    positive(
        Symbol::indexed("to_fp", vec![8, 24]),
        &[6],
        Sort::FloatingPoint(8, 24),
    );
    for indices in [vec![], vec![8], vec![8, 23], vec![8, 24, 0]] {
        negative(
            Symbol::indexed("to_fp", indices),
            &[6],
            Sort::FloatingPoint(8, 24),
        );
    }
    for args in [&[][..], &[7], &[1], &[3], &[6, 6, 6]] {
        negative(
            Symbol::indexed("to_fp", vec![8, 24]),
            args,
            Sort::FloatingPoint(8, 24),
        );
    }
    negative(Symbol::named("to_fp"), &[6], Sort::FloatingPoint(8, 24));
}

#[test]
fn rounded_to_fp_supports_existing_fp_real_int_signed_bv_sources() {
    for source in [1, 2, 4, 5, 6, 7] {
        positive(
            Symbol::indexed("to_fp", vec![8, 24]),
            &[0, source],
            Sort::FloatingPoint(8, 24),
        );
    }
    for args in [[0, 3], [0, 8], [3, 1], [8, 1]] {
        negative(
            Symbol::indexed("to_fp", vec![8, 24]),
            &args,
            Sort::FloatingPoint(8, 24),
        );
    }
    negative(
        Symbol::indexed("to_fp", vec![11, 53]),
        &[0, 1],
        Sort::FloatingPoint(8, 24),
    );
    negative(Symbol::indexed("to_fp", vec![8, 24]), &[0, 1], bv(32));
}

#[test]
fn unsigned_to_fp_does_not_accept_signed_or_unrounded_overloads() {
    positive(
        Symbol::indexed("to_fp_unsigned", vec![8, 24]),
        &[0, 6],
        Sort::FloatingPoint(8, 24),
    );
    for args in [
        &[][..],
        &[6],
        &[0, 1],
        &[0, 4],
        &[0, 5],
        &[3, 6],
        &[0, 6, 6],
    ] {
        negative(
            Symbol::indexed("to_fp_unsigned", vec![8, 24]),
            args,
            Sort::FloatingPoint(8, 24),
        );
    }
    negative(
        Symbol::named("to_fp_unsigned"),
        &[0, 6],
        Sort::FloatingPoint(8, 24),
    );
}

#[test]
fn signed_and_unsigned_integer_results_match_nonzero_index_rm_and_fp_source() {
    for name in ["fp.to_ubv", "fp.to_sbv"] {
        positive(Symbol::indexed(name, vec![8]), &[0, 1], bv(8));
        positive(Symbol::indexed(name, vec![32]), &[0, 2], bv(32));
        for indices in [vec![], vec![0], vec![7], vec![8, 0]] {
            negative(Symbol::indexed(name, indices), &[0, 1], bv(8));
        }
        for args in [&[][..], &[1], &[8, 1], &[3, 1], &[0, 6], &[0, 1, 1]] {
            negative(Symbol::indexed(name, vec![8]), args, bv(8));
        }
        negative(Symbol::indexed(name, vec![8]), &[0, 1], Sort::Int);
        negative(Symbol::indexed(name, vec![0]), &[0, 1], bv(0));
        negative(Symbol::named(name), &[0, 1], bv(8));
    }
}

#[test]
fn checked_width_arithmetic_rejects_overflow_without_wrapping() {
    let mut values = fp_entries();
    values[1].1 = Sort::FloatingPoint(u32::MAX, 2);
    for (symbol, args, result) in [
        (Symbol::named("fp.to_ieee_bv"), ids(&[1]), bv(1)),
        (
            Symbol::indexed("to_fp", vec![u32::MAX, 2]),
            ids(&[6]),
            Sort::FloatingPoint(u32::MAX, 2),
        ),
    ] {
        assert!(matches!(
            run(&values, &symbol, &args, &result),
            Err(ProofCheckError::MalformedProofBundle { .. })
        ));
    }
}

#[test]
fn malformed_floating_formats_and_nonbuiltin_rm_sorts_are_not_accepted() {
    let mut values = fp_entries();
    for bad in [Sort::FloatingPoint(1, 24), Sort::FloatingPoint(8, 1)] {
        values[1].1 = bad.clone();
        assert!(matches!(
            run(&values, &Symbol::named("fp.add"), &ids(&[0, 1, 1]), &bad),
            Err(ProofCheckError::MalformedProofBundle { .. })
        ));
        assert!(matches!(
            run(
                &values,
                &Symbol::indexed("to_fp", vec![8, 24]),
                &ids(&[0, 1]),
                &Sort::FloatingPoint(8, 24)
            ),
            Err(ProofCheckError::MalformedProofBundle { .. })
        ));
    }
    values[1].1 = Sort::FloatingPoint(8, 24);
    for bad in [
        Sort::Datatype(ay_core::DatatypeSort::new("RoundingMode", vec![])),
        Sort::Uninterpreted("RoundingMode ".into()),
    ] {
        values[0].1 = bad;
        assert!(matches!(
            run(
                &values,
                &Symbol::named("fp.add"),
                &ids(&[0, 1, 1]),
                &Sort::FloatingPoint(8, 24)
            ),
            Err(ProofCheckError::MalformedProofBundle { .. })
        ));
    }
}

#[test]
fn stronger_native_builtin_checks_are_explicitly_not_legacy_uf_authentication() {
    let values = fp_entries();
    for name in ["fp.add", "RNE"] {
        let symbol = Symbol::named(name);
        assert!(crate::bundle::validate_app_signature(
            &values,
            values.len(),
            &symbol,
            &ids(&[3, 5]),
            &Sort::RegLan
        )
        .is_ok());
        assert!(matches!(
            run(&values, &symbol, &ids(&[3, 5]), &Sort::RegLan),
            Err(ProofCheckError::MalformedProofBundle { .. })
        ));
    }
    for name in [
        "RNE_like",
        "fp.custom",
        "to_fp_custom",
        "arbitrary_function",
    ] {
        positive(Symbol::named(name), &[3, 5], Sort::RegLan);
        positive(Symbol::indexed(name, vec![0]), &[3, 5], Sort::RegLan);
    }
}
