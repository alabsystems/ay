// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn rational_wire_form_round_trips_and_rejects_non_canonical() {
    let r = BigRational::new(BigInt::from(-3), BigInt::from(4));
    assert_eq!(fmt_rat(&r), "-3/4");
    assert_eq!(parse_rat("-3/4"), Some(r));
    assert_eq!(fmt_rat(&BigRational::from_integer(7.into())), "7");
    assert_eq!(parse_rat("7"), Some(BigRational::from_integer(7.into())));
    // Non-canonical forms are malformed, not silently normalised.
    assert_eq!(parse_rat("2/4"), None);
    assert_eq!(parse_rat("3/1"), None);
    assert_eq!(parse_rat("1/0"), None);
    assert_eq!(parse_rat("1/-2"), None);
}

pub(super) fn bounded_rational_parser_preflights_decimal_size_and_checks_exact_bits() {
    let bit_cap = crate::block_angular_route::MAX_RATIONAL_BITS;
    let exact_decimal = BigRational::new(
        10_000_000_000_000_001_i64.into(),
        100_000_000_000_000_000_i64.into(),
    );
    assert_eq!(
        parse_rat_bounded("10000000000000001/100000000000000000", bit_cap),
        Ok(exact_decimal),
        "valid exact-decimal artifacts remain accepted"
    );

    let largest_power_within_cap = BigInt::one() << (bit_cap - 1);
    assert_eq!(
        parse_rat_bounded(&largest_power_within_cap.to_string(), bit_cap),
        Ok(BigRational::from_integer(largest_power_within_cap))
    );
    let first_power_above_cap = BigInt::one() << bit_cap;
    assert_eq!(
        parse_rat_bounded(&first_power_above_cap.to_string(), bit_cap),
        Err(BoundedRatParseError::BitLimit),
        "the exact bit check catches values at the decimal digit boundary"
    );

    let digit_cap = max_decimal_digits_for_bits(bit_cap).expect("small route cap");
    let allocation_attack = "9".repeat(digit_cap + 100_000);
    assert_eq!(
        parse_rat_bounded(&format!("{allocation_attack}/3"), bit_cap),
        Err(BoundedRatParseError::BitLimit),
        "an oversized numerator is rejected by length before BigInt parsing"
    );
    assert_eq!(
        parse_rat_bounded(&format!("1/{allocation_attack}"), bit_cap),
        Err(BoundedRatParseError::BitLimit),
        "an oversized denominator is rejected by length before BigInt parsing"
    );
}

pub(super) fn canonical_digest_is_stable_and_shape_sensitive() {
    let (m, _) = tiny();
    assert_eq!(canonical_digest(&m), canonical_digest(&m.clone()));
    let canonical = canonical_model_v1(&m);
    let historical: [u8; 32] = Sha256::digest(canonical.as_bytes()).into();
    assert_eq!(
        canonical_digest_bytes(&m),
        historical,
        "streaming digest must preserve canonical-v1 bytes exactly"
    );
    assert_eq!(
        canonical_digest_bytes_bounded(&m, None, canonical.len()),
        Some(historical),
        "the exact byte cap is inclusive"
    );
    assert_eq!(
        canonical_digest_bytes_bounded(&m, None, canonical.len() - 1),
        None,
        "the streaming writer declines before exceeding its cap"
    );
    let now = Instant::now();
    let expired = now
        .checked_sub(std::time::Duration::from_millis(1))
        .unwrap_or(now);
    assert_eq!(
        canonical_digest_bytes_bounded(&m, Some(expired), usize::MAX,),
        None,
        "an expired absolute deadline produces no partial digest"
    );
    let mut m2 = m.clone();
    m2.add_col(0.0, 1.0);
    assert_ne!(canonical_digest(&m), canonical_digest(&m2));

    let mut exact_offset = m.clone();
    let proxy_digest = canonical_digest(&exact_offset);
    exact_offset.record_inexact_obj_offset(BigRational::new(1.into(), 3.into()));
    assert_ne!(
        proxy_digest,
        canonical_digest(&exact_offset),
        "an exact-only offset mutation must change the frozen v1 digest"
    );
}

pub(super) fn sat_relu_emission_reuses_its_model_bound_digest() {
    let (model, _) = tiny();
    let retained = [0x5au8; 32];
    let certificate = SatReluInfeasibilityCertificate::from_wire_parts(
        1,
        retained,
        [0u8; 32],
        0,
        0,
        Vec::new(),
        0,
    );
    let infeasible = Outcome::Infeasible {
        cert: None,
        tree_cert: None,
    };
    assert_eq!(
        emitted_model_canon_digest(&model, &infeasible, Some(&certificate)),
        digest_hex(&retained),
        "the model-bound certificate already paid for this exact digest"
    );

    let optimal = Outcome::Optimal {
        value: BigRational::zero(),
        model_values: Vec::new(),
        cert: None,
    };
    assert_eq!(
        emitted_model_canon_digest(&model, &optimal, Some(&certificate)),
        canonical_digest(&model),
        "an unrelated verdict must never reuse stale SAT/ReLU evidence"
    );
}

pub(super) fn block_angular_wire_round_trips_and_is_bounded() {
    let certificate = crate::block_angular_route::certificate_from_parts(
        BigRational::from_integer(17.into()),
        vec![
            (3, BigRational::new(1.into(), 2.into())),
            (9, BigRational::from_integer(2.into())),
        ],
        vec![
            crate::block_angular_route::source_pattern(vec![4, 1], vec![0, 3]),
            crate::block_angular_route::certified_initial_pattern(2),
        ],
    );
    let block = block_angular_optimality_block(&certificate);
    let lines: Vec<&str> = block.lines().collect();
    let (decoded, next) = parse_block_angular_optimality(&lines, 0).expect("wire block parses");
    assert_eq!(decoded, certificate);
    assert_eq!(next, lines.len());

    let oversized = "block-angular-optimality value=0 frame=model masters=65 blocks=0\nend";
    let lines: Vec<&str> = oversized.lines().collect();
    assert!(parse_block_angular_optimality(&lines, 0).is_err());

    let malformed = "block-angular-optimality value=0 frame=model masters=0 blocks=1\n\
                         source width=2 1 2 exits 0\nend";
    let lines: Vec<&str> = malformed.lines().collect();
    assert!(parse_block_angular_optimality(&lines, 0).is_err());

    let bit_cap = crate::block_angular_route::MAX_RATIONAL_BITS;
    let digit_cap = max_decimal_digits_for_bits(bit_cap).expect("small route cap");
    let allocation_attack = "9".repeat(digit_cap + 100_000);
    let oversized_value = format!(
        "block-angular-optimality value={allocation_attack} frame=model masters=0 blocks=0\n\
             end"
    );
    let lines: Vec<&str> = oversized_value.lines().collect();
    assert!(matches!(
        parse_block_angular_optimality(&lines, 0),
        Err(CertIoError::RationalBitLimit {
            line: 1,
            field,
            max_bits,
        }) if field == "block-angular optimum value" && max_bits == bit_cap
    ));

    let oversized_denominator = format!(
        "block-angular-optimality value=0 frame=model masters=1 blocks=0\n\
             master 0 1/{allocation_attack}\n\
             end"
    );
    let lines: Vec<&str> = oversized_denominator.lines().collect();
    assert!(matches!(
        parse_block_angular_optimality(&lines, 0),
        Err(CertIoError::RationalBitLimit {
            line: 2,
            field,
            max_bits,
        }) if field == "block-angular master multiplier" && max_bits == bit_cap
    ));
}
