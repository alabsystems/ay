// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn absent_and_dangling_boolean_metadata_match_legacy_without_panicking() {
    for expected in [false, true] {
        for replacement in [
            None,
            Some(TermId::SENTINEL),
            Some(TermId(fixture().term_entries.len() as u32)),
        ] {
            let mut bundle = fixture();
            if expected {
                bundle.true_term = replacement;
            } else {
                bundle.false_term = replacement;
            }
            assert_malformed(
                compare(&bundle),
                if expected { "true_term" } else { "false_term" },
            );
        }
    }
}

#[test]
fn boolean_metadata_must_name_the_exact_expected_constant() {
    let mut swapped = fixture();
    std::mem::swap(&mut swapped.true_term, &mut swapped.false_term);
    assert_malformed(compare(&swapped), "is not the expected Boolean constant");
    let mut nonconstant = fixture();
    nonconstant.true_term = nonconstant.obligation_assertions.first().copied();
    assert_malformed(
        compare(&nonconstant),
        "is not the expected Boolean constant",
    );
    let mut integer = fixture();
    integer.true_term = Some(TermId(integer.term_entries.len() as u32));
    integer
        .term_entries
        .push((TermData::Const(Constant::Int(1.into())), Sort::Int));
    assert_malformed(compare(&integer), "is not the expected Boolean constant");
}

#[test]
fn obligations_require_live_boolean_terms_but_keep_duplicates_and_order() {
    let mut valid = fixture();
    valid.obligation_assertions.reverse();
    valid
        .obligation_assertions
        .push(valid.obligation_assertions[0]);
    compare(&valid).expect("positional repeated obligations remain structurally valid");
    let mut missing = fixture();
    missing.obligation_assertions.push(TermId::SENTINEL);
    assert_malformed(compare(&missing), "obligation assertion references term");
    let mut integer = fixture();
    integer
        .obligation_assertions
        .push(TermId(integer.term_entries.len() as u32));
    integer
        .term_entries
        .push((TermData::Const(Constant::Int(0.into())), Sort::Int));
    assert_malformed(compare(&integer), "obligation assertion");
}

#[test]
fn every_typed_signature_argument_and_result_sort_is_checked() {
    for result in [false, true] {
        let mut bundle = with_context();
        let signature = bundle.datatype_member_signatures.last_mut().unwrap();
        if result {
            signature.result_sort = Sort::bitvec(0);
        } else {
            signature
                .argument_sorts
                .extend([Sort::Int, Sort::bitvec(0)]);
        }
        assert_malformed(
            compare(&bundle),
            if result {
                "signature result sort"
            } else {
                "signature argument sort"
            },
        );
    }
}

#[test]
fn signature_sort_depth_is_guarded_in_both_positions_before_replay_cloning() {
    for result in [false, true] {
        let mut bundle = with_context();
        let mut sort = Sort::Int;
        for _ in 0..=MAX_BUNDLE_SORT_DEPTH {
            sort = Sort::Seq(Box::new(sort));
        }
        let signature = bundle.datatype_member_signatures.last_mut().unwrap();
        if result {
            signature.result_sort = sort;
        } else {
            signature.argument_sorts.push(sort);
        }
        assert_malformed(compare(&bundle), "maximum sort nesting depth");
    }
}

#[test]
fn static_signature_roles_do_not_copy_or_format_untrusted_identity_payloads() {
    let mut bundle = with_context();
    let mut baseline = 0usize;
    validate_signatures(&bundle, &mut |work, bytes| {
        baseline += work;
        bytes == 0
    })
    .expect("scalar sorts allocate nothing");
    bundle.datatype_member_signatures[0].identity = "large_identity".repeat(16_384);
    let mut measured = 0usize;
    validate_signatures(&bundle, &mut |work, bytes| {
        measured += work;
        bytes == 0
    })
    .expect("identity is not displayed or authenticated here");
    assert_eq!(measured, baseline);
    bundle.datatype_member_signatures[0].result_sort = Sort::bitvec(0);
    let mut largest_diagnostic = 0usize;
    assert_malformed(
        validate_signatures(&bundle, &mut |_, bytes| {
            largest_diagnostic = largest_diagnostic.max(bytes);
            true
        }),
        "signature result sort",
    );
    assert!(largest_diagnostic > 0 && largest_diagnostic < 4_096);
}
