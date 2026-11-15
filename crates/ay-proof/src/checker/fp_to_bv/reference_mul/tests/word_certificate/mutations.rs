// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn changed_source_rm_or_any_constructor_field_cannot_certify_the_old_output() {
    let mut f = CertificateFixture::new(3, 4);
    let TermData::App(_, args) = f.fixture.terms.get(f.fixture.source) else {
        panic!("mul source");
    };
    let args = args.clone();
    let other_rm = f.fixture.terms.mk_var(
        "other_actual_rm",
        Sort::Uninterpreted("RoundingMode".into()),
    );
    let changed_rm = app(
        &mut f.fixture.terms,
        "fp.mul",
        &[other_rm, args[1], args[2]],
        Sort::FloatingPoint(3, 4),
    );
    let forged = app(
        &mut f.fixture.terms,
        "=",
        &[changed_rm, f.lowered],
        Sort::Bool,
    );
    assert!(!recognizes(&f.fixture.terms, &[forged], &mut |_, _| true).expect("changed RM refuses"));
    for (field, width) in [(0, 1), (1, 3), (2, 3)] {
        let original = f.fixture.x;
        let mut fields = [original.sign, original.exponent, original.fraction];
        fields[field] = f
            .fixture
            .terms
            .mk_var(format!("changed_field_{field}"), Sort::bitvec(width));
        let x = app(
            &mut f.fixture.terms,
            "fp",
            &fields,
            Sort::FloatingPoint(3, 4),
        );
        let changed = app(
            &mut f.fixture.terms,
            "fp.mul",
            &[f.fixture.rm, x, args[2]],
            Sort::FloatingPoint(3, 4),
        );
        let forged = app(&mut f.fixture.terms, "=", &[changed, f.lowered], Sort::Bool);
        assert!(!recognizes(&f.fixture.terms, &[forged], &mut |_, _| true)
            .expect("changed field refuses"));
    }
}

#[test]
fn altered_full_product_or_shift_semantics_is_not_the_independent_recipe() {
    let f = CertificateFixture::new(3, 4);
    assert!(f.accepts());
    for (operation, wrong_name) in [(Binary::Mul, "bvadd"), (Binary::Lshr, "bvashr")] {
        let index = f
            .nodes
            .iter()
            .position(|node| {
                matches!(node.operation,
            Operation::Binary(actual, _, _) if actual == operation)
            })
            .expect("actual operation in output");
        let id = f.emitted[index];
        let mut entries = f.fixture.terms.entries_snapshot();
        let (TermData::App(_, args), sort) = entries[id.index()].clone() else {
            panic!("emitted operator");
        };
        entries[id.index()] = (TermData::App(Symbol::named(wrong_name), args), sort);
        let imported = TermStore::from_entries(entries, None, None, f.fixture.terms.var_counter());
        assert!(!recognizes(&imported, &[f.theorem], &mut |_, _| true)
            .expect("operator mutation declines"));
    }
}

#[test]
fn unrelated_rm_bv_carrier_cannot_replace_actual_five_value_translation() {
    let f = CertificateFixture::new(3, 4);
    let index = f
        .nodes
        .iter()
        .position(|node| node.operation == Operation::Input(f.fixture.rm))
        .expect("actual original RM source input");
    let mut entries = f.fixture.terms.entries_snapshot();
    let id = f.emitted[index];
    entries[id.index()] = (TermData::Var("fake_3bit_rm".into(), 999), Sort::bitvec(3));
    let imported = TermStore::from_entries(entries, None, None, f.fixture.terms.var_counter());
    assert!(!recognizes(&imported, &[f.theorem], &mut |_, _| true)
        .expect("domain-only carrier is not source authority"));
}

#[test]
fn target_missing_cycles_and_noncanonical_word_values_refuse_without_abstraction() {
    let f = CertificateFixture::new(3, 4);
    let index = f
        .nodes
        .iter()
        .position(|node| {
            matches!(
                node.operation,
                Operation::Binary(Binary::Eq | Binary::Ult, _, _)
            )
        })
        .expect("one-bit comparison wrapper");
    let TermData::Ite(_, id, _) = f.fixture.terms.get(f.emitted[index]) else {
        panic!("comparison wrapper");
    };
    let id = *id; // Actual canonical #b1 is shared by every word comparison.
    for bad in [
        TermData::Const(Constant::BitVec {
            value: BigInt::from(-1i8),
            width: 1,
        }),
        TermData::Const(Constant::BitVec {
            value: BigInt::from(2u8),
            width: 1,
        }),
        TermData::App(Symbol::named("bvnot"), vec![id]),
        TermData::App(Symbol::named("bvnot"), vec![TermId::SENTINEL]),
    ] {
        let mut entries = f.fixture.terms.entries_snapshot();
        entries[id.index()] = (bad, Sort::bitvec(1));
        let imported = TermStore::from_entries(entries, None, None, f.fixture.terms.var_counter());
        assert!(!recognizes(&imported, &[f.theorem], &mut |_, _| true)
            .expect("malformed target declines"));
    }
    let index = f
        .nodes
        .iter()
        .position(|node| matches!(node.operation, Operation::Binary(Binary::Mul, _, _)))
        .expect("full product");
    let id = f.emitted[index];
    let mut entries = f.fixture.terms.entries_snapshot();
    let (TermData::App(symbol, mut args), sort) = entries[id.index()].clone() else {
        panic!("full product");
    };
    args[0] = TermId::SENTINEL;
    entries[id.index()] = (TermData::App(symbol, args), sort);
    let imported = TermStore::from_entries(entries, None, None, f.fixture.terms.var_counter());
    assert!(!recognizes(&imported, &[f.theorem], &mut |_, _| true)
        .expect("actual missing child declines before indexing"));
}

#[test]
fn complete_word_replay_and_negative_match_observe_original_terminal_refusal() {
    let f = CertificateFixture::new(3, 4);
    for clause in [vec![f.theorem], vec![TermId::SENTINEL]] {
        let mut calls = 0;
        recognizes(&f.fixture.terms, &clause, &mut |_, _| {
            calls += 1;
            true
        })
        .expect("healthy scan");
        let mut remaining = calls - 1;
        let result = recognizes(&f.fixture.terms, &clause, &mut |_, _| {
            if remaining == 0 {
                false
            } else {
                remaining -= 1;
                true
            }
        });
        assert_eq!(result, Err(ReferenceError::Resource));
    }
}

#[test]
fn same_original_owner_refusal_is_sticky_across_orientation_attempts() {
    let f = CertificateFixture::new(3, 4);
    let mut calls = 0;
    let result = recognizes(&f.fixture.terms, &[f.theorem], &mut |_, _| {
        calls += 1;
        calls != 3 // Deliberately would revive on a later call.
    });
    assert_eq!(result, Err(ReferenceError::Resource));
    assert_eq!(
        calls, 3,
        "no second orientation or final callback revives a refused transaction"
    );
}

#[test]
fn word_walk_task_and_memo_payloads_are_not_unpriced_after_recipe_construction() {
    let f = CertificateFixture::new(3, 4);
    for refused_request in [2, 3] {
        let mut payload_requests = 0;
        let result = recognizes(&f.fixture.terms, &[f.theorem], &mut |_, bytes| {
            if bytes > 0 {
                payload_requests += 1;
            }
            bytes == 0 || payload_requests < refused_request
        });
        assert_eq!(result, Err(ReferenceError::Resource));
        assert_eq!(
            payload_requests, refused_request,
            "node/task/memo share the original cumulative sink"
        );
    }
}
