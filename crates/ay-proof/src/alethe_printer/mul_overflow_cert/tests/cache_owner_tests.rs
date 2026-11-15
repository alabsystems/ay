// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// The signed entry shares the unsigned entry's original owner and emits
/// the same certificate when that owner accepts every observation.
#[test]
fn signed_certificate_accepting_owner_preserves_text_and_final_id() {
    let (terms, eq) = signed_clause_of(4);
    let ordinary = AlethePrinter::new(&terms)
        .format_mul_overflow_division(ProofId(7), &[eq])
        .expect("ordinary signed certificate");
    let mut callback = || true;
    let controlled = AlethePrinter::new(&terms)
        .with_emission_progress(&mut callback)
        .format_mul_overflow_division(ProofId(7), &[eq])
        .expect("controlled signed certificate");
    assert_eq!(controlled, ordinary);
    assert!(controlled
        .lines()
        .last()
        .expect("last step")
        .starts_with("(step t7 "));
}

/// Refusal at entry, at an intermediate observation, or at final signed publication
/// is sticky; the same printer cannot retry with fresh permission.
#[test]
fn signed_certificate_inner_and_final_refusal_abandon_text() {
    use std::cell::Cell;
    LAST_CERTIFICATE.with(|last| *last.borrow_mut() = None);
    let (terms, eq) = signed_clause_of(4);
    let calls = Cell::new(0);
    let mut accepting = || {
        calls.set(calls.get() + 1);
        true
    };
    assert!(AlethePrinter::new(&terms)
        .with_emission_progress(&mut accepting)
        .format_mul_overflow_division(ProofId(7), &[eq])
        .is_some());
    assert!(
        calls.get() > 10,
        "exercise local children and signed publication"
    );
    for stop_at in [1, 10, calls.get()] {
        LAST_CERTIFICATE.with(|last| *last.borrow_mut() = None);
        let seen = Cell::new(0);
        let mut callback = || {
            seen.set(seen.get() + 1);
            seen.get() != stop_at
        };
        let printer = AlethePrinter::new(&terms).with_emission_progress(&mut callback);
        assert!(printer
            .format_mul_overflow_division(ProofId(7), &[eq])
            .is_none());
        assert_eq!(seen.get(), stop_at);
        assert!(printer
            .format_mul_overflow_division(ProofId(7), &[eq])
            .is_none());
        assert_eq!(seen.get(), stop_at);
    }
}

fn controlled_cache_key() -> CertificateKey {
    CertificateKey {
        m: 4,
        names: ["a", "b", "c", "d"].map(str::to_string),
        prefix: "@ay_owner_cache_".into(),
        final_id: "t_owner_cache".into(),
        clause: "(cl (= l r))".into(),
        signed: true,
    }
}

#[test]
fn a_retained_certificate_still_observes_the_original_owner() {
    use std::cell::Cell;
    LAST_CERTIFICATE.with(|last| *last.borrow_mut() = None);
    assert_eq!(
        remembered_certificate(controlled_cache_key(), |_| Some("kept".into())),
        Some("kept".into())
    );
    for stop_at in [1, 2] {
        let seen = Cell::new(0);
        let mut callback = || {
            seen.set(seen.get() + 1);
            seen.get() != stop_at
        };
        let progress = EmissionProgress::with_caller(&mut callback);
        let builds = Cell::new(0);
        let refused =
            remembered_certificate_with_progress(controlled_cache_key(), &progress, |_| {
                builds.set(builds.get() + 1);
                Some("different".into())
            });
        assert_eq!(refused, None);
        assert_eq!(builds.get(), 0, "a warmed hit must not rebuild");
        assert_eq!(seen.get(), stop_at);
        assert!(progress.refused());
        assert_eq!(
            remembered_certificate_with_progress(controlled_cache_key(), &progress, |_| Some(
                "retry".into()
            )),
            None
        );
        assert_eq!(seen.get(), stop_at);
    }
    let mut callback = || true;
    let progress = EmissionProgress::with_caller(&mut callback);
    assert_eq!(
        remembered_certificate_with_progress(controlled_cache_key(), &progress, |_| None),
        Some("kept".into())
    );
}

#[test]
fn every_certificate_cache_publication_observation_refuses_without_retaining_text() {
    use std::cell::Cell;
    LAST_CERTIFICATE.with(|last| *last.borrow_mut() = None);
    let total = Cell::new(0);
    let mut accepting = || {
        total.set(total.get() + 1);
        true
    };
    let owner = EmissionProgress::with_caller(&mut accepting);
    assert!(
        remembered_certificate_with_progress(controlled_cache_key(), &owner, |_| Some(
            "built".into()
        ))
        .is_some()
    );
    assert_eq!(
        total.get(),
        6,
        "exercise publication and cleanup observations"
    );
    for stop_at in 1..=total.get() {
        LAST_CERTIFICATE.with(|last| *last.borrow_mut() = None);
        let seen = Cell::new(0);
        let mut callback = || {
            seen.set(seen.get() + 1);
            seen.get() != stop_at
        };
        let owner = EmissionProgress::with_caller(&mut callback);
        assert_eq!(
            remembered_certificate_with_progress(controlled_cache_key(), &owner, |_| Some(
                "refused".into()
            )),
            None
        );
        assert!(LAST_CERTIFICATE.with(|last| last.borrow().is_none()));
        assert_eq!(seen.get(), stop_at);
        assert!(owner.refused());
    }
    for panic_at in [5, 6] {
        LAST_CERTIFICATE.with(|last| *last.borrow_mut() = None);
        let seen = Cell::new(0);
        let mut callback = || {
            seen.set(seen.get() + 1);
            assert_ne!(
                seen.get(),
                panic_at,
                "original owner unwound at publication"
            );
            true
        };
        let owner = EmissionProgress::with_caller(&mut callback);
        let attempted = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            remembered_certificate_with_progress(controlled_cache_key(), &owner, |_| {
                Some("refused".into())
            })
        }));
        assert!(attempted.is_err());
        assert!(owner.refused());
        assert!(LAST_CERTIFICATE.with(|last| last.borrow().is_none()));
        assert!(!owner.poll());
        assert_eq!(seen.get(), panic_at);
    }
}
