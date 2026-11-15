// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{AletheRule, BitVecSort, FpOp, NraSosCertificate, NraSosRational};

use super::*;

mod safety;
mod sos;

fn entries() -> Vec<(TermData, Sort)> {
    vec![
        (TermData::Const(Constant::Bool(true)), Sort::Bool),
        (TermData::Const(Constant::Bool(false)), Sort::Bool),
        (TermData::Var("x".into(), 0), Sort::Int),
    ]
}

fn lemma(clause: Vec<TermId>, kind: TheoryLemmaKind) -> ProofStep {
    ProofStep::TheoryLemma {
        theory: "preflight-only".into(),
        clause,
        farkas: None,
        kind,
        lia: None,
    }
}

fn generic(clause: Vec<TermId>, premises: Vec<ProofId>, args: Vec<TermId>) -> ProofStep {
    ProofStep::Step {
        rule: AletheRule::Refl,
        clause,
        premises,
        args,
    }
}

fn rational(value: i64) -> NraSosRational {
    NraSosRational {
        numerator: value.into(),
        denominator: 1.into(),
    }
}

fn certificate() -> NraSosCertificate {
    NraSosCertificate {
        basis: vec![vec![], vec![TermId(2)]],
        gram: vec![vec![rational(0); 2]; 2],
        terms: vec![],
        rhs: rational(-1),
    }
}

fn fixture() -> Vec<ProofStep> {
    vec![
        ProofStep::Assume(TermId(0)),
        ProofStep::Assume(TermId(1)),
        ProofStep::Resolution {
            clause: vec![],
            pivot: TermId(0),
            clause1: ProofId(0),
            clause2: ProofId(1),
        },
        lemma(vec![TermId(0)], TheoryLemmaKind::BoolTautology),
        lemma(
            vec![TermId(0)],
            TheoryLemmaKind::FpClassification {
                operation: FpOp::IsNaN,
            },
        ),
        generic(vec![TermId(0)], vec![ProofId(0)], vec![TermId(2)]),
        ProofStep::Anchor {
            end_step: ProofId(0),
            variables: vec![("bound".into(), Sort::Seq(Box::new(Sort::Int)))],
        },
        ProofStep::NraSos {
            clause: vec![TermId(0)],
            certificate: certificate(),
        },
    ]
}

fn measurements(steps: &[ProofStep], entries: &[(TermData, Sort)]) -> (usize, usize, usize) {
    let (mut calls, mut work, mut bytes) = (0, 0, 0);
    validate_proof_snapshot_with_progress(steps, entries, &mut |w, b| {
        calls += 1;
        work += w;
        bytes += b;
        true
    })
    .expect("structurally valid fixture");
    (calls, work, bytes)
}

fn assert_malformed(steps: &[ProofStep], entries: &[(TermData, Sort)]) {
    assert!(matches!(
        validate_proof_snapshot(steps, entries),
        Err(ProofCheckError::MalformedProofBundle { .. })
    ));
}

#[test]
fn compatibility_wrapper_preserves_all_step_shapes_without_authenticating_them() {
    let steps = fixture();
    let entries = entries();
    assert!(validate_proof_snapshot(&steps, &entries).is_ok());
    let (calls, work, bytes) = measurements(&steps, &entries);
    assert!(calls > 10 && work > 0 && bytes > 0);
    // Shape checks deliberately do not establish the SOS identity or an empty
    // terminal clause; semantic independent replay remains mandatory.
    let terms = TermStore::from_entries(entries, Some(TermId(0)), Some(TermId(1)), 1);
    assert!(crate::check_proof_strict(&Proof::from_steps(steps), &terms).is_err());
}

#[test]
fn every_callback_refusal_including_final_poll_is_immediate_and_read_only() {
    let steps = fixture();
    let entries = entries();
    let expected_steps = steps.clone();
    let expected_entries = entries.clone();
    let (calls, _, _) = measurements(&steps, &entries);
    for reject_at in 1..=calls {
        let mut observed = 0;
        let result = validate_proof_snapshot_with_progress(&steps, &entries, &mut |_, _| {
            observed += 1;
            // Would allow every subsequent callback: refusal must propagate.
            observed != reject_at
        });
        assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        assert_eq!(observed, reject_at);
        assert_eq!(steps, expected_steps);
        assert_eq!(entries, expected_entries);
    }
}

#[test]
fn shared_exact_work_and_byte_allowances_do_not_reset_between_calls() {
    let steps = fixture();
    let entries = entries();
    let (_, work, bytes) = measurements(&steps, &entries);
    for byte_limited in [false, true] {
        let mut remaining = if byte_limited { bytes } else { work };
        let mut progress = |w, b| {
            let cost = if byte_limited { b } else { w };
            match remaining.checked_sub(cost) {
                Some(next) => {
                    remaining = next;
                    true
                }
                None => false,
            }
        };
        assert!(validate_proof_snapshot_with_progress(&steps, &entries, &mut progress).is_ok());
        assert!(matches!(
            validate_proof_snapshot_with_progress(&steps, &entries, &mut progress),
            Err(ProofCheckError::ResourceLimit)
        ));
    }
}

#[test]
fn empty_proof_still_polls_entry_and_completion() {
    for reject_at in [1, 2] {
        let mut calls = 0;
        let result = validate_proof_snapshot_with_progress(&[], &[], &mut |_, _| {
            calls += 1;
            calls != reject_at
        });
        assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        assert_eq!(calls, reject_at);
    }
    assert!(validate_proof_snapshot(&[], &[]).is_ok());
}

#[test]
fn literal_pivot_argument_and_premise_handles_are_checked() {
    let entries = entries();
    for missing in [TermId(3), TermId(u32::MAX)] {
        let variants = [
            ProofStep::Assume(missing),
            generic(vec![missing], vec![], vec![]),
            generic(vec![], vec![], vec![missing]),
            lemma(vec![missing], TheoryLemmaKind::BoolTautology),
            ProofStep::Resolution {
                clause: vec![],
                pivot: missing,
                clause1: ProofId(0),
                clause2: ProofId(0),
            },
        ];
        for step in variants {
            assert_malformed(&[step], &entries);
        }
    }
    for premise in [ProofId(0), ProofId(1), ProofId(u32::MAX)] {
        assert_malformed(&[generic(vec![], vec![premise], vec![])], &entries);
    }
    assert_malformed(
        &[ProofStep::Anchor {
            end_step: ProofId(1),
            variables: vec![],
        }],
        &entries,
    );
    assert_malformed(&[ProofStep::Assume(TermId(2))], &entries);
    assert!(validate_proof_snapshot(&[generic(vec![], vec![], vec![TermId(2)])], &entries).is_ok());
}

#[test]
fn malformed_root_diagnostic_never_displays_a_recursive_sort() {
    let mut sort = Sort::Int;
    for _ in 0..=MAX_BUNDLE_SORT_DEPTH {
        sort = Sort::Seq(Box::new(sort));
    }
    let entries = vec![(TermData::Var("deep".into(), 0), sort)];
    assert_malformed(&[ProofStep::Assume(TermId(0))], &entries);
    let mut allocations = 0;
    let result = validate_proof_snapshot_with_progress(
        &[ProofStep::Assume(TermId(0))],
        &entries,
        &mut |_, b| {
            if b > 0 {
                allocations += 1;
                false
            } else {
                true
            }
        },
    );
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
    assert_eq!(allocations, 1);
}

#[test]
fn anchors_use_the_shared_recursive_sort_meter_and_inclusive_depth_limit() {
    let mut sort = Sort::Int;
    for _ in 0..MAX_BUNDLE_SORT_DEPTH {
        sort = Sort::Seq(Box::new(sort));
    }
    let steps = vec![ProofStep::Anchor {
        end_step: ProofId(0),
        variables: vec![("x".into(), sort.clone())],
    }];
    let (calls, _, _) = measurements(&steps, &[]);
    assert!(calls > MAX_BUNDLE_SORT_DEPTH);
    assert_malformed(
        &[ProofStep::Anchor {
            end_step: ProofId(0),
            variables: vec![("x".into(), Sort::Seq(Box::new(sort)))],
        }],
        &[],
    );
}
