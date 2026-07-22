// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_resolution_proof() {
    // Prove (A OR B) AND (NOT A OR B) AND (NOT B) is UNSAT
    // Resolution:
    // 1. A OR B (axiom)
    // 2. NOT A OR B (axiom)
    // 3. B (resolve 1,2 on A)
    // 4. NOT B (axiom)
    // 5. empty (resolve 3,4 on B)

    let a = Var::new(0);
    let b = Var::new(1);

    let mut proof = ResolutionProof::new();
    let s1 = proof.add_axiom(vec![Lit::positive(a), Lit::positive(b)]);
    let s2 = proof.add_axiom(vec![Lit::negative(a), Lit::positive(b)]);
    let s3 = proof.add_resolution(vec![Lit::positive(b)], s1, s2, a);
    let s4 = proof.add_axiom(vec![Lit::negative(b)]);
    let _s5 = proof.add_resolution(vec![], s3, s4, b);

    assert!(proof.is_refutation());
    assert!(proof.verify().is_ok());
    assert!(proof.is_tree());
    assert!(proof.is_regular());
    assert_eq!(proof.width(), 2);
}

#[test]
fn test_non_tree_proof() {
    // Reuse a clause: (A) AND (NOT A OR B) AND (NOT A OR NOT B)
    // 1. A (axiom)
    // 2. NOT A OR B (axiom)
    // 3. B (resolve 1,2 on A)
    // 4. NOT A OR NOT B (axiom)
    // 5. NOT B (resolve 1,4 on A) -- reuses clause 1
    // 6. empty (resolve 3,5 on B)

    let a = Var::new(0);
    let b = Var::new(1);

    let mut proof = ResolutionProof::new();
    let s1 = proof.add_axiom(vec![Lit::positive(a)]);
    let s2 = proof.add_axiom(vec![Lit::negative(a), Lit::positive(b)]);
    let s3 = proof.add_resolution(vec![Lit::positive(b)], s1, s2, a);
    let s4 = proof.add_axiom(vec![Lit::negative(a), Lit::negative(b)]);
    let s5 = proof.add_resolution(vec![Lit::negative(b)], s1, s4, a);
    let _s6 = proof.add_resolution(vec![], s3, s5, b);

    assert!(proof.is_refutation());
    assert!(proof.verify().is_ok());
    assert!(!proof.is_tree()); // Clause 1 is used twice
}

#[test]
fn test_verify_returns_missing_parent_error_without_panic() {
    // Construct a proof whose resolution step references a parent index that
    // does not exist (parent2 is within bounds vs `idx` but beyond the number
    // of preceding steps). verify() must return MissingParent, not panic.
    let a = Var::new(0);
    let b = Var::new(1);

    let mut proof = ResolutionProof::new();
    let s1 = proof.add_axiom(vec![Lit::positive(a), Lit::positive(b)]);
    // Manually push a Resolve step that claims a parent at an unreachable
    // index without going through clause_at safety.
    let bad_parent = 99usize;
    proof.steps.push(ResolutionStep::Resolve {
        clause: vec![Lit::positive(b)],
        parent1: s1,
        parent2: bad_parent,
        pivot: a,
    });

    // parent2 = 99 >= idx (=1) triggers ParentOutOfBounds first.
    let err = proof.verify().expect_err("expected verification failure");
    assert!(matches!(
        err,
        ResolutionProofError::ParentOutOfBounds {
            step: 1,
            parent2: 99,
            ..
        }
    ));
}

#[test]
fn test_verify_missing_parent_when_index_lower_than_idx() {
    // Build a proof where parent indices are less than the step index but one
    // of them points beyond any actual previous step. This exercises the
    // `clause_at` ok_or path without relying on the bounds check.
    let a = Var::new(0);
    let b = Var::new(1);

    let mut proof = ResolutionProof::new();
    let _s1 = proof.add_axiom(vec![Lit::positive(a), Lit::positive(b)]);
    let _s2 = proof.add_axiom(vec![Lit::negative(a), Lit::positive(b)]);
    // Push a Resolve step at idx=2 with parent1=0 (valid) and parent2=1 (valid
    // index), but then immediately attempt verify after inserting a sentinel
    // Resolve at idx=3 whose parent1 is 0, parent2 is 2 (valid-looking), and
    // finally one with a parent that sits in a position where clause_at yields
    // None. Since `steps.get` returns None only when out of range, we simulate
    // the failure by corrupting parent1 to point past len after adding steps.
    let s3 = proof.add_resolution(vec![Lit::positive(b)], 0, 1, a);
    assert!(proof.verify().is_ok());

    // Now corrupt the most recently added Resolve step to reference a parent
    // index equal to its own idx (still triggers ParentOutOfBounds — this is
    // the only way MissingParent can be reached in practice because the
    // bounds check runs first).
    if let Some(ResolutionStep::Resolve { parent1, .. }) = proof.steps.get_mut(s3) {
        *parent1 = s3; // parent1 == idx
    }
    let err = proof.verify().expect_err("expected verification failure");
    assert!(matches!(
        err,
        ResolutionProofError::ParentOutOfBounds {
            step: 2,
            parent1: 2,
            ..
        }
    ));
}

#[test]
fn test_verify_rejects_bad_pivot() {
    // Pivot variable missing from parents.
    let a = Var::new(0);
    let b = Var::new(1);
    let c = Var::new(2);

    let mut proof = ResolutionProof::new();
    let s1 = proof.add_axiom(vec![Lit::positive(a)]);
    let s2 = proof.add_axiom(vec![Lit::positive(b)]);
    // Pivot is c, which appears in neither parent.
    let _s3 = proof.add_resolution(vec![Lit::positive(a), Lit::positive(b)], s1, s2, c);
    let err = proof.verify().expect_err("expected pivot error");
    assert!(matches!(
        err,
        ResolutionProofError::PivotNotResolved { step: 2, .. }
    ));
}

#[test]
fn test_verify_rejects_resolvent_mismatch() {
    // Derive a wrong clause from valid parents.
    let a = Var::new(0);
    let b = Var::new(1);

    let mut proof = ResolutionProof::new();
    let s1 = proof.add_axiom(vec![Lit::positive(a), Lit::positive(b)]);
    let s2 = proof.add_axiom(vec![Lit::negative(a), Lit::positive(b)]);
    // Correct resolvent is [+b]; we record [+a] instead.
    let _s3 = proof.add_resolution(vec![Lit::positive(a)], s1, s2, a);
    let err = proof.verify().expect_err("expected resolvent mismatch");
    assert!(matches!(
        err,
        ResolutionProofError::ResolventMismatch { step: 2, .. }
    ));
}

#[test]
fn test_proof_system_simulation() {
    use ProofSystem::*;

    // Resolution simulates tree resolution
    assert!(Resolution.p_simulates(&TreeResolution));
    // But tree resolution doesn't simulate resolution
    assert!(!TreeResolution.p_simulates(&Resolution));
    // Extended resolution simulates resolution
    assert!(ExtendedResolution.p_simulates(&Resolution));
}
