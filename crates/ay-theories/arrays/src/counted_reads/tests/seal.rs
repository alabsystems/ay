// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn seal_rejects_a_clone_with_identical_numeric_ids_and_terms() {
    let original = ample();
    let mut f = fixture(&original, IndexRelation::Symbolic).unwrap();
    let closure = derive_fixture(&mut f, &original);
    let foreign = f.terms.clone();
    assert_eq!(foreign.len(), f.terms.len());
    assert_eq!(foreign.get(f.read), f.terms.get(f.read));
    assert_eq!(closure.validate_source(&foreign), Err(Error::Invalid));
    closure.validate_source(&f.terms).unwrap();
    original.check().unwrap();
    closure.finish().unwrap();
}

#[test]
fn paid_append_only_proof_terms_preserve_the_exact_source_prefix() {
    let original = ample();
    let mut f = fixture(&original, IndexRelation::Symbolic).unwrap();
    let before = f.terms.entry_stamp(f.read).unwrap();
    let closure = derive_fixture(&mut f, &original);
    let sealed_len = f.terms.len();
    let mut builder = CountedTermBuilder::new(&mut f.terms, &original).unwrap();
    let extra = builder
        .variable("later-proof-variable", &Sort::Bool)
        .unwrap();
    let _not = builder.apply(CountedBuiltin::Not, &[extra]).unwrap();
    builder.finish().unwrap();
    assert!(f.terms.len() > sealed_len);
    assert_eq!(f.terms.entry_stamp(f.read), Some(before));
    closure.validate_source(&f.terms).unwrap();
    closure.finish().unwrap();
}

#[test]
fn rollback_of_only_later_scratch_still_retires_the_seal() {
    let original = ample();
    let mut f = fixture(&original, IndexRelation::Symbolic).unwrap();
    let closure = derive_fixture(&mut f, &original);
    let saved_len = f.terms.len();
    let checkpoint = f.terms.rollback_checkpoint();
    {
        let mut builder = CountedTermBuilder::new(&mut f.terms, &original).unwrap();
        let _scratch = builder.variable("discarded-scratch", &Sort::Bool).unwrap();
        builder.finish().unwrap();
    }
    // No IDs in the discarded suffix survive. The closure's IDs all precede
    // this checkpoint, but the structural-generation seal still must retire.
    f.terms.rollback_to(checkpoint);
    assert_eq!(f.terms.len(), saved_len);
    assert_eq!(closure.validate_source(&f.terms), Err(Error::Invalid));
    closure.finish().unwrap();
}

#[test]
fn compaction_cannot_reuse_a_closure_as_numeric_term_authority() {
    let original = ample();
    let mut f = fixture(&original, IndexRelation::Symbolic).unwrap();
    let closure = derive_fixture(&mut f, &original);
    let _remap = f.terms.mark_and_compact(&[f.root]);
    // Only the opaque stamp is queried after compaction; none of the retained
    // numeric source records is dereferenced in the changed universe.
    assert_eq!(closure.validate_source(&f.terms), Err(Error::Invalid));
    closure.finish().unwrap();
}
