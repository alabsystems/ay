// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Typed array-theorem recognition for the final trust closer.

use super::*;

// #trust-closer-retag. This closer's head clause is exactly the negation of
// the leaves the chain below resolves against — i.e. the claim "these leaves
// are jointly inconsistent". That claim is USUALLY an unproved trust stub,
// but for array refutations it is frequently a STANDALONE array theorem the
// strict checker already validates: `storecomm_3idx` closes on
// `(cl (= i1 i2) (= i1 i3) (= i2 i3) (= lhs rhs))`, which is precisely the
// `ArrayStorePermutation` schema, and every other producer in the engine would
// have typed it. Only this closer conceded `Generic` without ever asking, so a
// refutation that had a checkable justification published a hole.
//
// Ask the CHECKER'S OWN recognizer, never a local shape test:
// `recognize_array_theory_lemma` is documented and maintained as the exact
// inverse of the `validate_array_*` entry points and shares their `matches_*`
// bodies, so the kind assigned here is by construction the kind strict mode
// accepts — no classifier/validator drift is representable. A decline leaves
// the trust stub exactly as before (fail-closed): this never converts an
// unprovable head into a typed one, it only stops discarding the provable ones.
//
// Scoped to the array recognizer on purpose. The wider funnel can return kinds
// whose validators need a payload this closer has none of (a positional Farkas
// certificate for `LiaGeneric`/`LraFarkas`); emitting one of those would turn
// today's `Generic` rejection — which the deferred trust discharge is defined
// over and can still rescue — into an `InvalidTheoryLemma` rejection it
// declines, converting published `unsat` into `unknown`. Array kinds carry no
// payload, so they cannot do that.
pub(super) fn add_head(terms: &TermStore, proof: &mut Proof, negated_clause: &[TermId]) -> ProofId {
    match ay_proof::recognize_array_theory_lemma(terms, negated_clause) {
        Some(kind) => proof.add_theory_lemma_with_kind("Arrays", negated_clause.to_vec(), kind),
        // Genuine trust fallback: SAT proof reconstruction could not derive the
        // empty clause from existing steps and no theory schema covers the
        // head, so `Generic` is the honest label.
        None => proof.add_theory_lemma_with_kind(
            "trust",
            negated_clause.to_vec(),
            TheoryLemmaKind::Generic,
        ),
    }
}
