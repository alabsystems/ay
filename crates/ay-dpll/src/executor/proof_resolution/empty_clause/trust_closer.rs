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
// Scoped to PAYLOAD-FREE recognizers on purpose, and that is the whole rule
// here. The wider funnel can return kinds whose validators need a payload this
// closer has none of (a positional Farkas certificate for
// `LiaGeneric`/`LraFarkas`); emitting one of those would turn today's
// `Generic` rejection — which the deferred trust discharge is defined over and
// can still rescue — into an `InvalidTheoryLemma` rejection it declines,
// converting published `unsat` into `unknown`.
//
// #4751: `recognize_int_cut_lattice_gap` satisfies the same test the array
// recognizer does and is admitted on the same terms. It carries NO annotation,
// it IS `validate_int_cut_lattice_gap` (the checker's own entry point calls
// this exact function), and it subsumes `recognize_int_bound_lattice_gap`, so
// one call covers both integer rules. A head it accepts therefore cannot
// become an `InvalidTheoryLemma` rejection: the strict checker re-runs the
// identical decision procedure on the identical clause. A head it declines is
// left exactly as before.
//
// These heads are the closer's claim "the leaves this chain resolves against
// are jointly inconsistent", and on #4751 that claim is an INTEGER fact —
// their negations are satisfiable over ℚ — which is why no Farkas
// reconstruction ever rescued them.
pub(super) fn add_head(terms: &TermStore, proof: &mut Proof, negated_clause: &[TermId]) -> ProofId {
    if let Some(id) = add_validated_head(terms, proof, negated_clause) {
        return id;
    }
    // Genuine trust fallback: SAT proof reconstruction could not derive the
    // empty clause from existing steps and no theory schema covers the head,
    // so `Generic` is the honest label.
    proof.add_theory_lemma_with_kind("trust", negated_clause.to_vec(), TheoryLemmaKind::Generic)
}

/// The VALIDATED half of [`add_head`]: the three payload-free recognizers and
/// nothing else. `None` means "no authority for this head" — and the caller,
/// not this module, decides whether a trust stub is licensed there.
///
/// #closer-derived-leaf-head. The distinction matters because the closer has
/// TWO leaf sources and only one of them licenses a trust stub.
///
/// * The proof's ASSUME-family leaves (`assume` steps and the premiseless unit
///   `trust` steps a demotion pass turns authored assumptions into) are the
///   proof's record of the authored problem. The solve answered UNSAT about
///   exactly that set, so "these leaves are jointly inconsistent" is the
///   solver's own verdict restated — unproved, hence `Generic`, but not a
///   false claim.
/// * A unit `TheoryLemma` CONCLUSION is a DERIVED fact the same proof already
///   asserts as theory-valid. A set of theory-valid clauses is true in every
///   model, so its joint negation is FALSE in every model. Asserting such a
///   head does not restate the solver's verdict; it contradicts the proof's
///   own other steps.
///
/// Measured on `benchmarks/smt/QF_AX/write_write_overwrite.smt2` before this
/// split: the closer emitted
/// `(cl (not (= (select (store a i v2) j) (select a j)))
///      (not (= (select a j) (select (store a i v1) j))))`
/// over two unit ROW2 lemmas, and an independent bounded array model falsifies
/// it at `i = j`, `v1 = v2 = e`, `a[j] = e` — both literals fail at once. On
/// `benchmarks/smt/chc_dt_option_enum.smt2` the same route negated eleven
/// datatype leaves, TEN of which carry the emitter's own strict-checkable
/// kinds (`DatatypeExhaustive`, `DatatypeTesterEval`, …), so that head is false
/// in every model of the datatype.
///
/// A head this function ACCEPTS is different in kind: the checker's own
/// recognizer re-derives it from the clause alone, so every step the closer
/// then adds is independently validated and no trust claim is made at all.
pub(super) fn add_validated_head(
    terms: &TermStore,
    proof: &mut Proof,
    negated_clause: &[TermId],
) -> Option<ProofId> {
    if let Some(kind) = ay_proof::recognize_array_theory_lemma(terms, negated_clause) {
        return Some(proof.add_theory_lemma_with_kind("Arrays", negated_clause.to_vec(), kind));
    }
    if ay_core::proof_validation::recognize_int_cut_lattice_gap(terms, negated_clause) {
        return Some(proof.add_theory_lemma_with_kind(
            "LIA",
            negated_clause.to_vec(),
            TheoryLemmaKind::IntCutLatticeGap,
        ));
    }
    // #4751 clause-1 endgame: the guarded mod-witness heads carry the joint
    // inconsistency of unit leaves AGAINST a substituted goal disjunction, so
    // no single-form (or two-row-cut) pool over the linear literals alone can
    // exhibit a gap and `recognize_int_cut_lattice_gap` correctly declines.
    // `recognize_int_guarded_split_gap` is admitted on the identical terms as
    // the two rules above: it carries NO annotation, it IS the checker's own
    // entry point (`validate_int_guarded_split_gap` calls this exact
    // function), so a head it accepts cannot become an `InvalidTheoryLemma`
    // rejection, and a head it declines is left exactly as before.
    if ay_core::proof_validation::recognize_int_guarded_split_gap(terms, negated_clause) {
        return Some(proof.add_theory_lemma_with_kind(
            "LIA",
            negated_clause.to_vec(),
            TheoryLemmaKind::IntGuardedSplitGap,
        ));
    }
    None
}
