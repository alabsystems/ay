// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The INTRINSIC-tautology battery: clauses whose validity needs no premise,
//! no certificate payload and no problem context — only the checker's own
//! recognizer run on the clause exactly as recorded.
//!
//! Every entry is a `recognize_*` that IS its strict validator (each is
//! literally `validate_*(..).is_ok()`), so a clause this battery accepts is a
//! clause `check_proof_strict` re-derives from scratch. That property is what
//! lets a caller REPLACE an unjustified leaf with the returned kind: the
//! producer places no authority, it merely names the rule the checker is
//! about to re-run.
//!
//! Shared so the two consumers cannot drift:
//!
//! * `sat_proof_manager::exact_fragment::intrinsic_authority` — emission time,
//!   for an original clause that reaches the exact fragment with no annotation
//!   channel;
//! * `executor::proof::intrinsic_leaf_promotion` — finalize time, for the
//!   residual leaves the demotion pass already turned into premiseless
//!   `trust`, which no emission-time lane can reach any more.
//!
//! ORDER IS LOAD-BEARING and is the historical emission-time order: the
//! cheapest structural recognizers first, then EUF, then the array schemas.
//! Any clause at most one arm accepts is unaffected by the order; where two
//! could accept, keeping the emission-time order means the finalize-time
//! consumer labels a clause exactly as the emission-time consumer would have.

use ay_core::{TermId, TermStore, TheoryLemmaKind};

/// Name the strict-checkable rule for a clause that is valid on its own, or
/// `None` when no recognizer accepts it IN THE RECORDED ORDER.
///
/// Deliberately does NOT reorder. The EUF validators are order-sensitive, and
/// a caller that replaces a leaf in place cannot change the clause its
/// consumers already reference — so a permutation this battery would need is
/// reported as a decline (fail-closed), never as an accept.
#[must_use]
pub(crate) fn recognize_intrinsic_tautology_kind(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<(&'static str, TheoryLemmaKind)> {
    if ay_proof::recognize_bool_tautology(terms, clause) {
        return Some(("bool", TheoryLemmaKind::BoolTautology));
    }
    if ay_proof::recognize_arith_clause_tautology(terms, clause) {
        return Some(("arith", TheoryLemmaKind::ArithClauseTautology));
    }
    if ay_proof::recognize_ite_branch_projection(terms, clause) {
        return Some(("ite", TheoryLemmaKind::IteBranchProjection));
    }
    if ay_proof::recognize_euf_congruent(terms, clause) {
        return Some(("EUF", TheoryLemmaKind::EufCongruent));
    }
    if ay_proof::recognize_euf_transitive(terms, clause) {
        return Some(("EUF", TheoryLemmaKind::EufTransitive));
    }
    if ay_proof::recognize_array_guarded_row_expansion(terms, clause) {
        return Some(("array", TheoryLemmaKind::ArrayGuardedRowExpansion));
    }
    // Only Bool-indexed finite carriers are available without the typed
    // datatype registry. The shared recognizer rejects incomplete,
    // duplicated, foreign-array, and ill-sorted branch sets.
    if ay_proof::recognize_array_finite_select_expansion(terms, clause) {
        return Some(("array", TheoryLemmaKind::ArrayFiniteSelectExpansion));
    }
    // LAST, and deliberately so. This is the WIDEST EUF entry — a full
    // congruence-closure explanation subsumes the `eq_transitive` shape above
    // whenever that one's ORDER requirement happens to be met — so putting it
    // last leaves every label the battery already produced byte-identical, and
    // it only ever fires where every earlier arm declined.
    //
    // Corpus-measured (639 in-tree `.smt2` benchmarks): this is the single
    // largest residual class of premiseless `trust` leaves, the packed
    // `(cl (or ..))` congruence explanations the QF_AX / QF_AUFLIA array lanes
    // emit. Unlike the order-sensitive EUF entries it is ORDER-FREE, so the
    // finalize-time consumer can relabel a leaf in place without touching the
    // clause its consumers already reference.
    if ay_proof::recognize_euf_congruence_explanation(terms, clause) {
        return Some(("EUF", TheoryLemmaKind::EufCongruenceExplanation));
    }
    // DEAD LAST, after every entry that predates it, so no label this battery
    // already produced changes. `ArrayRowChain` sub-schema (K): the read of a
    // `store` chain under an array-equality premise whose value side is the
    // chain's ITE-FOLDED symbolic evaluation. Deliberately NOT the whole of
    // `recognize_array_theory_lemma` — wiring that would widen the battery to
    // eight further sub-schemas plus `ArrayDefaultConst` and
    // `ArrayStorePermutation`, measured at zero additional leaves.
    if ay_proof::recognize_array_row_chain_ite_eval(terms, clause) {
        return Some(("array", TheoryLemmaKind::ArrayRowChain));
    }
    // DEAD LAST in turn, behind the entry it shares a KIND with. Sub-schema (P)
    // of `EufCongruenceExplanation`: the congruence explanation whose
    // conclusion is a PREDICATE application rather than an equality. Its scope
    // guard requires a literal that is not a (possibly negated) equality, which
    // is precisely what sub-schema (E) above declines, so the two are disjoint
    // and this arm can only ever take a clause every earlier entry refused.
    //
    // Corpus-measured (639 in-tree `.smt2` benchmarks): the B-method `mem`
    // membership explanations of the two `clearsy` QF_UF files, 32 premiseless
    // `Generic` lemmas, the largest single residual group left by the
    // 2026-08-24 census.
    if ay_proof::recognize_euf_polarity_congruence(terms, clause) {
        return Some(("EUF", TheoryLemmaKind::EufCongruenceExplanation));
    }
    None
}
