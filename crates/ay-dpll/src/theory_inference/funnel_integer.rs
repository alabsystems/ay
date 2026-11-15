// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The funnel's PAYLOAD-FREE integer arms, in priority order.
//!
//! Every recognizer is the strict checker's own validator entry point run on
//! exactly the clause that will be recorded, in exactly its order, and no
//! kind carries an annotation — so the classifier cannot promote a clause the
//! checker will reject, and there is nothing for a producer to forge. That is
//! the discipline `lia_bound_lattice` established and `lia_cut_lattice`,
//! `lia_guarded_split` and `lia_cut_chain` inherit.
//!
//! * `IntBoundLatticeGap` is asked first: it is the narrower rule and it names
//!   its own wire rule, so a clause both can reach keeps the more specific
//!   label.
//! * `IntGuardedSplitGap` reaches the CDCL(T) learned-conflict shape neither
//!   lattice rule can: a wide clause whose negation is rationally satisfiable
//!   and integrally infeasible only after case-splitting one of its own
//!   literals — a negated disjunction, or a POSITIVE integer equality read as
//!   the disequality it negates — or after substituting its equality literals,
//!   which both lattice rules skip entirely (`parse_int_bound` returns `None`
//!   for `=`). Before this arm the whole family stopped at `LiaGeneric`, which
//!   both recorders normalize straight back to `Generic`/trust for want of a
//!   certificate it can never have.
//! * `IntCgCutChain` is asked last: a clause whose negation is refuted only by
//!   a CHAIN of Chvátal–Gomory roundings (a rounded bound feeding the next
//!   rounding), which every rule above declines — the
//!   `QF_LIA_ring_2exp16_5vars_cascade_unsat` carry-chain lemma is the corpus
//!   instance. Its lowering prints checked `la_generic` steps, but only when
//!   the row carcara reads off every PRINTED literal equals the internal one:
//!   a surface that changes a row keeps the honest `hole`
//!   (`cut_chain_tests::a_surface_that_changes_a_row_keeps_the_hole`). It
//!   stays last so no clause an established arm takes changes label. The
//!   residual it takes includes rationally infeasible clauses whose Farkas
//!   multipliers are not all one, which the payload-free unit arm declines
//!   (`funnel_cut_chain_tests::a_non_unit_farkas_clause_reaches_the_cut_chain_arm`).
//!
//! Callers place this strictly AFTER every rational arm, so a lemma that DOES
//! have a Farkas certificate keeps the externally checkable `la_generic` wire
//! and only the residual takes an honest `hole`. Two second-chance passes can
//! still upgrade the guarded-split residual to a certificate-bearing kind —
//! `promote_lia_divisibility_lemmas` and `synthesize_equality_farkas` — and
//! both are asked ahead of the guarded-split label. Neither is asked ahead of
//! `IntCgCutChain`: `generic_promotion` consults `synthesize_equality_farkas`
//! only for a `LiaGeneric` or `IntGuardedSplitGap` inference, and
//! `promote_lia_divisibility_lemmas` does not match this kind, so a cut-chain
//! label is never traded for the `Divisibility` `lia_generic` the pinned
//! checker reads as a hole. The one pass that does revisit it is
//! `reconstruct_missing_farkas_coefficients`: a lemma its LRA reconstruction
//! certifies takes that certificate and its certificate kind (`LraFarkas` for
//! the non-unit clause above,
//! `proof_farkas_tests::reconstruction_relabels_a_non_unit_farkas_cut_chain`);
//! its equality-synthesis fallbacks attach a validated certificate and keep
//! the kind.

use ay_core::{TermId, TermStore, TheoryLemmaKind};

/// The most specific payload-free integer kind for `clause`, or `None`.
///
/// This is the funnel's ONLY source of the three kinds below, so `None` here
/// means the funnel cannot answer one of them for `clause` either; the
/// conflict recorder's integer residual relies on that to skip the funnel.
pub(in crate::theory_inference) fn integer_lattice_kind(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<TheoryLemmaKind> {
    if ay_core::proof_validation::recognize_int_bound_lattice_gap(terms, clause) {
        return Some(TheoryLemmaKind::IntBoundLatticeGap);
    }
    if ay_core::proof_validation::recognize_int_guarded_split_gap(terms, clause) {
        return Some(TheoryLemmaKind::IntGuardedSplitGap);
    }
    if ay_core::proof_validation::recognize_int_cg_cut_chain(terms, clause) {
        return Some(TheoryLemmaKind::IntCgCutChain);
    }
    None
}
