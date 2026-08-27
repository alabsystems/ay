// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The funnel's PAYLOAD-FREE integer arms, in priority order.
//!
//! Both recognizers are the strict checker's own validator entry points run on
//! exactly the clause that will be recorded, in exactly its order, and neither
//! kind carries an annotation — so the classifier cannot promote a clause the
//! checker will reject, and there is nothing for a producer to forge. That is
//! the discipline `lia_bound_lattice` established and `lia_cut_lattice` and
//! `lia_guarded_split` inherit.
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
//!
//! Callers place this strictly AFTER every rational arm, so a lemma that DOES
//! have a Farkas certificate keeps the externally checkable `la_generic` wire
//! and only the residual takes an honest `hole`. The two second-chance passes
//! that can still upgrade such a residual to a certificate-bearing kind —
//! `promote_lia_divisibility_lemmas` and `synthesize_equality_farkas` — are
//! both asked ahead of the guarded-split label in `generic_promotion`, so this
//! arm can only ever take what they decline.

use ay_core::{TermId, TermStore, TheoryLemmaKind};

/// The most specific payload-free integer kind for `clause`, or `None`.
pub(super) fn integer_lattice_kind(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<TheoryLemmaKind> {
    if ay_core::proof_validation::recognize_int_bound_lattice_gap(terms, clause) {
        return Some(TheoryLemmaKind::IntBoundLatticeGap);
    }
    if ay_core::proof_validation::recognize_int_guarded_split_gap(terms, clause) {
        return Some(TheoryLemmaKind::IntGuardedSplitGap);
    }
    None
}
