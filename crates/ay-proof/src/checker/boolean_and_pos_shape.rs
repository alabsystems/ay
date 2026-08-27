// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The `O(1)` shape test that licenses charging `and_pos` on its reachable DAG.
//!
//! A sibling of [`super::boolean`] rather than a part of it only because that
//! file is at its size ceiling; everything this module knows is a claim about
//! [`super::boolean::validate_and_pos`]'s control flow, and it uses that
//! module's OWN decoders so the two cannot disagree about what an `or`-headed
//! literal is.

use ay_core::{TermId, TermStore};

use super::boolean::{decode_app, strip_not};

/// Decide, in `O(1)`, whether [`super::boolean::validate_and_pos`]'s two negation matchers are
/// STRUCTURALLY UNABLE to recurse on this step — i.e. whether the whole
/// validator is bounded by the step's reachable DAG rather than by its tree
/// unfolding.
///
/// It is a claim about `validate_and_pos`'s control flow, and it is the
/// metering side's only licence to charge that rule on `payload.work`
/// (`SemanticChargeClass::AndPosShallowMatch`). It reads the SAME `decode_app`
/// and `strip_not` the validator does, so the two cannot drift apart on what
/// an `or`-headed literal is.
///
/// # What the validator can spend, and where
///
/// `validate_and_pos` calls exactly two recursive helpers:
///
///  * the GATE scan's `matches_negation_of_term``(lit, source_term)`; and
///  * the CONJUNCT scan's `matches_positive_literal_of_term``(lit, args[i])`.
///
/// Everything else it does — the length guard, `decode_and_source`, the index
/// guard, and the `inner_args == args` slice comparison — is one pass over the
/// clause and one over the source's argument list.
///
/// `matches_negation_of_term``(lit, term)` recurses ONLY through
/// `decode_ite(term)`, `TermData::Not(_)`, and the two De Morgan arms, and BOTH
/// De Morgan arms open by demanding the literal be headed by the DUAL connective
/// (`term` an `and` needs `lit` an `or`, and vice versa). So:
///
///  * with `source_term` an `and` application, `decode_ite` is `None` and the
///    only live arm is the `and` one, which returns `false` in `O(1)` unless the
///    literal is `or`-headed;
///  * `matches_positive_literal_of_term``(lit, args[i])` descends only when
///    `args[i]` is `and`-headed, and then only into
///    `matches_negation_of_term(strip_not(lit), args[i])` — which by the same
///    argument returns `false` in `O(1)` unless `strip_not(lit)` is `or`-headed.
///
/// Requiring that NO clause literal is `or`-headed and that NO clause literal's
/// negand is `or`-headed therefore kills every recursive edge on both call
/// sites, whatever the indexed conjunct looks like.
///
/// This grants NO proof authority and changes NOTHING the checker accepts: it is
/// read only by the charge model. It fails CLOSED — every step it declines keeps
/// the conservative `General` tree-unfolded product.
pub(crate) fn and_pos_matchers_are_shallow(
    terms: &TermStore,
    clause: &[TermId],
    source_term: Option<TermId>,
) -> bool {
    // Anything else is refused by the length guard before a matcher runs, but
    // the bound below is stated over exactly two literals, so say so.
    if clause.len() != 2 {
        return false;
    }
    // The `and`-headed source is what makes `decode_ite` structurally `None` and
    // pins `decode_and_source` to its first branch (so the slice compared
    // against `inner_args` is this term's own argument list).
    let Some(source) = source_term else {
        return false;
    };
    if decode_app(terms, source, "and").is_none() {
        return false;
    }
    clause.iter().copied().all(|lit| {
        decode_app(terms, lit, "or").is_none()
            && strip_not(terms, lit).is_none_or(|inner| decode_app(terms, inner, "or").is_none())
    })
}
