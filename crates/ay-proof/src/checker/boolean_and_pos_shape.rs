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
/// Decide, in `O(1)`, whether `clause` is EXACTLY the emitted `and_pos` shape
/// `(cl (not source) source_args[index])` — gate first, indexed conjunct
/// second, both by `TermId` IDENTITY — against an `and`-headed `source`.
///
/// # Why this shape cannot reach a matcher recursion, whatever the conjunct is
///
/// [`and_pos_matchers_are_shallow`] above kills every recursive edge by
/// requiring that no clause literal (and no negand) is `or`-headed. That
/// declines the emitted step whose indexed conjunct IS a disjunction — and on
/// QF_IDL's folded assertion bodies that is the POPULATION: the `EqDiffVar`
/// derivation lane splices `and_pos` steps whose conjunct is an `or` of
/// guards, and each such step was billed the `General` tree product
/// (`work * unfolded_work`, measured 39,695,940 per step on
/// `sal/bakery/inf-bakery-mutex-8` and 511,491,267 on ONE step of
/// `mathsat/fischer/FISCHER5-3-ninc`) for a validation that is O(1). This arm
/// admits that population by pinning the ORDER and the IDENTITIES, which
/// makes headedness irrelevant:
///
///  * `has_gate` scans the clause IN ORDER and short-circuits. Its first
///    probe is `matches_negation_of_term(clause[0], source)`, which opens
///    with `strip_not(lit) == Some(term)` — exactly the identity this arm
///    requires — so it returns `true` on its first comparison and NO other
///    gate probe runs. The second literal is never handed to a matcher here.
///  * `has_conjunct` also scans in order. Its first probe is
///    `matches_positive_literal_of_term((not source), args[index])`:
///    - the identity test fails (`(not source)` cannot equal a strict
///      subterm of `source`: the term DAG is acyclic);
///    - if `args[index]` is not `and`-headed the guard fails in O(1);
///    - if it IS `and`-headed, the recursion is
///      `matches_negation_of_term(source, args[index])`, which is O(1):
///      `strip_not(source)` is `None` (an `and` application),
///      `decode_ite(args[index])` is `None` (`and`-headed), and the `and`
///      arm demands `source` be `or`-headed, which it is not.
///    Its second probe is `clause[1] == args[index]` — the other identity
///    this arm requires — so it returns `true` with no matcher call.
///
/// So on an admitted step the validator performs a constant number of
/// primitives (about two dozen: the length guard, `decode_and_source`'s first
/// branch, the index guard, one `strip_not` identity hit, one O(1)
/// `matches_positive_literal_of_term` miss and one `TermId` identity hit),
/// and the existing `AndPosShallowMatch` charge `32 * payload.work + 32`
/// covers it from its constant tail alone.
///
/// The ORDER is load-bearing, not pedantry: with the clause REVERSED,
/// `has_gate` evaluates the conjunct literal FIRST, and an `or`-headed
/// conjunct whose arity equals the source's enters
/// `matches_negated_components` — the unmemoized De Morgan recursion the
/// doubling refutations in `metering_and_pos.rs` cost at `2^k`. A reversed or
/// otherwise non-identical clause therefore keeps the `General` product.
///
/// This grants NO proof authority and changes NOTHING the checker accepts: it
/// is read only by the charge model, and it fails CLOSED — every step it
/// declines keeps the conservative `General` tree-unfolded product.
pub(crate) fn and_pos_is_emitted_identity_shape(
    terms: &TermStore,
    clause: &[TermId],
    position: u32,
    source_term: Option<TermId>,
) -> bool {
    // The bound is stated over exactly two literals, like the sibling gate.
    if clause.len() != 2 {
        return false;
    }
    let Some(source) = source_term else {
        return false;
    };
    // `and`-headed source: `decode_ite(source)` is structurally `None` and
    // `decode_and_source` is pinned to its first branch.
    let Some(args) = decode_app(terms, source, "and") else {
        return false;
    };
    // A `position` past the argument list is rejected by the validator's own
    // index guard before either scan runs; decline rather than reason about it.
    let Some(&target) = args.get(position as usize) else {
        return false;
    };
    // Gate first, indexed conjunct second, both by identity — see above for
    // why each scan then terminates on its FIRST probe.
    strip_not(terms, clause[0]) == Some(source) && clause[1] == target
}

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
