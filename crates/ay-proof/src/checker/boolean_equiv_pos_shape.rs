// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The `O(1)` shape test that licenses charging `equiv_pos1`/`equiv_pos2` on
//! the step's reachable DAG instead of its tree-unfolded product.
//!
//! Everything this module knows is a claim about the control flow of
//! [`super::boolean_derived::validate_equiv_pos1`] and
//! [`super::boolean_derived::validate_equiv_pos2`], and it reads the SAME
//! `decode_app`/`strip_not` decoders those validators read, so the two cannot
//! disagree about what an equality or a negation is.

use ay_core::{TermId, TermStore};

use super::boolean::{decode_app, strip_not};

/// Decide, in `O(1)`, whether `clause` is EXACTLY the emitted
/// `equiv_pos2` shape `(cl (not (= a b)) (not a) b)` (`positive == true`) or
/// the emitted `equiv_pos1` shape `(cl (not (= a b)) a (not b))`
/// (`positive == false`): gate first, then the two operand literals in operand
/// order, every literal by `TermId` identity.
///
/// # Why the validator is constant-time on exactly this shape
///
/// Both validators are `check_any_candidate` over `negated_apps(clause, "=")`
/// with one `clause_matches_expected` per candidate, against
/// `[Lit(gate), Not(a), Lit(b)]` (`equiv_pos2`) or `[Lit(gate), Lit(a),
/// Not(b)]` (`equiv_pos1`). The only recursive helper on that path is
/// `matches_negation_of_term`, reached through an `ExpectedLit::Not` entry.
///
///  * `negated_apps` yields `clause[0]` FIRST (it is a negated binary `=`), so
///    the first candidate is the gate and its `args` are `[a, b]`.
///  * `clause_matches_expected` scans the clause in order and, per literal,
///    the expected entries in order, skipping matched ones before any matcher
///    runs. `clause[0]` matches entry 0 by identity on the first probe. For
///    `clause[1]`, entry 0 is matched and skipped, entry 1 is probed first:
///    `equiv_pos2`'s `matches_negation_of_term(clause[1], a)` opens with
///    `strip_not(clause[1]) == Some(a)`, which this predicate demands, so it
///    returns on its first comparison; `equiv_pos1`'s `Lit(a)` is one
///    `TermId` comparison. For `clause[2]`, entries 0 and 1 are skipped and
///    entry 2 is the identity `Lit(b)` (`equiv_pos2`) or the
///    `strip_not(clause[2]) == Some(b)` opening of `matches_negation_of_term`
///    (`equiv_pos1`).
///
/// So the whole validation is a fixed program of about thirty primitive reads
/// and comparisons and one three-entry `matched` vector, whatever `a` and `b`
/// are. The De Morgan / `ite` arms of `matches_negation_of_term` are never
/// entered: every probe that reaches it returns on its opening identity test.
///
/// This grants NO proof authority and changes NOTHING the checker accepts: it
/// is read only by the charge model. It fails CLOSED — every step it declines
/// (any other order, a double-negation-collapsed operand, a non-binary or
/// non-`=` gate, a wider clause) keeps the conservative `General` product.
pub(crate) fn equiv_pos_is_emitted_identity_shape(
    terms: &TermStore,
    clause: &[TermId],
    positive: bool,
) -> bool {
    let [gate, first, second] = clause else {
        return false;
    };
    let Some(equality) = strip_not(terms, *gate) else {
        return false;
    };
    let Some([a, b]) = decode_app(terms, equality, "=") else {
        return false;
    };
    if positive {
        strip_not(terms, *first) == Some(*a) && *second == *b
    } else {
        *first == *a && strip_not(terms, *second) == Some(*b)
    }
}
