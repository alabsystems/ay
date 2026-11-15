// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Which channel an Int equality or `distinct` takes in the combined
//! adapters (#compound-side-bv2nat-channel).

use super::{is_compound_arith_term, is_lia_relevant_term};
use ay_core::term::{Symbol, TermData};
use ay_core::{TermId, TermStore};

/// True when `term` is a `bv2nat` application: the BV/LIA bridge's Int view
/// of a bit-vector term (`bv2int` and `ubv_to_int` elaborate to it).
fn is_bv2nat_bridge_term(terms: &TermStore, term: TermId) -> bool {
    matches!(
        terms.get(term),
        TermData::App(Symbol::Named(name), args) if name == "bv2nat" && args.len() == 1
    )
}

/// Whether the Int arithmetic channel (`assert_literal`) claims an equality
/// or `distinct` over `sides`: every side is LIA-relevant, or some side is a
/// compound arithmetic application ([`is_compound_arith_term`]) and no side
/// is a bare `bv2nat` term (#compound-side-bv2nat-channel).
///
/// The compound rule (a628c3b2a) is for an arithmetic relation with an
/// uninterpreted leaf, such as the symbolic-div decomposition
/// `(= a (+ (* (p 3) q) r))` or its UF-dividend form
/// `(= (f 0) (+ (* (p 3) q) r))`, which the arithmetic solver cannot see
/// otherwise. The `bv2nat` exemption leaves the BV/LIA bridge's definitional
/// equalities on the channel they had before that rule: the shared-equality
/// channel (`is_uf_int_equality`) where the adapter has one, EUF otherwise.
/// Those equalities are the exact residue congruence
/// `(= (bv2nat (int2bv w s)) (- s (* 2^w k)))` and the extract links
/// `(= (bv2nat t) (+ (* 2^(h+1) hi) ...))`.
///
/// Claiming them for `assert_literal` changed which AUF/LIA candidate the
/// bridge finds first in later incremental checks. The candidates of
/// `bv_lia_int_blast_lane`'s `hi_00222` check 3 (default) and `hi_00483`
/// check 3 (`--z3-mode`) then violated a bit constraint the bridge does not
/// encode (a `zero_extend` or `extract` of an `int2bv` against a constant).
/// The model gate rejected them, the Int-blast lane did not decide those
/// checks, and two pinned `sat` results became `unknown`.
pub(super) fn int_arith_channel_claims(terms: &TermStore, sides: &[TermId]) -> bool {
    sides.iter().all(|&side| is_lia_relevant_term(terms, side))
        || (sides
            .iter()
            .any(|&side| is_compound_arith_term(terms, side))
            && !sides.iter().any(|&side| is_bv2nat_bridge_term(terms, side)))
}
