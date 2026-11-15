// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An authored arithmetic comparison against the canonical comparison that
//! states it with its operands swapped.
//!
//! Elaboration stores `(>= y 0)` as `(<= 0 y)` and `(> x 5)` as `(< 5 x)`. The
//! authored-assume equivalence engine already bridges such a pair at the root
//! of an `assume` (`authored_assume::comparison_reversal_step`); this schema
//! lets a derivation over the DOCUMENT's rendering use the same `comp_simplify`
//! steps for a comparison nested in a larger authored term. MEASURED at
//! `e9ba9acac`: `(=> (>= y 0) (<= x 3))` over the canonical
//! `(or (<= x 3) (not (<= 0 y)))`, once its antecedent's own row confines
//! `(<= 0 y)` to that text, pairs the literal `(not (>= y 0))` with the
//! disjunct `(not (<= 0 y))` and no other schema relates the two comparisons.
//!
//! Each step is pinned carcara's `comp_simplify` over the exact printed text
//! (`checker/rules/simplification.rs` at `9a352ee`): one step for a
//! non-strict pair, and the `(not (<= ..))` detour joined by `trans` for a
//! strict one, because `comp_simplify` rewrites `(> a b)` to
//! `(not (<= a b))`, never to `(< b a)`; a strict pair whose `(< ..)` leg
//! pinned carcara would EVALUATE instead (two numerals, one term twice) is
//! declined (`authored_assume/comp_simplify_evaluation.rs`), so a ground
//! `forall_inst` instance such as `(> 3 3)` keeps the document it had before
//! this schema. The canonical node must be an
//! arithmetic comparison over `Int` or `Real` whose text is the document's
//! rendering of its operands, and the authored operands must be those texts
//! verbatim. Admitted only on a second attempt, after every established
//! schema declined the whole pair, so a pair an established schema relates
//! keeps its derivation byte for byte. A pair only this schema relates is now
//! bridged wherever a printed equivalence is asked for: the authored-assume
//! document bridge, and also the confined `forall_inst` instance, whose
//! authored `(> (f a0) a0)` is confined to its `forall_inst` and derived onto
//! the canonical `(< a0 (f a0))` instead of riding the document (pinned
//! carcara checks those documents `valid`; one that held a `hole` for the
//! pair, `(=> (>= y 0) (P (g y)))` instantiated at a Skolem witness, no
//! longer does).

use super::super::authored_assume::{comparison_reversal_step, EquivalenceDirection};
use super::super::*;
use super::{CanonicalNode, Derivation, SchemaTier};

impl AlethePrinter<'_> {
    /// `(= surface canonical)` for an operand-swapped arithmetic comparison,
    /// or `false` with `derivation` unchanged.
    pub(super) fn arithmetic_comparison_reversal(
        &self,
        id: &str,
        surface: &str,
        canonical: CanonicalNode<'_>,
        derivation: &mut Derivation,
    ) -> bool {
        if derivation.tier != SchemaTier::Extended {
            return false;
        }
        let TermData::App(symbol, args) = self.terms.get(canonical.term) else {
            return false;
        };
        let head = Self::format_symbol(symbol);
        if !matches!(head.as_str(), "<=" | ">=" | "<" | ">") {
            return false;
        }
        let [left, _] = args.as_slice() else {
            return false;
        };
        if !matches!(self.terms.sort(*left), Sort::Int | Sort::Real)
            || self.canonical_printed_children(canonical, &head).is_none()
        {
            return false;
        }
        comparison_reversal_step(
            id,
            surface,
            canonical.text,
            EquivalenceDirection::SurfaceToCanonical,
            &mut derivation.steps,
        )
    }
}
