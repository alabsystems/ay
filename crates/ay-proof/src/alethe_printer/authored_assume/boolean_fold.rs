// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked Boolean-FOLD equivalences for authored assumption spellings.
//!
//! # The claim this removes
//!
//! Elaboration folds Boolean structure over constants and syntactic
//! identities before any proof step exists. `(or (< x 3) false)`,
//! `(= (< x 3) true)`, `(xor (< x 3) false)`, `(distinct (< x 3) false)`,
//! `(ite r A A)` and `(not (and (not A) (= x x)))` all intern as the bare
//! `(< x 3)` / `A`, so the proof's `assume` leaf carries the FOLDED term.
//! Pinned carcara matches every `assume` against the problem file's own text.
//! Measured at `2c356fd15` on `(assert (or (< x 3) false))` +
//! `(assert (>= x 5))` (and the six sibling shapes): AY answered `unsat`,
//! published `(assume t0 (< x 3))` under `foreign_assumes=yes`, carcara 1.1.0
//! answered `invalid` ("could not match term to any of the original problem
//! premises"), and `--strict-proofs` answered `unknown`.
//!
//! # The bridge
//!
//! This leaf of the authored-assume equivalence engine re-derives the fold
//! from the AUTHORED text with carcara's own simplification rules, bottom-up:
//! the operands of a node are folded first (one `cong` over the changed
//! operands), then the node's connective is rewritten by ONE step of its
//! rule, and the result is folded again; the equalities chain with `trans`.
//! The folded text is then handed back to the equivalence engine, so a fold
//! composes with every other leaf (`(and (> x 3) (= x x))` folds to
//! `(> x 3)`, which `comp_simplify` turns into the canonical `(< 3 x)`).
//!
//! Every rewrite is an exact mirror of one step of the rule in
//! `carcara/src/checker/rules/simplification.rs` (and `clausification.rs`,
//! `tautology.rs`) at git `9a352ee`:
//!
//! * `and_simplify` / `or_simplify` (`generic_and_or_simplify`): drop the
//!   neutral constant, drop repeated operands (first occurrence kept), then
//!   short-circuit on the absorbing constant or on a complementary pair read
//!   through all leading `not`s. A single survivor that is itself an
//!   application of the same operator is declined: carcara reads such a
//!   result as ITS operands and cannot state it.
//! * `not_simplify`, `equiv_simplify`, `eq_simplify` (only its reflexive
//!   pattern; the numeric-constant pattern reads `as_signed_number` and is
//!   never emitted), `ite_simplify`, `implies_simplify`: carcara applies the
//!   FIRST pattern that matches and accepts a step whose right side is that
//!   one rewrite, so the mirror computes exactly the first matching pattern
//!   in carcara's order and emits nothing when that pattern is one it does
//!   not reproduce (`ite_simplify`'s two nested-condition patterns).
//! * `distinct_elim` on a binary `distinct`, and `connective_def` on a
//!   binary `xor` with a constant or repeated operand (carcara has no
//!   `xor_simplify`): these only RE-SPELL a connective, so on their own they
//!   are not a fold (see `normalize::Normalized::folded`).
//!
//! Term identity is carcara's parser identity on printed text
//! (`surface_literal::same_printed_term`): identical bytes, or bit-vector literals spelled
//! two ways.
//!
//! Anything else declines and the caller keeps its existing arms: the
//! folded-conjunction projection, the other bridges, or the honest
//! `foreign_assumes` disclosure. No `hole` is ever introduced here.
//!
//! The fold also declines under a bridge root with a strict descendant or a
//! strict ancestor the producer re-spelled: confining the root beside that
//! spelling would print one term two ways ([`document_spelling`]).

mod document_equivalence;
mod document_spelling;
mod mirror;
mod normalize;

#[cfg(test)]
pub(super) use document_equivalence::render_folded_document_equivalence;
pub(super) use document_equivalence::render_folded_document_equivalence_with_progress;
pub(in crate::alethe_printer) use document_spelling::BooleanFoldScope;

use super::super::quantifier_surface::printed_terms_alpha_equivalent;
use super::*;
use mirror::negation_operand;
use normalize::fold_surface_with_progress;

/// The [`AuthoredAssumeBridge::FoldedLinearImplication`] bridge for the
/// `assume` `id`, with the fold's node count: the authored `surface` folds to
/// an arithmetic comparison, and one unit `la_generic` implication (the
/// checked two-row schema of
/// [`crate::printed_la_generic_unit_implication_is_supported`]) yields the
/// canonical comparison. The canonical term is what the rest of the document
/// prints, so no authored text rides past the `assume`.
///
/// ```text
/// (assume t0.a (or (< y 2.5) false))
/// (step t0.n (cl (= (or (< y 2.5) false) (< y 2.5))) :rule or_simplify)
/// (step t0.e (cl (not (= (or (< y 2.5) false) (< y 2.5))) (not (or (< y 2.5) false)) (< y 2.5)) :rule equiv_pos2)
/// (step t0.f (cl (< y 2.5)) :rule resolution :premises (t0.e t0.n t0.a))
/// (step t0.l (cl (not (< y 2.5)) (< y (/ 5.0 2.0))) :rule la_generic :args (1 1))
/// (step t0 (cl (< y (/ 5.0 2.0))) :rule resolution :premises (t0.l t0.f))
/// ```
pub(super) fn render_folded_linear_implication_with_progress(
    id: impl std::fmt::Display,
    surface: &str,
    canonical: &str,
    progress: &mut dyn FnMut(u64) -> bool,
) -> (Option<String>, usize) {
    let mut nodes = 0;
    let fold_id = format!("{id}.n");
    let Some((folded, steps, true)) =
        fold_surface_with_progress(surface, &fold_id, 0, &mut nodes, progress)
    else {
        return (None, nodes);
    };
    if folded == canonical
        || !crate::printed_la_generic_unit_implication_is_supported(&folded, canonical)
    {
        return (None, nodes);
    }
    let output_bound = steps
        .iter()
        .try_fold(1024usize, |sum, step| sum.checked_add(step.len() + 1))
        .and_then(|sum| {
            surface
                .len()
                .checked_add(folded.len())
                .and_then(|sum| sum.checked_add(canonical.len()))
                .and_then(|text| text.checked_mul(16))
                .and_then(|text| sum.checked_add(text))
        });
    let Some(output_bound) = output_bound.and_then(|bytes| u64::try_from(bytes).ok()) else {
        return (None, nodes);
    };
    if !progress(output_bound) {
        return (None, nodes);
    }
    let mut output = format!("(assume {id}.a {surface})\n");
    for step in steps {
        output.push_str(&step);
        output.push('\n');
    }
    output.push_str(&format!(
        "(step {id}.e (cl (not (= {surface} {folded})) (not {surface}) {folded}) :rule equiv_pos2)\n\
         (step {id}.f (cl {folded}) :rule resolution :premises ({id}.e {fold_id} {id}.a))\n\
         (step {id}.l (cl (not {folded}) {canonical}) :rule la_generic :args (1 1))\n\
         (step {id} (cl {canonical}) :rule resolution :premises ({id}.l {id}.f))"
    ));
    (Some(output), nodes)
}

/// Whether `surface` carries a construct the fold must not read through: an
/// annotation (carcara 1.1.0's `:named` capture), a `let`, or a binder.
fn fold_reads_opaque_syntax(surface: &str) -> bool {
    [
        "(! ", "(let ", "(forall ", "(exists ", "(match ", "(lambda ",
    ]
    .iter()
    .any(|marker| surface.contains(marker))
}

impl AlethePrinter<'_> {
    /// The producer-side preflight behind
    /// [`crate::folded_authored_assume_bridge_is_supported`]: the planner's
    /// admission bounds, then its equivalence attempt, then the
    /// folded-conjunction projection `plan_folded_and_assumes` owns.
    pub(crate) fn folded_authored_assume_bridge_supported(
        &self,
        term: TermId,
        surface: &str,
    ) -> bool {
        if !self.admit_emission_work(surface.len() as u64) {
            return false;
        }
        if surface.len() > MAX_EQUIVALENCE_BYTES
            || !matches!(self.terms.sort(term), Sort::Bool)
            || !canonical_term_is_bounded_for_authored_assume(self.terms, term).is_bounded()
        {
            return false;
        }
        let Some(charge) = bounds::canonical_rendering_work_upper_bound(self.terms, term) else {
            return false;
        };
        if !self.admit_emission_work(charge) {
            return false;
        }
        let canonical = crate::render_term_canonical(self.terms, term);
        if surface == canonical
            || surface
                .len()
                .checked_add(canonical.len())
                .is_none_or(|bytes| bytes > MAX_EQUIVALENCE_BYTES)
        {
            return false;
        }
        self.authored_equivalence("probe", surface, term, &mut 0, &mut Vec::new())
            || self.folded_linear_implication_admitted(term, surface, &canonical)
            || self.folded_conjunction_projection_supported(term, surface)
    }

    /// Whether [`AuthoredAssumeBridge::FoldedLinearImplication`] applies: a
    /// genuine fold of `surface` onto an arithmetic comparison that the unit
    /// `la_generic` implication turns into `canonical`. An authored `and` over
    /// a term that is no conjunction stays the projection's, as in
    /// [`Self::boolean_fold_step`].
    pub(super) fn folded_linear_implication_admitted(
        &self,
        term: TermId,
        surface: &str,
        canonical: &str,
    ) -> bool {
        let canonical_is_conjunction = matches!(
            self.terms.get(term),
            TermData::App(symbol, _) if symbol.name() == "and"
        );
        if fold_reads_opaque_syntax(surface)
            || (split_application(surface, "and").is_some() && !canonical_is_conjunction)
            || !self.fold_root_is_coherent(term)
        {
            return false;
        }
        render_folded_linear_implication_with_progress("probe", surface, canonical, &mut |amount| {
            self.admit_emission_work(amount)
        })
        .0
        .is_some()
    }

    /// The Boolean-fold leaf: fold `surface` with checked simplification
    /// steps, then bridge the folded text to the canonical term with the rest
    /// of the equivalence engine.
    ///
    /// Declines, and leaves the caller's other arms in place, when:
    /// * the schema reads no authored spellings, or the direction is not
    ///   surface-to-canonical;
    /// * at the root of a bridge (`depth == 0`): the surface is an authored
    ///   `and` over a canonical term that is no conjunction (the
    ///   folded-conjunction projection owns it: `and_pos` needs no dropped
    ///   conjunct to be trivially true), a pure `not` shell (the negation
    ///   shell channel owns it), or nothing but a connective re-spelling
    ///   fired (`distinct_elim` alone is the dedicated distinct bridge's);
    /// * the surface names an annotation, a `let` or a binder;
    /// * another override re-spells a strict descendant or a strict ancestor
    ///   of the bridge ROOT ([`document_spelling`]).
    #[expect(
        clippy::too_many_arguments,
        reason = "the exact authored/canonical proof schema and traversal ledgers stay explicit"
    )]
    pub(super) fn boolean_fold_step(
        &self,
        id: &str,
        surface: &str,
        canonical: &str,
        canonical_term: TermId,
        schema: EquivalenceLeafSchema,
        direction: EquivalenceDirection,
        depth: usize,
        nodes: &mut usize,
        output: &mut Vec<String>,
        shared: Option<&shared_canonical::SharedInput<'_>>,
    ) -> bool {
        if shared.is_some() {
            return false;
        }

        if !schema.reads_authored_spellings()
            || !matches!(direction, EquivalenceDirection::SurfaceToCanonical)
            || fold_reads_opaque_syntax(surface)
            || !self.boolean_fold_scope_is_coherent()
        {
            return false;
        }
        if depth == 0 {
            let canonical_is_conjunction = matches!(
                self.terms.get(canonical_term),
                TermData::App(symbol, _) if symbol.name() == "and"
            );
            if (split_application(surface, "and").is_some() && !canonical_is_conjunction)
                || negation_shell_pairs(surface, canonical).is_some()
            {
                return false;
            }
        }
        // Dry run under throwaway ids: learn the folded text, then emit under
        // the ids the result needs. The fold is a pure function of the text.
        let mut dry_nodes = *nodes;
        let Some((folded_text, _, folded)) =
            fold_surface_with_progress(surface, id, depth, &mut dry_nodes, &mut |amount| {
                self.admit_emission_work(amount)
            })
        else {
            return false;
        };
        if !folded && depth == 0 {
            return false;
        }
        if folded_text == canonical {
            let Some((_, steps, _)) =
                fold_surface_with_progress(surface, id, depth, nodes, &mut |amount| {
                    self.admit_emission_work(amount)
                })
            else {
                return false;
            };
            output.extend(steps);
            return true;
        }
        let fold_id = format!("{id}.f");
        let Some((folded_text, steps, _)) =
            fold_surface_with_progress(surface, &fold_id, depth, nodes, &mut |amount| {
                self.admit_emission_work(amount)
            })
        else {
            return false;
        };
        let mark = output.len();
        output.extend(steps);
        let rest_id = format!("{id}.r");
        if !self.fold_remainder(
            &rest_id,
            &folded_text,
            canonical,
            canonical_term,
            schema,
            direction,
            depth + 1,
            nodes,
            output,
        ) {
            output.truncate(mark);
            return false;
        }
        output.push(format!(
            "(step {id} (cl (= {surface} {canonical})) :rule trans :premises ({fold_id} {rest_id}))"
        ));
        true
    }
}

impl AlethePrinter<'_> {
    /// The equality between a folded text and the canonical rendering it
    /// differs from, under `id`:
    ///
    /// * `refl` when carcara's `alpha_equiv` already identifies them (it reads
    ///   equalities modulo operand order: the fold of `(or (= (f a) c) false)`
    ///   is `(= (f a) c)` while AY stores `(= c (f a))`);
    /// * `cong` under a shared `not`, recursively (`(= (> x 3) false)` folds to
    ///   `(not (> x 3))` over the canonical `(not (< 3 x))`);
    /// * otherwise the rest of the equivalence engine.
    #[expect(
        clippy::too_many_arguments,
        reason = "the exact authored/canonical proof schema and traversal ledgers stay explicit"
    )]
    fn fold_remainder(
        &self,
        id: &str,
        text: &str,
        canonical: &str,
        canonical_term: TermId,
        schema: EquivalenceLeafSchema,
        direction: EquivalenceDirection,
        depth: usize,
        nodes: &mut usize,
        output: &mut Vec<String>,
    ) -> bool {
        if depth > MAX_EQUIVALENCE_DEPTH
            || *nodes >= MAX_EQUIVALENCE_NODES
            || !self.admit_emission_work(text.len() as u64 + canonical.len() as u64)
        {
            return false;
        }
        *nodes += 1;
        if printed_terms_alpha_equivalent(text, canonical) {
            output.push(format!(
                "(step {id} (cl (= {text} {canonical})) :rule refl)"
            ));
            return true;
        }
        if let (Some(operand), TermData::Not(inner)) =
            (negation_operand(text), self.terms.get(canonical_term))
        {
            let inner = *inner;
            let inner_canonical = crate::render_term_canonical(self.terms, inner);
            let child_id = format!("{id}.c0");
            let mark = output.len();
            if operand != inner_canonical
                && self.fold_remainder(
                    &child_id,
                    &operand,
                    &inner_canonical,
                    inner,
                    schema,
                    direction,
                    depth + 1,
                    nodes,
                    output,
                )
            {
                output.push(format!(
                    "(step {id} (cl (= {text} {canonical})) :rule cong :premises ({child_id}))"
                ));
                return true;
            }
            output.truncate(mark);
        }
        self.build_authored_surface_equivalence(
            id,
            text,
            canonical_term,
            schema,
            direction,
            depth,
            nodes,
            output,
            None,
        )
    }
}

#[cfg(test)]
#[path = "boolean_fold/tests.rs"]
mod tests;
