// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authored `assume` bridges that read nullary `define-fun` premises.
//!
//! AY's frontend expands a nullary macro at every use, so no stored term names
//! it and the strict checker validates the EXPANDED assertion. Pinned carcara
//! 1.1.0, run without `--apply-function-defs`, instead reads
//! `(define-fun a () S body)` as a declaration of `a` plus the problem premise
//! `(= a body)`, and matches every `assume` against the authored text. The
//! authored spelling `(= v0 one)` of the canonical `(= v0 #b1)` is therefore
//! bridged exactly like any other authored spelling (`cong` under the
//! canonical head, `equiv_pos2`, `resolution`), with one extra leaf: where the
//! authored text names `one`, the leaf equality `(= one #b1)` IS that premise
//! and is `assume`d verbatim.
//!
//! MEASURED on pinned carcara (git 9a352ee): the bridge with
//! `(assume t0.n.c1 (= one #b1))` checks, while `(assume _ (= one #b0))` is
//! refused as "could not match term to any of the original problem premises".
//! An operand that differs only in bit-vector literal spelling
//! (`(_ bv16 64)` against `#b0…010000`) is one term to carcara's parser, so
//! `cong` needs no premise for it (`same_printed_term`); a macro body that
//! names another macro is bridged recursively and joined with `trans`, and an
//! authored double negation the canonical term no longer carries is stripped
//! with `not_simplify` (`double_negation_step`).
//!
//! This is its own schema, tried only after the ordinary equivalence bridge
//! declines and only when the export carries a definition table, so every
//! document without one plans exactly as before.

use super::super::surface_literal::same_printed_term;
use super::*;

impl EquivalenceLeafSchema {
    /// Whether authored-only respellings (Boolean folds of the authored text)
    /// are leaves here.
    pub(super) fn reads_authored_spellings(self) -> bool {
        matches!(self, Self::AuthoredAssume | Self::NullaryDefinition)
    }

    /// Whether a canonical `not` (a term constructor, not a symbol
    /// application) is a `cong` head. Only the definition schema reads it:
    /// `(assert (not lo))` over `(define-fun lo () Bool (bvult x #x3))` is
    /// bridged as `cong` over the leaf `(= lo (bvult x #x3))`, which pinned
    /// carcara 1.1.0 checks. Every document without a definition table keeps
    /// planning exactly as before.
    pub(super) fn congruent_under_not(self) -> bool {
        matches!(self, Self::NullaryDefinition)
    }

    /// Whether a canonical `ite` (a term constructor, not a symbol
    /// application) is a `cong` head. Only the definition schema reads it:
    /// `(assert (ite m1 (= x a) (= x b)))` over `(define-fun m1 () Bool (=
    /// mode #b0))` is bridged as `cong` over the leaf `(= m1 (= mode #b0))`,
    /// which pinned carcara 1.1.0 checks. MEASURED on
    /// `benchmarks/smt/known_bugs/bv_ite_shared_vars_minimal.smt2` before this
    /// arm: the query published the expanded `(assume t0 (ite (= mode_1 #b0)
    /// ..))` under `foreign_assumes=yes`, and pinned carcara refused it
    /// ("could not match term to any of the original problem premises").
    pub(super) fn congruent_under_ite(self) -> bool {
        matches!(self, Self::NullaryDefinition)
    }

    /// Whether `cong` needs no premise for this operand pair: identical text,
    /// or, under the definition schema only, text that differs just in
    /// bit-vector literal spelling (one term to carcara's parser).
    pub(super) fn needs_no_premise(self, surface: &str, canonical: &str) -> bool {
        surface == canonical
            || (matches!(self, Self::NullaryDefinition) && same_printed_term(surface, canonical))
    }
}

impl AlethePrinter<'_> {
    /// A leaf where the authored text names a nullary `define-fun`; `false`
    /// outside [`EquivalenceLeafSchema::NullaryDefinition`].
    ///
    /// The premise `(= name body)` is `assume`d verbatim. When the body prints
    /// as the canonical text (up to literal spelling) that premise is the
    /// leaf's equality; otherwise the body is bridged to the canonical term
    /// by the same schema (a nested macro, a literal respelling) and the two
    /// equalities are joined by `trans`; a body an earlier occurrence of the
    /// macro already bridged is cited, not derived again (`shared_body.rs`).
    /// The canonical-to-surface orientation flips the result with one `symm`.
    /// Anything the schema cannot bridge declines, and the caller keeps its
    /// ordinary fail-closed handling.
    #[expect(
        clippy::too_many_arguments,
        reason = "the exact nullary-definition proof schema and traversal ledgers stay explicit"
    )]
    pub(super) fn nullary_definition_leaf_step(
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
        if !matches!(schema, EquivalenceLeafSchema::NullaryDefinition) {
            return false;
        }
        let Some(body) = self
            .nullary_definitions
            .and_then(|definitions| definitions.get(surface))
        else {
            return false;
        };
        let forward_id = match direction {
            EquivalenceDirection::SurfaceToCanonical => id.to_string(),
            EquivalenceDirection::CanonicalToSurface => format!("{id}.f"),
        };
        if same_printed_term(body, canonical) {
            output.push(format!("(assume {forward_id} (= {surface} {body}))"));
        } else {
            let definition_id = format!("{id}.d");
            output.push(format!("(assume {definition_id} (= {surface} {body}))"));
            // An earlier occurrence of the macro already bridged its body.
            let body_id = match shared_body::earlier_equality_step(output, body, canonical) {
                Some(earlier) => earlier,
                None => {
                    let body_id = format!("{id}.b");
                    if !self.build_authored_surface_equivalence(
                        &body_id,
                        body,
                        canonical_term,
                        schema,
                        EquivalenceDirection::SurfaceToCanonical,
                        depth + 1,
                        nodes,
                        output,
                        shared,
                    ) {
                        return false;
                    }
                    body_id
                }
            };
            output.push(format!(
                "(step {forward_id} (cl (= {surface} {canonical})) :rule trans :premises \
                 ({definition_id} {body_id}))"
            ));
        }
        if matches!(direction, EquivalenceDirection::CanonicalToSurface) {
            output.push(format!(
                "(step {id} (cl (= {canonical} {surface})) :rule symm :premises ({forward_id}))"
            ));
        }
        true
    }

    /// `(not (not inner))` against a canonical term that `cong` could not
    /// reach; `false` outside [`EquivalenceLeafSchema::NullaryDefinition`].
    ///
    /// `TermStore::mk_not` drops a double negation at construction, so
    /// `(assert (not (not lo)))` over `(define-fun lo () Bool (< x 3))` has the
    /// canonical root `(< x 3)`: no `not` head is left for `cong`, and the
    /// negation-shell channel strips shells only down to the PRINTED text,
    /// which is not `lo`. `not_simplify` proves `(= (not (not lo)) lo)` and
    /// the schema bridges `lo` to the canonical term through its definition
    /// premise, joined by `trans`. MEASURED at the base on Int, Real, UF,
    /// array, equality and macro-of-macro bodies: the query published the
    /// canonical `(assume t0 (< x 3))` under `foreign_assumes=yes`, and pinned
    /// carcara 1.1.0 refused it ("could not match term to any of the original
    /// problem premises"); it checks `(step _ (cl (= (not (not m)) m)) :rule
    /// not_simplify)` and refuses `(= (not (not m)) (not m))`.
    #[expect(
        clippy::too_many_arguments,
        reason = "the exact nullary-definition proof schema and traversal ledgers stay explicit"
    )]
    pub(super) fn double_negation_step(
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
        // The shared-input lane borrows positional congruence arguments;
        // other existing schemas retain their ordinary bounded renderer.
        if shared.is_some() {
            return false;
        }
        if !matches!(schema, EquivalenceLeafSchema::NullaryDefinition) {
            return false;
        }
        let Some(once) = negation_operand(surface) else {
            return false;
        };
        let forward_id = match direction {
            EquivalenceDirection::SurfaceToCanonical => id.to_string(),
            EquivalenceDirection::CanonicalToSurface => format!("{id}.f"),
        };
        let mut premises = Vec::new();
        let (doubled, inner) = match negation_operand(&once) {
            Some(inner) => (surface.to_string(), inner),
            None => {
                let Some((doubled, inner)) =
                    self.negated_macro_unfolding(id, surface, &once, output)
                else {
                    return false;
                };
                premises.push(format!("{id}.nu"));
                (doubled, inner)
            }
        };
        if premises.is_empty() && schema.needs_no_premise(&inner, canonical) {
            output.push(format!(
                "(step {forward_id} (cl (= {surface} {canonical})) :rule not_simplify)"
            ));
        } else {
            let strip_id = format!("{id}.nn");
            output.push(format!(
                "(step {strip_id} (cl (= {doubled} {inner})) :rule not_simplify)"
            ));
            premises.push(strip_id);
            if !schema.needs_no_premise(&inner, canonical) {
                let inner_id = format!("{id}.nb");
                if !self.build_authored_surface_equivalence(
                    &inner_id,
                    &inner,
                    canonical_term,
                    schema,
                    EquivalenceDirection::SurfaceToCanonical,
                    depth + 1,
                    nodes,
                    output,
                    None,
                ) {
                    return false;
                }
                premises.push(inner_id);
            }
            output.push(format!(
                "(step {forward_id} (cl (= {surface} {canonical})) :rule trans :premises ({}))",
                premises.join(" ")
            ));
        }
        if matches!(direction, EquivalenceDirection::CanonicalToSurface) {
            output.push(format!(
                "(step {id} (cl (= {canonical} {surface})) :rule symm :premises ({forward_id}))"
            ));
        }
        true
    }

    /// `(not m)` over a nullary macro `m` whose definition body is itself a
    /// negation `(not inner)`: `assume`s the premise `(= m (not inner))` as
    /// `{id}.nd`, rewrites the surface with `cong` to `(not (not inner))` as
    /// `{id}.nu`, and returns that doubled text with `inner`, for
    /// [`Self::double_negation_step`] to strip. `None` for anything else.
    ///
    /// `mk_not` drops the double negation the unfolding exposes, so `(assert
    /// (not nlo))` over `(define-fun nlo () Bool (not (< x 3)))`, and `(assert
    /// (not hi))` over `(define-fun hi () Bool (not lo))`, have the canonical
    /// root `(< x 3)`: no `not` head is left for `cong`, and the authored text
    /// carries no textual double negation. MEASURED with the bare-symbol and
    /// double-negation bridges alone, on Int, Real and `>=` bodies (also
    /// `(assert top)` over `(define-fun top () Bool (not hi))`): the query
    /// published the canonical `(assume t0 (< x 3))` under
    /// `foreign_assumes=yes`, and pinned carcara 1.1.0 refused it ("could not
    /// match term to any of the original problem premises").
    fn negated_macro_unfolding(
        &self,
        id: &str,
        surface: &str,
        operand: &str,
        output: &mut Vec<String>,
    ) -> Option<(String, String)> {
        let body = self.nullary_definitions?.get(operand)?;
        let inner = negation_operand(body)?;
        let doubled = format!("(not {body})");
        output.push(format!("(assume {id}.nd (= {operand} {body}))"));
        output.push(format!(
            "(step {id}.nu (cl (= {surface} {doubled})) :rule cong :premises ({id}.nd))"
        ));
        Some((doubled, inner))
    }

    /// `(= a b)` against a canonical `(= b' a')`, the operands swapped;
    /// `false` outside [`EquivalenceLeafSchema::NullaryDefinition`].
    ///
    /// The term store orients a binary equality, so `(assert lo)` over
    /// `(define-fun lo () Bool (= 3 x))` has the canonical root `(= x 3)`:
    /// `cong` under `=` would need `3` equal to `x`. When the swapped operands
    /// print the same way (up to bit-vector literal spelling) one premise-free
    /// `eq_symmetric` step states the two orientations equal. MEASURED with
    /// the bare-symbol bridge alone: the query published the canonical
    /// `(assume t0 (= x 3))` under `foreign_assumes=yes`, and pinned carcara
    /// 1.1.0 refused it ("could not match term to any of the original problem
    /// premises").
    ///
    /// When a swapped operand ALSO names a macro, see
    /// [`Self::swapped_operand_congruence`]. `output` is unchanged whenever
    /// this answers `false`.
    #[expect(
        clippy::too_many_arguments,
        reason = "the exact equality proof schema and traversal ledgers stay explicit"
    )]
    pub(super) fn equality_symmetry_step(
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
        // The shared-input lane borrows positional congruence arguments;
        // other existing schemas retain their ordinary bounded renderer.
        if shared.is_some() {
            return false;
        }
        if !matches!(schema, EquivalenceLeafSchema::NullaryDefinition) {
            return false;
        }
        let TermData::App(symbol, children) = self.terms.get(canonical_term) else {
            return false;
        };
        if children.len() != 2 || Self::format_symbol(symbol) != "=" {
            return false;
        }
        let (canonical_left, canonical_right) = (children[0], children[1]);
        let (Some(authored), Some(printed)) = (
            split_application(surface, "="),
            split_application(canonical, "="),
        ) else {
            return false;
        };
        let [left, right] = authored.as_slice() else {
            return false;
        };
        let [printed_left, printed_right] = printed.as_slice() else {
            return false;
        };
        let equality = oriented_equivalence(surface, canonical, direction);
        let swapped = [
            (left.as_str(), printed_right.as_str(), canonical_right),
            (right.as_str(), printed_left.as_str(), canonical_left),
        ];
        if swapped
            .iter()
            .all(|(authored, printed, _)| same_printed_term(authored, printed))
        {
            output.push(format!("(step {id} (cl {equality}) :rule eq_symmetric)"));
            return true;
        }
        self.swapped_operand_congruence(id, &equality, swapped, direction, depth, nodes, output)
    }

    /// `(= a b)` against a canonical `(= b' a')` where `a`/`a'` or `b`/`b'`
    /// differ by a spelling this schema bridges: each such swapped pair is
    /// bridged by the schema itself, and one `cong` under `=` joins them.
    ///
    /// `mk_select` interns `(assert (not (= (select a2 i) (select a j))))`
    /// over `(define-fun a2 () (Array I E) (store a1 j (select a i)))` as
    /// `(not (= (select a j) (select (store (store a i ..) j ..) i)))`: the
    /// orientation flips AND one operand names the macro, so neither `cong` in
    /// the authored order nor `eq_symmetric` reaches it. Pinned carcara's
    /// `cong` checks a binary `=` in all four orientations, consuming its
    /// premises in operand order (`checker/rules/congruence.rs`, `cong`), so
    /// the premises are listed in the AUTHORED operand order. MEASURED on
    /// `QF_AX/swap_two_reads.smt2` (2026-10-06): without this arm the bridge
    /// declined, the authored spelling rode the root document-wide, and the
    /// export was REFUSED at the closing resolution ("the printed premises do
    /// not eliminate the printed resolution pivot"); the same document with
    /// this bridge is `valid` to pinned carcara 1.1.0 (git 9a352ee).
    #[expect(
        clippy::too_many_arguments,
        reason = "the exact swapped-operand proof schema and traversal ledgers stay explicit"
    )]
    fn swapped_operand_congruence(
        &self,
        id: &str,
        equality: &str,
        swapped: [(&str, &str, TermId); 2],
        direction: EquivalenceDirection,
        depth: usize,
        nodes: &mut usize,
        output: &mut Vec<String>,
    ) -> bool {
        let mark = output.len();
        let mut premises = Vec::new();
        for (position, (authored, printed, child)) in swapped.into_iter().enumerate() {
            if same_printed_term(authored, printed) {
                continue;
            }
            let child_id = format!("{id}.r{position}");
            if !self.build_authored_surface_equivalence(
                &child_id,
                authored,
                child,
                EquivalenceLeafSchema::NullaryDefinition,
                direction,
                depth + 1,
                nodes,
                output,
                None,
            ) {
                output.truncate(mark);
                return false;
            }
            premises.push(child_id);
        }
        output.push(format!(
            "(step {id} (cl {equality}) :rule cong :premises ({}))",
            premises.join(" ")
        ));
        true
    }

    /// The ordinary equivalence bridge's second attempt: derive `surface` =
    /// the canonical rendering of `term` under the definition schema, reading
    /// at least one definition premise. `output` is replaced; `nodes` is
    /// charged for the attempt, which itself starts from a fresh per-bridge
    /// node allowance so the planner, the emitter and the producer's
    /// preflight ([`crate::nullary_definition_assume_bridge_is_supported`])
    /// all decide the same way. Declines without a definition table, and
    /// declines a bridge that reads none (a pure literal respelling, say), so
    /// every document that names no nullary `define-fun` renders as before.
    pub(super) fn definition_bridge(
        &self,
        id: &str,
        surface: &str,
        term: TermId,
        nodes: &mut usize,
        output: &mut Vec<String>,
    ) -> bool {
        if self.nullary_definitions.is_none_or(HashMap::is_empty) {
            return false;
        }
        output.clear();
        let mut attempt = 0;
        let bridged = self.build_authored_surface_equivalence(
            id,
            surface,
            term,
            EquivalenceLeafSchema::NullaryDefinition,
            EquivalenceDirection::SurfaceToCanonical,
            0,
            &mut attempt,
            output,
            None,
        );
        *nodes = nodes.saturating_add(attempt);
        bridged
            && !self.work_budget_exhausted()
            && output.iter().any(|step| step.starts_with("(assume "))
    }

    /// The override channel downstream wire rules see once this printer's
    /// authored-assume planner has confined every spelling it can, reading
    /// whatever definition table the printer carries. See
    /// [`crate::effective_wire_term_overrides_for_authored_proof`].
    pub(crate) fn planned_wire_term_overrides(
        self,
        proof: &Proof,
    ) -> Result<Option<HashMap<TermId, String>>, AlethePrintError> {
        self.plan_equivalent_authored_assumes(proof)?;
        // The folded-conjunction projection confines its terms too; the wire
        // view must see the text the document prints for them.
        self.plan_folded_and_assumes(proof);
        self.check_emission_progress(0)?;
        // So does a certified `let` assume bridge (`let_assume_confinement.rs`).
        self.confine_certified_let_assumes(proof);
        self.check_emission_progress(0)?;
        Ok(self.wire_term_overrides.into_inner())
    }

    /// The producer-side preflight behind
    /// [`crate::nullary_definition_assume_bridge_is_supported`]: the planner's
    /// own admission bounds, then its equivalence attempts in its order.
    pub(crate) fn nullary_definition_assume_bridge_supported(
        &self,
        term: TermId,
        surface: &str,
    ) -> bool {
        if surface.len() > MAX_EQUIVALENCE_BYTES || !matches!(self.terms.sort(term), Sort::Bool) {
            return false;
        }
        match canonical_term_is_bounded_for_authored_assume(self.terms, term) {
            CanonicalRenderBound::UnsupportedShape => false,
            _ => self.authored_equivalence("probe", surface, term, &mut 0, &mut Vec::new()),
        }
    }
}

/// The one operand of a printed `(not x)`, or `None` for anything else.
fn negation_operand(surface: &str) -> Option<String> {
    let mut operands = split_application(surface, "not")?;
    (operands.len() == 1).then(|| operands.pop()).flatten()
}

#[path = "nullary_definition/shared_body.rs"]
mod shared_body;
#[cfg(test)]
#[path = "nullary_definition/tests.rs"]
mod tests;
