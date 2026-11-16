// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked equality between an AUTHORED printed term and the DOCUMENT's own
//! rendering of the internal term it elaborated to.
//!
//! A surface override re-spells one internal term with the problem file's
//! text. Where that term is also consumed by an ordinary inference (`cong`,
//! `and_pos`, `or`, resolution) the two spellings meet in one step and the
//! printer has to refuse it. The cure is to confine the authored text to the
//! one command that needs it (an `assume`, or the `forall_inst` that
//! instantiates an authored quantifier) and to DERIVE the canonical text there
//! with stock rules. This module builds that derivation.
//!
//! Every step it emits is an ordinary instance of a pinned-carcara rule over
//! the exact text it prints, so the external checker re-derives each one:
//!
//! * `refl` for two texts carcara's own `alpha_equiv` identifies (equality
//!   operand order and alternate bit-vector literal spellings);
//! * `distinct_elim` (+ `trans`) for a binary authored `distinct` over a
//!   canonical `(not (= x y))`;
//! * `pbblast_*` + `symm` + `trans` for an unsigned comparison the canonical
//!   term states with its operands swapped (`bvuge x y` as `bvule y x`),
//!   followed by `cong` when a swapped operand is itself re-spelled;
//! * `arrays_idx` (+ `trans`) for an authored read-over-write at the index it
//!   wrote, over the canonical element ([`read_over_write`]);
//! * `implies_pos`/`implies_neg*`, `and_pos`/`and_neg`, `or_pos`/`or_neg`,
//!   `equiv_*` and `resolution` for an authored `(=> A B)` whose canonical
//!   term is the flat disjunction of its literals in any order;
//! * `ite_intro`, `ite1`/`ite2`, `eq_congruent_pred`, `ite_pos*`/`ite_neg*`,
//!   `equiv_neg*` and `resolution` for an authored atom over a term-level
//!   `ite` whose canonical term is its Shannon-lifted formula;
//! * `cong` over one head with the same arity;
//! * only after every schema above declined the whole pair: `comp_simplify`
//!   for an arithmetic comparison with its operands swapped ([`comparison`]),
//!   `not_simplify` and `distinct_elim` for a double negation or a negated
//!   `distinct` ([`negation`]), and the `or_*`/`and_*`/`implies_*`/`equiv_*` tautologies
//!   and `resolution` for an authored clause whose connectives elaboration
//!   flattened into one canonical `or` ([`flattened_clause`]).
//!
//! Anything else declines, and the caller keeps its existing refusal. The
//! canonical side is always read from the term store AND checked against the
//! document's rendering of each child, so a derivation can never talk about a
//! spelling the rest of the document does not print.

use super::quantifier_surface::printed_terms_alpha_equivalent;
use super::surface_literal::same_printed_term;
use super::*;

const MAX_PRINTED_EQUIVALENCE_DEPTH: usize = 32;
const MAX_PRINTED_EQUIVALENCE_NODES: usize = 256;
const MAX_PRINTED_EQUIVALENCE_BYTES: usize = 64 * 1024;
const MAX_PRINTED_EQUIVALENCE_STEPS: usize = 4096;
/// Cap on the text one derivation may emit; a 64-bit `pbblast_*` pair alone
/// is several kilobytes.
const MAX_PRINTED_EQUIVALENCE_OUTPUT_BYTES: usize = 8 * 1024 * 1024;

/// One canonical node: the internal term and the exact text the document
/// prints for it.
#[derive(Clone, Copy)]
struct CanonicalNode<'t> {
    term: TermId,
    text: &'t str,
}

/// The schemas one derivation admits.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
enum SchemaTier {
    /// The schemas every document printed before [`negation`] and
    /// [`flattened_clause`] existed already relies on.
    #[default]
    Established,
    /// Those plus [`negation`] and [`flattened_clause`]: a second attempt only.
    Extended,
}

#[derive(Default)]
struct Derivation {
    steps: Vec<String>,
    nodes: usize,
    tier: SchemaTier,
}

fn term_children(terms: &TermStore, term: TermId) -> Vec<TermId> {
    match terms.get(term) {
        TermData::Not(inner) => vec![*inner],
        TermData::Ite(condition, then_branch, else_branch) => {
            vec![*condition, *then_branch, *else_branch]
        }
        TermData::App(_, args) => args.clone(),
        TermData::Let(bindings, body) => bindings
            .iter()
            .map(|(_, value)| *value)
            .chain(std::iter::once(*body))
            .collect(),
        TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => vec![*body],
        _ => Vec::new(),
    }
}

/// Heads whose arguments are not ordinary congruence positions.
fn is_binding_head(head: &str) -> bool {
    matches!(
        head,
        "forall" | "exists" | "let" | "!" | "match" | "lambda" | "choice" | "_"
    )
}

/// Node cap on the walk below every overridden term.
const MAX_OVERRIDE_DESCENDANT_NODES: usize = 1 << 20;

impl AlethePrinter<'_> {
    /// Every term that is a STRICT descendant of some term the producer's
    /// override table re-spells, or `None` when that walk exceeds its cap.
    ///
    /// Confining one term's authored spelling (printing its canonical text
    /// everywhere but its own `assume` / `forall_inst`) is only coherent when
    /// no OTHER override spells a larger term around it: that override would
    /// keep embedding the authored text, so one internal term would ship two
    /// spellings in steps that meet. MEASURED on `QF_ALIA/stack_pushpop_unsat`
    /// with an early cut of this change: confining the assumed
    /// `(= (select mem3 (- sp3 2)) val1)` while the assumed disjunction around
    /// it kept its authored override made the resolution orientation repair
    /// emit a `symm` for a spelling no premise printed, and carcara refused
    /// `t5` of a document the base published as verified. Callers decline
    /// confinement for every term this set contains.
    pub(super) fn strict_descendants_of_overridden_terms(&self) -> Option<HashSet<TermId>> {
        let mut descendants = HashSet::default();
        let Some(overrides) = self.term_overrides else {
            return Some(descendants);
        };
        let mut stack: Vec<TermId> = Vec::new();
        for &root in overrides.keys() {
            stack.extend(term_children(self.terms, root));
        }
        while let Some(term) = stack.pop() {
            if !descendants.insert(term) {
                continue;
            }
            if descendants.len() > MAX_OVERRIDE_DESCENDANT_NODES {
                return None;
            }
            stack.extend(term_children(self.terms, term));
        }
        self.charge(descendants.len() as u64);
        Some(descendants)
    }

    /// Steps concluding `(= surface canonical)` under `id`, where `canonical`
    /// is the document's rendering of `term`, or `None` when no supported
    /// schema relates them.
    pub(super) fn printed_surface_equivalence_steps(
        &self,
        id: &str,
        surface: &str,
        term: TermId,
        canonical: &str,
    ) -> Option<(Vec<String>, usize)> {
        if surface == canonical
            || surface.len() > MAX_PRINTED_EQUIVALENCE_BYTES
            || canonical.len() > MAX_PRINTED_EQUIVALENCE_BYTES
        {
            return None;
        }
        let mut derivation = Derivation::default();
        let node = CanonicalNode {
            term,
            text: canonical,
        };
        if !self.derive_printed_equivalence(id, surface, node, 0, &mut derivation) {
            // A second attempt from scratch admits the extended schemas at
            // every depth; every pair an established schema relates keeps its
            // derivation byte-for-byte. The per-attempt caps are unchanged.
            derivation = Derivation {
                tier: SchemaTier::Extended,
                ..Derivation::default()
            };
            if !self.derive_printed_equivalence(id, surface, node, 0, &mut derivation) {
                return None;
            }
        }
        let bytes = derivation
            .steps
            .iter()
            .try_fold(0usize, |bytes, step| bytes.checked_add(step.len()))?;
        self.charge(bytes as u64);
        (bytes <= MAX_PRINTED_EQUIVALENCE_OUTPUT_BYTES)
            .then_some((derivation.steps, derivation.nodes))
    }

    fn derive_printed_equivalence(
        &self,
        id: &str,
        surface: &str,
        canonical: CanonicalNode<'_>,
        depth: usize,
        derivation: &mut Derivation,
    ) -> bool {
        if surface == canonical.text
            || depth > MAX_PRINTED_EQUIVALENCE_DEPTH
            || derivation.nodes >= MAX_PRINTED_EQUIVALENCE_NODES
            || derivation.steps.len() >= MAX_PRINTED_EQUIVALENCE_STEPS
        {
            return false;
        }
        derivation.nodes += 1;
        if printed_terms_alpha_equivalent(surface, canonical.text) {
            derivation.steps.push(format!(
                "(step {id} (cl (= {surface} {})) :rule refl)",
                canonical.text
            ));
            return true;
        }
        let checkpoint = derivation.steps.len();
        let derived = self
            .distinct_elimination_equivalence(id, surface, canonical, depth, derivation)
            || self.unsigned_comparison_reversal(id, surface, canonical, depth, derivation)
            || self.read_over_write_equivalence(id, surface, canonical, depth, derivation)
            || self.implication_disjunction_equivalence(id, surface, canonical, depth, derivation)
            || self.ite_lift_equivalence(id, surface, canonical, depth, derivation)
            || self.arithmetic_product_equivalence(id, surface, canonical, derivation)
            || self.congruent_printed_equivalence(id, surface, canonical, depth, derivation)
            || self.arithmetic_comparison_reversal(id, surface, canonical, derivation)
            || self.negation_form_equivalence(id, surface, canonical, depth, derivation)
            || self.flattened_clause_equivalence(id, surface, canonical, depth, derivation);
        if !derived {
            derivation.steps.truncate(checkpoint);
        }
        derived
    }

    /// The canonical children of `node` under the printed `head`, each paired
    /// with the text the document prints for it. `None` unless the node's own
    /// text is exactly that application of those child renderings.
    ///
    /// A canonical `ite` is one head like any other, so `cong` can rebuild it:
    /// a nested lift (`s.update(1, a).update(2, b)`) reaches its canonical
    /// formula only through `cong` over the outer `ite` (`ite_lift`).
    fn canonical_printed_children(
        &self,
        node: CanonicalNode<'_>,
        head: &str,
    ) -> Option<Vec<(TermId, String)>> {
        let children: Vec<TermId> = match self.terms.get(node.term) {
            TermData::Not(inner) if head == "not" => vec![*inner],
            TermData::Ite(condition, then_branch, else_branch) if head == "ite" => {
                vec![*condition, *then_branch, *else_branch]
            }
            TermData::App(symbol, args) if Self::format_symbol(symbol) == head => args.clone(),
            _ => return None,
        };
        let texts = split_application(node.text, head)?;
        if texts.len() != children.len() {
            return None;
        }
        for (child, text) in children.iter().zip(&texts) {
            if self.format_term(*child) != *text {
                return None;
            }
        }
        Some(children.into_iter().zip(texts).collect())
    }

    /// A binary authored `(distinct a b)` over a canonical `(not (= x y))`.
    fn distinct_elimination_equivalence(
        &self,
        id: &str,
        surface: &str,
        canonical: CanonicalNode<'_>,
        depth: usize,
        derivation: &mut Derivation,
    ) -> bool {
        let Some(operands) = split_application(surface, "distinct") else {
            return false;
        };
        let [left, right] = operands.as_slice() else {
            return false;
        };
        let Some(negated) = self.canonical_printed_children(canonical, "not") else {
            return false;
        };
        let [(equality, equality_text)] = negated.as_slice() else {
            return false;
        };
        let equality_node = CanonicalNode {
            term: *equality,
            text: equality_text,
        };
        let Some(sides) = self.canonical_printed_children(equality_node, "=") else {
            return false;
        };
        let [(_, first), (_, second)] = sides.as_slice() else {
            return false;
        };
        let canonical_text = canonical.text;
        // carcara's `distinct_elim` accepts either operand order of the
        // eliminated equality, over parsed terms.
        if (same_printed_term(left, first) && same_printed_term(right, second))
            || (same_printed_term(left, second) && same_printed_term(right, first))
        {
            derivation.steps.push(format!(
                "(step {id} (cl (= {surface} {canonical_text})) :rule distinct_elim)"
            ));
            return true;
        }
        let eliminated = format!("(not (= {left} {right}))");
        let leg = format!("{id}.dr");
        if !self.derive_printed_equivalence(&leg, &eliminated, canonical, depth + 1, derivation) {
            return false;
        }
        derivation.steps.push(format!(
            "(step {id}.de (cl (= {surface} {eliminated})) :rule distinct_elim)"
        ));
        derivation.steps.push(format!(
            "(step {id} (cl (= {surface} {canonical_text})) :rule trans :premises ({id}.de {leg}))"
        ));
        true
    }

    /// An unsigned comparison the canonical term states with its operands
    /// swapped. Both sides blast to the SAME pseudo-Boolean constraint, so
    /// one `trans` joins the two `pbblast_*` equalities.
    ///
    /// When a swapped operand is not the canonical operand's own text (the
    /// canonical term folded a read-over-write the authored operand still
    /// spells), the reversal lands on the authored operands in canonical
    /// order, and a `cong` over the operands' own derived equalities finishes
    /// it. An operand no schema relates keeps the whole reversal declined.
    fn unsigned_comparison_reversal(
        &self,
        id: &str,
        surface: &str,
        canonical: CanonicalNode<'_>,
        depth: usize,
        derivation: &mut Derivation,
    ) -> bool {
        let Some(surface_operator) = printed_head_symbol(surface) else {
            return false;
        };
        let Some(canonical_operator) = swapped_unsigned_comparison(&surface_operator) else {
            return false;
        };
        let Some(surface_args) = split_application(surface, &surface_operator) else {
            return false;
        };
        let [x, y] = surface_args.as_slice() else {
            return false;
        };
        let Some(children) = self.canonical_printed_children(canonical, canonical_operator) else {
            return false;
        };
        let [(first_term, first), (_, second)] = children.as_slice() else {
            return false;
        };
        // A respelled operand: reverse onto the AUTHORED operands, then `cong`.
        let respelled = !same_printed_term(x, second) || !same_printed_term(y, first);
        let reversed = format!("({canonical_operator} {y} {x})");
        let (first, second, canonical_text) = if respelled {
            (y, x, reversed.as_str())
        } else {
            (first, second, canonical.text)
        };
        let Sort::BitVec(bits) = self.terms.sort(*first_term) else {
            return false;
        };
        let width = bits.width;
        if width == 0 || width > Self::MAX_BITBLAST_LOWERING_WIDTH {
            return false;
        }
        let blast = |operator: &str, left: &str, right: &str| -> Option<String> {
            let (left_minuend, threshold) = unsigned_comparison_pbblast(operator)?;
            let (minuend, subtrahend) = if left_minuend {
                (left, right)
            } else {
                (right, left)
            };
            Some(format!(
                "(>= (- {} {}) {threshold})",
                Self::pbblast_value_sum(minuend, width),
                Self::pbblast_value_sum(subtrahend, width)
            ))
        };
        let (Some(surface_blast), Some(canonical_blast)) = (
            blast(&surface_operator, x, y),
            blast(canonical_operator, first, second),
        ) else {
            return false;
        };
        let (Some(surface_step), Some(canonical_step)) = (
            unsigned_comparison_pbblast_step(
                &format!("{id}.ps"),
                &surface_operator,
                surface,
                &surface_blast,
            ),
            unsigned_comparison_pbblast_step(
                &format!("{id}.pc"),
                canonical_operator,
                canonical_text,
                &canonical_blast,
            ),
        ) else {
            return false;
        };
        let checkpoint = derivation.steps.len();
        derivation.steps.push(surface_step);
        derivation.steps.push(canonical_step);
        derivation.steps.push(format!(
            "(step {id}.cs (cl (= {canonical_blast} {canonical_text})) :rule symm :premises ({id}.pc))"
        ));
        let mut premises = format!("{id}.ps {id}.cs");
        if respelled {
            let (leg, next) = (format!("{id}.ro"), depth + 1);
            if !self.congruent_printed_equivalence(&leg, &reversed, canonical, next, derivation) {
                // Leave no `pbblast_*` step behind for a later schema to inherit.
                derivation.steps.truncate(checkpoint);
                return false;
            }
            premises = format!("{premises} {leg}");
        }
        derivation.steps.push(format!(
            "(step {id} (cl (= {surface} {})) :rule trans :premises ({premises}))",
            canonical.text
        ));
        true
    }

    /// A checked AC leaf for arithmetic product operands reordered by interning.
    fn arithmetic_product_equivalence(
        &self,
        id: &str,
        surface: &str,
        canonical: CanonicalNode<'_>,
        derivation: &mut Derivation,
    ) -> bool {
        if derivation.tier != SchemaTier::Extended
            || !matches!(self.terms.sort(canonical.term), Sort::Int | Sort::Real)
            || !matches!(self.terms.get(canonical.term), TermData::App(symbol, _) if symbol.name() == "*")
        {
            return false;
        }
        let Some(step) = aci_simp_step::ac_identity_step(id, surface, canonical.text) else {
            return false;
        };
        derivation.steps.push(step);
        true
    }

    /// Same head, same arity: one `cong` over the derived argument equalities.
    fn congruent_printed_equivalence(
        &self,
        id: &str,
        surface: &str,
        canonical: CanonicalNode<'_>,
        depth: usize,
        derivation: &mut Derivation,
    ) -> bool {
        let Some(head) = printed_head_symbol(surface) else {
            return false;
        };
        if is_binding_head(&head) {
            return false;
        }
        let Some(surface_args) = split_application(surface, &head) else {
            return false;
        };
        let Some(children) = self.canonical_printed_children(canonical, &head) else {
            return false;
        };
        if surface_args.len() != children.len() {
            return false;
        }
        let mut premises = Vec::new();
        for (position, (surface_arg, (child, child_text))) in
            surface_args.iter().zip(&children).enumerate()
        {
            if surface_arg == child_text {
                continue;
            }
            let leg = format!("{id}.c{position}");
            let node = CanonicalNode {
                term: *child,
                text: child_text,
            };
            if !self.derive_printed_equivalence(&leg, surface_arg, node, depth + 1, derivation) {
                return false;
            }
            premises.push(leg);
        }
        if premises.is_empty() {
            return false;
        }
        derivation.steps.push(format!(
            "(step {id} (cl (= {surface} {})) :rule cong :premises ({}))",
            canonical.text,
            premises.join(" ")
        ));
        true
    }
}

mod comparison;
mod flattened_clause;
mod implication;
mod ite_lift;
mod negation;
mod pbblast_table;
mod read_over_write;
use pbblast_table::{
    swapped_unsigned_comparison, unsigned_comparison_pbblast, unsigned_comparison_pbblast_step,
};

#[cfg(test)]
mod tests;
