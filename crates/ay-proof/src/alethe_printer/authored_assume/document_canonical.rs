// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authored `assume` bridges onto the DOCUMENT's rendering of the canonical
//! term.
//!
//! The planner's first schemas compare the authored text with
//! `render_term_canonical`, the override-free rendering. That is the text the
//! rest of the document prints only when no DESCENDANT of the assumed term
//! carries its own override. Datatype flattening breaks it: `(len v)` is an
//! internal field variable, printed back as `(len v)` by its own override,
//! so the override-free text of `(not (= fill (select <data field> k)))` names a
//! symbol the problem never declares and no bridge onto it can ever match the
//! authored `(distinct (select (data v) k) fill)`.
//!
//! When those schemas decline, this module retries against the text the
//! document prints for the term with only its OWN override removed (every
//! descendant keeps its channel), and additionally admits:
//!
//! * the binary `distinct` elimination of [`super::distinct`];
//! * a checked `(= surface canonical)` from `surface_equivalence`, used like
//!   the ordinary equivalence bridge (`equiv_pos2` + `resolution`);
//! * a Boolean FOLD of the authored text that lands on the document's
//!   rendering, byte for byte or up to carcara's `alpha_equiv`
//!   ([`super::boolean_fold::render_folded_document_equivalence_with_progress`]):
//!   `(= (bvult b #x03) false)` over `(not (bvult b #x03))`, where the
//!   assumed term's operand keeps its own authored spelling `(bvult b #x03)`
//!   (a bit-vector literal re-spelling AY stores as `#b00000011`), so the
//!   override-free fold target `(not (bvult b #b00000011))` would print one
//!   term two ways;
//! * [`congruent_conjunction`]: an authored equality `(= x y)` whose canonical
//!   term is a conjunction of unary congruences `(= (f x) (f y))` (a datatype
//!   equality between two variables, expanded field by field). This bridge is
//!   an IMPLICATION, not an equivalence: the `assume` only has to yield the
//!   canonical unit, and each conjunct is one `cong` over the authored
//!   equality.
//!
//! The canonical rendering chosen here is what `let_bridge_renderings` then
//! prints everywhere else, so it is the document's own spelling by
//! construction. A term consumed by an explicitly annotated resolution keeps
//! the document-wide authored spelling, exactly as [`super::distinct`] does.

use super::super::printed_head_symbol;
use super::super::quantifier_surface::printed_terms_alpha_equivalent;
use super::super::surface_literal::same_printed_term;
use super::*;

const MAX_CONGRUENT_CONJUNCTS: usize = 256;

#[cfg(test)]
#[path = "document_fold_resource_tests.rs"]
mod document_fold_resource_tests;

impl AlethePrinter<'_> {
    /// [`Self::document_canonical_bridge`] as a plan: the bridge concludes the
    /// DOCUMENT's rendering of the term, which `let_bridge_renderings` then
    /// prints everywhere else, so the plan's canonical text and its input size
    /// are that rendering's.
    pub(super) fn document_canonical_plan(
        &self,
        id: ProofId,
        term: TermId,
        surface: &str,
        planner: &AuthoredAssumePlanner,
    ) -> Result<Option<(AuthoredAssumeBridge, String, usize)>, AlethePrintError> {
        let Some((bridge, rendered)) = self.document_canonical_bridge(term, surface, planner)
        else {
            return Ok(None);
        };
        let Some(rendered_bytes) = surface.len().checked_add(rendered.len()) else {
            return Err(invalid_authored_assume_plan(
                id,
                "authored assume bridge input size overflowed",
            ));
        };
        Ok(Some((bridge, rendered, rendered_bytes)))
    }

    /// A bridge onto the document's rendering of `term`, with that rendering,
    /// or `None`.
    pub(super) fn document_canonical_bridge(
        &self,
        term: TermId,
        surface: &str,
        planner: &AuthoredAssumePlanner,
    ) -> Option<(AuthoredAssumeBridge, String)> {
        if planner.annotated_resolution_premises.contains(&term)
            || planner
                .override_descendants
                .get_or_init(|| match &planner.printed_roots {
                    Some(roots) => self.strict_descendants_of_printed_overridden_terms(roots),
                    None => self.strict_descendants_of_overridden_terms(),
                })
                .as_ref()
                .is_none_or(|descendants| descendants.contains(&term))
        {
            return None;
        }
        let rendered = self.format_term_without_own_override(term)?;
        // A pure respelling (equality operand order, bit-vector literal
        // notation) is one term to carcara's parser and `refl`, and the
        // document-wide override already has checked repairs at every
        // consumer (`surface_resolution`, the congruence literal legs). Leave
        // those documents exactly as they were.
        if rendered == surface
            || rendered.len() > MAX_EQUIVALENCE_BYTES
            || printed_terms_alpha_equivalent(surface, &rendered)
        {
            return None;
        }
        let bridge = if distinct::distinct_elimination_is_supported(surface, &rendered) {
            AuthoredAssumeBridge::DistinctElimination
        } else if congruent_conjunction(surface, &rendered).is_some() {
            AuthoredAssumeBridge::CongruentConjunction
        } else if self
            .printed_surface_equivalence_steps("probe", surface, term, &rendered)
            .is_some()
        {
            AuthoredAssumeBridge::PrintedEquivalence
        } else if self.folded_document_equivalence_admitted(term, surface, &rendered) {
            AuthoredAssumeBridge::FoldedDocumentEquivalence
        } else {
            return None;
        };
        Some((bridge, rendered))
    }

    /// Whether [`AuthoredAssumeBridge::FoldedDocumentEquivalence`] applies:
    /// the authored `surface` folds onto the document's `rendering` of
    /// `term`. An authored `and` over a term that is no conjunction stays
    /// the folded-conjunction projection's, as in the fold leaf.
    fn folded_document_equivalence_admitted(
        &self,
        term: TermId,
        surface: &str,
        rendering: &str,
    ) -> bool {
        // The conjunction screen can copy operand strings. Charge its scan,
        // bytes, and worst-case one String slot per input byte before parsing.
        let scan_work = surface
            .len()
            .checked_mul(size_of::<String>() + 2)
            .and_then(|work| u64::try_from(work).ok());
        if !scan_work.is_some_and(|work| self.admit_emission_work(work)) {
            return false;
        }
        let canonical_is_conjunction = matches!(
            self.terms.get(term),
            TermData::App(symbol, _) if symbol.name() == "and"
        );
        if split_application(surface, "and").is_some() && !canonical_is_conjunction {
            return false;
        }
        boolean_fold::render_folded_document_equivalence_with_progress(
            "probe",
            surface,
            rendering,
            &mut |amount| self.admit_emission_work(amount),
        )
        .0
        .is_some()
    }

    /// The `equiv_pos2` bridge over a `surface_equivalence` derivation.
    pub(super) fn render_printed_equivalence_bridge(
        &self,
        id: ProofId,
        term: TermId,
        surface: &str,
        canonical: &str,
    ) -> (Option<String>, usize) {
        let equality_id = format!("{id}.n");
        let Some((steps, nodes)) =
            self.printed_surface_equivalence_steps(&equality_id, surface, term, canonical)
        else {
            return (None, 1);
        };
        let equality = format!("(= {surface} {canonical})");
        let mut output = format!("(assume {id}.a {surface})\n");
        output.push_str(&steps.join("\n"));
        output.push('\n');
        output.push_str(&format!(
            "(step {id}.e (cl (not {equality}) (not {surface}) {canonical}) :rule equiv_pos2)\n\
             (step {id} (cl {canonical}) :rule resolution :premises ({id}.e {equality_id} {id}.a))"
        ));
        (Some(output), nodes)
    }
}

/// The canonical conjuncts when `surface` is `(= x y)` and `canonical` is
/// `(and c_1 .. c_n)` with every `c_i` spelled `(= (f x) (f y))` or
/// `(= (f y) (f x))` for a plain function symbol `f`.
fn congruent_conjunction(surface: &str, canonical: &str) -> Option<Vec<String>> {
    let sides = split_application(surface, "=")?;
    let [x, y] = sides.as_slice() else {
        return None;
    };
    let conjuncts = split_application(canonical, "and")?;
    if conjuncts.is_empty() || conjuncts.len() > MAX_CONGRUENT_CONJUNCTS {
        return None;
    }
    for conjunct in &conjuncts {
        let operands = split_application(conjunct, "=")?;
        let [left, right] = operands.as_slice() else {
            return None;
        };
        let head = printed_head_symbol(left)?;
        if head.starts_with('(')
            || matches!(
                head.as_str(),
                "forall" | "exists" | "let" | "!" | "match" | "lambda" | "choice" | "_"
            )
        {
            return None;
        }
        let left_args = split_application(left, &head)?;
        let right_args = split_application(right, &head)?;
        let ([left_arg], [right_arg]) = (left_args.as_slice(), right_args.as_slice()) else {
            return None;
        };
        let straight = same_printed_term(left_arg, x) && same_printed_term(right_arg, y);
        let swapped = same_printed_term(left_arg, y) && same_printed_term(right_arg, x);
        if !straight && !swapped {
            return None;
        }
    }
    Some(conjuncts)
}

/// `(assume tK.a (= x y))`, one `cong` per conjunct (carcara's `cong` reads
/// its premise in either orientation), `and_neg`, and one `resolution`
/// concluding the canonical conjunction under `tK`.
pub(super) fn render_congruent_conjunction_bridge(
    id: ProofId,
    surface: &str,
    canonical: &str,
) -> Option<String> {
    let conjuncts = congruent_conjunction(surface, canonical)?;
    let mut output = format!("(assume {id}.a {surface})\n");
    let mut premises = vec![format!("{id}.an")];
    for (index, conjunct) in conjuncts.iter().enumerate() {
        output.push_str(&format!(
            "(step {id}.c{index} (cl {conjunct}) :rule cong :premises ({id}.a))\n"
        ));
        premises.push(format!("{id}.c{index}"));
    }
    let negated: Vec<String> = conjuncts.iter().map(|c| format!("(not {c})")).collect();
    output.push_str(&format!(
        "(step {id}.an (cl {canonical} {}) :rule and_neg)\n\
         (step {id} (cl {canonical}) :rule resolution :premises ({}))",
        negated.join(" "),
        premises.join(" ")
    ));
    Some(output)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_field_wise_expansion_of_a_variable_equality_is_congruent() {
        let conjuncts = congruent_conjunction(
            "(= v7 v6)",
            "(and (= (ptr v6) (ptr v7)) (= (len v6) (len v7)) (= (data v7) (data v6)))",
        )
        .expect("each conjunct is one unary congruence over the authored pair");
        assert_eq!(conjuncts.len(), 3);
        let bridge = render_congruent_conjunction_bridge(
            ProofId(1),
            "(= v7 v6)",
            "(and (= (ptr v6) (ptr v7)) (= (data v7) (data v6)))",
        )
        .expect("bridge");
        assert_eq!(
            bridge,
            "(assume t1.a (= v7 v6))\n\
             (step t1.c0 (cl (= (ptr v6) (ptr v7))) :rule cong :premises (t1.a))\n\
             (step t1.c1 (cl (= (data v7) (data v6))) :rule cong :premises (t1.a))\n\
             (step t1.an (cl (and (= (ptr v6) (ptr v7)) (= (data v7) (data v6))) (not (= (ptr v6) (ptr v7))) (not (= (data v7) (data v6)))) :rule and_neg)\n\
             (step t1 (cl (and (= (ptr v6) (ptr v7)) (= (data v7) (data v6)))) :rule resolution :premises (t1.an t1.c0 t1.c1))"
        );
    }

    #[test]
    fn a_constructor_expansion_is_not_a_congruence_of_the_authored_equality() {
        // `(= v0 (mkVec 0 10))` expands to the selector VALUES, which only the
        // datatype theory relates to `v0`; pinned carcara has no rule for it.
        assert_eq!(
            congruent_conjunction(
                "(= v0 (mkVec #b0 #b1))",
                "(and (= (ptr v0) #b0) (= (len v0) #b1))"
            ),
            None
        );
        // A conjunct over a third term, or a binary function, declines too.
        assert_eq!(
            congruent_conjunction("(= a b)", "(and (= (f a) (f c)))"),
            None
        );
        assert_eq!(
            congruent_conjunction("(= a b)", "(and (= (g a a) (g b b)))"),
            None
        );
        // A non-conjunction canonical term is some other schema's business.
        assert_eq!(congruent_conjunction("(= a b)", "(= (f a) (f b))"), None);
    }
}
