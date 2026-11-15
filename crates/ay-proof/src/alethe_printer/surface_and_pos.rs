// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Linear, surface-safe rendering of flat Boolean `and_pos` steps.

use super::{
    split_alethe_application_bounded, split_application, split_binary_implies, AlethePrintError,
    AlethePrinter, AletheSurfaceParseError,
};
use ay_core::{AletheRule, ProofId, Sort, Symbol, TermData, TermId};

#[path = "surface_and_pos_alpha.rs"]
mod alpha;
mod quantified_body;

impl AlethePrinter<'_> {
    /// Render one exact, premise-free Boolean `and_pos` against its effective
    /// flat surface source. Specialized implication/De-Morgan bridges run
    /// before this method; once an ordinary flat AND reaches this boundary it
    /// either emits a spec-valid projection or fails closed.
    pub(super) fn format_flat_surface_and_pos(
        &self,
        id: ProofId,
        rule: &AletheRule,
        clause: &[TermId],
        premises: &[ProofId],
        args: &[TermId],
    ) -> Result<Option<String>, AlethePrintError> {
        let AletheRule::AndPos(internal_index) = rule else {
            return Ok(None);
        };
        if !premises.is_empty() {
            return Err(invalid_and_pos(id, "and_pos requires no premises"));
        }
        let [left, right] = clause else {
            return Err(invalid_and_pos(
                id,
                "and_pos clause must contain exactly the raw gate and indexed conjunct",
            ));
        };
        // Native strict checking uses the first internal argument only when it
        // is an AND source and historically ignores trailing bookkeeping
        // arguments. When it is absent or non-AND, recover the unique exact
        // raw `not(and ..)` gate whose indexed child is the other literal.
        let source = args
            .first()
            .copied()
            .filter(|&source| {
                matches!(
                    self.terms.get(source),
                    TermData::App(Symbol::Named(head), _) if head == "and"
                )
            })
            .or_else(|| infer_raw_and_source(self, [*left, *right], *internal_index))
            .ok_or_else(|| invalid_and_pos(id, "and_pos raw source is not uniquely inferable"))?;
        let (selected, canonical_arity) = {
            let TermData::App(Symbol::Named(head), conjuncts) = self.terms.get(source) else {
                return Err(invalid_and_pos(id, "and_pos source is not an application"));
            };
            if head != "and" || *self.terms.sort(source) != Sort::Bool || conjuncts.len() < 2 {
                return Err(invalid_and_pos(
                    id,
                    "and_pos source is not a flat Boolean and-term",
                ));
            }
            (
                conjuncts
                    .get(*internal_index as usize)
                    .copied()
                    .ok_or_else(|| {
                        invalid_and_pos(id, "and_pos canonical index is out of range")
                    })?,
                conjuncts.len(),
            )
        };
        self.charge(canonical_arity as u64);
        if self.work_budget_exhausted() {
            return Err(self.work_budget_error(id.0));
        }
        let TermData::App(_, conjuncts) = self.terms.get(source) else {
            return Err(invalid_and_pos(
                id,
                "and_pos source changed during validation",
            ));
        };
        if conjuncts
            .iter()
            .any(|&conjunct| *self.terms.sort(conjunct) != Sort::Bool)
        {
            return Err(invalid_and_pos(
                id,
                "and_pos source contains a non-Boolean conjunct",
            ));
        }
        let left_is_gate =
            matches!(self.terms.get(*left), TermData::Not(inner) if *inner == source);
        let right_is_gate =
            matches!(self.terms.get(*right), TermData::Not(inner) if *inner == source);
        let (gate_position, selected_position) = if left_is_gate && *right == selected {
            (0usize, 1usize)
        } else if right_is_gate && *left == selected {
            (1usize, 0usize)
        } else {
            return Err(invalid_and_pos(
                id,
                "and_pos native clause is not the exact raw gate/indexed-conjunct pair",
            ));
        };

        let source_surface = self.format_term(source);
        let printed = [self.format_term(*left), self.format_term(*right)];
        // One source scan, one comparison against each borrowed immediate
        // operand, and the eventual one-step output are all linear in these
        // already-rendered strings. Charge before the scanner allocates its
        // capped slice vector or `(not source)` is assembled.
        let source_bytes = source_surface.len() as u64;
        let clause_bytes = printed
            .iter()
            .map(|literal| literal.len() as u64)
            .sum::<u64>();
        self.charge(
            source_bytes
                .saturating_mul(3)
                .saturating_add(clause_bytes.saturating_mul(2)),
        );
        if self.work_budget_exhausted() {
            return Err(self.work_budget_error(id.0));
        }

        let surface_operands = match split_alethe_application_bounded(
            &source_surface,
            "and",
            source_surface.len(),
            source_surface.len(),
        ) {
            Ok(operands) if operands.len() >= 2 => operands,
            Ok(_) | Err(AletheSurfaceParseError::Malformed) => {
                return Err(invalid_and_pos(
                    id,
                    "and_pos effective source is not a flat and-term",
                ));
            }
            Err(AletheSurfaceParseError::BudgetExceeded) => {
                return Err(invalid_and_pos(
                    id,
                    "and_pos effective source exceeds its input-derived scan bound",
                ));
            }
        };
        let expected_gate = format!("(not {source_surface})");
        if printed[gate_position] != expected_gate {
            return Err(invalid_and_pos(
                id,
                "and_pos printed gate is not the exact negation of its effective source",
            ));
        }
        let selected_surface = &printed[selected_position];
        // carcara's `and_pos` compares PARSED terms (`#x00` is `#b00000000`).
        let Some(surface_index) = surface_operands.iter().position(|operand| {
            super::surface_literal::same_printed_term(operand, selected_surface)
        }) else {
            if let Some(text) = self.quantified_alpha_and_pos_bridge(
                id,
                selected,
                *internal_index as usize,
                &expected_gate,
                selected_surface,
                &surface_operands,
            )? {
                return Ok(Some(text));
            }
            // Bridge supported differences between the authored conjunction
            // and its canonical projection; every other shape still refuses.
            //
            // (1) The surface override re-nests AY's flat internal
            //     conjunction (the authored grouping), leaving the conjunct a
            //     DEEPER printed operand: derive the traced clause through
            //     the printed nesting — one genuine `and_pos` per hop plus a
            //     final resolution (shared navigator; declines on flat
            //     prints, missing operands, and budget exhaustion).
            if let Some(text) = self.navigate_and_pos_gate(id, &source_surface, selected_surface) {
                return Ok(Some(text));
            }
            if self.work_budget_exhausted() {
                return Err(self.work_budget_error(id.0));
            }
            // (2) The surface FLATTENS an authored nested conjunct, erasing
            //     the indexed and-term from the top-level operand list:
            //     project each of its printed children off the flat surface
            //     and reassemble the conjunct via `and_neg` + resolution.
            if let Some(text) = self.reassemble_flattened_and_pos_conjunct(
                id,
                &expected_gate,
                selected_surface,
                &surface_operands,
            ) {
                return Ok(Some(text));
            }
            if self.work_budget_exhausted() {
                return Err(self.work_budget_error(id.0));
            }
            // (3) Arithmetic elaboration can normalize one authored operand
            // while leaving the surrounding source conjunction in its exact
            // problem spelling. Project that exact operand first, then use
            // the same narrowly checked printed `la_generic` implication as
            // the authored-assume bridge to derive the canonical conjunct.
            // The recognizer replays the literal pair and exact `(1 1)`
            // certificate against the printed strings; a merely similar or
            // non-implying operand is therefore still rejected below.
            if let Some((surface_index, surface_operand)) =
                surface_operands.iter().enumerate().find(|(_, operand)| {
                    crate::printed_la_generic_unit_implication_is_supported(
                        operand,
                        selected_surface,
                    )
                })
            {
                return Ok(Some(format!(
                    "(step {id}.a (cl {expected_gate} {surface_operand}) :rule and_pos :args ({surface_index}))\n\
                     (step {id}.n (cl (not {surface_operand}) {selected_surface}) :rule la_generic :args (1 1))\n\
                     (step {id} (cl {expected_gate} {selected_surface}) :rule resolution :premises ({id}.a {id}.n))"
                )));
            }
            // (3b) The same normalization under a negation: the authored
            // `(not (>= (* c 2) (* c 4)))` is stored as `(not (<= (* c 4) (* c
            // 2)))`. Project the authored `(not A)`, then the printed
            // `la_generic` clause `(cl (not B) A)` for the canonical `(not B)`.
            if let Some(text) =
                negated_comparison_and_pos(id, &expected_gate, selected_surface, &surface_operands)
            {
                return Ok(Some(text));
            }
            // (4) Elaboration discharges an authored implication whose
            // antecedent is itself a sibling conjunct: `(and P (=> P Q))`
            // becomes `(and P Q)`. Project both authored operands and
            // eliminate the implication with `implies_pos`.
            if let Some(text) = contextual_implication_and_pos(
                id,
                &expected_gate,
                selected_surface,
                &surface_operands,
            ) {
                return Ok(Some(text));
            }
            // (5) The authored conjunct is the canonical one up to the
            // spelling differences the authored-assume equivalence proves
            // (`(* 2 c)` for `(* c 2)`, a reversed comparison, an equality's
            // orientation, all under congruence): project it, prove the
            // equality with those stock rules, and transport.
            if let Some(text) = self.equivalent_operand_and_pos(
                id,
                &expected_gate,
                selected,
                selected_surface,
                &surface_operands,
            ) {
                return Ok(Some(text));
            }
            if self.work_budget_exhausted() {
                return Err(self.work_budget_error(id.0));
            }
            // Printer-installed Skolem spellings retain the established hole
            // fallback. Producer-authored overrides still refuse export:
            // a changed projection cannot acquire proof authority here.
            if self.skolem_overrides.borrow().contains_key(&source) {
                return Ok(Some(format!(
                    "(step {id} (cl {} {}) :rule {})",
                    printed[0],
                    printed[1],
                    ay_core::UNPROVED_STEP_RULE
                )));
            }
            return Err(invalid_and_pos(
                id,
                format!(
                    "and_pos indexed conjunct is absent from its effective source \
                     (source={:?}; conjunct={:?})",
                    super::surface_congruence::bounded_surface_diagnostic(&source_surface),
                    super::surface_congruence::bounded_surface_diagnostic(selected_surface)
                ),
            ));
        };

        // The ordinary printer is already exact only when both the wire index
        // and literal order agree. Otherwise emit one corrected, spec-shaped
        // tautology under the same proof id; no positional candidate fanout is
        // needed, even when identical operands occur more than once.
        if surface_index == *internal_index as usize && gate_position == 0 && selected_position == 1
        {
            return Ok(None);
        }
        Ok(Some(format!(
            "(step {id} (cl {expected_gate} {selected_surface}) :rule and_pos :args ({surface_index}))"
        )))
    }

    /// Bridge (5) of [`Self::format_flat_surface_and_pos`]: the first authored
    /// operand (or operand of a nested authored conjunction, one level down)
    /// the authored-assume equivalence proves equal to the printed canonical
    /// conjunct. Declines unless the conjunct prints as its own canonical
    /// rendering, the right-hand side every equivalence concludes.
    fn equivalent_operand_and_pos(
        &self,
        id: ProofId,
        expected_gate: &str,
        selected: TermId,
        selected_surface: &str,
        surface_operands: &[&str],
    ) -> Option<String> {
        if crate::render_term_canonical(self.terms, selected) != selected_surface {
            return None;
        }
        // `(operand, the steps concluding (cl GATE operand) as {id}.a)`.
        let mut candidates: Vec<(String, String)> = Vec::new();
        for (index, operand) in surface_operands.iter().enumerate() {
            candidates.push((
                (*operand).to_string(),
                format!(
                    "(step {id}.a (cl {expected_gate} {operand}) :rule and_pos :args ({index}))"
                ),
            ));
            for (inner, child) in split_application(operand, "and")
                .unwrap_or_default()
                .into_iter()
                .enumerate()
            {
                candidates.push((
                    child.clone(),
                    format!(
                        "(step {id}.a0 (cl {expected_gate} {operand}) :rule and_pos :args ({index}))\n\
                         (step {id}.a1 (cl (not {operand}) {child}) :rule and_pos :args ({inner}))\n\
                         (step {id}.a (cl {expected_gate} {child}) :rule resolution :premises ({id}.a0 {id}.a1))"
                    ),
                ));
            }
        }
        let equality_id = format!("{id}.q");
        candidates.into_iter().find_map(|(operand, projection)| {
            let (mut nodes, mut steps) = (0, Vec::new());
            if !self.authored_equivalence(&equality_id, &operand, selected, &mut nodes, &mut steps) {
                return None;
            }
            let equality = format!("(= {operand} {selected_surface})");
            Some(format!(
                "{projection}\n\
                 {}\n\
                 (step {id}.e (cl (not {equality}) (not {operand}) {selected_surface}) :rule equiv_pos2)\n\
                 (step {id} (cl {expected_gate} {selected_surface}) :rule resolution :premises ({id}.a {equality_id} {id}.e))",
                steps.join("\n")
            ))
        })
    }

    /// Rebuild an `and_pos` tautology when the authored spelling wraps the
    /// canonical conjunction in `(or false C)`.
    ///
    /// Elaboration simplifies that wrapper to `C`, so the proof IR correctly
    /// records `and_pos` over `C`; the source override must nevertheless print
    /// the authored root so its `assume` matches the problem.  Printing the IR
    /// step directly would claim `and_pos` over an `or`.  Compose the exact
    /// Boolean rules instead:
    ///
    /// `or_pos(ROOT)`, `false`, and `and_pos(C)` resolve to `¬ROOT ∨ Ak`.
    pub(super) fn resugar_and_pos_false_or_and(
        &self,
        id: ProofId,
        rule: &AletheRule,
        clause: &[TermId],
        args: &[TermId],
    ) -> Option<String> {
        let AletheRule::AndPos(i) = rule else {
            return None;
        };
        let [source] = args else {
            return None;
        };
        let TermData::App(Symbol::Named(name), conjuncts) = self.terms.get(*source) else {
            return None;
        };
        if name != "and" || clause.len() != 2 {
            return None;
        }
        let ak = *conjuncts.get(*i as usize)?;
        let ak_str = self.format_term(ak);
        let printed: [String; 2] = [self.format_term(clause[0]), self.format_term(clause[1])];
        let ak_pos = printed.iter().position(|literal| *literal == ak_str)?;
        let gate = clause[1 - ak_pos];
        // The gate literal must be a negation of the SOURCE conjunction, in
        // either of the two spellings the tracer produces:
        //
        //   * the direct `(not C)` gate of an ordinary Tseitin `and_pos`, or
        //   * its De Morgan surface `(or (not A1) .. (not An))`.
        //
        // Both are re-slotted to the spec-shaped `(cl (not ROOT) Ak)` the
        // composition below derives. Requiring the De Morgan form ALONE (as
        // this guard originally did) left the direct-gate case — which is what
        // `(assert (or false (and ..)))` actually traces — with no certified
        // bridge at all: the printer fell through to the fail-loud
        // `and_pos source no longer prints as an and-term` rejection and the
        // whole proof came out as an `UNVERIFIABLE PROOF` error string, even
        // though the composition below applies verbatim. Nothing is loosened:
        // a gate that is neither spelling is still declined, and every printed
        // shape used below is re-derived from `format_term` and re-checked by
        // `split_application`.
        let gate_is_direct_negation =
            matches!(self.terms.get(gate), TermData::Not(inner) if *inner == *source);
        if !gate_is_direct_negation && !self.is_demorgan_negation(gate, *source) {
            return None;
        }

        let root = self.format_term(*source);
        let root_operands = split_application(&root, "or")?;
        if root_operands.len() != 2 {
            return None;
        }
        let (false_operand, inner) = if root_operands[0] == "false" {
            (&root_operands[0], &root_operands[1])
        } else if root_operands[1] == "false" {
            (&root_operands[1], &root_operands[0])
        } else {
            return None;
        };
        let inner_operands = split_application(inner, "and")?;
        let inner_index = inner_operands
            .iter()
            .position(|operand| operand == &ak_str)?;
        // Require an exact one-to-one printed conjunction. A nested/reordered
        // spelling needs a navigation proof; declining here is safer than
        // guessing an `and_pos` index.
        if inner_operands.len() != conjuncts.len()
            || inner_operands
                .iter()
                .filter(|operand| *operand == &ak_str)
                .count()
                != 1
        {
            return None;
        }

        let or_id = format!("{id}.ow0");
        let false_id = format!("{id}.ow1");
        let and_id = format!("{id}.ow2");
        let drop_id = format!("{id}.ow3");
        // `or_pos` lists the disjuncts in the ROOT's printed order: carcara
        // 1.1.0 compares them position by position. MEASURED at `2c356fd15`
        // on `(assert (or (and p q) false))` + `(assert (not p))`: the
        // false-first clause shipped under `trust_free=yes` and carcara
        // answered `invalid` ("expected terms to be equal: '(and p q)' and
        // 'false'").
        let (first, second) = (&root_operands[0], &root_operands[1]);
        Some(format!(
            "(step {or_id} (cl (not {root}) {first} {second}) :rule or_pos)\n\
             (step {false_id} (cl (not {false_operand})) :rule false)\n\
             (step {and_id} (cl (not {inner}) {ak_str}) :rule and_pos :args ({inner_index}))\n\
             (step {drop_id} (cl (not {root}) {inner}) :rule resolution :premises ({or_id} {false_id}))\n\
             (step {id} (cl (not {root}) {ak_str}) :rule resolution :premises ({drop_id} {and_id}))"
        ))
    }

    /// Bridge an `and_pos` whose indexed conjunct is an and-term ERASED from
    /// the printed source by surface flattening: internally the source is
    /// `(and A (and B C D))` but the effective surface prints `(and A B C D)`,
    /// so the selected conjunct `(and B C D)` is no printed operand at all.
    ///
    /// Every printed child of the selected conjunct is projected off the flat
    /// surface with a genuine `and_pos`, the conjunct is reassembled with the
    /// spec `and_neg` tautology, and one resolution restores the exact traced
    /// clause (carcara resolves with implicit factoring of the repeated gate
    /// literal — validated externally):
    ///
    /// ```text
    /// (step tK.f0 (cl (not (and A B C D)) B) :rule and_pos :args (1))
    /// (step tK.f1 (cl (not (and A B C D)) C) :rule and_pos :args (2))
    /// (step tK.f2 (cl (not (and A B C D)) D) :rule and_pos :args (3))
    /// (step tK.fa (cl (and B C D) (not B) (not C) (not D)) :rule and_neg)
    /// (step tK (cl (not (and A B C D)) (and B C D))
    ///     :rule resolution :premises (tK.fa tK.f0 tK.f1 tK.f2))
    /// ```
    ///
    /// Declines (`None`, caller fails loud) unless EVERY printed child of the
    /// selected conjunct is byte-identical to a top-level printed operand of
    /// the flat surface — an unbridgeable spelling must never guess.
    fn reassemble_flattened_and_pos_conjunct(
        &self,
        id: ProofId,
        expected_gate: &str,
        selected_surface: &str,
        surface_operands: &[&str],
    ) -> Option<String> {
        // One bounded scan of the selected conjunct plus one search over the
        // already-split surface operands per child; charge before allocating.
        self.charge((selected_surface.len() as u64).saturating_mul(3));
        if self.work_budget_exhausted() {
            return None;
        }
        let children = match split_alethe_application_bounded(
            selected_surface,
            "and",
            selected_surface.len(),
            selected_surface.len(),
        ) {
            Ok(children) if children.len() >= 2 => children,
            Ok(_) | Err(_) => return None,
        };
        let surface_bytes = surface_operands
            .iter()
            .map(|operand| operand.len() as u64)
            .sum::<u64>();
        self.charge(surface_bytes.saturating_mul(children.len() as u64));
        if self.work_budget_exhausted() {
            return None;
        }
        let mut projections = Vec::with_capacity(children.len());
        for child in &children {
            let index = surface_operands
                .iter()
                .position(|operand| operand == child)?;
            projections.push(index);
        }

        let mut out = String::new();
        let mut premises = vec![format!("{id}.fa")];
        for (hop, (child, index)) in children.iter().zip(&projections).enumerate() {
            let child_id = format!("{id}.f{hop}");
            let _ = std::fmt::Write::write_fmt(
                &mut out,
                format_args!(
                    "(step {child_id} (cl {expected_gate} {child}) :rule and_pos :args ({index}))\n"
                ),
            );
            premises.push(child_id);
        }
        let _ = std::fmt::Write::write_fmt(
            &mut out,
            format_args!("(step {id}.fa (cl {selected_surface}"),
        );
        for child in &children {
            let _ = std::fmt::Write::write_fmt(&mut out, format_args!(" (not {child})"));
        }
        let _ = std::fmt::Write::write_fmt(
            &mut out,
            format_args!(
                ") :rule and_neg)\n(step {id} (cl {expected_gate} {selected_surface}) \
                 :rule resolution :premises ({}))",
                premises.join(" ")
            ),
        );
        Some(out)
    }
}

fn infer_raw_and_source(
    printer: &AlethePrinter<'_>,
    clause: [TermId; 2],
    index: u32,
) -> Option<TermId> {
    // Mirror native `decode_and_source`: without an explicit source, a direct
    // positive AND literal takes precedence over a negated gate. Such a clause
    // is not the exact raw-gate/indexed-child shape this fallback authenticates.
    if clause.iter().any(|&literal| {
        matches!(
            printer.terms.get(literal),
            TermData::App(Symbol::Named(head), _) if head == "and"
        )
    }) {
        return None;
    }
    let mut source = None;
    for gate_position in 0..2 {
        let TermData::Not(candidate) = printer.terms.get(clause[gate_position]) else {
            continue;
        };
        let TermData::App(Symbol::Named(head), conjuncts) = printer.terms.get(*candidate) else {
            continue;
        };
        if head == "and"
            && conjuncts.get(index as usize) == Some(&clause[1 - gate_position])
            && source.replace(*candidate).is_some()
        {
            return None;
        }
    }
    source
}

fn invalid_and_pos(id: ProofId, reason: impl Into<String>) -> AlethePrintError {
    AlethePrintError::InvalidSurfaceStep {
        id,
        reason: reason.into(),
    }
}

/// Derive `(cl (not SOURCE) Q)` from the authored conjuncts `(=> P Q)` and
/// `P` of the printed conjunction `SOURCE`. Only the first implication (in
/// operand order) whose consequent is exactly the selected conjunct and whose
/// antecedent is exactly another operand is used; anything else declines.
fn contextual_implication_and_pos(
    id: ProofId,
    expected_gate: &str,
    selected_surface: &str,
    surface_operands: &[&str],
) -> Option<String> {
    surface_operands
        .iter()
        .enumerate()
        .find_map(|(implication_index, operand)| {
            let (antecedent, consequent) = split_binary_implies(operand)?;
            if consequent != selected_surface {
                return None;
            }
            let antecedent_index = surface_operands
                .iter()
                .enumerate()
                .find(|&(index, other)| index != implication_index && *other == antecedent)?
                .0;
            Some(format!(
                "(step {id}.i (cl {expected_gate} {operand}) :rule and_pos :args ({implication_index}))\n\
                 (step {id}.p (cl {expected_gate} {antecedent}) :rule and_pos :args ({antecedent_index}))\n\
                 (step {id}.e (cl (not {operand}) (not {antecedent}) {selected_surface}) :rule implies_pos)\n\
                 (step {id}.r (cl {expected_gate} {expected_gate} {selected_surface}) :rule resolution :premises ({id}.i {id}.p {id}.e))\n\
                 (step {id} (cl {expected_gate} {selected_surface}) :rule contraction :premises ({id}.r))"
            ))
        })
}

/// The atom `A` of a printed `(not A)`.
fn printed_negation_operand(printed: &str) -> Option<String> {
    let operands = split_application(printed, "not")?;
    let [operand] = operands.as_slice() else {
        return None;
    };
    Some(operand.clone())
}

/// Derive `(cl (not SOURCE) (not B))` from an authored conjunct `(not A)` of
/// the printed conjunction `SOURCE` when `B` implies `A` by the narrowly
/// checked printed `la_generic` unit implication (the recognizer of bridge
/// (3), with the roles of premise and conclusion swapped by the negation).
fn negated_comparison_and_pos(
    id: ProofId,
    expected_gate: &str,
    selected_surface: &str,
    surface_operands: &[&str],
) -> Option<String> {
    let canonical_atom = printed_negation_operand(selected_surface)?;
    surface_operands
        .iter()
        .enumerate()
        .find_map(|(surface_index, operand)| {
            let authored_atom = printed_negation_operand(operand)?;
            crate::printed_la_generic_unit_implication_is_supported(&canonical_atom, &authored_atom)
                .then(|| {
                    format!(
                        "(step {id}.a (cl {expected_gate} {operand}) :rule and_pos :args ({surface_index}))\n\
                         (step {id}.n (cl (not {canonical_atom}) {authored_atom}) :rule la_generic :args (1 1))\n\
                         (step {id} (cl {expected_gate} {selected_surface}) :rule resolution :premises ({id}.a {id}.n))"
                    )
                })
        })
}
