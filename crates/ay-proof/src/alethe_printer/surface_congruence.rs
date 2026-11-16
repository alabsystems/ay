// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked bridges for congruence whose printed operands differ from the term
//! DAG by an authored spelling: exact numeric identities (multiplication
//! commutation, comparison reversal, the additive identity, the lenient
//! negative literal), a bit-vector variable-plus-zero fold, or an equality
//! printed in the author's operand order.

use super::authored_assume::EquivalenceDirection;
use super::*;

mod checker_identity;
mod order;
mod readings;
mod zero_extend_zero;

const MAX_SURFACE_CONG_BRIDGE_STEPS: usize = 64 * 1024;
const MAX_SURFACE_CONG_BRIDGE_OUTPUT_BYTES: usize = 32 * 1024 * 1024;
const MAX_DIAGNOSTIC_CHARS: usize = 256;

struct SurfaceCongruenceApplication {
    left_args: Vec<String>,
    right_args: Vec<String>,
    left_internal_args: Vec<TermId>,
    right_internal_args: Vec<TermId>,
}

struct SurfaceCongruencePremise {
    id: ProofId,
    left: TermId,
    right: TermId,
    printed_left: String,
    printed_right: String,
}

struct SurfacePositionRepair {
    steps: Vec<String>,
    premise: String,
    consumed_premise: Option<usize>,
}

/// Whether a position repair may read a printed premise against its internal
/// endpoints crosswise ([`AlethePrinter::reversed_premise_bridge`]). Every
/// reading is tried positionally first, so a congruence that rendered before
/// renders byte-identically.
#[derive(Clone, Copy, PartialEq, Eq)]
enum PremiseReading {
    Positional,
    AllowReversed,
}

struct SurfacePremiseBridge<'a> {
    id: &'a str,
    target_left: &'a str,
    target_right: &'a str,
    internal_left: TermId,
    internal_right: TermId,
    premise_left: &'a str,
    premise_right: &'a str,
    premise: String,
}

impl AlethePrinter<'_> {
    /// Repair exact Int/Real multiplication commutations below
    /// position-preserving congruence. Every native premise is matched by its
    /// internal endpoints first; surface-only matches never acquire authority.
    pub(super) fn surface_ac_cong_bridge(
        &self,
        id: ProofId,
        clause: &[TermId],
        premises: &[ProofId],
        args: &[TermId],
    ) -> Result<Option<String>, String> {
        let readings = self.decode_surface_congruence(clause, args)?;
        if readings.is_empty() {
            return Ok(None);
        }
        let premise_rows = self.surface_congruence_premises(premises)?;
        let mut refusal = None;
        for premise_reading in [PremiseReading::Positional, PremiseReading::AllowReversed] {
            for application in &readings {
                match self.surface_ac_cong_bridge_under(
                    id,
                    clause,
                    application,
                    &premise_rows,
                    premise_reading,
                ) {
                    Ok(bridge) => return Ok(bridge),
                    // The FIRST reading is the stored order, so its refusal is
                    // the one every existing diagnostic names; a later reading
                    // that also fails must not rename it.
                    Err(error) => refusal = refusal.or(Some(error)),
                }
            }
        }
        Err(refusal.unwrap_or_else(|| "surface congruence has no printed reading".to_string()))
    }

    /// Build the bridge under ONE pairing of printed to internal arguments.
    fn surface_ac_cong_bridge_under(
        &self,
        id: ProofId,
        clause: &[TermId],
        application: &SurfaceCongruenceApplication,
        premise_rows: &[SurfaceCongruencePremise],
        premise_reading: PremiseReading,
    ) -> Result<Option<String>, String> {
        let (generated, ordered_premises) = self.repair_surface_congruence_positions(
            &id.to_string(),
            application,
            premise_rows,
            premise_reading,
        )?;
        if generated.is_empty() && readings::in_stored_order(&ordered_premises, premise_rows) {
            return Ok(None);
        }
        let mut output = generated.join("\n");
        output.push('\n');
        let _ = std::fmt::Write::write_fmt(
            &mut output,
            format_args!(
                "(step {id} {} :rule cong :premises ({}))",
                self.format_clause(clause),
                ordered_premises.join(" ")
            ),
        );
        Ok(Some(output))
    }

    /// Repair every printed argument position of `application` that differs,
    /// each against a premise matched by its INTERNAL endpoints, and require
    /// every premise to be consumed. Returns the generated steps and the
    /// `cong` premises in position order. Shared by the multiplication bridge
    /// above and the order-reversal bridge (`order::canonical_order_cong_steps`).
    fn repair_surface_congruence_positions(
        &self,
        id: &str,
        application: &SurfaceCongruenceApplication,
        premise_rows: &[SurfaceCongruencePremise],
        premise_reading: PremiseReading,
    ) -> Result<(Vec<String>, Vec<String>), String> {
        let mut used = vec![false; premise_rows.len()];
        let mut ordered_premises = Vec::new();
        let mut generated = Vec::new();
        let mut generated_bytes = 0usize;
        let mut bridge_count = 0usize;

        for position in 0..application.left_args.len() {
            if application.left_args[position] == application.right_args[position] {
                continue;
            }
            let bridge_id = format!("{id}.ac{bridge_count}");
            let repair = self.repair_surface_congruence_position(
                position,
                &bridge_id,
                application,
                premise_rows,
                &used,
                premise_reading,
            )?;
            if let Some(index) = repair.consumed_premise {
                used[index] = true;
            }
            append_generated_steps(&mut generated, &mut generated_bytes, repair.steps)?;
            ordered_premises.push(repair.premise);
            bridge_count += 1;
        }
        if used.iter().any(|used| !used) {
            return Err(
                "surface congruence carries a premise unused by its printed arguments".to_string(),
            );
        }
        Ok((generated, ordered_premises))
    }

    fn surface_congruence_premises(
        &self,
        premises: &[ProofId],
    ) -> Result<Vec<SurfaceCongruencePremise>, String> {
        let clauses = self.proof_clauses.borrow();
        let mut rows = Vec::with_capacity(premises.len());
        for &id in premises {
            let Some([literal]) = clauses.get(&id).map(Vec::as_slice) else {
                return Err("surface congruence premise is not a unit equality".to_string());
            };
            let TermData::App(Symbol::Named(equality), internal_args) = self.terms.get(*literal)
            else {
                return Err("surface congruence premise is not an internal equality".to_string());
            };
            let [left, right] = internal_args.as_slice() else {
                return Err("surface congruence premise has non-binary equality arity".to_string());
            };
            if equality != "=" {
                return Err("surface congruence premise is not an internal equality".to_string());
            }
            let printed = self.format_term(*literal);
            let Some([printed_left, printed_right]) = split_application(&printed, "=")
                .and_then(|parts| <[String; 2]>::try_from(parts).ok())
            else {
                return Err(format!(
                    "surface congruence premise is not a printed equality (printed={:?})",
                    bounded_surface_diagnostic(&printed)
                ));
            };
            // Keep each printed endpoint beside the internal endpoint it spells.
            let (printed_left, printed_right) =
                if self.printed_equality_is_flipped(*left, *right, &printed_left, &printed_right) {
                    (printed_right, printed_left)
                } else {
                    (printed_left, printed_right)
                };
            rows.push(SurfaceCongruencePremise {
                id,
                left: *left,
                right: *right,
                printed_left,
                printed_right,
            });
        }
        Ok(rows)
    }

    /// Whether a premise equality prints its endpoints in the opposite order
    /// from the term DAG.
    ///
    /// THE SHAPE. `mk_eq` orders an equality's operands canonically, while the
    /// surface-override ledger keeps the AUTHOR's spelling of the whole
    /// literal: the authored `(= x2 (+ x0 0))` interns as `(= x0 x2)` and
    /// prints `(= x2 (+ x0 0))` in every step that names it. Read positionally,
    /// that printed premise pairs `x2` with the internal `x0`, so a congruence
    /// citing it compared each spelling with the wrong endpoint and refused a
    /// step whose bridge was one `sum_simplify` away (measured on the
    /// OR-substitution fuzz: `left="x2"; right="x0"` over the premise above).
    ///
    /// The orientation is read off the document's own renderings of the two
    /// internal endpoints: the printed sides that MATCH a rendering decide it,
    /// and a tie keeps the stored order, which is what this decoder assumed
    /// before. Either way every repair after this is the same checked one, and
    /// a premise cited by `cong` or `trans` is accepted by the checker in
    /// either orientation, so this only chooses which spelling is compared
    /// with which endpoint.
    fn printed_equality_is_flipped(
        &self,
        left: TermId,
        right: TermId,
        printed_left: &str,
        printed_right: &str,
    ) -> bool {
        if left == right {
            return false;
        }
        let rendered_left = self.format_term(left);
        let rendered_right = self.format_term(right);
        let stored = usize::from(printed_left == rendered_left)
            + usize::from(printed_right == rendered_right);
        let flipped = usize::from(printed_left == rendered_right)
            + usize::from(printed_right == rendered_left);
        flipped > stored
    }

    fn repair_surface_congruence_position(
        &self,
        position: usize,
        bridge_id: &str,
        application: &SurfaceCongruenceApplication,
        premises: &[SurfaceCongruencePremise],
        used: &[bool],
        premise_reading: PremiseReading,
    ) -> Result<SurfacePositionRepair, String> {
        let left = application.left_internal_args[position];
        let right = application.right_internal_args[position];
        let left_surface = &application.left_args[position];
        let right_surface = &application.right_args[position];
        if left == right {
            // Different SMT-LIB spellings of the same bit-vector literal are
            // parsed as the same term. The bounded positional comparator also
            // admits this equivalence below otherwise identical applications;
            // make that identity explicit with `refl` before using it as a
            // congruence premise. Changed values, widths, heads, or argument
            // positions still fall through to the existing narrow repair.
            if surface_literal::equal_modulo_bitvec_literal_spelling(left_surface, right_surface) {
                return Ok(SurfacePositionRepair {
                    steps: vec![format!(
                        "(step {bridge_id} (cl (= {left_surface} {right_surface})) :rule refl)"
                    )],
                    premise: bridge_id.to_string(),
                    consumed_premise: None,
                });
            }
            let steps =
                self.identity_surface_pair_steps(bridge_id, left_surface, right_surface, left)?;
            return Ok(SurfacePositionRepair {
                steps,
                premise: bridge_id.to_string(),
                consumed_premise: None,
            });
        }

        let Some((index, premise, premise_left, premise_right)) =
            unused_premise_over(premises, used, left, right)
        else {
            return Err(format!(
                "printed argument {position} differs internally without a matching certified premise"
            ));
        };
        if left_surface == premise_left && right_surface == premise_right {
            return Ok(SurfacePositionRepair {
                steps: Vec::new(),
                premise: premise.id.to_string(),
                consumed_premise: Some(index),
            });
        }
        let bridge = SurfacePremiseBridge {
            id: bridge_id,
            target_left: left_surface,
            target_right: right_surface,
            internal_left: left,
            internal_right: right,
            premise_left,
            premise_right,
            premise: premise.id.to_string(),
        };
        let steps = match self.bridge_surface_premise_spelling(&bridge) {
            Ok(steps) => steps,
            // The positional refusal is the one every diagnostic names.
            Err(refusal) if premise_reading == PremiseReading::AllowReversed => {
                self.reversed_premise_bridge(&bridge).ok_or(refusal)?
            }
            Err(refusal) => return Err(refusal),
        };
        Ok(SurfacePositionRepair {
            steps,
            premise: bridge_id.to_string(),
            consumed_premise: Some(index),
        })
    }

    /// The premise read the other way round: an authored equality keeps its
    /// own operand order, so `(assert (= -2 x))` prints the premise
    /// `(= -2 x)` over the internal `(= x (- 2))`, whose endpoints the
    /// positional reading pairs crosswise (`x` with `-2`). `symm` turns the
    /// printed premise around, and the ordinary checked repair then bridges
    /// each side against the internal endpoint it actually spells. Only a
    /// premise whose printed side already IS the crosswise target on one end
    /// is read this way, and only after every reading failed positionally.
    /// `None` when neither end crosses or a side still has no certified repair.
    fn reversed_premise_bridge(&self, bridge: &SurfacePremiseBridge<'_>) -> Option<Vec<String>> {
        if bridge.target_left != bridge.premise_right && bridge.target_right != bridge.premise_left
        {
            return None;
        }
        if bridge.target_left == bridge.premise_right && bridge.target_right == bridge.premise_left
        {
            return Some(vec![format!(
                "(step {} (cl (= {} {})) :rule symm :premises ({}))",
                bridge.id, bridge.target_left, bridge.target_right, bridge.premise
            )]);
        }
        let flipped = format!("{}.s", bridge.id);
        let mut steps = vec![format!(
            "(step {flipped} (cl (= {} {})) :rule symm :premises ({}))",
            bridge.premise_right, bridge.premise_left, bridge.premise
        )];
        steps.extend(
            self.bridge_surface_premise_spelling(&SurfacePremiseBridge {
                premise_left: bridge.premise_right,
                premise_right: bridge.premise_left,
                premise: flipped,
                ..*bridge
            })
            .ok()?,
        );
        Some(steps)
    }

    fn bridge_surface_premise_spelling(
        &self,
        bridge: &SurfacePremiseBridge<'_>,
    ) -> Result<Vec<String>, String> {
        let mut output = Vec::new();
        let mut chain = Vec::new();
        if bridge.target_left != bridge.premise_left {
            let left_id = format!("{}.l", bridge.id);
            output.extend(self.identity_surface_pair_steps(
                &left_id,
                bridge.target_left,
                bridge.premise_left,
                bridge.internal_left,
            )?);
            chain.push(left_id);
        }
        chain.push(bridge.premise.clone());
        if bridge.premise_right != bridge.target_right {
            let right_id = format!("{}.r", bridge.id);
            output.extend(self.identity_surface_pair_steps(
                &right_id,
                bridge.premise_right,
                bridge.target_right,
                bridge.internal_right,
            )?);
            chain.push(right_id);
        }
        output.push(format!(
            "(step {} (cl (= {} {})) :rule trans :premises ({}))",
            bridge.id,
            bridge.target_left,
            bridge.target_right,
            chain.join(" ")
        ));
        Ok(output)
    }

    fn identity_surface_pair_steps(
        &self,
        id: &str,
        left: &str,
        right: &str,
        canonical_term: TermId,
    ) -> Result<Vec<String>, String> {
        if let Some(steps) = surface_literal::same_printed_term_steps(id, left, right) {
            return Ok(steps);
        }
        let canonical = crate::render_term_canonical(self.terms, canonical_term);
        // The authored `-2` beside the canonical `(- 2)` of a constant this
        // position holds: one term, which pinned carcara's `refl` re-derives.
        if let Some(steps) = surface_literal::negative_literal_shorthand_steps(
            self.terms,
            id,
            left,
            right,
            canonical_term,
        ) {
            return Ok(steps);
        }
        let steps = if right == canonical {
            self.format_nested_identity_surface_equivalence(
                id,
                left,
                canonical_term,
                EquivalenceDirection::SurfaceToCanonical,
            )
        } else if left == canonical {
            self.format_nested_identity_surface_equivalence(
                id,
                right,
                canonical_term,
                EquivalenceDirection::CanonicalToSurface,
            )
        } else {
            self.bridge_two_noncanonical_identity_surfaces(id, left, right, canonical_term)
        };
        if let Some(steps) = steps {
            return Ok(steps);
        }
        if let Some(steps) = comparison_reversal_pair_steps(id, left, right, &canonical) {
            return Ok(steps);
        }
        if let Some(steps) =
            self.format_bv_add_zero_surface_equivalence(id, left, right, canonical_term)
        {
            return Ok(steps);
        }
        if let Some(steps) = self.checker_identity_pair_steps(id, left, right, canonical_term) {
            return Ok(steps);
        }
        // No arithmetic identity relates the two spellings — but the PROBLEM
        // may already assert the equality between them.
        if let Some(steps) = self.authored_assume_equality_steps(id, left, right) {
            return Ok(steps);
        }
        Err(unsupported_surface_pair_reason(left, right, &canonical))
    }

    /// Derive `(= left right)` under `id` from an `assume` the document has
    /// already emitted, when the two printed spellings are exactly a problem
    /// assertion.
    ///
    /// THE SHAPE THIS REPAIRS. Equality substitution rewrites `(+ F37 a48)` to
    /// `1` because the query asserts `(= (+ F37 a48) 1)`. Both sides of the
    /// resulting congruence conclusion then hold the SAME internal argument
    /// while one side still prints the authored spelling its surface override
    /// records and the other prints the canonical `1`. Nothing in the proof
    /// object explains that divergence — internally the position is reflexive —
    /// and the multiplication-commutation repair above correctly declines: the
    /// two spellings are not AC-variants and no arithmetic identity relates
    /// them. Measured on QF_LIA `CircularTrains-PT-096__RC-02` as
    /// `left="(+ F37 a48)"; right="1"; canonical="1"`.
    ///
    /// WHY CITING THE `assume` IS A DERIVATION AND NOT A FABRICATED BRIDGE.
    /// The cited id names an `assume` command already in the document, and
    /// carcara matches every `assume` against the ORIGINAL problem's
    /// assertions before it checks a single rule — MEASURED: an `assume` whose
    /// term is absent from the problem fails as "could not match term to any of
    /// the original problem premises", and the document is `invalid`. So the
    /// equality this reads is a hypothesis of the query itself, the very
    /// hypothesis that licensed AY to identify the two terms; the steps below
    /// add no assumption the document did not already carry, and every one of
    /// them is an ordinary instance of its rule over the printed operands.
    ///
    /// FAILS CLOSED. Only an EXACT textual match of the whole equality, in one
    /// of its two orientations, against a plain already-emitted `assume`
    /// counts. A partial, modulo-AC, or single-endpoint match declines and the
    /// caller's loud refusal is unchanged.
    fn authored_assume_equality_steps(
        &self,
        id: &str,
        left: &str,
        right: &str,
    ) -> Option<Vec<String>> {
        let PrintedAssumeEquality {
            assume,
            reversed,
            conjunct,
        } = self.printed_assume_equality(left, right)?;
        let (mut steps, assume) = match conjunct {
            None => (Vec::new(), assume.to_string()),
            Some(AssumedConjunctEquality { gate, kind }) => {
                // Project the equality off the assumed conjunction with
                // ordinary `and_pos` steps (through `implies_pos` when it is
                // the consequent of an authored implication whose antecedent
                // is a sibling conjunct), then resolve the gate away against
                // the `assume` itself.
                let carried = if reversed {
                    format!("(= {right} {left})")
                } else {
                    format!("(= {left} {right})")
                };
                let mut steps = Vec::new();
                let premises = match kind {
                    AssumedConjunctKind::Direct(index) => {
                        steps.push(format!(
                            "(step {id}.ap (cl {gate} {carried}) :rule and_pos :args ({index}))"
                        ));
                        format!("{id}.ap")
                    }
                    AssumedConjunctKind::Implied {
                        implication,
                        implication_text,
                        antecedent,
                        antecedent_text,
                    } => {
                        steps.push(format!(
                            "(step {id}.ai (cl {gate} {implication_text}) :rule and_pos :args ({implication}))"
                        ));
                        steps.push(format!(
                            "(step {id}.aa (cl {gate} {antecedent_text}) :rule and_pos :args ({antecedent}))"
                        ));
                        steps.push(format!(
                            "(step {id}.ae (cl (not {implication_text}) (not {antecedent_text}) {carried}) :rule implies_pos)"
                        ));
                        format!("{id}.ai {id}.aa {id}.ae")
                    }
                };
                steps.push(format!(
                    "(step {id}.cj (cl {carried}) :rule resolution :premises ({assume} {premises}))"
                ));
                (steps, format!("{id}.cj"))
            }
        };
        if reversed {
            // The assume concludes `(= right left)`.
            steps.push(format!(
                "(step {id} (cl (= {left} {right})) :rule symm :premises ({assume}))"
            ));
            return Some(steps);
        }
        // The assume concludes `(= left right)` already. `id` must still be the
        // step that carries it, because the caller chains on `id`; re-derive it
        // with a reflexive first leg rather than renaming the assume.
        steps.push(format!("(step {id}.eq (cl (= {left} {left})) :rule refl)"));
        steps.push(format!(
            "(step {id} (cl (= {left} {right})) :rule trans :premises ({id}.eq {assume}))"
        ));
        Some(steps)
    }

    fn bridge_two_noncanonical_identity_surfaces(
        &self,
        id: &str,
        left: &str,
        right: &str,
        canonical_term: TermId,
    ) -> Option<Vec<String>> {
        let left_id = format!("{id}.l");
        let right_id = format!("{id}.r");
        let mut output = self.format_nested_identity_surface_equivalence(
            &left_id,
            left,
            canonical_term,
            EquivalenceDirection::SurfaceToCanonical,
        )?;
        output.extend(self.format_nested_identity_surface_equivalence(
            &right_id,
            right,
            canonical_term,
            EquivalenceDirection::CanonicalToSurface,
        )?);
        output.push(format!(
            "(step {id} (cl (= {left} {right})) :rule trans :premises ({left_id} {right_id}))"
        ));
        Some(output)
    }

    pub(super) fn surface_cong_has_different_order_operators(&self, clause: &[TermId]) -> bool {
        let [conclusion] = clause else {
            return false;
        };
        let Some([left, right]) = split_application(&self.format_term(*conclusion), "=")
            .and_then(|args| <[String; 2]>::try_from(args).ok())
        else {
            return false;
        };
        matches!(
            (
                surface_order_operator(left.as_str()),
                surface_order_operator(right.as_str())
            ),
            (Some(left_op), Some(right_op)) if left_op != right_op
        )
    }

    pub(super) fn surface_cong_has_uncheckable_operands(
        &self,
        clause: &[TermId],
    ) -> Option<String> {
        let [conclusion] = clause else {
            return None;
        };
        let [left, right] = split_application(&self.format_term(*conclusion), "=")
            .and_then(|args| <[String; 2]>::try_from(args).ok())?;
        match (printed_head_symbol(&left), printed_head_symbol(&right)) {
            (Some(left_head), Some(right_head)) if left_head != right_head => Some(format!(
                "surface rewriting gives the two congruence applications different operators ('{left_head}' and '{right_head}')"
            )),
            (Some(_), Some(_)) => None,
            _ => Some(format!(
                "a congruence operand is not a printed application ('{left}' and '{right}'), which no congruence rule can check"
            )),
        }
    }
}

/// The first unused premise whose INTERNAL endpoints are `left` and `right`,
/// in either orientation, with its printed endpoints in that same order.
fn unused_premise_over<'p>(
    premises: &'p [SurfaceCongruencePremise],
    used: &[bool],
    left: TermId,
    right: TermId,
) -> Option<(usize, &'p SurfaceCongruencePremise, &'p String, &'p String)> {
    premises.iter().enumerate().find_map(|(index, premise)| {
        if used[index] {
            return None;
        }
        if premise.left == left && premise.right == right {
            Some((
                index,
                premise,
                &premise.printed_left,
                &premise.printed_right,
            ))
        } else if premise.left == right && premise.right == left {
            Some((
                index,
                premise,
                &premise.printed_right,
                &premise.printed_left,
            ))
        } else {
            None
        }
    })
}

fn append_generated_steps(
    output: &mut Vec<String>,
    output_bytes: &mut usize,
    steps: Vec<String>,
) -> Result<(), String> {
    let Some(next_steps) = output.len().checked_add(steps.len()) else {
        return Err("surface congruence bridge step count overflowed".to_string());
    };
    let step_bytes = steps.iter().try_fold(0usize, |bytes, step| {
        bytes.checked_add(step.len().saturating_add(1))
    });
    let Some(next_bytes) = step_bytes.and_then(|bytes| output_bytes.checked_add(bytes)) else {
        return Err("surface congruence bridge output size overflowed".to_string());
    };
    if next_steps > MAX_SURFACE_CONG_BRIDGE_STEPS
        || next_bytes > MAX_SURFACE_CONG_BRIDGE_OUTPUT_BYTES
    {
        return Err("surface congruence bridge exceeds its aggregate output bound".to_string());
    }
    *output_bytes = next_bytes;
    output.extend(steps);
    Ok(())
}

/// `(= left right)` when one side is the canonical comparison and the other
/// its argument-swapped authored spelling, e.g. a `forall_inst` instance of
/// the authored body `(> y x)` beside the canonical `(< x x)` its premise
/// prints. The steps are `comparison_reversal_step`'s `comp_simplify` chain,
/// the one the authored-assume bridge already ships for the same pair.
fn comparison_reversal_pair_steps(
    id: &str,
    left: &str,
    right: &str,
    canonical: &str,
) -> Option<Vec<String>> {
    let (surface, direction) = if right == canonical {
        (left, EquivalenceDirection::SurfaceToCanonical)
    } else if left == canonical {
        (right, EquivalenceDirection::CanonicalToSurface)
    } else {
        return None;
    };
    let mut steps = Vec::new();
    authored_assume::comparison_reversal_step(id, surface, canonical, direction, &mut steps)
        .then_some(steps)
}

fn unsupported_surface_pair_reason(left: &str, right: &str, canonical: &str) -> String {
    let left = bounded_surface_diagnostic(left);
    let right = bounded_surface_diagnostic(right);
    let canonical = bounded_surface_diagnostic(canonical);
    format!(
        "printed congruence operands are not position-preserving congruence over exact arithmetic identities; left={left:?}; right={right:?}; canonical={canonical:?}"
    )
}

pub(super) fn bounded_surface_diagnostic(surface: &str) -> String {
    let mut diagnostic: String = surface.chars().take(MAX_DIAGNOSTIC_CHARS).collect();
    if surface.chars().count() > MAX_DIAGNOSTIC_CHARS {
        diagnostic.push_str("...");
    }
    diagnostic
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_reversed_comparison_beside_its_canonical_spelling_is_bridged() {
        assert_eq!(
            comparison_reversal_pair_steps("t", "(> 5 x)", "(< x 5)", "(< x 5)"),
            Some(vec![
                "(step t.s0 (cl (= (> 5 x) (not (<= 5 x)))) :rule comp_simplify)".to_string(),
                "(step t.s1 (cl (= (not (<= 5 x)) (< x 5))) :rule comp_simplify)".to_string(),
                "(step t (cl (= (> 5 x) (< x 5))) :rule trans :premises (t.s0 t.s1))".to_string(),
            ])
        );
        assert_eq!(
            comparison_reversal_pair_steps("t", "(> 5 x)", "(< x 6)", "(< x 6)"),
            None,
            "the operands must be the canonical ones, swapped"
        );
        assert_eq!(
            comparison_reversal_pair_steps("t", "(> 5 x)", "(< x 5)", "(<= x 5)"),
            None,
            "one side must be the canonical rendering"
        );
    }

    /// REGRESSION (p6 probe, `(forall ((y Int)) (or (< y -3) (> y x)))` at
    /// `y := x`): the reordering chain's `(= (not (<= x x)) (< x x))` is no
    /// `comp_simplify` instance to pinned carcara, which folds the self
    /// comparison first. The pair meets at `false` in either orientation.
    #[test]
    fn a_strict_self_comparison_reversal_meets_at_false() {
        for (left, right, last) in [
            (
                "(> x x)",
                "(< x x)",
                "(step t (cl (= (> x x) (< x x))) :rule trans :premises (t.g4 t.l1))",
            ),
            (
                "(< x x)",
                "(> x x)",
                "(step t (cl (= (< x x) (> x x))) :rule trans :premises (t.l0 t.g5))",
            ),
        ] {
            let steps = comparison_reversal_pair_steps("t", left, right, "(< x x)")
                .unwrap_or_else(|| panic!("{left} / {right}"));
            assert!(
                steps
                    .iter()
                    .all(|step| !step.contains("(= (not (<= x x)) (< x x))")),
                "{steps:?}"
            );
            assert!(steps
                .contains(&"(step t.l0 (cl (= (< x x) false)) :rule comp_simplify)".to_string()));
            assert_eq!(steps.last().map(String::as_str), Some(last));
        }
    }

    #[test]
    fn test_cong_bridge_aggregate_step_cap_fails_closed() {
        let mut output = Vec::new();
        let mut bytes = 0;
        let steps = vec![String::new(); MAX_SURFACE_CONG_BRIDGE_STEPS + 1];
        assert!(append_generated_steps(&mut output, &mut bytes, steps).is_err());
        assert_eq!(output.as_slice(), &[] as &[String]);
    }

    #[test]
    fn test_cong_bridge_aggregate_byte_cap_fails_closed_atomically() {
        let mut output = Vec::new();
        let mut bytes = MAX_SURFACE_CONG_BRIDGE_OUTPUT_BYTES;
        assert!(append_generated_steps(&mut output, &mut bytes, vec![String::new()]).is_err());
        assert_eq!(output.as_slice(), &[] as &[String]);
        assert_eq!(bytes, MAX_SURFACE_CONG_BRIDGE_OUTPUT_BYTES);
    }
}
