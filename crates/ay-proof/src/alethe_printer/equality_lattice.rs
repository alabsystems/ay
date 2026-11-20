// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked lowering of an all-equality integer lattice lemma.
//!
//! An `IntGuardedSplitGap` lemma whose literals are all negated integer
//! equalities `(not (= L_i R_i))` is certified by AY's strict checker through
//! the guarded-split validator's zero-split case (equality substitution and the
//! attainable-value gap). Pinned carcara has no rule for that argument, so the
//! step used to print as an honest `hole`. It does, however, check the same
//! lattice fact through `la_generic`, whose integer strengthening turns
//! `x > c` into `x ≥ ⌊c⌋ + gcd(coefficients, c)` — the rule the unit
//! divisibility lowering in `promoted_lia` already relies on.
//!
//! [`ay_core::proof_validation::lia_equality_lattice_witness`] recovers the
//! integer multipliers `λ` of the validator's elimination: the single derived
//! row `D = Σ λ_i·(L_i − R_i)` takes values only in `d + gℤ`, which skips zero
//! (`lower < 0 < upper` its neighbours, `upper − lower = g`). The lowering is
//! the unit divisibility derivation over that `D`:
//!
//! ```text
//! split: (cl (<= D lower) (<= upper D))            la_generic (1 1)
//! lo:    (cl ¬E_1 … ¬E_n (not (<= D lower)))       la_generic (λ_1 … λ_n 1)
//! hi:    (cl ¬E_1 … ¬E_n (not (<= upper D)))       la_generic (−λ_1 … −λ_n 1)
//! then two resolutions to (cl ¬E_1 … ¬E_n)
//! ```
//!
//! `lo` and `hi` are rational identities (`D` is spelled from the very
//! printed operands `L_i`, `R_i`, so the rows cancel by construction); `split`
//! is the lattice step and holds only because every atom of `D` is an
//! integer. A ground witness (`D` a nonzero constant) needs no split: one
//! `la_generic` over the literals with the multipliers `λ`.
//!
//! What makes it safe to publish:
//!
//! * the lowering is bound to the strict checker: it renders only an
//!   `IntGuardedSplitGap` step, and the witness exists only for a clause the
//!   checker's own recognizer (`recognize_int_guarded_split_gap`) accepts;
//! * the witness recomputes `D` from the literals through the all-`Int`
//!   normalizer and re-runs the gcd test;
//! * the PRINTED row of every literal — as the pinned checker's `la_generic`
//!   reads it (`la_generic_surface`) — must equal that literal's internal
//!   row atom for atom, each internal atom keyed by its own rendering, two
//!   atoms of one literal never sharing one key. So a surface channel may
//!   re-spell the literal (`(* 4096 c1)` for `(* c1 4096)`), but never change
//!   a row or make an atom of `D` anything but an internal `Int` term —
//!   carcara's strengthening does not check sorts, so this is where
//!   integrality is enforced. The check is per literal: two literals whose
//!   distinct internal atoms render alike ship a substitution instance of the
//!   same valid lemma, whose merged coefficients are sums of multiples of `g`,
//!   so `D` still skips zero;
//! * every emitted `la_generic` is replayed over its bytes by the printer's
//!   `judge_printed_la_generic` chokepoint, which holes the step on refusal.
//!
//! Any other clause, kind or surface keeps the honest `hole`.
//!
//! This surface policy is deliberately looser than the unit lowering's, which
//! requires an `Identical` clause surface
//! ([`crate::lia_divisibility_lowering_supported`]): the ring rows print their
//! products in the problem's own spelling, and a row-for-row match is what the
//! lattice argument needs. It rests on the byte-level replay above and on the
//! standing assumption of every surface channel that a term override is a
//! sort-preserving re-spelling.
//!
//! `AlethePrinter::format_lia_lattice` is the printer's one entry to the
//! integer-lattice lowerings (this one, the unit Divisibility lowering in
//! `promoted_lia`, and the `IntCgCutChain` lowering in `cut_chain`), and
//! [`lia_lattice_lowering_supported`] is the publication wire-gap screen's,
//! over the same predicates. The screen asks through a
//! fresh printer over the producer's override table alone, like the unit
//! screen: it sees neither the real printer's let-bridge and Skolem renderings
//! nor the judge's step cap, so it can admit a step the real printer then
//! prints as the honest `hole` (the cut-chain screen at least replays its own
//! rendering). It never lets an unjudged `la_generic` out.

use super::la_generic_surface::readings::{printed_atom_key, printed_linear_difference};
use super::*;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

/// Render allowance for the publication gate's replay of this lowering.
const MAX_WORK: u64 = 4 * 1024 * 1024;

/// One printed clause literal `(not (= left right))`.
struct PrintedEquality {
    literal: String,
    left: String,
    right: String,
}

/// The printed derivation of one lemma, before rendering.
struct EqualityLatticePlan {
    rows: Vec<PrintedEquality>,
    multipliers: Vec<BigInt>,
    gap: Option<(BigInt, BigInt)>,
}

/// Whether one proof step is a theory lemma with one of the checked
/// integer-lattice lowerings — the unit Divisibility theorem
/// ([`crate::lia_divisibility_lowering_supported`]), this module's
/// all-equality `IntGuardedSplitGap`, or an `IntCgCutChain` (`cut_chain`) —
/// under the surface channel the exporter will print it with. This is the
/// publication wire-gap screen's question; the printer asks the same
/// predicates in `AlethePrinter::format_lia_lattice`.
#[must_use]
pub fn lia_lattice_lowering_supported(
    terms: &TermStore,
    step: &ProofStep,
    overrides: Option<&HashMap<TermId, String>>,
) -> bool {
    let ProofStep::TheoryLemma {
        clause, kind, lia, ..
    } = step
    else {
        return false;
    };
    crate::lia_divisibility_lowering_supported(terms, clause, lia.as_ref(), overrides)
        || lia_equality_lattice_lowering_supported(terms, clause, kind, overrides)
        || cut_chain::lia_cut_chain_lowering_supported(terms, clause, kind, overrides)
        || singleton::lowering_supported(terms, clause, kind, overrides)
}

/// Whether one theory lemma has this module's checked lowering, under exactly
/// the surface channel the exporter will print it with, through the same plan
/// the printer renders.
#[must_use]
pub(crate) fn lia_equality_lattice_lowering_supported(
    terms: &TermStore,
    clause: &[TermId],
    kind: &ay_core::TheoryLemmaKind,
    overrides: Option<&HashMap<TermId, String>>,
) -> bool {
    if !matches!(kind, ay_core::TheoryLemmaKind::IntGuardedSplitGap) {
        return false;
    }
    let printer = AlethePrinter::new_with_overrides_and_budget(terms, overrides, Some(MAX_WORK))
        .with_assembled_rendering(AssembledRendering::CachedWithinBudget);
    printer.equality_lattice_plan(clause).is_some() && !printer.work_budget_exhausted()
}

impl AlethePrinter<'_> {
    /// The checked integer-lattice lowerings of one theory lemma. `Ok(None)`
    /// keeps the honest `hole` the caller falls back to.
    pub(super) fn format_lia_lattice(
        &self,
        id: ProofId,
        clause: &[TermId],
        kind: &ay_core::TheoryLemmaKind,
        lia: Option<&ay_core::LiaAnnotation>,
        wire_overrides: Option<&HashMap<TermId, String>>,
    ) -> Result<Option<String>, AlethePrintError> {
        // The pinned checker treats bare `lia_generic` as a hole, but its
        // checked `la_generic` rule can certify the exact integer lattice
        // split behind a unit Divisibility theorem. Emit that derivation only
        // when the shared publication predicate replays the native witness
        // against an identity surface.
        if crate::lia_divisibility_lowering_supported(self.terms, clause, lia, wire_overrides) {
            return self
                .format_lia_divisibility(id, clause)
                .map(Some)
                .ok_or_else(|| AlethePrintError::InvalidSurfaceStep {
                    id,
                    reason: "validated divisibility lowering lost its lattice witness".to_string(),
                });
        }
        // Its multi-equality form: an `IntGuardedSplitGap` whose literals are
        // all negated integer equalities, lowered through the integer
        // combination the strict checker's own elimination finds; and an
        // `IntCgCutChain`, lowered cut by cut (`cut_chain`).
        Ok(self
            .format_lia_equality_lattice(id, clause, kind)
            .or_else(|| self.format_lia_cut_chain(id, clause, kind))
            .or_else(|| singleton::render(self, id, clause, kind)))
    }

    /// The checked derivation of an all-equality `IntGuardedSplitGap` lemma,
    /// or `None` to keep the honest `hole`. See the module docs.
    pub(super) fn format_lia_equality_lattice(
        &self,
        id: ProofId,
        clause: &[TermId],
        kind: &ay_core::TheoryLemmaKind,
    ) -> Option<String> {
        if !matches!(kind, ay_core::TheoryLemmaKind::IntGuardedSplitGap) {
            return None;
        }
        let plan = self.equality_lattice_plan(clause)?;
        (!self.work_budget_exhausted()).then(|| plan.render(id))
    }

    fn equality_lattice_plan(&self, clause: &[TermId]) -> Option<EqualityLatticePlan> {
        let witness = ay_core::proof_validation::lia_equality_lattice_witness(self.terms, clause)?;
        // The literals exactly as the step's own clause prints them.
        let printed_clause = self.format_clause(clause);
        let literals = split_application(&printed_clause, "cl")?;
        if literals.len() != clause.len() {
            return None;
        }
        let mut rows = Vec::with_capacity(literals.len());
        for (literal, (form, constant)) in literals.into_iter().zip(&witness.rows) {
            let [equality] = split_application(&literal, "not")?.try_into().ok()?;
            let [left, right] = split_application(&equality, "=")?.try_into().ok()?;
            if !self.printed_row_is_internal_row(form, constant, &left, &right) {
                return None;
            }
            rows.push(PrintedEquality {
                literal,
                left,
                right,
            });
        }
        Some(EqualityLatticePlan {
            rows,
            multipliers: witness.multipliers,
            gap: witness.gap,
        })
    }

    /// Whether `left − right`, read as `la_generic` reads it, is the internal
    /// row `form + constant` with each internal atom keyed by its rendering.
    fn printed_row_is_internal_row(
        &self,
        form: &std::collections::BTreeMap<TermId, BigInt>,
        constant: &BigInt,
        left: &str,
        right: &str,
    ) -> bool {
        let mut expected = std::collections::BTreeMap::new();
        for (&atom, coeff) in form {
            let Some(key) = printed_atom_key(&self.format_term(atom)) else {
                return false;
            };
            // Two internal atoms one checker atom: the printed row is a
            // different (merged) row, and integrality of `D` would rest on it.
            if expected
                .insert(key, BigRational::from_integer(coeff.clone()))
                .is_some()
            {
                return false;
            }
        }
        printed_linear_difference(left, right).is_some_and(|(atoms, printed_constant)| {
            atoms == expected && printed_constant == BigRational::from_integer(constant.clone())
        })
    }
}

impl EqualityLatticePlan {
    fn render(&self, id: ProofId) -> String {
        let literals = self
            .rows
            .iter()
            .map(|row| row.literal.as_str())
            .collect::<Vec<_>>()
            .join(" ");
        let multipliers = coefficient_list(&self.multipliers, false);
        let Some((lower, upper)) = &self.gap else {
            return format!("(step {id} (cl {literals}) :rule la_generic :args ({multipliers}))");
        };
        let negated = coefficient_list(&self.multipliers, true);
        let combination = self.combination();
        let low = format!("(<= {combination} {})", format_integer(lower));
        let high = format!("(<= {} {combination})", format_integer(upper));
        format!(
            "(step {id}.split (cl {low} {high}) :rule la_generic :args (1 1))\n\
             (step {id}.lo (cl {literals} (not {low})) :rule la_generic :args ({multipliers} 1))\n\
             (step {id}.hi (cl {literals} (not {high})) :rule la_generic :args ({negated} 1))\n\
             (step {id}.r (cl {literals} {high}) :rule resolution :premises ({id}.split {id}.lo))\n\
             (step {id} (cl {literals}) :rule resolution :premises ({id}.r {id}.hi))"
        )
    }

    /// `D = Σ λ_i·(L_i − R_i)` over the printed operands, each summand
    /// oriented so its printed scale is positive.
    fn combination(&self) -> String {
        let summands: Vec<String> = self
            .rows
            .iter()
            .zip(&self.multipliers)
            .filter(|(_, multiplier)| !multiplier.is_zero())
            .map(|(row, multiplier)| {
                let (left, right) = if multiplier.is_negative() {
                    (&row.right, &row.left)
                } else {
                    (&row.left, &row.right)
                };
                let difference = format!("(- {left} {right})");
                if multiplier.abs().is_one() {
                    difference
                } else {
                    format!("(* {} {difference})", multiplier.abs())
                }
            })
            .collect();
        match summands.as_slice() {
            [single] => single.clone(),
            _ => format!("(+ {})", summands.join(" ")),
        }
    }
}

fn coefficient_list(multipliers: &[BigInt], negate: bool) -> String {
    multipliers
        .iter()
        .map(|multiplier| {
            let value = if negate {
                -multiplier.clone()
            } else {
                multiplier.clone()
            };
            format_integer(&value)
        })
        .collect::<Vec<_>>()
        .join(" ")
}

fn format_integer(value: &BigInt) -> String {
    if value.is_negative() {
        format!("(- {})", value.magnitude())
    } else {
        value.to_string()
    }
}

mod cut_chain;
mod singleton;

#[cfg(test)]
mod tests;
