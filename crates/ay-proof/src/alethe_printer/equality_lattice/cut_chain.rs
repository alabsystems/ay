// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked lowering of a Chvátal–Gomory cut-chain lemma.
//!
//! An `IntCgCutChain` lemma is certified by AY's strict checker through
//! [`ay_core::proof_validation::recognize_int_cg_cut_chain`]: the rows its
//! literals' negations assert are refuted by a chain of cuts `G_k ≥ c_k`, each
//! a non-negative combination of the rows and earlier cuts rounded up over the
//! integers, and a final combination `0 ≥ β > 0`. Pinned carcara checks each
//! of those steps with `la_generic`, whose integer strengthening of a negated
//! literal IS the rounding: the negation of the cut literal `(>= G_k c_k)` is
//! `G_k < c_k`, which it strengthens to `−G_k ≥ 1 − c_k` (`G_k` has coprime
//! integer coefficients, so the gcd it adds is 1). With `s` clearing the
//! denominators of cut `k`'s multipliers `(r, t)`:
//!
//! ```text
//! c1:  (cl L_1 … L_n (>= G_1 c_1))                         la_generic (s·r … s)
//! ck:  (cl L_1 … L_n (not C_1) … (not C_{k−1}) C_k)        la_generic (s·r … s·t … s)
//! f:   (cl L_1 … L_n (not C_1) … (not C_K))                la_generic (final)
//! then K resolutions, one cut literal each, down to (cl L_1 … L_n)
//! ```
//!
//! Cut `k`'s step sums to `0 ≥ s·(β_k + 1 − c_k) > 0` because `c_k ≤ ⌈β_k⌉`.
//!
//! What makes it safe to publish, beyond the strict checker's own replay:
//!
//! * the lowering renders only an `IntCgCutChain` step, and the witness
//!   exists only for a clause the checker's recognizer accepts;
//! * the row the pinned checker reads off every PRINTED literal must equal
//!   the literal's internal row atom for atom (a strict literal reads as its
//!   non-strict row moved by one), each internal atom keyed by its own
//!   rendering and no two atoms sharing a key — carcara's strengthening does
//!   not check sorts, so this is where integrality is enforced;
//! * a cut literal never coincides with a clause literal or another cut, so
//!   every resolution pivot is the cut it names;
//! * every emitted `la_generic` is replayed over its bytes by the printer's
//!   `judge_printed_la_generic` chokepoint, which holes the step on refusal,
//!   and the publication screen ([`lia_cut_chain_lowering_supported`])
//!   replays the same rendering, so it admits only a plan the printer ships.

use super::super::la_generic_surface::readings::{
    printed_atom_key, printed_hypothesis_row, PrintedRelation,
};
use super::super::la_generic_surface::{
    printed_arith_commands, printed_la_generic_holds, PrintedArithCommand,
};
use super::*;

use num_integer::Integer;

/// Render allowance for the publication gate's replay of this lowering.
const MAX_WORK: u64 = 4 * 1024 * 1024;

/// The printed derivation of one lemma, before rendering.
struct CutChainPlan {
    literals: Vec<String>,
    /// Each cut as a positive literal.
    cuts: Vec<String>,
    /// Per cut: integer `la_generic` args over the literals, the earlier cuts
    /// and the cut itself.
    cut_args: Vec<Vec<BigInt>>,
    /// Integer args over the literals and every cut.
    final_args: Vec<BigInt>,
}

/// Whether one theory lemma has this module's checked lowering, under exactly
/// the surface channel the exporter will print it with: the plan exists AND
/// every command it renders passes the same byte-level `la_generic` replay
/// the printer's `judge_printed_la_generic` chokepoint applies, so the screen
/// admits what the printer ships rather than what it would hole.
#[must_use]
pub(crate) fn lia_cut_chain_lowering_supported(
    terms: &TermStore,
    clause: &[TermId],
    kind: &ay_core::TheoryLemmaKind,
    overrides: Option<&HashMap<TermId, String>>,
) -> bool {
    if !matches!(kind, ay_core::TheoryLemmaKind::IntCgCutChain) {
        return false;
    }
    let printer = AlethePrinter::new_with_overrides_and_budget(terms, overrides, Some(MAX_WORK))
        .with_assembled_rendering(AssembledRendering::CachedWithinBudget);
    screen_admits(&printer, printer.cut_chain_plan(clause))
}

/// The screen's verdict on one plan: it exists, the render allowance held,
/// and every command it renders replays.
fn screen_admits(printer: &AlethePrinter<'_>, plan: Option<CutChainPlan>) -> bool {
    plan.is_some_and(|plan| !printer.work_budget_exhausted() && plan.printed_steps_hold())
}

impl AlethePrinter<'_> {
    /// The checked derivation of an `IntCgCutChain` lemma, or `None` to keep
    /// the honest `hole`. See the module docs.
    pub(super) fn format_lia_cut_chain(
        &self,
        id: ProofId,
        clause: &[TermId],
        kind: &ay_core::TheoryLemmaKind,
    ) -> Option<String> {
        if !matches!(kind, ay_core::TheoryLemmaKind::IntCgCutChain) {
            return None;
        }
        let plan = self.cut_chain_plan(clause)?;
        (!self.work_budget_exhausted()).then(|| plan.render(id))
    }

    fn cut_chain_plan(&self, clause: &[TermId]) -> Option<CutChainPlan> {
        let witness = ay_core::proof_validation::lia_cut_chain_witness(self.terms, clause)?;
        let printed_clause = self.format_clause(clause);
        let literals = split_application(&printed_clause, "cl")?;
        if literals.len() != clause.len() {
            return None;
        }
        let mut keys: std::collections::BTreeMap<TermId, String> = Default::default();
        let mut taken = std::collections::BTreeSet::new();
        for atom in witness.rows.iter().flat_map(|row| row.form.keys()) {
            if keys.contains_key(atom) {
                continue;
            }
            let key = printed_atom_key(&self.format_term(*atom))?;
            // Two internal atoms, one checker atom: the printed rows would be
            // different (merged) rows, and the rounding would rest on them.
            if !taken.insert(key.clone()) {
                return None;
            }
            let _ = keys.insert(*atom, key);
        }
        for (literal, row) in literals.iter().zip(&witness.rows) {
            let (relation, atoms, constant) = printed_hypothesis_row(literal)?;
            let expected: std::collections::BTreeMap<String, BigRational> = row
                .form
                .iter()
                .map(|(atom, coeff)| {
                    Some((keys.get(atom)?.clone(), BigRational::from(coeff.clone())))
                })
                .collect::<Option<_>>()?;
            let bound = BigRational::from(row.bound.clone());
            let row_constant = match (row.equality, relation) {
                (true, PrintedRelation::Equal) | (false, PrintedRelation::AtLeast) => bound,
                (false, PrintedRelation::Above) => bound - BigRational::one(),
                _ => return None,
            };
            if atoms != expected || constant != row_constant {
                return None;
            }
        }
        let cuts: Vec<String> = witness
            .cuts
            .iter()
            .map(|cut| self.cut_literal(&cut.form, &cut.bound))
            .collect();
        for (index, cut) in cuts.iter().enumerate() {
            let negated = format!("(not {cut})");
            if literals
                .iter()
                .any(|literal| *literal == *cut || *literal == negated)
                || cuts[..index].contains(cut)
            {
                return None;
            }
        }
        let cut_args = witness
            .cuts
            .iter()
            .map(|cut| {
                let mut multipliers = cut.row_multipliers.clone();
                multipliers.extend(cut.cut_multipliers.iter().cloned());
                multipliers.push(BigRational::one());
                integer_args(&multipliers)
            })
            .collect();
        let mut last = witness.final_row_multipliers.clone();
        last.extend(witness.final_cut_multipliers.iter().cloned());
        Some(CutChainPlan {
            literals,
            cuts,
            cut_args,
            final_args: integer_args(&last),
        })
    }

    /// `(>= G c)`, or `(<= −G −c)` when `G`'s first coefficient is negative,
    /// spelled over each atom's own rendering.
    fn cut_literal(
        &self,
        form: &std::collections::BTreeMap<TermId, BigInt>,
        bound: &BigInt,
    ) -> String {
        let flip = form.values().next().is_some_and(Signed::is_negative);
        let summands: Vec<String> = form
            .iter()
            .map(|(atom, coeff)| {
                let coeff = if flip { -coeff } else { coeff.clone() };
                let atom = self.format_term(*atom);
                if coeff.is_one() {
                    atom
                } else {
                    format!("(* {} {atom})", format_integer(&coeff))
                }
            })
            .collect();
        let sum = match summands.as_slice() {
            [single] => single.clone(),
            _ => format!("(+ {})", summands.join(" ")),
        };
        if flip {
            format!("(<= {sum} {})", format_integer(&-bound))
        } else {
            format!("(>= {sum} {})", format_integer(bound))
        }
    }
}

impl CutChainPlan {
    /// Whether pinned carcara's `la_generic`, replayed over the bytes
    /// [`Self::render`] prints, accepts every arithmetic command of the
    /// rendering; a command the reader cannot read is a refusal.
    fn printed_steps_hold(&self) -> bool {
        let rendered = self.render(ProofId(0));
        printed_arith_commands(&rendered).is_some_and(|commands| {
            !commands.is_empty()
                && commands.iter().all(|command| match command {
                    PrintedArithCommand::LaGeneric(command) => {
                        printed_la_generic_holds(&command.literals, &command.args)
                    }
                    PrintedArithCommand::PolySimp { .. }
                    | PrintedArithCommand::Unreadable { .. } => false,
                })
        })
    }

    fn render(&self, id: ProofId) -> String {
        let literals = self.literals.join(" ");
        let negations: Vec<String> = self.cuts.iter().map(|cut| format!("(not {cut})")).collect();
        let args = |values: &[BigInt]| {
            values
                .iter()
                .map(format_integer)
                .collect::<Vec<_>>()
                .join(" ")
        };
        let prefix = |count: usize| -> String {
            negations[..count]
                .iter()
                .fold(String::new(), |mut out, negation| {
                    out.push(' ');
                    out.push_str(negation);
                    out
                })
        };
        let cut_count = self.cuts.len();
        if cut_count == 0 {
            return format!(
                "(step {id} (cl {literals}) :rule la_generic :args ({}))",
                args(&self.final_args)
            );
        }
        let mut out = Vec::with_capacity(2 * cut_count + 1);
        for (index, (cut, cut_args)) in self.cuts.iter().zip(&self.cut_args).enumerate() {
            out.push(format!(
                "(step {id}.c{} (cl {literals}{} {cut}) :rule la_generic :args ({}))",
                index + 1,
                prefix(index),
                args(cut_args)
            ));
        }
        out.push(format!(
            "(step {id}.f (cl {literals}{}) :rule la_generic :args ({}))",
            prefix(cut_count),
            args(&self.final_args)
        ));
        for k in (1..=cut_count).rev() {
            let previous = if k == cut_count {
                format!("{id}.f")
            } else {
                format!("{id}.r{}", k + 1)
            };
            let name = if k == 1 {
                id.to_string()
            } else {
                format!("{id}.r{k}")
            };
            out.push(format!(
                "(step {name} (cl {literals}{}) :rule resolution :premises ({previous} {id}.c{k}))",
                prefix(k - 1)
            ));
        }
        out.join("\n")
    }
}

/// `multipliers` scaled by the lcm of their denominators.
fn integer_args(multipliers: &[BigRational]) -> Vec<BigInt> {
    let scale = multipliers
        .iter()
        .fold(BigInt::one(), |lcm, value| lcm.lcm(value.denom()));
    multipliers
        .iter()
        .map(|value| (value * BigRational::from(scale.clone())).to_integer())
        .collect()
}

#[cfg(test)]
#[path = "cut_chain_tests.rs"]
mod tests;
