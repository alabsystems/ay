// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked derivations for GUARDED instance clauses
//! (#quantifier-guarded-instances, #guarded-instance-checked-derivation).
//!
//! The guarded lane (`add_guarded_instance_clauses`) asserts
//! `(or (not q) B[t̄])` against the proxy `q` that `purify_quantifier_atoms`
//! minted for an un-entailed universal `Q = (forall x̄ B)`. The clause is a
//! consequence of the ABSTRACTION, and `q` is not authored vocabulary, so the
//! clause itself can never be assumed in a published proof: before this module
//! every refutation resting on one was a disclosed hole (`discharged-trust`),
//! refused under `--rigor strict`.
//!
//! What the authored scope DOES derive is the clause's resolvent on `q`. When
//! the authored `and`-conjunct `C = (or L₁ … Q … Lₙ)` carries `Q` itself as a
//! literal, eliminating `q` between `σ(C) = (or L₁ … q … Lₙ)` and the guarded
//! clause leaves
//!
//! ```text
//! (or L₁ … B[t̄] … Lₙ)
//! ```
//!
//! and that is exactly a [`ConsequencePlan::ClausalInstance`]: `or` clausifies
//! `C`, `forall_inst` concludes `(or (not Q) B[t̄])`, `or` + `resolution` on `Q`
//! substitute the instance for the literal, and `or_neg` closes the clause as
//! a formula. Every one of those steps has a strict validator and prints as a
//! carcara rule, so the guarded instance reaches the document as a checked
//! `forall_inst` step instead of a hole.
//!
//! # What this does not take on the record's word
//!
//! The recorded `(quantifier, binding)` pairs are HINTS, like every other
//! consequence-replay provenance: the source clause must be a derivable
//! authored conjunct, the instance is recomputed from the clause's own literal
//! and the binding, the strict `forall_inst` validator re-derives the exact
//! substitution, and the stitched candidate commits only through the shared
//! strict installation boundary. A wrong or stale record can only cost a
//! declined candidate. The plan only ever ADDS consequences of the authored
//! problem to a probe; it cannot make a satisfiable consequence set unsat.
//!
//! # Coverage
//!
//! Only a universal that is a DIRECT literal of an authored ROOT written as
//! that `or` is planned: the root's source row must itself be an `or` of the
//! same arity with a `forall` at every guarded position. Elaboration folds
//! other connectives into an `or` — `(ite c true Q)` becomes `(or c Q)` — and
//! the printer cannot bridge a binder-bearing root back to such a surface, so
//! a stitched proof over the folded root renders an `assume` the input never
//! states, which the pinned checker rejects (measured: carcara `invalid`
//! where the guarded refutation was `holey` before). Such a refutation, like
//! one whose universal sits under a nested `and` or any other connective,
//! gets no plan and keeps its honest `discharged-trust` disclosure. When one
//! clause carries several guarded universals, the plan is the cross product
//! of their recorded bindings (the full resolution closure over their
//! proxies), bounded by the caller's instance cap and by
//! [`MAX_GUARDED_COMBINATIONS`] combinations visited, planned or declined. A
//! clause whose unguarded literal still carries a quantifier is never walked:
//! every one of its consequences would keep that quantifier.

use super::types::{AndConjunctClosure, ClausalLiteral, ConsequencePlan};
use super::*;

/// Recorded bindings per guarded universal, deduplicated, in record order.
type GuardedBindings = ay_core::kani_compat::DetHashMap<TermId, Vec<Vec<TermId>>>;

/// Binding combinations one planning pass may visit across all clauses,
/// planned or declined. The caller's instance cap bounds only the PLANNED
/// ones, and the planner runs on every consequence-replay entry point: without
/// this bound a clause whose combinations are declined walks, and interns a
/// term for, the whole cross product `Π |bindings|` (measured on the CLI: a
/// four-universal clause beside a quantified sibling with 15 ground terms per
/// function went from `unsat` in 0.09 s to `canceled` at 120 s and 3.4 GB).
const MAX_GUARDED_COMBINATIONS: usize = 1_024;

impl Executor {
    /// Plan one [`ConsequencePlan::ClausalInstance`] per authored clause
    /// carrying a guarded universal literal and per combination of the
    /// recorded bindings of its guarded literals, appending each quantifier-free
    /// consequence to `instances` until `cap` is reached.
    pub(super) fn plan_guarded_clausal_instances(
        &mut self,
        derivable_sources: &AndConjunctClosure,
        instance_plan: &mut ay_core::kani_compat::DetHashMap<TermId, ConsequencePlan>,
        instances: &mut Vec<TermId>,
        cap: usize,
    ) {
        if self.guarded_instance_records.is_empty() {
            return;
        }
        let bindings = self.guarded_bindings();
        let mut visited = 0usize;
        for &source in &derivable_sources.ordered {
            let TermData::App(Symbol::Named(name), literals) = self.ctx.terms.get(source).clone()
            else {
                continue;
            };
            if name != "or" {
                continue;
            }
            let guarded: Vec<(usize, &[Vec<TermId>])> = literals
                .iter()
                .enumerate()
                .filter_map(|(index, literal)| bindings.get(literal).map(|b| (index, &b[..])))
                .collect();
            if guarded.is_empty() {
                continue;
            }
            let positions: Vec<usize> = guarded.iter().map(|&(index, _)| index).collect();
            if !self.guarded_source_is_written_as_this_clause(source, literals.len(), &positions) {
                replay_note(|| format!("guarded clause: {source:?} is not written as this `or`"));
                continue;
            }
            // Every consequence keeps the unguarded literals verbatim, so one
            // that still carries a quantifier declines EVERY combination: skip
            // the clause instead of walking its cross product for nothing.
            if literals.iter().enumerate().any(|(index, &literal)| {
                !positions.contains(&index)
                    && crate::ematching::contains_quantifier(&self.ctx.terms, literal)
            }) {
                replay_note(|| format!("guarded clause: {source:?} keeps a quantified literal"));
                continue;
            }
            // Odometer over the cross product of the guarded literals' bindings;
            // a full wrap of the last slot ends this clause.
            let mut odometer = vec![0usize; guarded.len()];
            loop {
                if instances.len() >= cap || visited >= MAX_GUARDED_COMBINATIONS {
                    return;
                }
                visited += 1;
                let choice: Vec<(usize, &[TermId])> = guarded
                    .iter()
                    .zip(&odometer)
                    .map(|(&(index, choices), &at)| (index, &choices[at][..]))
                    .collect();
                if let Some((consequence, kinds)) = self.guarded_clause_instance(&literals, &choice)
                {
                    if !instance_plan.contains_key(&consequence) {
                        let plan = ConsequencePlan::ClausalInstance {
                            source,
                            literals: kinds,
                        };
                        instance_plan.insert(consequence, plan);
                        instances.push(consequence);
                    }
                }
                let mut slot = 0;
                while slot < odometer.len() {
                    odometer[slot] += 1;
                    if odometer[slot] < guarded[slot].1.len() {
                        break;
                    }
                    odometer[slot] = 0;
                    slot += 1;
                }
                if slot == odometer.len() {
                    break;
                }
            }
        }
    }

    /// The recorded bindings of each guarded universal, each distinct binding
    /// once, in record order.
    fn guarded_bindings(&self) -> GuardedBindings {
        let mut bindings = GuardedBindings::default();
        let mut seen = ay_core::kani_compat::DetHashSet::default();
        for record in &self.guarded_instance_records {
            if seen.insert((record.quantifier, &record.binding[..])) {
                let entry = bindings.entry(record.quantifier).or_default();
                entry.push(record.binding.clone());
            }
        }
        bindings
    }

    /// The clause `literals` with each `(index, binding)` of `choice`
    /// instantiated, and its literal plan; `None` when a chosen literal is not
    /// a `forall`, its exact instance is refused, or the consequence still
    /// carries a quantifier.
    fn guarded_clause_instance(
        &mut self,
        literals: &[TermId],
        choice: &[(usize, &[TermId])],
    ) -> Option<(TermId, Vec<ClausalLiteral>)> {
        let mut kinds = vec![ClausalLiteral::Keep; literals.len()];
        let mut rewritten = literals.to_vec();
        for &(index, binding) in choice {
            let TermData::Forall(binders, body, _) = self.ctx.terms.get(literals[index]).clone()
            else {
                return None;
            };
            rewritten[index] = crate::cegqi::lra_nested::tree::instantiate(
                &mut self.ctx.terms,
                body,
                &binders,
                binding,
            )?;
            kinds[index] = ClausalLiteral::Forall {
                binding: binding.to_vec(),
            };
        }
        // Checked BEFORE the `or` is interned, so a declined combination mints
        // no clause term.
        if rewritten
            .iter()
            .any(|&literal| crate::ematching::contains_quantifier(&self.ctx.terms, literal))
        {
            return None;
        }
        let consequence = self
            .ctx
            .terms
            .mk_app(Symbol::named("or"), rewritten, Sort::Bool);
        Some((consequence, kinds))
    }

    /// Whether every source row of the authored root `source` is written as
    /// an `or` of `arity` literals with a `forall` at each of `positions`, so
    /// the printer can `assume` the root as the input states it. `false` when
    /// the parsed rows are not aligned with the authored roots, or `source` is
    /// not a root.
    ///
    /// A context that keeps no source rows, or whose row for the root is the
    /// native-API placeholder (an API-built query, or a disposable probe over
    /// an isolated window), has no written form to diverge from: its authored
    /// roots ARE the terms the proof assumes, and any document an outer query
    /// renders from such a probe passes that query's own premise gate.
    fn guarded_source_is_written_as_this_clause(
        &self,
        source: TermId,
        arity: usize,
        positions: &[usize],
    ) -> bool {
        use crate::executor::proof_surface_syntax::strip_frontend_annotations;
        use ay_frontend::command::Term as FrontendTerm;
        let parsed = self.ctx.assertions_parsed();
        if parsed.is_empty() && !self.ctx.retains_parsed_assertions() {
            return true;
        }
        let originals = self.proof_original_problem_assertions_slice();
        if parsed.len() != originals.len() {
            return false;
        }
        let mut rows = originals
            .iter()
            .zip(parsed)
            .filter(|(original, _)| **original == source)
            .peekable();
        rows.peek().is_some()
            && rows.all(|(_, row)| match strip_frontend_annotations(row) {
                // The native-API placeholder: the root's exact term IS its
                // whole written form.
                FrontendTerm::Symbol(name) => {
                    name == crate::executor::NATIVE_API_ASSERTION_PLACEHOLDER
                }
                FrontendTerm::App(name, args) => {
                    name == "or"
                        && args.len() == arity
                        && positions.iter().all(|&index| {
                            matches!(
                                args.get(index).map(strip_frontend_annotations),
                                Some(FrontendTerm::Forall(..))
                            )
                        })
                }
                _ => false,
            })
    }
}

#[cfg(test)]
#[path = "guarded_clausal_tests.rs"]
mod tests;
