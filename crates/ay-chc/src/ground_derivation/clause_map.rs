// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ground back-translation for transforms whose clauses map 1:1.
//!
//! Most preprocessing passes rewrite clauses in place: they drop unreachable
//! clauses, pin constants, forward stores, concretize table reads, project
//! locals away, slice dead argument positions, or merge parallel edges. In all
//! of those the DERIVATION SHAPE is unchanged — one output step is one input
//! step with the same premise structure — and the only things that differ are
//! the clause index and which variables exist.
//!
//! [`ClauseMapGroundTranslator`] handles that entire family with one piece of
//! data: for each output clause, the candidate input clauses it came from.
//! Steps are re-indexed, environments are completed by ground propagation
//! against the input clause (see [`super::complete`]), and the result is
//! validated against the input problem before being returned. Passes whose
//! mapping is ambiguous (a merged multi-edge with several origins) supply all
//! candidates; the translator picks the one that actually ground-validates,
//! which is a decision, not a guess.

use super::complete::complete_env_for_clause;
use super::{
    log_ground_translation_detail, validate_ground_derivation, GroundDerivation,
    GroundDerivationStep,
};
use crate::clause::HornClause;
use crate::smt::SmtValue;
use crate::ChcProblem;
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::sync::Arc;

/// Optional pass-specific pre-seeding of a step's environment.
///
/// Ground unit propagation recovers most erased values from the input clause's
/// own equalities, but some passes destroyed the syntactic link entirely — a
/// datatype flattener replaces `v` by a family of scalar columns, and no
/// equality in the original clause relates them. Such a pass supplies a seeder
/// that rebuilds those values from its own layout before propagation runs.
///
/// A seeder is a HINT: whatever it writes is checked by the validator like any
/// other binding.
pub(crate) type EnvSeeder = dyn Fn(&HornClause, &FxHashMap<String, SmtValue>, &mut FxHashMap<String, SmtValue>)
    + Send
    + Sync;

/// Ground back-translator for a 1:1 (or 1:candidate-set) clause correspondence.
pub(crate) struct ClauseMapGroundTranslator {
    /// The problem this translator maps derivations BACK to.
    input_problem: Arc<ChcProblem>,
    /// For each clause index of the OUTPUT problem, the input clause indices it
    /// may correspond to. An empty candidate list means the output clause has
    /// no input counterpart, which fails the translation closed.
    candidates: Vec<Vec<usize>>,
    /// Name used in diagnostics.
    name: &'static str,
    /// Optional pass-specific environment pre-seeder.
    seeder: Option<Box<EnvSeeder>>,
}

impl ClauseMapGroundTranslator {
    /// Build a translator from a per-output-clause candidate table.
    pub(crate) fn new(
        name: &'static str,
        input_problem: Arc<ChcProblem>,
        candidates: Vec<Vec<usize>>,
    ) -> Self {
        Self {
            input_problem,
            candidates,
            name,
            seeder: None,
        }
    }

    /// Attach a pass-specific environment pre-seeder (see [`EnvSeeder`]).
    pub(crate) fn with_seeder(mut self, seeder: Box<EnvSeeder>) -> Self {
        self.seeder = Some(seeder);
        self
    }

    /// Build a translator from an exact output→input index map.
    pub(crate) fn from_index_map(
        name: &'static str,
        input_problem: Arc<ChcProblem>,
        output_to_input: &[usize],
    ) -> Self {
        Self::new(
            name,
            input_problem,
            output_to_input.iter().map(|index| vec![*index]).collect(),
        )
    }

    /// Map `derivation` (over the output problem) to a derivation over the
    /// input problem, or `None` if any step cannot be mapped and validated.
    pub(crate) fn translate(&self, derivation: &GroundDerivation) -> Option<GroundDerivation> {
        let clauses = self.input_problem.clauses();
        let mut steps: Vec<GroundDerivationStep> = Vec::with_capacity(derivation.steps.len());

        for (index, step) in derivation.steps.iter().enumerate() {
            let candidates = self
                .candidates
                .get(step.clause_index)
                .map_or(&[][..], |c| c);
            if candidates.is_empty() {
                log_ground_translation_detail(format_args!(
                    "{}: output clause {} has no input counterpart (step {index})",
                    self.name, step.clause_index
                ));
                return None;
            }
            // Prefer a candidate whose body-predicate arity matches the step's
            // premise count; among those, the first whose environment completes.
            let mut chosen = None;
            for &candidate in candidates {
                let Some(clause) = clauses.get(candidate) else {
                    continue;
                };
                if clause.body.predicates.len() != step.premises.len() {
                    continue;
                }
                if clause.is_query() != (index == derivation.query_step) {
                    continue;
                }
                let mut env = step.env.clone();
                if let Some(seeder) = &self.seeder {
                    seeder(clause, &step.env, &mut env);
                }
                // Argument passing is what makes a derivation a derivation, so
                // make it hold BY CONSTRUCTION rather than by luck: a body
                // predicate argument that is a bare variable takes the value
                // its premise actually derived. Without this, two steps can
                // reconstruct the same logical value differently (one from a
                // recovered column, one from a sort default) and the derivation
                // is rejected for a disagreement that is an artifact of
                // reconstruction rather than a real gap. Steps are processed in
                // topological order, so every premise is already final.
                seed_from_premises(clauses, clause, &step.premises, &steps, &mut env);
                if !complete_env_for_clause(clause, &mut env) {
                    continue;
                }
                chosen = Some(GroundDerivationStep {
                    clause_index: candidate,
                    env,
                    premises: step.premises.clone(),
                });
                break;
            }
            let Some(chosen) = chosen else {
                log_ground_translation_detail(format_args!(
                    "{}: no input clause among {:?} completes for output clause {} (step {index})",
                    self.name, candidates, step.clause_index
                ));
                return None;
            };
            steps.push(chosen);
        }

        let translated = GroundDerivation {
            steps,
            query_step: derivation.query_step,
        };
        // Self-check against the input problem. This is what makes an ambiguous
        // candidate table safe and a stale map harmless: a mapping that does not
        // actually reproduce the derivation is rejected here, not passed on.
        if let Err(err) = validate_ground_derivation(&self.input_problem, &translated) {
            log_ground_translation_detail(format_args!(
                "{}: translated derivation does not validate on the input problem ({err})",
                self.name
            ));
            return None;
        }
        Some(translated)
    }
}

/// Bind a clause's body-predicate argument variables to the values its premises
/// derived.
///
/// Only bare-variable argument positions can be bound this way; a compound
/// argument expression is left to ground evaluation, which the validator then
/// checks against the premise value as usual.
fn seed_from_premises(
    clauses: &[HornClause],
    clause: &HornClause,
    premises: &[usize],
    steps: &[GroundDerivationStep],
    env: &mut FxHashMap<String, SmtValue>,
) {
    for (position, (_, args)) in clause.body.predicates.iter().enumerate() {
        let Some(premise) = premises.get(position).and_then(|index| steps.get(*index)) else {
            continue;
        };
        let Some(premise_clause) = clauses.get(premise.clause_index) else {
            continue;
        };
        let crate::clause::ClauseHead::Predicate(_, head_args) = &premise_clause.head else {
            continue;
        };
        if head_args.len() != args.len() {
            continue;
        }
        for (arg, head_arg) in args.iter().zip(head_args.iter()) {
            let crate::ChcExpr::Var(var) = arg else {
                continue;
            };
            if let Some(value) = super::eval_ground_pub(head_arg, &premise.env) {
                env.insert(var.name.clone(), value);
            }
        }
    }
}
