// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Inductive-subset model building for safety proofs.
//!
//! When the algebraic-only model doesn't block errors, builds a model from
//! algebraic lemmas + individually self-inductive non-algebraic lemmas.
//! Also includes error-guided lemma discovery for multi-predicate problems.

use super::*;

#[cfg(test)]
mod error_guided_tests;
mod outcome;
#[cfg(test)]
mod query_translation_tests;
pub(super) use outcome::InductiveSubsetOutcome;
mod subset_analysis;

impl PdrSolver {
    /// Inductive-subset fast-accept (#5425/#5401).
    ///
    /// When the algebraic-only model doesn't block errors, build a model from
    /// algebraic lemmas + individually self-inductive non-algebraic lemmas. If this
    /// inductive subset still blocks all errors, accept it immediately.
    ///
    /// This handles multi-predicate problems like s_multipl_25 where:
    /// - Sum invariants (algebraic) are discovered for all predicates
    /// - Propagated bounds from inter-predicate transitions are in frame[1]
    ///   but are NOT self-inductive (they hold at entry but not through self-loops)
    /// - The algebraic model alone doesn't block errors
    /// - verify_model_fast times out because non-inductive frame lemmas create
    ///   Unknown SMT results on transition clauses
    ///
    /// The inductive-subset model excludes non-inductive propagated bounds,
    /// keeping only algebraically-verified + self-inductive lemmas.
    ///
    /// For multi-predicate: also requires entry-inductiveness of each non-algebraic
    /// lemma, because self-inductiveness alone doesn't guarantee the lemma holds
    /// at inter-predicate transitions.
    ///
    /// `model` is the full frame model, consumed for the all-inductive path.
    pub(super) fn try_inductive_subset_model(
        &mut self,
        queries: &[HornClause],
        model: InvariantModel,
    ) -> InductiveSubsetOutcome {
        self.evaluate_inductive_subset(queries, model)
    }

    /// A single-body query's predicate, that predicate's canonical variables,
    /// and the query's error region over them, exactly. A variable argument
    /// renames to its position's canonical variable; any other argument (an
    /// expression, or a variable already renamed) is pinned by
    /// `(= canonical argument)`, its variables staying query locals under
    /// their own names (`to_canonical`), as does every other local. So a
    /// caller that makes lemmas of it must check closedness, and one that
    /// conjoins it with another clause must rename that clause apart.
    ///
    /// Renaming an expression argument's variables onto its canonical
    /// variable instead (#2492's shape) describes a different region: under
    /// `P(x + 1)` it reads `x = 4` as `canonical = 4` where the error is
    /// `canonical = 5`, and a Bool `b` in `P((ite b 1 0))` lands on an Int.
    pub(super) fn canonical_query_error(
        &self,
        query: &HornClause,
    ) -> Option<(PredicateId, Vec<ChcVar>, ChcExpr)> {
        let [(qpred, qbody_args)] = query.body.predicates.as_slice() else {
            return None;
        };
        let qcanonical_vars = self.canonical_vars(*qpred)?.to_vec();
        if qbody_args.len() != qcanonical_vars.len() {
            return None;
        }
        let mut qvar_map: FxHashMap<String, ChcVar> = FxHashMap::default();
        let mut pinned = Vec::new();
        for (arg, canon) in qbody_args.iter().zip(qcanonical_vars.iter()) {
            match arg {
                ChcExpr::Var(v) if !qvar_map.contains_key(&v.name) => {
                    qvar_map.insert(v.name.clone(), canon.clone());
                }
                arg => pinned.push((canon, arg)),
            }
        }
        let constraint = query.body.constraint.as_ref().map_or_else(
            || Some(ChcExpr::Bool(true)),
            |c| Self::to_canonical(c, &qvar_map),
        );
        let pins = pinned.into_iter().map(|(canon, arg)| {
            Self::to_canonical(arg, &qvar_map)
                .map(|arg| ChcExpr::eq(ChcExpr::var(canon.clone()), arg))
        });
        let qerror = std::iter::once(constraint)
            .chain(pins)
            .collect::<Option<Vec<_>>>()?;
        Some((*qpred, qcanonical_vars, ChcExpr::and_all(qerror)))
    }

    /// Error-guided lemma discovery (#5425).
    ///
    /// For multi-predicate problems with non-strictly-inductive lemmas,
    /// build a strictly-self-inductive model by extracting error
    /// constraint negation components as candidate lemmas.
    fn try_error_guided_discovery(
        &mut self,
        queries: &[HornClause],
        strictly_inductive_lemmas: &[(PredicateId, ChcExpr)],
    ) -> Option<InvariantModel> {
        let mut error_guided_lemmas = strictly_inductive_lemmas.to_vec();
        let mut found_new = false;

        for query in queries {
            let Some((qpred, qcanonical_vars, qerror)) = self.canonical_query_error(query) else {
                continue;
            };

            let conjuncts = Self::extract_conjuncts(&qerror);
            for conjunct in &conjuncts {
                let negated = Self::negate_atomic_constraint(conjunct);
                if let Some(candidate) = negated {
                    // A conjunct over a query local keeps that local free under
                    // its source name, and a frame lemma has no binder for it:
                    // it is captured by whatever clause the lemma meets, at
                    // that clause's sort (#5805's shape). Only a candidate
                    // closed over the predicate's canonical variables is a
                    // lemma, and it is refused before any check builds a query
                    // around it.
                    if !self.closed_over(&candidate, &qcanonical_vars) {
                        continue;
                    }
                    let blocking = ChcExpr::not(candidate.clone());
                    let strict = self.is_strictly_self_inductive_blocking(&blocking, qpred);
                    if !strict {
                        continue;
                    }
                    let init_valid = !self.predicate_has_facts(qpred)
                        || self.blocks_initial_states(qpred, &blocking);
                    if !init_valid {
                        continue;
                    }
                    let entry = self.is_entry_inductive(&candidate, qpred, 1);
                    if !entry {
                        continue;
                    }
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: error-guided discovery: found strictly self-inductive lemma {} for pred {}",
                            candidate, qpred.index()
                        );
                    }
                    error_guided_lemmas.push((qpred, candidate.clone()));
                    let lemma = Lemma::new(qpred, candidate, 1);
                    self.frames[1].add_lemma(lemma);
                    found_new = true;
                }
            }
        }

        if found_new {
            let guided_model =
                self.build_model_from_algebraic_plus_inductive(1, &error_guided_lemmas);
            let guided_blocks = self.algebraic_model_blocks_all_errors(&guided_model, queries);
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: error-guided model ({} strictly-ind + error-guided) blocks errors: {}",
                    error_guided_lemmas.len(),
                    guided_blocks
                );
            }
            if guided_blocks {
                let mut guided_model = guided_model;
                guided_model.individually_inductive = true;
                return Some(guided_model);
            }
        }

        None
    }
}
