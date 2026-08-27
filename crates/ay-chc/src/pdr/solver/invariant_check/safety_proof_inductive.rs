// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Inductive-subset model building for safety proofs.
//!
//! When the algebraic-only model doesn't block errors, builds a model from
//! algebraic lemmas + individually self-inductive non-algebraic lemmas.
//! Also includes error-guided lemma discovery for multi-predicate problems.

use super::*;

mod outcome;
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
            if query.body.predicates.len() != 1 {
                continue;
            }
            let (qpred_id, qbody_args) = &query.body.predicates[0];
            let qpred = *qpred_id;

            let qcanonical_vars = match self.canonical_vars(qpred) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            let mut qvar_map: FxHashMap<String, ChcVar> = FxHashMap::default();
            for (arg, canon) in qbody_args.iter().zip(qcanonical_vars.iter()) {
                match arg {
                    ChcExpr::Var(v) => {
                        qvar_map.insert(v.name.clone(), canon.clone());
                    }
                    expr => {
                        for v in expr.vars() {
                            qvar_map
                                .entry(v.name.clone())
                                .or_insert_with(|| canon.clone());
                        }
                    }
                }
            }

            let qerror = match &query.body.constraint {
                Some(c) => match Self::to_canonical(c, &qvar_map) {
                    Some(ec) => ec,
                    None => continue,
                },
                None => continue,
            };

            let conjuncts = Self::extract_conjuncts(&qerror);
            for conjunct in &conjuncts {
                let negated = Self::negate_atomic_constraint(conjunct);
                if let Some(candidate) = negated {
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
