// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Counterexample construction from proof obligation chains and reach-fact DAGs.

use super::super::{
    ChcExpr, ChcSort, ChcVar, Counterexample, CounterexampleStep, DerivationWitness,
    DerivationWitnessEntry, FxHashMap, FxHashSet, PdrSolver, PredicateId, ProofObligation,
    ReachFactId, ReachFactStore, SmtValue, WitnessBuilder,
};

impl PdrSolver {
    pub(in crate::pdr::solver) fn smt_value_for_var_constant(
        var: &ChcVar,
        value: i128,
    ) -> SmtValue {
        match var.sort {
            ChcSort::BitVec(width) => {
                SmtValue::BitVec(Self::bitvec_bits_from_i64(value, width), width)
            }
            _ => SmtValue::Int(value),
        }
    }

    fn bitvec_bits_from_i64(value: i128, width: u32) -> u128 {
        let mask = if width >= 128 {
            u128::MAX
        } else if width == 0 {
            0
        } else {
            (1u128 << width) - 1
        };
        (value as u128) & mask
    }

    /// Build counterexample from proof obligation chain
    pub(in crate::pdr::solver) fn build_cex(&self, pob: &ProofObligation) -> Counterexample {
        let mut chain: Vec<&ProofObligation> = Vec::new();

        // Walk up the parent chain (leaf -> root)
        let mut current = Some(pob);
        while let Some(p) = current {
            chain.push(p);
            current = p.parent.as_deref();
        }

        // Convert to init -> bad order
        chain.reverse();

        let steps: Vec<CounterexampleStep> = chain
            .iter()
            .map(|p| {
                // Extract integer assignments from SMT model
                let assignments = if let Some(ref model) = p.smt_model {
                    model
                        .iter()
                        .filter_map(|(name, value)| match value {
                            // i128-lockstep: CounterexampleStep assignments are
                            // i64 (public API); skip values outside i64 range
                            // rather than truncating the trace.
                            SmtValue::Int(n) => i64::try_from(*n).ok().map(|v| (name.clone(), v)),
                            SmtValue::Real(r) => {
                                use num_traits::{One, ToPrimitive};
                                if r.denom().is_one() {
                                    r.numer().to_i64().map(|v| (name.clone(), v))
                                } else {
                                    None
                                }
                            }
                            SmtValue::BitVec(n, _) => {
                                i64::try_from(*n).ok().map(|v| (name.clone(), v))
                            }
                            // Beyond-i128 witnesses never fit the i64 public
                            // API; skip (the derivation witness still carries
                            // them via SmtValue's derived Debug).
                            SmtValue::BigInt(_)
                            | SmtValue::Bool(_)
                            | SmtValue::Opaque(_)
                            | SmtValue::ConstArray(_)
                            | SmtValue::ArrayMap { .. }
                            | SmtValue::Datatype(..) => None,
                        })
                        .collect()
                } else {
                    FxHashMap::default()
                };
                let mut step = CounterexampleStep::new(p.predicate, assignments);
                // Annotate step with TLA+ action from transition clause (#8215)
                if let Some(clause_idx) = p.incoming_clause {
                    step.clause_index = Some(clause_idx);
                    if let Some(action) = self.problem.clause_action(clause_idx) {
                        step.action_id = Some(action);
                    }
                }
                step
            })
            .collect();

        // Build witness entries, handling hyperedge clauses (#1503)
        //
        // For hyperedge clauses (multiple body predicates like P(x) ∧ Q(y) → R(x,y)),
        // the POB chain only traces ONE body predicate path. We need to synthesize
        // witness entries for the other body predicates using the SMT model.
        //
        // Strategy:
        // 1. First pass: create entries for the chain with placeholder premises
        // 2. Second pass: for hyperedge entries, create synthetic entries for missing body predicates
        // 3. Third pass: wire up premise indices correctly

        // Map from (predicate, level) to entry index for finding existing entries
        let mut pred_level_to_entry: FxHashMap<(PredicateId, usize), usize> = FxHashMap::default();

        // First pass: create basic entries from chain
        let mut entries: Vec<DerivationWitnessEntry> = chain
            .iter()
            .enumerate()
            .map(|(i, p)| {
                pred_level_to_entry.insert((p.predicate, p.level), i);
                let instances = if let Some(ref model) = p.smt_model {
                    model
                        .iter()
                        .map(|(name, value)| (name.clone(), value.clone()))
                        .collect()
                } else {
                    FxHashMap::default()
                };
                DerivationWitnessEntry {
                    predicate: p.predicate,
                    level: p.level,
                    state: p.state.clone(),
                    incoming_clause: p.incoming_clause,
                    premises: Vec::new(), // Will be filled in later
                    instances,
                }
            })
            .collect();

        // Second pass: for hyperedge clauses, synthesize entries for missing body predicates
        // We iterate in reverse (bad→init) so we can add synthetic entries without index confusion
        let chain_len = chain.len();
        for p in &chain {
            if let Some(clause_idx) = p.incoming_clause {
                if let Some(clause) = self.problem.clauses().get(clause_idx) {
                    let body_preds = &clause.body.predicates;
                    // Hyperedge: multiple body predicates
                    if body_preds.len() > 1 {
                        let prev_level = if p.level > 0 { p.level - 1 } else { 0 };
                        // Check which body predicates are missing entries
                        for (body_pred, body_args) in body_preds {
                            if pred_level_to_entry.contains_key(&(*body_pred, prev_level)) {
                                continue; // Already have an entry for this
                            }
                            // Synthesize entry from SMT model
                            if let (Some(ref model), Some(canon_vars)) =
                                (&p.smt_model, self.canonical_vars(*body_pred))
                            {
                                // Build state from body args evaluated in the model
                                let mut state_conjuncts = Vec::new();
                                for (j, (arg, canon_var)) in
                                    body_args.iter().zip(canon_vars.iter()).enumerate()
                                {
                                    // Try to find value for this argument in model
                                    let value = match arg {
                                        ChcExpr::Var(v) => model.get(&v.name).cloned(),
                                        ChcExpr::Int(n) => Some(SmtValue::Int(*n)),
                                        _ => None,
                                    };
                                    if let Some(SmtValue::Int(n)) = value {
                                        state_conjuncts.push(ChcExpr::eq(
                                            ChcExpr::var(canon_var.clone()),
                                            ChcExpr::Int(n),
                                        ));
                                    } else if let Some(SmtValue::Bool(b)) = value {
                                        state_conjuncts.push(ChcExpr::eq(
                                            ChcExpr::var(canon_var.clone()),
                                            ChcExpr::Bool(b),
                                        ));
                                    }
                                    // Extract instances from model for this body predicate
                                    let _ = j; // suppress warning
                                }
                                let state = if state_conjuncts.is_empty() {
                                    ChcExpr::Bool(true)
                                } else if state_conjuncts.len() == 1 {
                                    state_conjuncts.swap_remove(0)
                                } else {
                                    state_conjuncts
                                        .into_iter()
                                        .reduce(ChcExpr::and)
                                        .unwrap_or(ChcExpr::Bool(true))
                                };

                                // Build instances for the synthetic entry
                                let mut instances: FxHashMap<String, SmtValue> =
                                    FxHashMap::default();
                                for (arg, canon_var) in body_args.iter().zip(canon_vars.iter()) {
                                    if let ChcExpr::Var(v) = arg {
                                        if let Some(val) = model.get(&v.name) {
                                            instances.insert(canon_var.name.clone(), val.clone());
                                        }
                                    }
                                }

                                let new_idx = entries.len();
                                pred_level_to_entry.insert((*body_pred, prev_level), new_idx);
                                entries.push(DerivationWitnessEntry {
                                    predicate: *body_pred,
                                    level: prev_level,
                                    state,
                                    incoming_clause: None, // Unknown derivation for synthetic entry
                                    premises: Vec::new(),
                                    instances,
                                });
                            }
                        }
                    }
                }
            }
        }

        // Third pass: wire up premises
        // Using explicit index because we need mutable access to entries[i] and also
        // reference i + 1 for fallback linking.
        #[allow(clippy::needless_range_loop)]
        for i in 0..entries.len() {
            let entry = &entries[i];
            let is_init = entry.level == 0
                && entry
                    .incoming_clause
                    .and_then(|idx| self.problem.clauses().get(idx))
                    .is_some_and(|c| c.body.predicates.is_empty());

            if is_init {
                // Fact clause: no premises
                continue;
            }

            if let Some(clause_idx) = entry.incoming_clause {
                if let Some(clause) = self.problem.clauses().get(clause_idx) {
                    let prev_level = if entry.level > 0 { entry.level - 1 } else { 0 };
                    let mut premises = Vec::new();
                    for (body_pred, _) in &clause.body.predicates {
                        if let Some(&premise_idx) =
                            pred_level_to_entry.get(&(*body_pred, prev_level))
                        {
                            premises.push(premise_idx);
                        }
                    }
                    // Only set premises if we found all of them
                    if premises.len() == clause.body.predicates.len() {
                        // SAFETY: we're modifying entries[i] which we already read from
                        let entry_mut = &mut entries[i];
                        entry_mut.premises = premises;
                    } else if !clause.body.predicates.is_empty() {
                        // Fallback: point to next entry in chain (original linear behavior)
                        let entry_mut = &mut entries[i];
                        if i + 1 < chain_len {
                            entry_mut.premises = vec![i + 1];
                        }
                    }
                }
            } else {
                // No incoming clause: point to next entry in chain if available
                if i + 1 < chain_len {
                    entries[i].premises = vec![i + 1];
                }
            }
        }

        let witness = DerivationWitness {
            // query_clause is set on the ROOT of the obligation chain (highest level).
            // The chain was built leaf→root, then reversed. After reverse, root is first.
            query_clause: chain.first().and_then(|p| p.query_clause),
            root: 0,
            entries,
        };

        Counterexample {
            steps,
            witness: Some(witness),
            ground_derivation: None,
        }
    }

    /// Build counterexample by traversing a reach_fact justification DAG.
    ///
    /// The returned witness is a compact derivation DAG rooted at `root_rf_id`.
    /// The linear `steps` path follows a single premise edge, preferring edges that decrease level.
    ///
    /// Returns `None` if reach facts referenced in the derivation DAG have been
    /// pruned (e.g., by bounded cache eviction from #2780). Callers should treat
    /// `None` as Unknown rather than panicking.
    pub(in crate::pdr::solver) fn build_cex_from_reach_facts(
        &self,
        root_rf_id: ReachFactId,
        query_clause: Option<usize>,
    ) -> Option<Counterexample> {
        fn add_witness_node(
            store: &ReachFactStore,
            witness_builder: &mut WitnessBuilder,
            rf_to_wit: &mut FxHashMap<ReachFactId, usize>,
            rf_id: ReachFactId,
        ) -> Option<usize> {
            if let Some(&idx) = rf_to_wit.get(&rf_id) {
                return Some(idx);
            }
            let rf = store.get(rf_id)?;
            let idx = witness_builder.node(rf.predicate, rf.level, &rf.state, Some(&rf.instances));
            rf_to_wit.insert(rf_id, idx);
            let mut premise_idxs: Vec<usize> = Vec::with_capacity(rf.premises.len());
            for &p in &rf.premises {
                premise_idxs.push(add_witness_node(store, witness_builder, rf_to_wit, p)?);
            }
            if let Some(incoming_clause) = rf.incoming_clause {
                witness_builder.set_derivation(idx, incoming_clause, premise_idxs);
            }
            Some(idx)
        }

        let mut witness_builder = WitnessBuilder::default();
        let mut rf_to_wit: FxHashMap<ReachFactId, usize> = FxHashMap::default();
        let witness_root = add_witness_node(
            &self.reachability.reach_facts,
            &mut witness_builder,
            &mut rf_to_wit,
            root_rf_id,
        )?;

        // Build a linear trace by following a single premise edge.
        // Prefer premises that strictly decrease the reach_fact level (toward init).
        let mut trace: Vec<ReachFactId> = Vec::new();
        let mut seen: FxHashSet<ReachFactId> = FxHashSet::default();
        let mut current = root_rf_id;
        while seen.insert(current) {
            trace.push(current);
            let Some(rf) = self.reachability.reach_facts.get(current) else {
                break;
            };
            let Some(next) = rf
                .premises
                .iter()
                .copied()
                .filter_map(|p| {
                    self.reachability
                        .reach_facts
                        .get(p)
                        .map(|prf| (p, prf.level))
                })
                .filter(|(_p, lvl)| *lvl < rf.level)
                .min_by_key(|(p, lvl)| (*lvl, p.0))
                .map(|(p, _lvl)| p)
                .or_else(|| rf.premises.iter().copied().min_by_key(|p| p.0))
            else {
                break;
            };
            current = next;
        }
        trace.reverse();

        let steps: Vec<CounterexampleStep> = trace
            .iter()
            .filter_map(|id| self.reachability.reach_facts.get(*id))
            .map(|rf| {
                let assignments = rf
                    .instances
                    .iter()
                    .filter_map(|(name, value)| match value {
                        // i128-lockstep: CounterexampleStep assignments are
                        // i64 (public API); skip values outside i64 range
                        // rather than truncating the trace.
                        SmtValue::Int(n) => i64::try_from(*n).ok().map(|v| (name.clone(), v)),
                        SmtValue::Real(r) => {
                            use num_traits::{One, ToPrimitive};
                            if r.denom().is_one() {
                                r.numer().to_i64().map(|v| (name.clone(), v))
                            } else {
                                None
                            }
                        }
                        SmtValue::BitVec(n, _) => i64::try_from(*n).ok().map(|v| (name.clone(), v)),
                        // Beyond-i128 witnesses never fit the i64 public API;
                        // skip (fail-closed, never truncate).
                        SmtValue::BigInt(_)
                        | SmtValue::Bool(_)
                        | SmtValue::Opaque(_)
                        | SmtValue::ConstArray(_)
                        | SmtValue::ArrayMap { .. }
                        | SmtValue::Datatype(..) => None,
                    })
                    .collect();
                let mut step = CounterexampleStep::new(rf.predicate, assignments);
                // Annotate step with TLA+ action from transition clause (#8215)
                if let Some(clause_idx) = rf.incoming_clause {
                    step.clause_index = Some(clause_idx);
                    if let Some(action) = self.problem.clause_action(clause_idx) {
                        step.action_id = Some(action);
                    }
                }
                step
            })
            .collect();

        Some(Counterexample {
            steps,
            witness: Some(DerivationWitness {
                query_clause,
                root: witness_root,
                entries: witness_builder.entries,
            }),
            ground_derivation: None,
        })
    }
}
