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
            ChcSort::BitVec(width) => SmtValue::bitvec_from_bigint(value.into(), width),
            _ => SmtValue::Int(value),
        }
    }

    /// Build counterexample from proof obligation chain
    ///
    /// `pob` is the chain's leaf (it reached an initial state at level 0) and
    /// its parents lead to the root (the bad state). The derivation witness is
    /// laid out ROOT FIRST (`root: 0`, entry `i + 1` is entry `i`'s chain
    /// premise), while `steps` run leaf first, i.e. initial state -> ... -> bad
    /// state as [`Counterexample::steps`] documents. Each step carries the
    /// query model of the clause that derived it (`incoming_clause`). Listing
    /// the steps root first made the exported trace-validity obligation pin the
    /// root's values at time 0 (refuted by `init`) and the certificate trace
    /// read bad -> init.
    pub(in crate::pdr::solver) fn build_cex(&self, pob: &ProofObligation) -> Counterexample {
        let mut chain: Vec<&ProofObligation> = Vec::new();

        // Walk up the parent chain (leaf -> root)
        let mut current = Some(pob);
        while let Some(p) = current {
            chain.push(p);
            current = p.parent.as_deref();
        }

        // Root first, the witness layout; `steps` read it back leaf first.
        chain.reverse();

        let steps: Vec<CounterexampleStep> = chain
            .iter()
            .rev()
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
                            SmtValue::BigBitVec(n, _) => {
                                num_traits::ToPrimitive::to_i64(n.as_ref())
                                    .map(|v| (name.clone(), v))
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

        // Third pass: wire up premises.
        self.wire_witness_premises(&mut entries, chain_len, &pred_level_to_entry);

        let witness = DerivationWitness {
            // query_clause is set on the chain ROOT (highest level), which is first.
            query_clause: chain.first().and_then(|p| p.query_clause),
            root: 0,
            entries,
        };

        Counterexample {
            steps,
            witness: Some(witness),
            compact_derivation: None,
            ground_derivation: None,
        }
    }

    /// Third pass of [`Self::build_cex`]: each entry's `premises`.
    ///
    /// `entries[..chain_len]` is the POB chain, root first: the chain child
    /// `entries[i + 1]` was found as the predecessor of entry `i` through its
    /// `incoming_clause`, so it IS the premise at that clause's body position
    /// with the child's predicate, and it is wired by POSITION. The
    /// `(predicate, level - 1)` lookup is kept for the other body positions of
    /// a hyperedge (the synthesized entries). Reading the traced premise through
    /// the lookup as well assumed every chain node sits exactly one level below
    /// its parent with a unique `(predicate, level)`: a POB push (`use_pob_push`
    /// re-queues a blocked POB at `level + 1`, parent unchanged) breaks both, the
    /// last-writer-wins lookup wired a node to a deeper node with the same key,
    /// the premise/head alignment check (`cex_entries.rs`) rejected the genuine
    /// derivation as spurious, and the search rebuilt the same witness until the
    /// spurious-cex limit returned Unknown. On a push-free chain (levels strictly
    /// decrease) both readings wire the same entries.
    fn wire_witness_premises(
        &self,
        entries: &mut [DerivationWitnessEntry],
        chain_len: usize,
        pred_level_to_entry: &FxHashMap<(PredicateId, usize), usize>,
    ) {
        for i in 0..entries.len() {
            let entry = &entries[i];
            let clause = entry
                .incoming_clause
                .and_then(|idx| self.problem.clauses().get(idx));
            if entry.level == 0 && clause.is_some_and(|c| c.body.predicates.is_empty()) {
                // Fact clause: no premises.
                continue;
            }
            let chain_child = (i + 1 < chain_len).then_some(i + 1);
            let Some(clause) = clause else {
                // No (resolvable) incoming clause: the next chain entry, if any
                // (an unresolvable index keeps no premises, as before).
                if entry.incoming_clause.is_none() {
                    if let Some(c) = chain_child {
                        entries[i].premises = vec![c];
                    }
                }
                continue;
            };
            let prev_level = entry.level.saturating_sub(1);
            let mut child_used = false;
            let mut premises = Vec::with_capacity(clause.body.predicates.len());
            for (body_pred, _) in &clause.body.predicates {
                if !child_used {
                    if let Some(c) = chain_child.filter(|&c| entries[c].predicate == *body_pred) {
                        premises.push(c);
                        child_used = true;
                        continue;
                    }
                }
                if let Some(&premise_idx) = pred_level_to_entry.get(&(*body_pred, prev_level)) {
                    premises.push(premise_idx);
                }
            }
            if premises.len() == clause.body.predicates.len() {
                entries[i].premises = premises;
            } else if !clause.body.predicates.is_empty() {
                // Fallback: the next chain entry (original linear behaviour).
                if let Some(c) = chain_child {
                    entries[i].premises = vec![c];
                }
            }
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
                        SmtValue::BigBitVec(n, _) => {
                            num_traits::ToPrimitive::to_i64(n.as_ref()).map(|v| (name.clone(), v))
                        }
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
            compact_derivation: None,
            ground_derivation: None,
        })
    }
}
