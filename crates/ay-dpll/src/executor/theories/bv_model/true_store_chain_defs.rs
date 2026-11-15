// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The store-chain and const-array definitions the BV/Bool model makes true:
//! top-level equalities, and equalities reached through true Boolean or BV1
//! `ite` arms, true equality sides and model-forced `or` arms.

use super::*;

impl Executor {
    pub(super) fn collect_true_store_chain_defs(
        terms: &TermStore,
        bv_model: &BvModel,
        term: TermId,
        truth: StoreChainTruth,
        depth: usize,
        visited: &mut HashSet<(TermId, StoreChainTruth)>,
        seen_store_defs: &mut HashSet<(TermId, TermId, TermId)>,
        store_defs: &mut Vec<(TermId, TermId, TermId)>,
    ) {
        const MAX_DEPTH: usize = 4096;
        if depth >= MAX_DEPTH || !visited.insert((term, truth)) {
            return;
        }

        match truth {
            StoreChainTruth::BoolTrue => {
                if let Some((var_id, store_term)) =
                    Self::store_chain_definition_from_equality(terms, term)
                {
                    let base = Self::store_chain_base(terms, store_term);
                    if seen_store_defs.insert((var_id, store_term, base)) {
                        store_defs.push((var_id, store_term, base));
                    }
                    return;
                }
                Self::propagate_bool_true_store_chain_defs(
                    terms,
                    bv_model,
                    term,
                    depth,
                    visited,
                    seen_store_defs,
                    store_defs,
                );
            }
            StoreChainTruth::Bv1True => {
                Self::propagate_bv1_true_store_chain_defs(
                    terms,
                    bv_model,
                    term,
                    depth,
                    visited,
                    seen_store_defs,
                    store_defs,
                );
            }
        }
    }

    fn propagate_bool_true_store_chain_defs(
        terms: &TermStore,
        bv_model: &BvModel,
        term: TermId,
        depth: usize,
        visited: &mut HashSet<(TermId, StoreChainTruth)>,
        seen_store_defs: &mut HashSet<(TermId, TermId, TermId)>,
        store_defs: &mut Vec<(TermId, TermId, TermId)>,
    ) {
        match terms.get(term) {
            TermData::Not(_) | TermData::Const(_) | TermData::Var(_, _) => {}
            TermData::Ite(cond, then_term, else_term) if *terms.sort(term) == Sort::Bool => {
                Self::propagate_true_bool_ite(
                    terms,
                    bv_model,
                    *cond,
                    *then_term,
                    *else_term,
                    depth,
                    visited,
                    seen_store_defs,
                    store_defs,
                );
            }
            TermData::Ite(_, _, _) => {}
            TermData::App(sym, args) if *terms.sort(term) == Sort::Bool => match sym.name() {
                "and" => {
                    for &arg in args {
                        Self::collect_true_store_chain_defs(
                            terms,
                            bv_model,
                            arg,
                            StoreChainTruth::BoolTrue,
                            depth + 1,
                            visited,
                            seen_store_defs,
                            store_defs,
                        );
                    }
                }
                "=" if args.len() == 2 => {
                    Self::propagate_true_equality_side(
                        terms,
                        bv_model,
                        args[0],
                        args[1],
                        depth,
                        visited,
                        seen_store_defs,
                        store_defs,
                    );
                    Self::propagate_true_equality_side(
                        terms,
                        bv_model,
                        args[1],
                        args[0],
                        depth,
                        visited,
                        seen_store_defs,
                        store_defs,
                    );
                }
                "ite" if args.len() == 3 => {
                    Self::propagate_true_bool_ite(
                        terms,
                        bv_model,
                        args[0],
                        args[1],
                        args[2],
                        depth,
                        visited,
                        seen_store_defs,
                        store_defs,
                    );
                }
                "or" if !args.is_empty() => {
                    Self::propagate_forced_or_arm(
                        terms,
                        bv_model,
                        args,
                        depth,
                        visited,
                        seen_store_defs,
                        store_defs,
                    );
                }
                _ => {}
            },
            TermData::App(_, _) => {}
            TermData::Let(_, _) | TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {}
            _ => {}
        }
    }

    /// #8512-forced-or: an asserted-true disjunction forces an arm exactly when
    /// every OTHER arm is false under the model — unit propagation. That arm
    /// then holds, so its conjuncts (including a store-chain definition) are
    /// real definitions and may be walked, the same discipline
    /// [`Self::propagate_true_bool_ite`] applies to a model-forced `ite` branch.
    ///
    /// With two or more arms still live the model is free to satisfy either one,
    /// and adopting a definition out of one of them would FABRICATE an array
    /// value. Nothing is collected then: the variables involved keep the
    /// partial interpretation their reads give them, which the gate judges
    /// (see [`Self::array_vars_defined_only_under_nested_equality`]).
    ///
    /// The liveness test never consults an array interpretation — only the BV
    /// assignment — so it cannot depend on the very definitions being decided.
    fn propagate_forced_or_arm(
        terms: &TermStore,
        bv_model: &BvModel,
        args: &[TermId],
        depth: usize,
        visited: &mut HashSet<(TermId, StoreChainTruth)>,
        seen_store_defs: &mut HashSet<(TermId, TermId, TermId)>,
        store_defs: &mut Vec<(TermId, TermId, TermId)>,
    ) {
        let mut memo = BvEvalMemo::default();
        let mut false_cache: HashMap<TermId, bool> = HashMap::default();
        let mut live: Option<TermId> = None;
        let mut live_count = 0usize;
        for &arg in args {
            if Self::model_bool_is_false(terms, bv_model, arg, 0, &mut memo, &mut false_cache) {
                continue;
            }
            live_count += 1;
            if live_count > 1 {
                return;
            }
            live = Some(arg);
        }
        if let Some(arm) = live {
            Self::collect_true_store_chain_defs(
                terms,
                bv_model,
                arm,
                StoreChainTruth::BoolTrue,
                depth + 1,
                visited,
                seen_store_defs,
                store_defs,
            );
        }
    }

    fn propagate_true_bool_ite(
        terms: &TermStore,
        bv_model: &BvModel,
        cond: TermId,
        then_term: TermId,
        else_term: TermId,
        depth: usize,
        visited: &mut HashSet<(TermId, StoreChainTruth)>,
        seen_store_defs: &mut HashSet<(TermId, TermId, TermId)>,
        store_defs: &mut Vec<(TermId, TermId, TermId)>,
    ) {
        match Self::model_bool_value(terms, bv_model, cond) {
            Some(true) => {
                // A model-true condition may BE the definition: ite-lifting
                // puts `(= m (store ...))` in condition position, and taking
                // only the branch would leave `m` read-conflicted.
                Self::collect_true_store_chain_defs(
                    terms,
                    bv_model,
                    cond,
                    StoreChainTruth::BoolTrue,
                    depth + 1,
                    visited,
                    seen_store_defs,
                    store_defs,
                );
                Self::collect_true_store_chain_defs(
                    terms,
                    bv_model,
                    then_term,
                    StoreChainTruth::BoolTrue,
                    depth + 1,
                    visited,
                    seen_store_defs,
                    store_defs,
                );
            }
            Some(false) => Self::collect_true_store_chain_defs(
                terms,
                bv_model,
                else_term,
                StoreChainTruth::BoolTrue,
                depth + 1,
                visited,
                seen_store_defs,
                store_defs,
            ),
            None => match (
                Self::model_bool_value(terms, bv_model, then_term),
                Self::model_bool_value(terms, bv_model, else_term),
            ) {
                (Some(true), Some(false)) => Self::collect_true_store_chain_defs(
                    terms,
                    bv_model,
                    cond,
                    StoreChainTruth::BoolTrue,
                    depth + 1,
                    visited,
                    seen_store_defs,
                    store_defs,
                ),
                (Some(false), Some(true)) => Self::collect_true_store_chain_defs(
                    terms,
                    bv_model,
                    else_term,
                    StoreChainTruth::BoolTrue,
                    depth + 1,
                    visited,
                    seen_store_defs,
                    store_defs,
                ),
                _ => {}
            },
        }
    }

    fn propagate_true_equality_side(
        terms: &TermStore,
        bv_model: &BvModel,
        known_side: TermId,
        implied_side: TermId,
        depth: usize,
        visited: &mut HashSet<(TermId, StoreChainTruth)>,
        seen_store_defs: &mut HashSet<(TermId, TermId, TermId)>,
        store_defs: &mut Vec<(TermId, TermId, TermId)>,
    ) {
        if *terms.sort(known_side) != *terms.sort(implied_side) {
            return;
        }
        match terms.sort(known_side) {
            Sort::Bool if Self::model_bool_value(terms, bv_model, known_side) == Some(true) => {
                Self::collect_true_store_chain_defs(
                    terms,
                    bv_model,
                    implied_side,
                    StoreChainTruth::BoolTrue,
                    depth + 1,
                    visited,
                    seen_store_defs,
                    store_defs,
                );
            }
            Sort::BitVec(bv)
                if bv.width == 1
                    && Self::model_bv1_value(terms, bv_model, known_side) == Some(true) =>
            {
                Self::collect_true_store_chain_defs(
                    terms,
                    bv_model,
                    implied_side,
                    StoreChainTruth::Bv1True,
                    depth + 1,
                    visited,
                    seen_store_defs,
                    store_defs,
                );
            }
            _ => {}
        }
    }

    fn propagate_bv1_true_store_chain_defs(
        terms: &TermStore,
        bv_model: &BvModel,
        term: TermId,
        depth: usize,
        visited: &mut HashSet<(TermId, StoreChainTruth)>,
        seen_store_defs: &mut HashSet<(TermId, TermId, TermId)>,
        store_defs: &mut Vec<(TermId, TermId, TermId)>,
    ) {
        if !matches!(terms.sort(term), Sort::BitVec(bv) if bv.width == 1) {
            return;
        }

        match terms.get(term) {
            TermData::Ite(cond, then_term, else_term) => {
                Self::propagate_true_bv1_ite(
                    terms,
                    bv_model,
                    *cond,
                    *then_term,
                    *else_term,
                    depth,
                    visited,
                    seen_store_defs,
                    store_defs,
                );
            }
            TermData::App(sym, args) => match sym.name() {
                "bvand" => {
                    for &arg in args {
                        Self::collect_true_store_chain_defs(
                            terms,
                            bv_model,
                            arg,
                            StoreChainTruth::Bv1True,
                            depth + 1,
                            visited,
                            seen_store_defs,
                            store_defs,
                        );
                    }
                }
                "ite" if args.len() == 3 => {
                    Self::propagate_true_bv1_ite(
                        terms,
                        bv_model,
                        args[0],
                        args[1],
                        args[2],
                        depth,
                        visited,
                        seen_store_defs,
                        store_defs,
                    );
                }
                _ => {}
            },
            _ => {}
        }
    }

    fn propagate_true_bv1_ite(
        terms: &TermStore,
        bv_model: &BvModel,
        cond: TermId,
        then_term: TermId,
        else_term: TermId,
        depth: usize,
        visited: &mut HashSet<(TermId, StoreChainTruth)>,
        seen_store_defs: &mut HashSet<(TermId, TermId, TermId)>,
        store_defs: &mut Vec<(TermId, TermId, TermId)>,
    ) {
        match (
            Self::model_bv1_value(terms, bv_model, then_term),
            Self::model_bv1_value(terms, bv_model, else_term),
        ) {
            (Some(true), Some(false)) => {
                Self::collect_true_store_chain_defs(
                    terms,
                    bv_model,
                    cond,
                    StoreChainTruth::BoolTrue,
                    depth + 1,
                    visited,
                    seen_store_defs,
                    store_defs,
                );
            }
            _ => match Self::model_bool_value(terms, bv_model, cond) {
                Some(true) => {
                    // As in `propagate_true_bool_ite`: a condition the
                    // model makes true may itself carry the definition.
                    Self::collect_true_store_chain_defs(
                        terms,
                        bv_model,
                        cond,
                        StoreChainTruth::BoolTrue,
                        depth + 1,
                        visited,
                        seen_store_defs,
                        store_defs,
                    );
                    Self::collect_true_store_chain_defs(
                        terms,
                        bv_model,
                        then_term,
                        StoreChainTruth::Bv1True,
                        depth + 1,
                        visited,
                        seen_store_defs,
                        store_defs,
                    );
                }
                Some(false) => Self::collect_true_store_chain_defs(
                    terms,
                    bv_model,
                    else_term,
                    StoreChainTruth::Bv1True,
                    depth + 1,
                    visited,
                    seen_store_defs,
                    store_defs,
                ),
                None => {}
            },
        }
    }
}

#[cfg(test)]
#[path = "true_store_chain_defs_tests.rs"]
mod tests;
