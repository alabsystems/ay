// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sort-unique variable naming for the text-driven ay-dpll executor lanes
//! (Rung 0 of the CHC-COMP 2026 bridge-hygiene work,
//! the development design notes).
//!
//! A [`ChcVar`] is identified by `(name, sort)`. CHC clauses independently
//! scope their `forall` variables and reuse short names (`A`, `B`, ..., `J`)
//! with DIFFERENT sorts, and clause inlining / transition-relation construction
//! routinely puts `J:Int` and `J:Bool` into ONE query. The internal DPLL(T)
//! lane keys its term map by `name_sort`, so it already treats them as
//! distinct; the SMT-LIB text emitters did not: they declared
//! `(declare-const J Int)` AND `(declare-const J Bool)` and ay-dpll's frontend
//! rejected the whole script (`unsupported: ambiguous nullary symbol 'J'`) ->
//! Unknown. Measured on DRAGON_10_000 (kind2): 78–89 % of the executor
//! Unknowns were this rejection, all decided in ~25 ms once disambiguated
//! (`MICROBENCH_QUERY_REPLAY_2026-09-18.md` §4 item ii).
//!
//! Fix at the name->sort mapping: within one script every name carries ONE
//! sort. Among the variables sharing a name, the one with the smallest sort
//! rank (Bool < Int < Real < BitVec < Array < Datatype < Uninterpreted, then
//! `ChcSort`'s derived order) keeps the plain name; every other one is emitted
//! as `name!<sort-tag>` (`J!Int`) consistently in the declarations AND in the
//! formula body (via [`ChcExpr::substitute`], which matches on the full
//! `(name, sort)` identity). `!` is a legal SMT-LIB simple-symbol character, so
//! the qualified name round-trips through `get-model` unchanged.
//!
//! Model mapping back: a model is keyed by NAME (`FxHashMap<String, SmtValue>`,
//! consumed via `model.get(&v.name)` at ~230 sites), so it can hold only one
//! value under `J`. The plain entry belongs to the rank winner and the other
//! sorts live under their qualified name; [`crate::expr::lookup_model_value`]
//! (used by the strict model evaluator and the missing-variable census)
//! consults the qualified entry whenever the plain entry has the wrong sort.
//! The internal lane's model extraction emits the same key layout, so strict
//! SAT validation against the ORIGINAL expression is exact on both lanes.
//!
//! Persistent (push/pop) sessions declare a name once per session: there the
//! reserved-sort rule applies — a name already declared with another sort is
//! the winner and the new sort is qualified ([`SortUniqueRenaming::plan_with_reserved`]).

use crate::{ChcExpr, ChcSort, ChcVar};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

/// Rank used to pick which sort keeps the plain name (lower wins).
pub(crate) fn sort_rank(sort: &ChcSort) -> u8 {
    match sort {
        ChcSort::Bool => 0,
        ChcSort::Int => 1,
        ChcSort::Real => 2,
        ChcSort::BitVec(_) => 3,
        ChcSort::Array(..) => 4,
        ChcSort::Datatype { .. } => 5,
        ChcSort::Uninterpreted(_) => 6,
    }
}

/// For every NAME that occurs with more than one sort in a query, the sort that
/// owns the PLAIN model key (rank rule); the other sorts are keyed `name!<tag>`.
/// Used wherever a model entry is produced from a bare name (the internal
/// lane's var=const propagation), so it lands under the same key layout the
/// theory-model extraction and the executor scripts use.
#[derive(Debug, Default)]
pub(crate) struct PlainKeyOwners(FxHashMap<String, ChcSort>);

impl PlainKeyOwners {
    pub(crate) fn from_vars(vars: &[ChcVar]) -> Self {
        let mut sorts: FxHashMap<&str, Vec<&ChcSort>> = FxHashMap::default();
        for v in vars {
            let entry = sorts.entry(v.name.as_str()).or_default();
            if !entry.contains(&&v.sort) {
                entry.push(&v.sort);
            }
        }
        Self(
            sorts
                .into_iter()
                .filter(|(_, sorts)| sorts.len() > 1)
                .filter_map(|(name, sorts)| {
                    sorts
                        .into_iter()
                        .min_by_key(|s| (sort_rank(s), (*s).clone()))
                        .map(|winner| (name.to_owned(), winner.clone()))
                })
                .collect(),
        )
    }

    /// The model key for `(name, sort)`: the plain name unless another sort
    /// owns it, in which case `name!<tag>`.
    pub(crate) fn key(&self, name: &str, sort: &ChcSort) -> String {
        match self.0.get(name) {
            Some(owner) if owner != sort => ChcVar::new(name, sort.clone()).sort_qualified_name(),
            _ => name.to_owned(),
        }
    }
}

/// The renaming a script must apply so that every variable NAME carries one sort.
#[derive(Debug, Clone, Default)]
pub(crate) struct SortUniqueRenaming {
    /// `(original, renamed)` for every variable that does NOT keep its plain name.
    pairs: Vec<(ChcVar, ChcVar)>,
}

impl SortUniqueRenaming {
    /// Plan for a self-contained script: among the variables sharing a name the
    /// smallest-ranked sort keeps the plain name. `None` when every name is
    /// already sort-unique (the common case).
    pub(crate) fn plan(vars: &[ChcVar]) -> Option<Self> {
        Self::plan_with_reserved(vars, |_| None)
    }

    /// Plan for a persistent session: `reserved(name)` returns the sort a name
    /// is already declared with in the session; that sort keeps the plain name
    /// regardless of rank, so declarations stay consistent across queries.
    pub(crate) fn plan_with_reserved(
        vars: &[ChcVar],
        reserved: impl Fn(&str) -> Option<ChcSort>,
    ) -> Option<Self> {
        // name -> the sort that keeps the plain name.
        let mut winner: FxHashMap<&str, ChcSort> = FxHashMap::default();
        let mut clash = false;
        for v in vars {
            match winner.get_mut(v.name.as_str()) {
                None => {
                    let w = reserved(&v.name).unwrap_or_else(|| v.sort.clone());
                    if w != v.sort {
                        clash = true;
                    }
                    winner.insert(v.name.as_str(), w);
                }
                Some(w) => {
                    if *w != v.sort {
                        clash = true;
                        // A reserved winner is fixed; otherwise the smaller rank wins.
                        if reserved(&v.name).is_none()
                            && (sort_rank(&v.sort), &v.sort) < (sort_rank(w), &*w)
                        {
                            *w = v.sort.clone();
                        }
                    }
                }
            }
        }
        if !clash {
            return None;
        }
        let names: FxHashSet<&str> = vars.iter().map(|v| v.name.as_str()).collect();
        let mut pairs: Vec<(ChcVar, ChcVar)> = Vec::new();
        let mut seen: FxHashSet<&ChcVar> = FxHashSet::default();
        for v in vars {
            if !seen.insert(v) {
                continue;
            }
            let Some(w) = winner.get(v.name.as_str()) else {
                continue;
            };
            if *w == v.sort {
                continue;
            }
            let base = v.sort_qualified_name();
            let mut candidate = base.clone();
            // Never collide with a real variable name or an earlier qualified one.
            let mut k = 1u32;
            while names.contains(candidate.as_str())
                || pairs.iter().any(|(_, r)| r.name == candidate)
            {
                candidate = format!("{base}!{k}");
                k += 1;
            }
            pairs.push((v.clone(), ChcVar::new(candidate, v.sort.clone())));
        }
        if pairs.is_empty() {
            None
        } else {
            Some(Self { pairs })
        }
    }

    /// Apply the renaming to an expression (only the qualified variables change).
    pub(crate) fn apply(&self, expr: &ChcExpr) -> ChcExpr {
        let subst: Vec<(ChcVar, ChcExpr)> = self
            .pairs
            .iter()
            .map(|(original, renamed)| (original.clone(), ChcExpr::var(renamed.clone())))
            .collect();
        expr.substitute(&subst)
    }

    /// The declaration list: `vars` with every qualified variable replaced.
    pub(crate) fn renamed_vars(&self, vars: &[ChcVar]) -> Vec<ChcVar> {
        vars.iter()
            .map(|v| {
                self.pairs
                    .iter()
                    .find(|(original, _)| original == v)
                    .map_or_else(|| v.clone(), |(_, renamed)| renamed.clone())
            })
            .collect()
    }

    /// Number of variables that carry a qualified name.
    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.pairs.len()
    }
}
