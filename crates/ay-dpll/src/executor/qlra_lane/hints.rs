// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The nested SAT route's expansion HINTS for the quantified model gate
//! (#qlra-nested-cegqi M3b, plan §4.2).
//!
//! After a nested `Sat`, the search's instance log Γ says which instances
//! make the Herbrand expansion of each authored `¬R` refutable under the
//! installed model. This module spells them for the gate's expansion route
//! (`independent_gate/expansion_route.rs`), keyed by the AUTHORED quantifier
//! term opening each binder chain ([`super::hints_origin`] finds it):
//!
//! * a node's frozen tuples become templates over the authored names of the
//!   enclosing binders (counterexample constant → binder name), with every
//!   top-level Skolem replaced by its value in the installed model;
//! * a top-level Skolemized existential (a universal of `¬R`) gets the
//!   model values of its Skolem constants.
//!
//! A tuple whose spelling would be ambiguous (a lane constant with no
//! in-scope name, a free constant shadowed by an enclosing binder) is
//! dropped. Everything here is UNTRUSTED DATA: the gate re-derives the
//! expansion itself and confirms only through a checked ground refutation,
//! so a wrong or missing hint can only cost a confirmation.

use std::cell::Cell;

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{Sort, TermId};
use num_rational::BigRational;
use num_traits::Zero;

use super::super::expansion::qf_formula::binder_chain;
use super::super::expansion::{ExpansionHints, InstanceHints};
use super::super::model::EvalValue;
use super::super::Executor;
use super::hints_origin::{origins, Origins, Scope};
use crate::cegqi::lra_nested::approx::NInstance;
use crate::cegqi::lra_nested::ntree::NestedTree;

/// Tuples installed per query, over every key.
const MAX_HINT_TUPLES: usize = 4096;
/// Tuples per Skolemized chain (one choice of witness per level).
const MAX_SKOLEM_COMBOS: usize = 16;

/// What a nested `Sat` hands the SAT route to build hints from.
pub(super) struct HintSource<'a> {
    pub(super) tree: &'a NestedTree,
    pub(super) gamma: &'a [Vec<NInstance>],
}

/// Lane constants a template must not leak: counterexample constants and
/// Skolems.
struct LaneConstants {
    all: HashSet<TermId>,
    /// Skolem → its value in the installed model.
    skolem_values: HashMap<TermId, TermId>,
}

fn push_distinct(hints: &mut InstanceHints, key: TermId, tuple: Vec<TermId>) -> bool {
    let entry = hints.entry(key).or_default();
    if entry.contains(&tuple) {
        return false;
    }
    entry.push(tuple);
    true
}

impl Executor {
    /// Build the hints for the authored `roots` from a nested `Sat` and
    /// install them for this query. Needs the installed model (`last_model`).
    pub(super) fn qlra_install_expansion_hints(
        &mut self,
        roots: &[TermId],
        source: &HintSource<'_>,
    ) {
        let found = origins(&self.ctx.terms, source.tree, roots);
        let lane = self.qlra_lane_constants(source.tree);
        let mut tuples = InstanceHints::default();
        let mut count = 0usize;
        for &(node, authored, scope) in &found.nodes {
            let scope = found.scopes[scope].clone();
            for instance in &source.gamma[node] {
                if count >= MAX_HINT_TUPLES {
                    break;
                }
                if let Some(tuple) = self.qlra_template(&instance.tuple, &scope, &lane) {
                    count += usize::from(push_distinct(&mut tuples, authored, tuple));
                }
            }
        }
        let mut sites: Vec<TermId> = found.skolem_levels.keys().copied().collect();
        sites.sort();
        for authored in sites {
            for tuple in self.qlra_skolem_chain_tuples(authored, &found, &lane) {
                if count >= MAX_HINT_TUPLES {
                    break;
                }
                count += usize::from(push_distinct(&mut tuples, authored, tuple));
            }
        }
        let extra = &mut self.last_statistics;
        extra.set_int("qlra.hints", count as u64);
        extra.set_int("qlra.hints_complete", u64::from(found.complete));
        let Ok(query_roots) = self.independent_gate_query_roots() else {
            self.qlra_lane.expansion_hints = None;
            return;
        };
        let hints = ExpansionHints {
            epoch: self.query_authority_epoch.clone(),
            roots: query_roots,
            stamp: self.ctx.terms.snapshot_stamp(),
            tuples,
            consulted: Cell::new(0),
            confirmed: Cell::new(0),
        };
        self.qlra_lane.expansion_hints = Some(Box::new(hints));
    }

    /// Counterexample constants, Skolems, and each Skolem's model value.
    fn qlra_lane_constants(&mut self, tree: &NestedTree) -> LaneConstants {
        let mut all: HashSet<TermId> = tree
            .nodes
            .iter()
            .flat_map(|node| node.ce_vars.iter().copied())
            .collect();
        all.extend(tree.skolems.iter().copied());
        let evaluated: Vec<(TermId, EvalValue)> = match self.last_model.as_ref() {
            Some(model) => tree
                .skolems
                .iter()
                .map(|&sk| (sk, self.evaluate_term(model, sk)))
                .collect(),
            None => Vec::new(),
        };
        let mut skolem_values = HashMap::default();
        for (sk, value) in evaluated {
            let term = match (value, self.ctx.terms.sort(sk)) {
                (EvalValue::Rational(r), Sort::Real) => self.ctx.terms.mk_rational(r),
                (EvalValue::Bool(b), Sort::Bool) => self.ctx.terms.mk_bool(b),
                _ => continue,
            };
            skolem_values.insert(sk, term);
        }
        LaneConstants { all, skolem_values }
    }

    /// A node tuple spelled over the authored names in `scope`, or `None`
    /// when a lane constant has no in-scope name or a free constant is
    /// shadowed there.
    fn qlra_template(
        &mut self,
        tuple: &[TermId],
        scope: &Scope,
        lane: &LaneConstants,
    ) -> Option<Vec<TermId>> {
        let mut names: HashMap<TermId, String> = HashMap::default();
        let mut bound: HashSet<String> = HashSet::default();
        for (name, image) in scope.iter().rev() {
            if bound.insert(name.clone()) {
                if let Some(image) = image {
                    names.entry(*image).or_insert_with(|| name.clone());
                }
            }
        }
        let mut memo: HashMap<TermId, TermId> = HashMap::default();
        tuple
            .iter()
            .map(|&t| self.qlra_respell(t, &names, &bound, lane, &mut memo))
            .collect()
    }

    fn qlra_respell(
        &mut self,
        term: TermId,
        names: &HashMap<TermId, String>,
        bound: &HashSet<String>,
        lane: &LaneConstants,
        memo: &mut HashMap<TermId, TermId>,
    ) -> Option<TermId> {
        if let Some(&done) = memo.get(&term) {
            return Some(done);
        }
        let out = match self.ctx.terms.get(term).clone() {
            TermData::Var(name, _) => {
                if let Some(&value) = lane.skolem_values.get(&term) {
                    value
                } else if lane.all.contains(&term) {
                    let sort = self.ctx.terms.sort(term).clone();
                    self.ctx.terms.mk_var(names.get(&term)?.clone(), sort)
                } else if bound.contains(&name) {
                    return None;
                } else {
                    term
                }
            }
            TermData::Const(_) => term,
            TermData::App(symbol, args) => {
                let mut rewritten = Vec::with_capacity(args.len());
                for &arg in &args {
                    rewritten.push(self.qlra_respell(arg, names, bound, lane, memo)?);
                }
                if rewritten == args {
                    term
                } else {
                    let sort = self.ctx.terms.sort(term).clone();
                    self.ctx.terms.mk_app(symbol, rewritten, sort)
                }
            }
            TermData::Not(inner) => {
                let inner = self.qlra_respell(inner, names, bound, lane, memo)?;
                self.ctx.terms.mk_not_raw(inner)
            }
            TermData::Ite(c, a, b) => {
                let c = self.qlra_respell(c, names, bound, lane, memo)?;
                let a = self.qlra_respell(a, names, bound, lane, memo)?;
                let b = self.qlra_respell(b, names, bound, lane, memo)?;
                self.ctx.terms.mk_ite_raw(c, a, b)
            }
            _ => return None,
        };
        memo.insert(term, out);
        Some(out)
    }

    /// Witness tuples for the Skolemized chain opened by `authored`: per
    /// level, each recorded occurrence's Skolem values (a binder that never
    /// occurs takes the sort's zero / `false`), combined across levels.
    fn qlra_skolem_chain_tuples(
        &mut self,
        authored: TermId,
        found: &Origins,
        lane: &LaneConstants,
    ) -> Vec<Vec<TermId>> {
        let Some((_, binders, _)) = binder_chain(&self.ctx.terms, authored) else {
            return Vec::new();
        };
        let mut combos: Vec<Vec<TermId>> = vec![Vec::new()];
        let mut level = authored;
        let mut covered = 0usize;
        while covered < binders.len() {
            let (width, next) = match self.ctx.terms.get(level) {
                TermData::Forall(b, body, _) | TermData::Exists(b, body, _) => (b.len(), *body),
                _ => return Vec::new(),
            };
            let Some(occurrences) = found.skolem_levels.get(&level) else {
                return Vec::new();
            };
            let sorts: Vec<Sort> = binders[covered..covered + width]
                .iter()
                .map(|(_, sort)| sort.clone())
                .collect();
            let mut choices: Vec<Vec<TermId>> = Vec::new();
            for images in occurrences {
                let values: Option<Vec<TermId>> = images
                    .iter()
                    .zip(&sorts)
                    .map(|(image, sort)| self.qlra_skolem_value(*image, sort, lane))
                    .collect();
                if let Some(values) = values.filter(|v| !choices.contains(v)) {
                    choices.push(values);
                }
            }
            combos = combos
                .iter()
                .flat_map(|prefix| {
                    choices.iter().map(move |choice| {
                        let mut tuple = prefix.clone();
                        tuple.extend(choice.iter().copied());
                        tuple
                    })
                })
                .take(MAX_SKOLEM_COMBOS)
                .collect();
            covered += width;
            level = next;
        }
        combos
    }

    fn qlra_skolem_value(
        &mut self,
        image: Option<TermId>,
        sort: &Sort,
        lane: &LaneConstants,
    ) -> Option<TermId> {
        if let Some(value) = image.and_then(|sk| lane.skolem_values.get(&sk)) {
            return Some(*value);
        }
        match sort {
            Sort::Real => Some(self.ctx.terms.mk_rational(BigRational::zero())),
            Sort::Bool => Some(self.ctx.terms.mk_bool(false)),
            _ => None,
        }
    }
}
