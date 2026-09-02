// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded equality plans for authored arithmetic definitions.
//!
//! The planner never treats normalization as an axiom.  Every variable
//! expansion cites an exact authored equality, every contextual rewrite is an
//! `eq_congruent` derivation, and the one premise-free arithmetic step is
//! admitted only when both independent exact polynomial recognizers accept it.

use ay_core::{Sort, Symbol, TermData, TermId, TermStore};

mod emit;
mod occurs;

pub(super) use emit::emit_eq_plan;
use occurs::contains_term_bounded;

const MAX_VARIANTS: usize = 32;
const MAX_DEPTH: usize = 24;
const MAX_APP_ARITY: usize = 16;
const MAX_PLAN_NODES: u32 = 4_096;
const POLY_ATTEMPT_WORK: usize = 512;
pub(super) const MAX_POLY_ATTEMPTS: u16 = 32;
const MAX_BRIDGE_FARKAS_ATTEMPTS: u16 = 32;

pub(super) struct EqBudget {
    work: u32,
    poly_attempts: u16,
    bridge_farkas_attempts: u16,
}

impl EqBudget {
    pub(super) const fn new(work: u32) -> Self {
        Self {
            work,
            poly_attempts: MAX_POLY_ATTEMPTS,
            bridge_farkas_attempts: MAX_BRIDGE_FARKAS_ATTEMPTS,
        }
    }

    #[cfg(test)]
    pub(super) const fn remaining_poly_attempts(&self) -> u16 {
        self.poly_attempts
    }

    fn spend_work(&mut self, amount: usize) -> bool {
        let Ok(amount) = u32::try_from(amount) else {
            return false;
        };
        let Some(remaining) = self.work.checked_sub(amount) else {
            return false;
        };
        self.work = remaining;
        true
    }

    fn spend_poly_attempt(&mut self) -> bool {
        let Some(remaining) = self.poly_attempts.checked_sub(1) else {
            return false;
        };
        if !self.spend_work(POLY_ATTEMPT_WORK) {
            return false;
        }
        self.poly_attempts = remaining;
        true
    }

    pub(super) fn spend_bridge_farkas_attempt(&mut self) -> bool {
        let Some(remaining) = self.bridge_farkas_attempts.checked_sub(1) else {
            return false;
        };
        self.bridge_farkas_attempts = remaining;
        true
    }
}

#[derive(Clone)]
pub(super) struct Definition {
    variable: TermId,
    value: TermId,
    assumption: TermId,
    reversed: bool,
}

impl Definition {
    fn decode(terms: &TermStore, assumption: TermId) -> Vec<Self> {
        let TermData::App(Symbol::Named(name), args) = terms.get(assumption) else {
            return Vec::new();
        };
        let [left, right] = args.as_slice() else {
            return Vec::new();
        };
        if name != "=" || terms.sort(*left) != &Sort::Int || terms.sort(*right) != &Sort::Int {
            return Vec::new();
        }
        let mut decoded = Vec::with_capacity(2);
        for (variable, value, reversed) in [(*left, *right, false), (*right, *left, true)] {
            if !matches!(terms.get(variable), TermData::Var(..))
                || contains_term_bounded(terms, value, variable)
            {
                continue;
            }
            decoded.push(Self {
                variable,
                value,
                assumption,
                reversed,
            });
        }
        decoded
    }
}

pub(super) fn collect_definitions(terms: &TermStore, roots: &[TermId]) -> Vec<Definition> {
    roots
        .iter()
        .flat_map(|&root| Definition::decode(terms, root))
        .collect()
}

#[derive(Clone)]
pub(super) struct EqPlan {
    lhs: TermId,
    rhs: TermId,
    eq: TermId,
    neg_eq: TermId,
    nodes: u32,
    kind: EqPlanKind,
}

#[derive(Clone)]
enum EqPlanKind {
    Refl,
    Assumed { assumption: TermId, reversed: bool },
    PolySimp,
    Symm(Box<EqPlan>),
    Cong { children: Vec<EqPlan> },
    Trans(Box<EqPlan>, Box<EqPlan>),
}

impl EqPlan {
    pub(super) fn equality(&self) -> TermId {
        self.eq
    }

    pub(super) fn negated_equality(&self) -> TermId {
        self.neg_eq
    }

    /// Conservative number of proof steps emitted by this plan when none of
    /// its authored assumptions has been cached yet. Assumption reuse can only
    /// reduce the actual count. Keep this structural instead of trusting
    /// `nodes`: a reversed authored definition emits both `assume` and `symm`.
    pub(super) fn emitted_step_upper_bound(&self) -> Option<usize> {
        match &self.kind {
            EqPlanKind::Refl | EqPlanKind::PolySimp => Some(1),
            EqPlanKind::Assumed { reversed, .. } => Some(usize::from(*reversed) + 1),
            EqPlanKind::Symm(inner) => inner.emitted_step_upper_bound()?.checked_add(1),
            EqPlanKind::Cong { children } => children.iter().try_fold(1usize, |total, child| {
                total.checked_add(child.emitted_step_upper_bound()?)
            }),
            EqPlanKind::Trans(left, right) => left
                .emitted_step_upper_bound()?
                .checked_add(right.emitted_step_upper_bound()?)?
                .checked_add(1),
        }
    }

    fn refl(terms: &mut TermStore, term: TermId) -> Self {
        let eq = raw_eq(terms, term, term);
        let neg_eq = terms.mk_not_raw(eq);
        Self {
            lhs: term,
            rhs: term,
            eq,
            neg_eq,
            nodes: 1,
            kind: EqPlanKind::Refl,
        }
    }

    fn assumed(terms: &mut TermStore, definition: &Definition) -> Self {
        let eq = raw_eq(terms, definition.variable, definition.value);
        let neg_eq = terms.mk_not_raw(eq);
        Self {
            lhs: definition.variable,
            rhs: definition.value,
            eq,
            neg_eq,
            nodes: 1,
            kind: EqPlanKind::Assumed {
                assumption: definition.assumption,
                reversed: definition.reversed,
            },
        }
    }

    fn symm(terms: &mut TermStore, inner: EqPlan) -> Option<Self> {
        let nodes = inner.nodes.checked_add(1)?;
        if nodes > MAX_PLAN_NODES {
            return None;
        }
        let eq = raw_eq(terms, inner.rhs, inner.lhs);
        let neg_eq = terms.mk_not_raw(eq);
        Some(Self {
            lhs: inner.rhs,
            rhs: inner.lhs,
            eq,
            neg_eq,
            nodes,
            kind: EqPlanKind::Symm(Box::new(inner)),
        })
    }

    fn trans(terms: &mut TermStore, left: EqPlan, right: EqPlan) -> Option<Self> {
        if left.rhs != right.lhs {
            return None;
        }
        // The strict Alethe `trans` rule rejects redundant premises.  Elide a
        // reflexive side instead of emitting `trans(refl, p)` / `trans(p,
        // refl)`, and use `refl` directly when a non-trivial path returns to
        // its start.
        if left.lhs == left.rhs {
            return Some(right);
        }
        if right.lhs == right.rhs {
            return Some(left);
        }
        if left.lhs == right.rhs {
            return Some(Self::refl(terms, left.lhs));
        }
        let nodes = left.nodes.checked_add(right.nodes)?.checked_add(1)?;
        if nodes > MAX_PLAN_NODES {
            return None;
        }
        let eq = raw_eq(terms, left.lhs, right.rhs);
        let neg_eq = terms.mk_not_raw(eq);
        Some(Self {
            lhs: left.lhs,
            rhs: right.rhs,
            eq,
            neg_eq,
            nodes,
            kind: EqPlanKind::Trans(Box::new(left), Box::new(right)),
        })
    }
}

#[derive(Clone)]
struct Variant {
    term: TermId,
    plan: EqPlan,
}

pub(super) fn plan_numeric_equality(
    terms: &mut TermStore,
    lhs: TermId,
    rhs: TermId,
    definitions: &[Definition],
    budget: &mut EqBudget,
) -> Option<EqPlan> {
    if terms.sort(lhs) != &Sort::Int || terms.sort(rhs) != &Sort::Int {
        return None;
    }
    if lhs == rhs {
        return Some(EqPlan::refl(terms, lhs));
    }
    let directly_expandable = definitions
        .iter()
        .any(|definition| definition.variable == lhs || definition.variable == rhs);
    if !directly_expandable {
        if let Some(identity) = exact_poly_identity(terms, lhs, rhs, budget) {
            return Some(identity);
        }
    }

    let left_variants = variants(terms, lhs, definitions, &mut Vec::new(), 0, budget);
    let right_variants = variants(terms, rhs, definitions, &mut Vec::new(), 0, budget);
    // Authored definitions append progressively expanded forms.  Prefer the
    // most-expanded pair: fixture equalities normally meet there directly,
    // and a near miss cannot consume the small global polynomial-attempt cap
    // by trying every shallower cross-product first.
    for left in left_variants.iter().rev() {
        for right in right_variants.iter().rev() {
            let middle = if left.term == right.term {
                EqPlan::refl(terms, left.term)
            } else {
                let Some(identity) = exact_poly_identity(terms, left.term, right.term, budget)
                else {
                    continue;
                };
                identity
            };
            if !budget.spend_work(left.plan.nodes.saturating_add(right.plan.nodes) as usize) {
                return None;
            }
            let prefix = EqPlan::trans(terms, left.plan.clone(), middle)?;
            let suffix = EqPlan::symm(terms, right.plan.clone())?;
            return EqPlan::trans(terms, prefix, suffix);
        }
    }
    None
}

fn exact_poly_identity(
    terms: &mut TermStore,
    lhs: TermId,
    rhs: TermId,
    budget: &mut EqBudget,
) -> Option<EqPlan> {
    if !budget.spend_poly_attempt() {
        return None;
    }
    let eq = raw_eq(terms, lhs, rhs);
    let clause = [eq];
    if !ay_proof::recognize_arith_poly_simp(terms, &clause)
        || !ay_proof::recognize_arith_clause_tautology(terms, &clause)
    {
        return None;
    }
    Some(EqPlan {
        lhs,
        rhs,
        eq,
        neg_eq: terms.mk_not_raw(eq),
        nodes: 1,
        kind: EqPlanKind::PolySimp,
    })
}

fn variants(
    terms: &mut TermStore,
    term: TermId,
    definitions: &[Definition],
    active: &mut Vec<TermId>,
    depth: usize,
    budget: &mut EqBudget,
) -> Vec<Variant> {
    if depth > MAX_DEPTH || !budget.spend_work(1) {
        return Vec::new();
    }
    let mut out = vec![Variant {
        term,
        plan: EqPlan::refl(terms, term),
    }];

    if matches!(terms.get(term), TermData::Var(..)) && !active.contains(&term) {
        active.push(term);
        for definition in definitions
            .iter()
            .filter(|definition| definition.variable == term)
        {
            let base = EqPlan::assumed(terms, definition);
            for expanded in variants(
                terms,
                definition.value,
                definitions,
                active,
                depth + 1,
                budget,
            ) {
                if !budget.spend_work(base.nodes as usize) {
                    let _ = active.pop();
                    return out;
                }
                let Some(plan) = EqPlan::trans(terms, base.clone(), expanded.plan) else {
                    continue;
                };
                push_variant(
                    &mut out,
                    Variant {
                        term: expanded.term,
                        plan,
                    },
                );
                if out.len() == MAX_VARIANTS {
                    break;
                }
            }
            if out.len() == MAX_VARIANTS {
                break;
            }
        }
        let _ = active.pop();
        return out;
    }

    let TermData::App(symbol, args) = terms.get(term) else {
        return out;
    };
    if !matches!(&symbol, Symbol::Named(name) if matches!(name.as_str(), "+" | "-" | "*"))
        || args.is_empty()
        || args.len() > MAX_APP_ARITY
        || !budget.spend_work(args.len())
    {
        return out;
    }
    let symbol = symbol.clone();
    let args = args.clone();
    let child_variants: Vec<Vec<Variant>> = args
        .iter()
        .map(|&arg| variants(terms, arg, definitions, active, depth + 1, budget))
        .collect();
    if child_variants.iter().any(Vec::is_empty) {
        return out;
    }
    let mut selections = vec![Vec::<Variant>::new()];
    for children in child_variants {
        let mut next = Vec::new();
        for prefix in &selections {
            for child in &children {
                if next.len() == MAX_VARIANTS {
                    break;
                }
                let plan_nodes = prefix
                    .iter()
                    .map(|variant| variant.plan.nodes)
                    .sum::<u32>()
                    .saturating_add(child.plan.nodes);
                if !budget.spend_work(
                    prefix
                        .len()
                        .saturating_add(1)
                        .saturating_add(plan_nodes as usize),
                ) {
                    return out;
                }
                let mut selection = prefix.clone();
                selection.push(child.clone());
                next.push(selection);
            }
        }
        selections = next;
    }
    for selection in selections {
        if !budget.spend_work(selection.len().saturating_mul(2)) {
            return out;
        }
        let normalized_args: Vec<TermId> = selection.iter().map(|entry| entry.term).collect();
        let normalized = terms.mk_app(symbol.clone(), &normalized_args, Sort::Int);
        if normalized == term {
            continue;
        }
        let children: Vec<EqPlan> = selection
            .into_iter()
            .map(|entry| entry.plan)
            .filter(|child| child.lhs != child.rhs)
            .collect();
        let nodes = children
            .iter()
            .try_fold(1_u32, |total, child| total.checked_add(child.nodes));
        let Some(nodes) = nodes.filter(|&nodes| nodes <= MAX_PLAN_NODES) else {
            continue;
        };
        let eq = raw_eq(terms, term, normalized);
        let neg_eq = terms.mk_not_raw(eq);
        push_variant(
            &mut out,
            Variant {
                term: normalized,
                plan: EqPlan {
                    lhs: term,
                    rhs: normalized,
                    eq,
                    neg_eq,
                    nodes,
                    kind: EqPlanKind::Cong { children },
                },
            },
        );
        if out.len() == MAX_VARIANTS {
            break;
        }
    }
    out
}

fn push_variant(out: &mut Vec<Variant>, candidate: Variant) {
    if out.len() < MAX_VARIANTS && !out.iter().any(|entry| entry.term == candidate.term) {
        out.push(candidate);
    }
}

fn raw_eq(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [lhs, rhs], Sort::Bool)
}

#[cfg(test)]
#[path = "eq_plan/tests.rs"]
mod tests;
