// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Build a complete substitution image before projecting a Boolean consequence.
//! Candidate construction carries no authority: the unchanged strict substitution
//! validator must accept the whole image, and ordinary Boolean rules derive the unit.

use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Constant, Proof, ProofId, Sort, Symbol, TermData, TermId, TermStore};
use ay_sat::ResolutionValidationError;

use super::{ExactOriginalProofError, GroundSubstitutionState, SatProofManager};

const MAX_IMAGE_VISITS: usize = 512;
const MAX_IMAGE_DEPTH: usize = 32;

#[cfg(test)]
mod tests;

pub(super) struct GroundImage {
    pub(super) term: TermId,
    hops: Vec<(TermId, u32, TermId)>,
    disjuncts: Option<Vec<TermId>>,
}

/// Expanded visits bound both recursion-free rebuilding and the checker's walks.
fn bounded_order(terms: &TermStore, root: TermId) -> Option<Vec<TermId>> {
    let mut stack = vec![(root, 0, false)];
    let mut order = Vec::new();
    let mut visits = 0;
    while let Some((node, depth, finished)) = stack.pop() {
        if finished {
            order.push(node);
            continue;
        }
        visits += 1;
        if visits > MAX_IMAGE_VISITS || depth > MAX_IMAGE_DEPTH {
            return None;
        }
        stack.push((node, depth, true));
        match terms.get(node) {
            TermData::Const(_) | TermData::Var(..) => {}
            TermData::App(_, args)
                if args.len() <= MAX_IMAGE_VISITS - visits
                    && stack.len() + order.len() + args.len() <= 2 * MAX_IMAGE_VISITS =>
            {
                stack.extend(args.iter().rev().map(|&arg| (arg, depth + 1, false)));
            }
            TermData::Not(inner) => stack.push((*inner, depth + 1, false)),
            TermData::Ite(c, t, e) => {
                stack.extend([
                    (*e, depth + 1, false),
                    (*t, depth + 1, false),
                    (*c, depth + 1, false),
                ]);
            }
            _ => return None,
        }
    }
    Some(order)
}

fn int_comparison(terms: &TermStore, node: TermId) -> bool {
    matches!(terms.get(node), TermData::App(Symbol::Named(name), args)
        if matches!(name.as_str(), "<" | "<=" | ">" | ">=") && args.len() == 2
            && args.iter().all(|&arg| terms.sort(arg) == &Sort::Int))
}

/// Preserve junction order; only remove literal identities and absorbers.
fn rebuild_app(
    terms: &mut TermStore,
    node: TermId,
    symbol: Symbol,
    mut args: Vec<TermId>,
) -> TermId {
    if let Symbol::Named(name) = &symbol {
        if name == "and" || name == "or" {
            let identity = name == "and";
            if args.iter().any(|&arg| matches!(terms.get(arg), TermData::Const(Constant::Bool(v)) if *v != identity)) {
                return terms.mk_bool(!identity);
            }
            args.retain(|&arg| !matches!(terms.get(arg), TermData::Const(Constant::Bool(v)) if *v == identity));
            match args.as_slice() {
                [] => return terms.mk_bool(identity),
                [only] => return *only,
                _ => {}
            }
        } else if name == "=" && args.len() == 2 && args[0] == args[1] {
            return terms.true_term();
        }
    }
    terms.mk_app(symbol, args, terms.sort(node).clone())
}

impl SatProofManager<'_> {
    pub(super) fn ground_image_plan(
        &mut self,
        source: TermId,
        pairs: &[(TermId, TermId)],
        state: &mut GroundSubstitutionState<'_>,
    ) -> Result<Option<GroundImage>, ExactOriginalProofError> {
        if ay_proof::ground_substitution_image_matches(self.terms, source, state.unit, pairs) {
            return Ok(Some(GroundImage {
                term: state.unit,
                hops: Vec::new(),
                disjuncts: None,
            }));
        }
        if pairs.len() > 16 {
            return Ok(None);
        }
        // Charge bounded scratch space before either walk can allocate it.
        (state.progress)(MAX_IMAGE_VISITS * 4, MAX_IMAGE_VISITS * 2048)?;
        let (Some(order), Some(target_order)) = (
            bounded_order(self.terms, source),
            bounded_order(self.terms, state.unit),
        ) else {
            return Ok(None);
        };
        let walk_charge =
            (order.len() + target_order.len() + 1) * (pairs.len() + 8 + 8 * MAX_IMAGE_DEPTH);
        let mut rewritten: DetHashMap<TermId, TermId> = pairs.iter().copied().collect();
        for node in order {
            if rewritten.contains_key(&node) {
                continue;
            }
            let value =
                if int_comparison(self.terms, state.unit) && int_comparison(self.terms, node) {
                    (state.progress)(walk_charge, 0)?;
                    ay_proof::ground_substitution_image_matches(self.terms, node, state.unit, pairs)
                        .then_some(state.unit)
                } else {
                    None
                };
            let value = match value {
                Some(value) => value,
                None => rebuild_node(self.terms, node, &rewritten),
            };
            rewritten.insert(node, value);
        }
        // Charge every candidate's actual interning, including refused candidates.
        self.reconcile_term_store_growth(
            state.term_store_baseline,
            state.charged_term_store_growth,
            state.progress,
        )?;
        let Some(&image) = rewritten.get(&source) else {
            return Ok(None);
        };
        let Some(plan) = projection_plan(self.terms, image, state.unit) else {
            return Ok(None);
        };
        (state.progress)(walk_charge, 0)?;
        Ok(
            ay_proof::ground_substitution_image_matches(self.terms, source, image, pairs)
                .then_some(plan),
        )
    }
}

fn rebuild_node(
    terms: &mut TermStore,
    node: TermId,
    rewritten: &DetHashMap<TermId, TermId>,
) -> TermId {
    let mapped = |id| rewritten.get(&id).copied().unwrap_or(id);
    match terms.get(node).clone() {
        TermData::App(symbol, args) => {
            rebuild_app(terms, node, symbol, args.into_iter().map(mapped).collect())
        }
        TermData::Not(inner) => {
            let inner = mapped(inner);
            match terms.get(inner) {
                TermData::Const(Constant::Bool(value)) => terms.mk_bool(!*value),
                TermData::Not(value) => *value,
                _ => terms.mk_not_raw(inner),
            }
        }
        TermData::Ite(c, t, e) => {
            let (c, t, e) = (mapped(c), mapped(t), mapped(e));
            match terms.get(c) {
                TermData::Const(Constant::Bool(true)) => t,
                TermData::Const(Constant::Bool(false)) => e,
                _ => terms.mk_ite_raw(c, t, e),
            }
        }
        _ => node,
    }
}

fn projection_plan(terms: &TermStore, image: TermId, unit: TermId) -> Option<GroundImage> {
    let mut stack = vec![(image, Vec::new())];
    while let Some((node, hops)) = stack.pop() {
        if node == unit {
            return Some(GroundImage {
                term: image,
                hops,
                disjuncts: None,
            });
        }
        let TermData::App(Symbol::Named(name), args) = terms.get(node) else {
            continue;
        };
        if name == "and" {
            for (index, &child) in args.iter().enumerate().rev() {
                let mut path = hops.clone();
                path.push((node, u32::try_from(index).ok()?, child));
                stack.push((child, path));
            }
        } else if name == "or" {
            let TermData::App(Symbol::Named(target), target_args) = terms.get(unit) else {
                continue;
            };
            let mut a = args.clone();
            let mut b = target_args.clone();
            a.sort_unstable();
            b.sort_unstable();
            if target == "or" && a == b && !a.is_empty() {
                return Some(GroundImage {
                    term: image,
                    hops,
                    disjuncts: Some(args.clone()),
                });
            }
        }
    }
    None
}

impl GroundImage {
    pub(super) fn emit_projection(
        &self,
        terms: &mut TermStore,
        proof: &mut Proof,
        mut current: ProofId,
        unit: TermId,
        progress: &mut dyn FnMut(usize, usize) -> Result<(), ResolutionValidationError>,
    ) -> Result<ProofId, ResolutionValidationError> {
        let disjunct_count = self.disjuncts.as_ref().map_or(0, Vec::len);
        let (work, bytes) = SatProofManager::unit_chain_charge(
            2 * self.hops.len() + 2 * disjunct_count + 1,
            4 * self.hops.len() + (disjunct_count + 1) * (disjunct_count + 1),
        )?;
        progress(work, bytes)?;
        for &(parent, index, child) in &self.hops {
            let not_parent = terms.mk_not_raw(parent);
            let tautology = proof.add_rule_step(
                AletheRule::AndPos(index),
                vec![not_parent, child],
                Vec::new(),
                vec![parent],
            );
            current = proof.add_resolution(vec![child], parent, tautology, current);
        }
        if let Some(disjuncts) = &self.disjuncts {
            // Repack a reordered OR through individual, exact or_neg steps.
            let mut clause = disjuncts.clone();
            current =
                proof.add_rule_step(AletheRule::Or, clause.clone(), vec![current], Vec::new());
            for &disjunct in disjuncts {
                if !clause.contains(&disjunct) {
                    continue;
                }
                let complement = terms.mk_not_raw(disjunct);
                let intro = proof.add_rule_step(
                    AletheRule::OrNeg,
                    vec![unit, complement],
                    Vec::new(),
                    Vec::new(),
                );
                clause.retain(|&term| term != disjunct);
                if !clause.contains(&unit) {
                    clause.push(unit);
                }
                current = proof.add_resolution(clause.clone(), disjunct, current, intro);
            }
        }
        Ok(current)
    }
}
