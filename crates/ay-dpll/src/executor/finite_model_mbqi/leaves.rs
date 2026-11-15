// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Which obligations the generic model check reads off the authored window.
//!
//! Every `Forall`/`Exists` node reachable from the authored roots must end up
//! either as a leaf or as COVERED by one: the authority installed later names
//! exactly this node set (`checked_full_domain_sat_authority`), so a node
//! that is neither would be an undischarged obligation.
//!
//! A node whose body nests quantifiers of the SAME effective kind in
//! monotone positions is one prenex block, e.g. the SPARK shape
//! `forall j. (A ⇒ forall j1. (B ⇒ forall j2. C))`:
//!
//! ```text
//!   forall x. (A ∨ forall y. B)  ≡  forall x y. (A ∨ B)       (y ∉ fv(A))
//!   forall x. (A ∧ forall y. B)  ≡  forall x y. (A ∧ B)       (y ∉ fv(A))
//!   forall x. (A ⇒ forall y. B)  ≡  forall x y. (A ⇒ B)       (y ∉ fv(A))
//!   forall x. ((exists y. B) ⇒ A) ≡ forall x y. (B ⇒ A)       (y ∉ fv(A))
//! ```
//!
//! and dually for `exists`. The side condition is met by construction: every
//! pulled binder is renamed to a fresh variable with the capture-avoiding
//! `subst_vars` before its body is spliced in, so no pulled name can occur
//! anywhere else. A quantifier of the other effective kind (an alternation),
//! or one under a non-monotone connective (`=`, `xor`, an `ite` condition,
//! a theory atom), leaves the node unflattened and the pass declines.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{Sort, Symbol, TermData, TermId};

use super::{trace, AuthoredUniversal};
use crate::ematching::{contains_quantifier, subst_vars};
use crate::executor::Executor;

/// The binders one prenex block accumulates, and the nested nodes it covers.
struct Block {
    vars: Vec<(String, Sort)>,
    covered: Vec<TermId>,
}

impl Executor {
    /// Classify one quantifier node for the generic check: any binder sorts
    /// except regular languages, and a quantifier-free body after prenexing
    /// its block.
    fn qmc_classify(&mut self, node: TermId) -> Option<AuthoredUniversal> {
        let (vars, body, universal) = match self.ctx.terms.get(node) {
            TermData::Forall(vars, body, _) => (vars.clone(), *body, true),
            TermData::Exists(vars, body, _) => (vars.clone(), *body, false),
            _ => return None,
        };
        if vars.is_empty() {
            return None;
        }
        let mut block = Block {
            vars,
            covered: Vec::new(),
        };
        let body = if contains_quantifier(&self.ctx.terms, body) {
            let pulled = self.qmc_pull(body, universal, true, &mut block)?;
            // A successful pull removed EVERY nested quantifier. Renaming
            // rebuilt the deeper ones under new ids, so the covered set is
            // read off the original body, which is what the authority's
            // node inventory walks.
            let mut nested: Vec<TermId> =
                crate::executor::bv_mbqi::quantifier_nodes_in(&self.ctx.terms, &[body])
                    .into_iter()
                    .collect();
            nested.sort_unstable();
            block.covered = nested;
            pulled
        } else {
            body
        };
        if block
            .vars
            .iter()
            .any(|(_, sort)| matches!(sort, Sort::RegLan))
        {
            return None;
        }
        Some(AuthoredUniversal {
            node,
            vars: block.vars,
            body,
            negate_body: false,
            universal,
            refinable: false,
            dual_refinable: false,
            covered: block.covered,
        })
    }

    /// `term` with every quantifier of the block's kind removed and its
    /// (renamed) binders appended to `block`; `None` on an alternation or a
    /// quantifier in a non-monotone position.
    fn qmc_pull(
        &mut self,
        term: TermId,
        universal: bool,
        positive: bool,
        block: &mut Block,
    ) -> Option<TermId> {
        if !contains_quantifier(&self.ctx.terms, term) {
            return Some(term);
        }
        match self.ctx.terms.get(term).clone() {
            TermData::Forall(vars, body, _) | TermData::Exists(vars, body, _) => {
                let is_forall = matches!(self.ctx.terms.get(term), TermData::Forall(..));
                if (is_forall == positive) != universal {
                    return None;
                }
                let renamed = self.qmc_rename_binders(&vars, body, block);
                self.qmc_pull(renamed, universal, positive, block)
            }
            TermData::Not(inner) => {
                let pulled = self.qmc_pull(inner, universal, !positive, block)?;
                Some(self.ctx.terms.mk_not(pulled))
            }
            TermData::Ite(c, t, e) if !contains_quantifier(&self.ctx.terms, c) => {
                let t = self.qmc_pull(t, universal, positive, block)?;
                let e = self.qmc_pull(e, universal, positive, block)?;
                Some(self.ctx.terms.mk_ite(c, t, e))
            }
            TermData::App(Symbol::Named(name), args)
                if matches!(name.as_str(), "and" | "or" | "=>") =>
            {
                let last = args.len().saturating_sub(1);
                let mut pulled = Vec::with_capacity(args.len());
                for (i, &arg) in args.iter().enumerate() {
                    // `=>`: every premise is negative, the conclusion positive.
                    let arg_positive = if name == "=>" && i < last {
                        !positive
                    } else {
                        positive
                    };
                    pulled.push(self.qmc_pull(arg, universal, arg_positive, block)?);
                }
                Some(
                    self.ctx
                        .terms
                        .mk_app(Symbol::Named(name), pulled, Sort::Bool),
                )
            }
            _ => None,
        }
    }

    /// Rename `vars` to fresh variables in `body` and append them to `block`.
    fn qmc_rename_binders(
        &mut self,
        vars: &[(String, Sort)],
        body: TermId,
        block: &mut Block,
    ) -> TermId {
        let mut subst = ay_core::kani_compat::DetHashMap::default();
        for (name, sort) in vars {
            let fresh = self
                .ctx
                .terms
                .mk_fresh_var(&format!("qmc!{name}"), sort.clone());
            let fresh_name = match self.ctx.terms.get(fresh) {
                TermData::Var(fresh_name, _) => fresh_name.clone(),
                _ => name.clone(),
            };
            subst.insert(name.clone(), fresh);
            block.vars.push((fresh_name, sort.clone()));
        }
        subst_vars(&mut self.ctx.terms, body, &subst)
    }

    /// Every quantifier node of the authored window, classified for the
    /// generic check, or `None` if one is neither a leaf nor covered by one.
    pub(super) fn qmc_leaves(&mut self, roots: &[TermId]) -> Option<Vec<AuthoredUniversal>> {
        let nodes = crate::executor::bv_mbqi::quantifier_nodes_in(&self.ctx.terms, roots);
        if nodes.is_empty() {
            return None;
        }
        let mut sorted: Vec<TermId> = nodes.into_iter().collect();
        sorted.sort_unstable();
        let mut classified = Vec::with_capacity(sorted.len());
        let mut unclassified = Vec::new();
        for node in sorted {
            match self.qmc_classify(node) {
                Some(leaf) => classified.push(leaf),
                None => unclassified.push(node),
            }
        }
        let covered: HashSet<TermId> = classified
            .iter()
            .flat_map(|leaf| leaf.covered.iter().copied())
            .collect();
        if let Some(node) = unclassified.iter().find(|&&node| !covered.contains(&node)) {
            trace(|| format!("qmc: node {node:?} is not admissible"));
            return None;
        }
        let conjunctive = self.forall_ids_in_conjunctive_position(roots);
        let mut leaves: Vec<AuthoredUniversal> = classified
            .into_iter()
            .filter(|leaf| !covered.contains(&leaf.node))
            .collect();
        for leaf in &mut leaves {
            match self.ctx.terms.get(leaf.node).clone() {
                TermData::Forall(..) => leaf.refinable = conjunctive.contains(&leaf.node),
                // `(not (exists x̄. b))` in conjunctive position is the entailed
                // universal `forall x̄. (not b)`; the shared helper builds
                // exactly this term for it, so membership is the test.
                TermData::Exists(vars, body, triggers) => {
                    let negated = self.ctx.terms.mk_not(body);
                    let dual = self
                        .ctx
                        .terms
                        .mk_forall_with_triggers(vars, negated, triggers);
                    leaf.dual_refinable = conjunctive.contains(&dual);
                }
                _ => {}
            }
        }
        trace(|| {
            let refinable = leaves
                .iter()
                .filter(|l| l.refinable || l.dual_refinable)
                .count();
            format!(
                "qmc: leaves={} covered={} refinable={refinable}",
                leaves.len(),
                covered.len()
            )
        });
        Some(leaves)
    }
}

/// Every node the leaves discharge: their own and the ones they cover.
pub(super) fn certified_nodes(leaves: &[AuthoredUniversal]) -> Vec<TermId> {
    let mut nodes: Vec<TermId> = leaves
        .iter()
        .flat_map(|leaf| std::iter::once(leaf.node).chain(leaf.covered.iter().copied()))
        .collect();
    nodes.sort_unstable();
    nodes.dedup();
    nodes
}
