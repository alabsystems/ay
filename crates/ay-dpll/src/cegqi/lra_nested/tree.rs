// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The quantifier node tree (plan §3.1), M1 scope: depth-1 nodes in
//! conjunctive position.
//!
//! Every authored root is walked through its `and`-conjunct closure — exactly
//! the closure the consequence-replay publication route derives by `and_pos`,
//! so every node source this builder admits is one the route can reach. Each
//! conjunct is one of:
//!
//! * quantifier-free — a GROUND sibling;
//! * `(forall x⃗ B)` with quantifier-free `B` — an effective-∀ node whose
//!   instances are `forall_inst` consequences of the authored conjunct;
//! * `(not (exists x⃗ B))` with quantifier-free `B` — an effective-∀ node over
//!   the exact De Morgan dual `(forall x⃗ (not B))`, the same dual the
//!   negated-exists lane mints and `qnt_neg_exists` re-derives;
//! * `(exists ((x S)) B)`, ONE binder, quantifier-free `B` — Skolemized
//!   through the persistent choice registry, so the certificate's `sko_ex`
//!   witness is the very constant the search uses.
//!
//! Anything else (a quantifier under a connective, nested quantifiers, a
//! multi-binder existential, `(not (forall ...))`) declines the whole problem:
//! M1 never publishes a partial treatment.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{SkolemChoice, Sort, TermId, TermStore};

use super::caps::MAX_NODES;
use crate::ematching::{contains_quantifier, subst_vars_exact_qf};

/// Where a node's instances come from, for publication.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum NodeSource {
    /// An authored `(forall x⃗ B)` conjunct; instances are `forall_inst` of it.
    Forall { quantifier: TermId },
    /// An authored `(not (exists x⃗ B))` conjunct; instances are `forall_inst`
    /// of the dual `(forall x⃗ (not B))`.
    NegatedExists {
        not_exists: TermId,
        exists: TermId,
        dual: TermId,
    },
}

/// One effective-∀ block.
#[derive(Clone, Debug)]
pub(crate) struct QNode {
    pub(crate) source: NodeSource,
    /// Binder names and sorts, in authored order.
    pub(crate) binders: Vec<(String, Sort)>,
    /// Effective-∀ body over the binders (the dual's body for ¬∃).
    pub(crate) body: TermId,
    /// Fresh counterexample constants, one per binder.
    pub(crate) ce_vars: Vec<TermId>,
    /// `body[x⃗ := e⃗]`.
    pub(crate) ce_body: TermId,
}

impl QNode {
    /// The universal whose instances this node logs.
    pub(crate) fn instance_source(&self) -> TermId {
        match self.source {
            NodeSource::Forall { quantifier } => quantifier,
            NodeSource::NegatedExists { dual, .. } => dual,
        }
    }
}

/// A Skolemized top-level existential.
#[derive(Clone, Debug)]
pub(crate) struct SkolemRoot {
    /// The authored `(exists ((x S)) B)` conjunct.
    pub(crate) source: TermId,
    /// The registered Skolem constant.
    pub(crate) witness: TermId,
    /// Exact raw `B[x := witness]`.
    pub(crate) instance: TermId,
}

/// The whole problem as the lane sees it.
#[derive(Clone, Debug, Default)]
pub(crate) struct QlraTree {
    /// Quantifier-free conjuncts plus Skolem instances.
    pub(crate) ground: Vec<TermId>,
    pub(crate) nodes: Vec<QNode>,
    pub(crate) skolems: Vec<SkolemRoot>,
}

impl QlraTree {
    /// Every counterexample constant of every node.
    pub(crate) fn all_ce_vars(&self) -> Vec<TermId> {
        self.nodes
            .iter()
            .flat_map(|node| node.ce_vars.iter().copied())
            .collect()
    }
}

/// Why the builder refused the problem.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TreeDecline {
    /// A quantifier outside conjunctive position (under or/ite/iff/...).
    QuantifierUnderConnective,
    /// A quantifier body that itself contains a quantifier (M2 scope).
    Nested,
    /// `(exists ...)` with more than one binder, or `(not (forall ...))`.
    ExistentialShape,
    /// A binder sort other than Real or Bool.
    BinderSort,
    /// More nodes than [`MAX_NODES`].
    TooManyNodes,
    /// No quantified conjunct at all.
    NoQuantifier,
    /// The exact raw substitution refused (shadowing/capture).
    Substitution,
}

enum Conjunct {
    Ground(TermId),
    Node(NodeSource, Vec<(String, Sort)>, TermId),
    Skolem(TermId, String, Sort, TermId),
}

fn and_conjunct_closure(terms: &TermStore, roots: &[TermId]) -> Vec<TermId> {
    let mut out = Vec::new();
    let mut seen = ay_core::kani_compat::DetHashSet::default();
    let mut stack: Vec<TermId> = roots.iter().rev().copied().collect();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::App(symbol, args) if symbol.name() == "and" => {
                stack.extend(args.iter().rev().copied());
            }
            _ => out.push(term),
        }
    }
    out
}

fn binders_admissible(binders: &[(String, Sort)]) -> bool {
    !binders.is_empty()
        && binders
            .iter()
            .all(|(_, sort)| matches!(sort, Sort::Real | Sort::Bool))
}

fn classify(terms: &mut TermStore, conjunct: TermId) -> Result<Conjunct, TreeDecline> {
    if !contains_quantifier(terms, conjunct) {
        return Ok(Conjunct::Ground(conjunct));
    }
    let data = terms.get(conjunct).clone();
    let (binders, body, source) = match data {
        TermData::Forall(binders, body, _) => (
            binders,
            body,
            NodeSource::Forall {
                quantifier: conjunct,
            },
        ),
        TermData::Not(inner) => match terms.get(inner).clone() {
            TermData::Exists(binders, body, _) => {
                if contains_quantifier(terms, body) {
                    return Err(TreeDecline::Nested);
                }
                if !binders_admissible(&binders) {
                    return Err(TreeDecline::BinderSort);
                }
                // The exact dual `validate_qnt_neg_exists` recomputes from the
                // authored existential; `mk_not_raw` keeps the body unfolded.
                let negated_body = terms.mk_not_raw(body);
                let dual = terms.mk_forall(binders.clone(), negated_body);
                let source = NodeSource::NegatedExists {
                    not_exists: conjunct,
                    exists: inner,
                    dual,
                };
                return Ok(Conjunct::Node(source, binders, negated_body));
            }
            TermData::Forall(..) => return Err(TreeDecline::ExistentialShape),
            _ => return Err(TreeDecline::QuantifierUnderConnective),
        },
        TermData::Exists(binders, body, _) => {
            if contains_quantifier(terms, body) {
                return Err(TreeDecline::Nested);
            }
            let [(name, sort)] = binders.as_slice() else {
                return Err(TreeDecline::ExistentialShape);
            };
            if !binders_admissible(&binders) {
                return Err(TreeDecline::BinderSort);
            }
            return Ok(Conjunct::Skolem(conjunct, name.clone(), sort.clone(), body));
        }
        _ => return Err(TreeDecline::QuantifierUnderConnective),
    };
    if contains_quantifier(terms, body) {
        return Err(TreeDecline::Nested);
    }
    if !binders_admissible(&binders) {
        return Err(TreeDecline::BinderSort);
    }
    Ok(Conjunct::Node(source, binders, body))
}

fn exact_subst(
    terms: &mut TermStore,
    body: TermId,
    binders: &[(String, Sort)],
    values: &[TermId],
) -> Option<TermId> {
    let mut map: HashMap<String, TermId> = HashMap::default();
    for ((name, _), &value) in binders.iter().zip(values) {
        map.insert(name.clone(), value);
    }
    subst_vars_exact_qf(terms, body, &map)
}

/// Exact raw instance `body[binders := values]`; `None` on any refusal of the
/// certificate-grade substitution.
pub(crate) fn instantiate(
    terms: &mut TermStore,
    body: TermId,
    binders: &[(String, Sort)],
    values: &[TermId],
) -> Option<TermId> {
    if binders.len() != values.len() {
        return None;
    }
    exact_subst(terms, body, binders, values)
}

/// Build the depth-1 tree, or say why M1 cannot treat this problem.
///
/// All classification happens BEFORE any term is minted, so a declined
/// problem leaves the store with at most the dual universals `classify`
/// hash-conses (no Skolem registration, no counterexample constants).
pub(crate) fn build_depth1_tree(
    terms: &mut TermStore,
    roots: &[TermId],
) -> Result<QlraTree, TreeDecline> {
    let conjuncts = and_conjunct_closure(terms, roots);
    let mut classified = Vec::with_capacity(conjuncts.len());
    for conjunct in conjuncts {
        classified.push(classify(terms, conjunct)?);
    }
    let node_count = classified
        .iter()
        .filter(|entry| matches!(entry, Conjunct::Node(..)))
        .count();
    if node_count == 0 {
        return Err(TreeDecline::NoQuantifier);
    }
    if node_count > MAX_NODES {
        return Err(TreeDecline::TooManyNodes);
    }
    let mut tree = QlraTree::default();
    for entry in classified {
        match entry {
            Conjunct::Ground(term) => tree.ground.push(term),
            Conjunct::Node(source, binders, body) => {
                let ce_vars: Vec<TermId> = binders
                    .iter()
                    .map(|(name, sort)| terms.mk_fresh_var(&format!("qlra!e!{name}"), sort.clone()))
                    .collect();
                let ce_body = instantiate(terms, body, &binders, &ce_vars)
                    .ok_or(TreeDecline::Substitution)?;
                tree.nodes.push(QNode {
                    source,
                    binders,
                    body,
                    ce_vars,
                    ce_body,
                });
            }
            Conjunct::Skolem(source, name, sort, body) => {
                let witness = terms.mk_fresh_var(&format!("sk!{name}"), sort.clone());
                if let TermData::Var(fresh_name, _) = terms.get(witness).clone() {
                    terms.mark_skolem_symbol(fresh_name);
                }
                let binder = [(name.clone(), sort.clone())];
                let instance = instantiate(terms, body, &binder, &[witness])
                    .ok_or(TreeDecline::Substitution)?;
                terms.register_skolem_choice(
                    witness,
                    SkolemChoice {
                        binder: name,
                        sort,
                        body,
                    },
                );
                tree.ground.push(instance);
                tree.skolems.push(SkolemRoot {
                    source,
                    witness,
                    instance,
                });
            }
        }
    }
    Ok(tree)
}
