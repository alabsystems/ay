// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Where each nested-search node and top-level Skolem comes from in the
//! AUTHORED roots.
//!
//! The nested tree (`cegqi::lra_nested::ntree`) rewrites the roots: it
//! Skolemizes top-level effective existentials, and it rewrites every node's
//! body over fresh counterexample constants. Both rewrites are exact,
//! structure-preserving substitutions (raw constructors), so the authored
//! root and the tree's root can be walked IN PARALLEL: an authored quantifier
//! whose image is a node's quantifier term is that node's origin; any other
//! authored quantifier was Skolemized, and its body continues against the
//! same image. A structural mismatch abandons the walk (the hints are then
//! incomplete — never unsound: they are untrusted data).
//!
//! Each record carries the SCOPE at the authored occurrence — the enclosing
//! binder names and the lane constant (counterexample constant or Skolem)
//! each one denotes — so instance templates can be spelled back over the
//! authored binder names.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{TermId, TermStore};

use crate::cegqi::lra_nested::ntree::{Kind, NestedTree};
use crate::executor::expansion::qf_formula::binder_chain;

/// Walk steps before the origin walk gives up.
const MAX_ORIGIN_WORK: usize = 1 << 20;

/// An in-scope authored binder: its name and the lane constant it denotes
/// (`None`: a Skolemized binder that never occurs, so it has no image).
pub(super) type Scope = Vec<(String, Option<TermId>)>;

/// The parallel walk's findings.
#[derive(Default)]
pub(super) struct Origins {
    /// (node, authored quantifier opening its chain, scope there).
    pub(super) nodes: Vec<(usize, TermId, usize)>,
    /// Authored quantifier LEVEL the tree Skolemized → one image per binder,
    /// per occurrence.
    pub(super) skolem_levels: HashMap<TermId, Vec<Vec<Option<TermId>>>>,
    /// Scopes by id.
    pub(super) scopes: Vec<Scope>,
    /// The walk finished without a mismatch or cap.
    pub(super) complete: bool,
}

struct Walk<'a> {
    terms: &'a TermStore,
    tree: &'a NestedTree,
    out: Origins,
    scope_ids: HashMap<Scope, usize>,
    seen: HashSet<(TermId, TermId, usize)>,
    quantified: HashMap<TermId, bool>,
    work: usize,
    failed: bool,
}

/// Map every authored root onto the tree's rewritten root of the same index.
pub(super) fn origins(terms: &TermStore, tree: &NestedTree, roots: &[TermId]) -> Origins {
    let mut walk = Walk {
        terms,
        tree,
        out: Origins::default(),
        scope_ids: HashMap::default(),
        seen: HashSet::default(),
        quantified: HashMap::default(),
        work: 0,
        failed: roots.len() != tree.roots.len(),
    };
    let empty = walk.scope_id(Vec::new());
    for (&authored, &lane) in roots.iter().zip(&tree.roots) {
        if !walk.failed {
            walk.walk(authored, lane, empty);
        }
    }
    let mut out = walk.out;
    out.complete = !walk.failed;
    out
}

impl Walk<'_> {
    fn scope_id(&mut self, scope: Scope) -> usize {
        if let Some(&id) = self.scope_ids.get(&scope) {
            return id;
        }
        self.out.scopes.push(scope.clone());
        let id = self.out.scopes.len() - 1;
        self.scope_ids.insert(scope, id);
        id
    }

    fn has_quantifier(&mut self, term: TermId) -> bool {
        if let Some(&known) = self.quantified.get(&term) {
            return known;
        }
        let children: Vec<TermId> = match self.terms.get(term) {
            TermData::App(_, args) => args.clone(),
            TermData::Not(inner) => vec![*inner],
            TermData::Ite(c, a, b) => vec![*c, *a, *b],
            TermData::Var(..) | TermData::Const(..) => Vec::new(),
            _ => {
                self.quantified.insert(term, true);
                return true;
            }
        };
        let known = stacker::maybe_grow(64 * 1024, 2 * 1024 * 1024, || {
            children.into_iter().any(|c| self.has_quantifier(c))
        });
        self.quantified.insert(term, known);
        known
    }

    fn walk(&mut self, authored: TermId, lane: TermId, scope: usize) {
        self.work += 1;
        if self.failed || self.work > MAX_ORIGIN_WORK {
            self.failed = true;
            return;
        }
        if !self.has_quantifier(authored) || !self.seen.insert((authored, lane, scope)) {
            return;
        }
        let pairs = match (self.terms.get(authored), self.terms.get(lane)) {
            (TermData::Forall(..) | TermData::Exists(..), _) => {
                return self.quantifier(authored, lane, scope);
            }
            (TermData::Not(a), TermData::Not(l)) => vec![(*a, *l)],
            (TermData::App(s, a), TermData::App(t, l)) if s == t && a.len() == l.len() => {
                a.iter().copied().zip(l.iter().copied()).collect()
            }
            (TermData::Ite(a0, a1, a2), TermData::Ite(l0, l1, l2)) => {
                vec![(*a0, *l0), (*a1, *l1), (*a2, *l2)]
            }
            _ => {
                self.failed = true;
                return;
            }
        };
        stacker::maybe_grow(64 * 1024, 2 * 1024 * 1024, || {
            for (a, l) in pairs {
                self.walk(a, l, scope);
            }
        });
    }

    fn quantifier(&mut self, authored: TermId, lane: TermId, scope: usize) {
        let Some((forall, binders, body)) = binder_chain(self.terms, authored) else {
            self.failed = true;
            return;
        };
        if let Some(&node) = self.tree.node_of.get(&lane) {
            let n = &self.tree.nodes[node];
            let kind_matches = matches!(
                (n.kind, forall),
                (Kind::Forall, true) | (Kind::Exists, false)
            );
            let names_match = n.binders.len() == binders.len()
                && n.binders.iter().zip(&binders).all(|(a, b)| a.0 == b.0);
            if kind_matches && names_match {
                self.out.nodes.push((node, authored, scope));
                let mut inner = self.out.scopes[scope].clone();
                inner.extend(
                    binders
                        .iter()
                        .map(|(name, _)| name.clone())
                        .zip(n.ce_vars.iter().map(|&e| Some(e))),
                );
                let (inner, ce_body) = (self.scope_id(inner), n.ce_body);
                return self.walk(body, ce_body, inner);
            }
        }
        // Not a node: the tree Skolemized this ONE level; its body continues
        // against the same image.
        let (level_binders, level_body) = match self.terms.get(authored) {
            TermData::Forall(b, body, _) | TermData::Exists(b, body, _) => (b.clone(), *body),
            _ => {
                self.failed = true;
                return;
            }
        };
        let mut images = Vec::with_capacity(level_binders.len());
        for (name, _) in &level_binders {
            let mut visited = HashSet::default();
            let image = self.find_image(level_body, lane, name, &mut visited);
            images.push(image.filter(|sk| self.tree.skolems.contains(sk)));
        }
        let mut inner = self.out.scopes[scope].clone();
        inner.extend(
            level_binders
                .iter()
                .map(|(name, _)| name.clone())
                .zip(images.iter().copied()),
        );
        self.out
            .skolem_levels
            .entry(authored)
            .or_default()
            .push(images);
        let inner = self.scope_id(inner);
        self.walk(level_body, lane, inner);
    }

    /// The image in `lane` of a free occurrence of binder `name` in
    /// `authored`, if the parallel descent finds one.
    fn find_image(
        &mut self,
        authored: TermId,
        lane: TermId,
        name: &str,
        visited: &mut HashSet<(TermId, TermId)>,
    ) -> Option<TermId> {
        self.work += 1;
        if self.work > MAX_ORIGIN_WORK || !visited.insert((authored, lane)) {
            return None;
        }
        let pairs: Vec<(TermId, TermId)> = match (self.terms.get(authored), self.terms.get(lane)) {
            (TermData::Var(n, _), _) if n == name => return Some(lane),
            (TermData::Var(..) | TermData::Const(..), _) => return None,
            (TermData::Forall(b, body, _), other) | (TermData::Exists(b, body, _), other) => {
                if b.iter().any(|(n, _)| n == name) {
                    return None;
                }
                match other {
                    TermData::Forall(c, lane_body, _) | TermData::Exists(c, lane_body, _)
                        if c.iter().map(|x| &x.0).eq(b.iter().map(|x| &x.0)) =>
                    {
                        vec![(*body, *lane_body)]
                    }
                    // A Skolemized level: its body against the same image.
                    _ => vec![(*body, lane)],
                }
            }
            (TermData::Not(a), TermData::Not(l)) => vec![(*a, *l)],
            (TermData::App(s, a), TermData::App(t, l)) if s == t && a.len() == l.len() => {
                a.iter().copied().zip(l.iter().copied()).collect()
            }
            (TermData::Ite(a0, a1, a2), TermData::Ite(l0, l1, l2)) => {
                vec![(*a0, *l0), (*a1, *l1), (*a2, *l2)]
            }
            _ => return None,
        };
        stacker::maybe_grow(64 * 1024, 2 * 1024 * 1024, || {
            pairs
                .into_iter()
                .find_map(|(a, l)| self.find_image(a, l, name, visited))
        })
    }
}
