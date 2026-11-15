// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Which terms the hub holds before the search, decided once (design H1, H2).
//!
//! Registration chooses each arithmetic family's plug-in from the terms the
//! hub will share with it (difference logic can carry only a vertex plus a
//! constant), and the kernel then builds the hub. Both read this one layout,
//! so the plug-in chosen always accepts every term the hub attaches to it:
//! a check whose shared terms difference logic cannot carry goes to the
//! simplex before the search instead of giving up in it.
//!
//! The layout, in the order the kernel creates the nodes (KC9):
//! - every uninterpreted application (in canonical order, arguments first),
//!   with each argument a node first: an equality node when the argument is
//!   an equality the hub watches, a leaf otherwise;
//! - then every equality atom (in the atoms' canonical order) the hub
//!   watches: one over an uninterpreted sort, or one with either side
//!   already a node; its sides become nodes (leaves) first.
//!
//! In the search, the hub only adds equality nodes whose sides are both
//! nodes already, so no term reaches a plug-in that this layout did not
//! name.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{Sort, TermData, TermId, TermStore};

use crate::atoms::Family;
use crate::content::is_uf_app;

/// One node-creating step of the layout.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Step {
    /// A node for a term that is not an uninterpreted application.
    Leaf(TermId),
    /// An equality node over two sides that are nodes already.
    Eq(TermId),
    /// An argument of an application (a node already): a shared term.
    Arg(TermId),
    /// An uninterpreted application over argument nodes.
    App(TermId),
}

/// The hub's registration-time nodes.
#[derive(Debug, Default)]
pub(crate) struct HubLayout {
    pub(crate) steps: Vec<Step>,
    nodes: HashSet<TermId>,
}

impl HubLayout {
    /// The layout of the applications `apps` (canonical order) and the
    /// atoms `atoms` (canonical order; only equalities matter).
    pub(crate) fn new(terms: &TermStore, apps: &[TermId], atoms: &[TermId]) -> Self {
        let mut layout = Self::default();
        for &app in apps {
            if layout.nodes.contains(&app) {
                continue;
            }
            let TermData::App(_, args) = terms.get(app) else {
                continue;
            };
            for &arg in args {
                // An equality argument keeps its meaning in the hub: it is an
                // equality node when its sides matter to the hub.
                layout.watch_equality(terms, arg);
                layout.leaf(arg);
                layout.steps.push(Step::Arg(arg));
            }
            layout.nodes.insert(app);
            layout.steps.push(Step::App(app));
        }
        for &atom in atoms {
            layout.watch_equality(terms, atom);
        }
        layout
    }

    fn leaf(&mut self, term: TermId) {
        if self.nodes.insert(term) {
            self.steps.push(Step::Leaf(term));
        }
    }

    fn watch_equality(&mut self, terms: &TermStore, eq: TermId) {
        if self.nodes.contains(&eq) {
            return;
        }
        let Some((a, b)) = watched_sides(terms, eq) else {
            return;
        };
        let watch =
            terms.sort(a).is_uninterpreted() || self.nodes.contains(&a) || self.nodes.contains(&b);
        if !watch {
            return;
        }
        self.leaf(a);
        self.leaf(b);
        self.nodes.insert(eq);
        self.steps.push(Step::Eq(eq));
    }

    /// The families the nodes need: EUF for any application or term of an
    /// uninterpreted sort, and the arithmetic family of every arithmetic
    /// node (each carries a variable of that family's plug-in).
    pub(crate) fn families(&self, terms: &TermStore) -> Vec<Family> {
        let mut needed = Vec::new();
        for step in &self.steps {
            let (Step::Leaf(t) | Step::App(t)) = *step else {
                continue;
            };
            let sort = terms.sort(t);
            let family = if matches!(step, Step::App(_)) || sort.is_uninterpreted() {
                Some(Family::Uf)
            } else {
                None
            };
            for f in family.into_iter().chain(Family::of_arith_sort(sort)) {
                if !needed.contains(&f) {
                    needed.push(f);
                }
            }
        }
        needed
    }

    /// The terms the hub attaches to `family`'s plug-in: every leaf and
    /// application of its sort.
    pub(crate) fn shared(&self, terms: &TermStore, family: Family) -> Vec<TermId> {
        self.steps
            .iter()
            .filter_map(|step| match *step {
                Step::Leaf(t) | Step::App(t) => Some(t),
                Step::Eq(_) | Step::Arg(_) => None,
            })
            .filter(|&t| Family::of_arith_sort(terms.sort(t)) == Some(family))
            .collect()
    }
}

/// The sides of a binary equality over a non-Boolean sort.
fn watched_sides(terms: &TermStore, eq: TermId) -> Option<(TermId, TermId)> {
    let TermData::App(sym, args) = terms.get(eq) else {
        return None;
    };
    let mut it = args.iter();
    let (Some(&a), Some(&b), None) = (it.next(), it.next(), it.next()) else {
        return None;
    };
    (sym.name() == "=" && terms.sort(a) != &Sort::Bool).then_some((a, b))
}

/// Whether a leaf step names an application: the scan registers every
/// application, so one reaching the hub as a leaf is a registration bug.
pub(crate) fn unregistered_app(terms: &TermStore, step: Step) -> bool {
    matches!(step, Step::Leaf(t) if is_uf_app(terms, t))
}
