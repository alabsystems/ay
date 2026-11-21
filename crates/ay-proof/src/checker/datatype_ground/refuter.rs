// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Constant, Symbol, TermData, TermId, TermStore};

use super::super::datatype_axiom::{
    constructor_datatype, constructor_head, equality_sides, selector_field_index,
    tester_application, DatatypeDecls, SelectorDecls,
};
use super::cycle::has_cycle;
use super::resources::Control;

mod boolean;

const MAX_GROUND_NODES: usize = 4096;
const TRUE_NODE: u64 = 1 << 33;
const FALSE_NODE: u64 = (1 << 33) + 1;

/// Independent bounded congruence-closure and datatype refuter.
pub(super) struct GroundRefuter<'a> {
    terms: &'a TermStore,
    dt_decls: DatatypeDecls<'a>,
    ctor_selectors: SelectorDecls<'a>,
    parent: HashMap<u64, u64>,
    rank: HashMap<u64, u32>,
    universe: Vec<TermId>,
    diseqs: Vec<(u64, u64)>,
    eq_false_seen: HashSet<TermId>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
enum SigOp {
    App(Symbol),
    Not,
    Ite,
}

impl<'a> GroundRefuter<'a> {
    pub(super) fn new(
        terms: &'a TermStore,
        dt_decls: DatatypeDecls<'a>,
        ctor_selectors: SelectorDecls<'a>,
    ) -> Self {
        Self {
            terms,
            dt_decls,
            ctor_selectors,
            parent: HashMap::default(),
            rank: HashMap::default(),
            universe: Vec::new(),
            diseqs: Vec::new(),
            eq_false_seen: HashSet::default(),
        }
    }

    fn node(&self, term: TermId) -> u64 {
        if let TermData::Const(Constant::Bool(value)) = self.terms.get(term) {
            if *value {
                TRUE_NODE
            } else {
                FALSE_NODE
            }
        } else {
            u64::from(term.0)
        }
    }

    fn find(&mut self, mut node: u64) -> u64 {
        let mut root = node;
        while let Some(&parent) = self.parent.get(&root) {
            if parent == root {
                break;
            }
            root = parent;
        }
        while let Some(&parent) = self.parent.get(&node) {
            if parent == root || parent == node {
                break;
            }
            self.parent.insert(node, root);
            node = parent;
        }
        root
    }

    fn union(&mut self, first: u64, second: u64) -> bool {
        let (first_root, second_root) = (self.find(first), self.find(second));
        if first_root == second_root {
            return false;
        }
        let first_rank = *self.rank.get(&first_root).unwrap_or(&0);
        let second_rank = *self.rank.get(&second_root).unwrap_or(&0);
        let (child, root) = if first_rank < second_rank {
            (first_root, second_root)
        } else {
            (second_root, first_root)
        };
        self.parent.insert(child, root);
        if first_rank == second_rank {
            self.rank.insert(root, first_rank + 1);
        }
        true
    }

    pub(super) fn collect_universe(
        &mut self,
        atoms: &[TermId],
        control: &mut Control<'_>,
    ) -> Result<(), ()> {
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut pending = atoms.to_vec();
        while let Some(term) = pending.pop() {
            if !control.poll() {
                return Err(());
            }
            if !seen.insert(term) {
                continue;
            }
            if seen.len() > MAX_GROUND_NODES {
                return Err(());
            }
            self.universe.push(term);
            match self.terms.get(term) {
                TermData::App(_, args) => pending.extend(args.iter().copied()),
                TermData::Not(inner) => pending.push(*inner),
                TermData::Ite(condition, then_term, else_term) => {
                    pending.push(*condition);
                    pending.push(*then_term);
                    pending.push(*else_term);
                }
                TermData::Const(_) | TermData::Var(_, _) => {}
                _ => return Err(()),
            }
        }
        Ok(())
    }

    pub(super) fn assume(&mut self, term: TermId, polarity: bool) {
        let pole = if polarity { TRUE_NODE } else { FALSE_NODE };
        let node = self.node(term);
        self.union(node, pole);
        if let Some((first, second)) = equality_sides(self.terms, term) {
            let nodes = (self.node(first), self.node(second));
            if polarity {
                self.union(nodes.0, nodes.1);
            } else if self.eq_false_seen.insert(term) {
                self.diseqs.push(nodes);
            }
        }
    }

    pub(super) fn round(&mut self, changed: &mut bool, control: &mut Control<'_>) -> bool {
        self.close_congruence(changed, control);
        self.close_boolean_semantics(changed, control);
        let classes = self.classes(control);
        if self.close_datatype_structure(&classes, changed, control) {
            return true;
        }
        self.close_tester_evaluation(&classes, changed, control);
        self.close_selector_projection(&classes, changed, control);
        self.close_equality_clash(&classes, changed, control);
        self.has_tester_exclusivity(control)
            || self.has_direct_contradiction(control)
            || self.has_structural_cycle(&classes, control)
    }

    fn signature(&mut self, term: TermId, control: &mut Control<'_>) -> Option<(SigOp, Vec<u64>)> {
        match self.terms.get(term) {
            TermData::App(symbol, args) => {
                let symbol = symbol.clone();
                let args = args.clone();
                let mut children = Vec::with_capacity(args.len());
                for argument in args {
                    if !control.poll() {
                        return None;
                    }
                    let node = self.node(argument);
                    children.push(self.find(node));
                }
                Some((SigOp::App(symbol), children))
            }
            TermData::Not(inner) => {
                let node = self.node(*inner);
                Some((SigOp::Not, vec![self.find(node)]))
            }
            TermData::Ite(condition, then_term, else_term) => {
                let terms = [*condition, *then_term, *else_term];
                let children = terms
                    .into_iter()
                    .map(|term| {
                        let node = self.node(term);
                        self.find(node)
                    })
                    .collect();
                Some((SigOp::Ite, children))
            }
            _ => None,
        }
    }

    fn close_congruence(&mut self, changed: &mut bool, control: &mut Control<'_>) {
        let mut signatures: HashMap<(SigOp, Vec<u64>), u64> = HashMap::default();
        for index in 0..self.universe.len() {
            if !control.poll() {
                return;
            }
            let term = self.universe[index];
            let Some(signature) = self.signature(term, control) else {
                continue;
            };
            let node = self.node(term);
            if let Some(&other) = signatures.get(&signature) {
                *changed |= self.union(node, other);
            } else {
                signatures.insert(signature, node);
            }
        }
    }
    fn classes(&mut self, control: &mut Control<'_>) -> HashMap<u64, Vec<TermId>> {
        let mut classes: HashMap<u64, Vec<TermId>> = HashMap::default();
        for index in 0..self.universe.len() {
            if !control.poll() {
                return classes;
            }
            let term = self.universe[index];
            let node = self.node(term);
            let root = self.find(node);
            classes.entry(root).or_default().push(term);
        }
        classes
    }
    fn close_datatype_structure(
        &mut self,
        classes: &HashMap<u64, Vec<TermId>>,
        changed: &mut bool,
        control: &mut Control<'_>,
    ) -> bool {
        for members in classes.values() {
            if !control.poll() {
                return false;
            }
            let heads: Vec<(String, &str, TermId)> = members
                .iter()
                .filter_map(|&member| {
                    constructor_head(self.terms, self.dt_decls, member)
                        .map(|(constructor, datatype)| (constructor, datatype, member))
                })
                .collect();
            for first in 0..heads.len() {
                if !control.poll() {
                    return false;
                }
                for second in (first + 1)..heads.len() {
                    if !control.poll() {
                        return false;
                    }
                    let (first_ctor, first_dt, first_term) =
                        (&heads[first].0, heads[first].1, heads[first].2);
                    let (second_ctor, second_dt, second_term) =
                        (&heads[second].0, heads[second].1, heads[second].2);
                    if first_dt != second_dt {
                        continue;
                    }
                    if first_ctor != second_ctor {
                        return true;
                    }
                    let pairs = match (self.terms.get(first_term), self.terms.get(second_term)) {
                        (TermData::App(_, first_args), TermData::App(_, second_args))
                            if first_args.len() == second_args.len() =>
                        {
                            first_args
                                .iter()
                                .copied()
                                .zip(second_args.iter().copied())
                                .collect::<Vec<_>>()
                        }
                        _ => continue,
                    };
                    for (first_arg, second_arg) in pairs {
                        if !control.poll() {
                            return false;
                        }
                        let nodes = (self.node(first_arg), self.node(second_arg));
                        *changed |= self.union(nodes.0, nodes.1);
                    }
                }
            }
        }
        false
    }

    /// Falsify an equality atom whose two sides sit in classes with
    /// CLASHING registered constructor heads of the same datatype
    /// (#dt-context-derivation): distinct constructors build distinct
    /// values, so the equality is FALSE in every model. This is the
    /// cross-class complement of the in-class clash rule — the transition
    /// guards' skipped move-enum equalities die by exactly this inference
    /// once the taken move's enum fact is assumed.
    fn close_equality_clash(
        &mut self,
        classes: &HashMap<u64, Vec<TermId>>,
        changed: &mut bool,
        control: &mut Control<'_>,
    ) {
        let mut head_by_root: HashMap<u64, (String, String)> = HashMap::default();
        for (&root, members) in classes {
            if !control.poll() {
                return;
            }
            for &member in members {
                if !control.poll() {
                    return;
                }
                if let Some((constructor, datatype)) =
                    constructor_head(self.terms, self.dt_decls, member)
                {
                    head_by_root
                        .entry(root)
                        .or_insert_with(|| (constructor, datatype.to_string()));
                    break;
                }
            }
        }
        for index in 0..self.universe.len() {
            if !control.poll() {
                return;
            }
            let term = self.universe[index];
            let Some((first, second)) = equality_sides(self.terms, term) else {
                continue;
            };
            let first_node = self.node(first);
            let second_node = self.node(second);
            let first_root = self.find(first_node);
            let second_root = self.find(second_node);
            if first_root == second_root {
                continue;
            }
            let (Some((first_ctor, first_dt)), Some((second_ctor, second_dt))) = (
                head_by_root.get(&first_root),
                head_by_root.get(&second_root),
            ) else {
                continue;
            };
            if first_dt == second_dt && first_ctor != second_ctor {
                let node = self.node(term);
                *changed |= self.union(node, FALSE_NODE);
            }
        }
    }
    fn close_tester_evaluation(
        &mut self,
        classes: &HashMap<u64, Vec<TermId>>,
        changed: &mut bool,
        control: &mut Control<'_>,
    ) {
        for index in 0..self.universe.len() {
            if !control.poll() {
                return;
            }
            let term = self.universe[index];
            let Some((tester_ctor, subject)) = tester_application(self.terms, term) else {
                continue;
            };
            let tester_ctor = tester_ctor.to_string();
            let Some(tester_dt) = constructor_datatype(self.dt_decls, &tester_ctor) else {
                continue;
            };
            let tester_dt = tester_dt.to_string();
            let subject_node = self.node(subject);
            let subject_root = self.find(subject_node);
            let head = classes.get(&subject_root).and_then(|members| {
                members.iter().find_map(|&member| {
                    constructor_head(self.terms, self.dt_decls, member)
                        .filter(|(_, datatype)| *datatype == tester_dt)
                })
            });
            if let Some((head_ctor, _)) = head {
                let node = self.node(term);
                let pole = if head_ctor == tester_ctor {
                    TRUE_NODE
                } else {
                    FALSE_NODE
                };
                *changed |= self.union(node, pole);
            }
        }
    }
    fn close_selector_projection(
        &mut self,
        classes: &HashMap<u64, Vec<TermId>>,
        changed: &mut bool,
        control: &mut Control<'_>,
    ) {
        for index in 0..self.universe.len() {
            if !control.poll() {
                return;
            }
            let term = self.universe[index];
            let TermData::App(Symbol::Named(selector), args) = self.terms.get(term) else {
                continue;
            };
            let [subject] = args.as_slice() else {
                continue;
            };
            let (selector, subject) = (selector.clone(), *subject);
            let subject_node = self.node(subject);
            let subject_root = self.find(subject_node);
            let projected = classes.get(&subject_root).and_then(|members| {
                members.iter().find_map(|&member| {
                    let (constructor, _) = constructor_head(self.terms, self.dt_decls, member)?;
                    let field = selector_field_index(self.ctor_selectors, &constructor, &selector)?;
                    let (_, selectors) = self
                        .ctor_selectors
                        .iter()
                        .find(|(candidate, _)| *candidate == constructor)?;
                    match self.terms.get(member) {
                        TermData::App(_, ctor_args)
                            if ctor_args.len() == selectors.len() && field < ctor_args.len() =>
                        {
                            Some(ctor_args[field])
                        }
                        _ => None,
                    }
                })
            });
            if let Some(argument) = projected {
                let nodes = (self.node(term), self.node(argument));
                *changed |= self.union(nodes.0, nodes.1);
            }
        }
    }
    fn has_tester_exclusivity(&mut self, control: &mut Control<'_>) -> bool {
        let true_root = self.find(TRUE_NODE);
        let mut true_testers: Vec<(u64, String, String)> = Vec::new();
        for index in 0..self.universe.len() {
            if !control.poll() {
                return false;
            }
            let term = self.universe[index];
            let Some((constructor, subject)) = tester_application(self.terms, term) else {
                continue;
            };
            let constructor = constructor.to_string();
            let Some(datatype) = constructor_datatype(self.dt_decls, &constructor) else {
                continue;
            };
            let datatype = datatype.to_string();
            let node = self.node(term);
            if self.find(node) != true_root {
                continue;
            }
            let subject_node = self.node(subject);
            let subject_root = self.find(subject_node);
            if true_testers
                .iter()
                .any(|(other_root, other_ctor, other_dt)| {
                    *other_root == subject_root
                        && *other_dt == datatype
                        && *other_ctor != constructor
                })
            {
                return true;
            }
            true_testers.push((subject_root, constructor, datatype));
        }
        false
    }
    fn has_direct_contradiction(&mut self, control: &mut Control<'_>) -> bool {
        if self.find(TRUE_NODE) == self.find(FALSE_NODE) {
            return true;
        }
        for index in 0..self.diseqs.len() {
            if !control.poll() {
                return false;
            }
            let (first, second) = self.diseqs[index];
            if self.find(first) == self.find(second) {
                return true;
            }
        }
        false
    }

    pub(super) fn has_sequence_owned_cycle(
        &mut self,
        budget: &mut ay_core::proof_validation::OwnedSubvalueBudget,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<bool, super::ProofCheckError> {
        use ay_core::proof_validation::{
            owned_subvalue_cycle_with_progress, OwnedSubvalueConstructor,
        };
        let count = self
            .dt_decls
            .iter()
            .map(|(_, constructors)| constructors.len())
            .fold(0usize, usize::saturating_add);
        budget
            .charge_with_progress(
                self.dt_decls.len().saturating_add(count),
                count.saturating_mul(std::mem::size_of::<OwnedSubvalueConstructor<'_>>()),
                progress,
            )
            .map_err(|_| super::ProofCheckError::ResourceLimit)?;
        let mut constructors = Vec::new();
        constructors
            .try_reserve_exact(count)
            .map_err(|_| super::ProofCheckError::ResourceLimit)?;
        for (carrier, names) in self.dt_decls {
            budget
                .charge_with_progress(0, 0, progress)
                .map_err(|_| super::ProofCheckError::ResourceLimit)?;
            constructors.extend(
                names
                    .iter()
                    .map(|identity| OwnedSubvalueConstructor { identity, carrier }),
            );
        }
        // The callback mutates only the fresh checker's path-compression
        // state. Its facts were rebuilt from the negation of this exact clause.
        let universe = std::mem::take(&mut self.universe);
        let result = owned_subvalue_cycle_with_progress(
            self.terms,
            &constructors,
            &universe,
            &mut |term| {
                let node = self.node(term);
                let class = self.find(node);
                let truth = if class == self.find(TRUE_NODE) {
                    Some(true)
                } else if class == self.find(FALSE_NODE) {
                    Some(false)
                } else {
                    None
                };
                (class, truth)
            },
            budget,
            progress,
        )
        .map(|witness| witness.is_some())
        .map_err(|_| super::ProofCheckError::ResourceLimit);
        self.universe = universe;
        result
    }
    fn has_structural_cycle(
        &mut self,
        classes: &HashMap<u64, Vec<TermId>>,
        control: &mut Control<'_>,
    ) -> bool {
        let mut edges: HashMap<u64, Vec<u64>> = HashMap::default();
        let mut roots = Vec::new();
        for (&root, members) in classes {
            if !control.poll() {
                return false;
            }
            for &member in members {
                if !control.poll() {
                    return false;
                }
                if constructor_head(self.terms, self.dt_decls, member).is_none() {
                    continue;
                }
                let TermData::App(_, args) = self.terms.get(member) else {
                    continue;
                };
                let args = args.clone();
                for argument in args {
                    if !control.poll() {
                        return false;
                    }
                    let node = self.node(argument);
                    let argument_root = self.find(node);
                    edges.entry(root).or_default().push(argument_root);
                }
            }
            roots.push(root);
        }
        has_cycle(&edges, &roots, control)
    }
}
