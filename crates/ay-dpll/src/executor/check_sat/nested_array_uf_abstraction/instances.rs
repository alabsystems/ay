// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Building the axiom instances appended to `alpha(phi)`
//! (#nested-array-checked-rung).
//!
//! The pure renaming forgets every array and datatype axiom. This adds back a
//! bounded set of GROUND instances of those axioms, stated over the fresh
//! functions of the renaming witness:
//!
//! - selector over constructor: `(s_k' (C' x_1 .. x_n)) = x_k` for a renamed
//!   constructor application and every renamed selector of the same carrier
//!   whose name the store registers as `C`'s `k`-th field;
//! - read over write, at the written index: `(select' (store' a i v) i) = v`;
//! - read over write, at every other ground index `j` read or written at the
//!   same array sort: `(or (= i j) (= (select' (store' a i v) j) (select' a j)))`;
//! - read over constant: `(select' (const' v) j) = v` for every such `j`.
//!
//! Each holds in the structure a model of the original induces (fresh symbol
//! := the operation it renames), whatever its arguments denote, so adding it
//! keeps the abstraction an over-approximation. Nothing here is trusted:
//! [`super::check_instances::instances_are_valid`] re-derives every instance's
//! validity from the witness and the store before and after the refutation.
//!
//! Only instances whose functions the renaming already minted are built (an
//! instance over a function the problem never applies cannot take part in a
//! refutation), and only over ground images: subterms of the abstract roots
//! that mention no quantifier and no variable named by any binder, so no
//! instance can capture or release a bound variable. Past
//! [`MAX_AXIOM_INSTANCES`] the rung falls back to the pure renaming.

use super::build::{ArrayUfAbstraction, RenamingWitness, SymbolKey};
use super::*;
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{Sort, Symbol};

/// Cap on appended instances. The MODEL_CHECKER_CONSUMER record/Vec shapes this serves need
/// a handful; past the cap the pure renaming is refuted alone.
pub(super) const MAX_AXIOM_INSTANCES: usize = 256;

/// The fresh function a typed original operation was renamed to, inverted.
pub(super) fn preimages(witness: &RenamingWitness) -> HashMap<Symbol, SymbolKey> {
    witness
        .symbols
        .iter()
        .map(|(key, fresh)| (fresh.clone(), key.clone()))
        .collect()
}

/// The subterms of `roots` (quantifier bodies and triggers included) that
/// mention no quantifier and no variable whose name any quantifier in `roots`
/// binds. Post-order with an explicit stack, so each node is decided once
/// after its children: linear in the DAG, not in its tree unfolding.
///
/// Shared with the checker on purpose: groundness is hygiene, not the
/// soundness argument. Every instance is valid whatever its leaves denote; the
/// restriction only keeps a bound variable from also occurring free in a root.
pub(super) fn ground_images(terms: &TermStore, roots: &[TermId]) -> HashSet<TermId> {
    let mut binders = HashSet::default();
    let mut decided: HashMap<TermId, bool> = HashMap::default();
    let mut order = Vec::new();
    let mut stack: Vec<(TermId, bool)> = roots.iter().map(|&root| (root, false)).collect();
    while let Some((node, expanded)) = stack.pop() {
        if decided.contains_key(&node) {
            continue;
        }
        if expanded {
            decided.insert(node, false);
            order.push(node);
            continue;
        }
        stack.push((node, true));
        match terms.get(node) {
            TermData::App(_, args) => stack.extend(args.iter().map(|&arg| (arg, false))),
            TermData::Not(inner) => stack.push((*inner, false)),
            TermData::Ite(c, t, e) => stack.extend([(*c, false), (*t, false), (*e, false)]),
            TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                binders.extend(vars.iter().map(|(name, _)| name.as_str()));
                stack.push((*body, false));
                stack.extend(triggers.iter().flatten().map(|&pattern| (pattern, false)));
            }
            _ => {}
        }
    }
    // `order` is post-order, so every child is decided before its parent.
    for &node in &order {
        let ground = |child: &TermId| decided.get(child).copied().unwrap_or(false);
        let is_ground = match terms.get(node) {
            TermData::Const(_) => true,
            TermData::Var(name, _) => !binders.contains(name.as_str()),
            TermData::App(_, args) => args.iter().all(ground),
            TermData::Not(inner) => ground(inner),
            TermData::Ite(c, t, e) => [c, t, e].into_iter().all(ground),
            _ => false,
        };
        decided.insert(node, is_ground);
    }
    decided
        .into_iter()
        .filter_map(|(node, ground)| ground.then_some(node))
        .collect()
}

/// The instances for `abstraction`, or none when they would exceed the cap.
pub(super) fn axiom_instances(
    terms: &mut TermStore,
    abstraction: &ArrayUfAbstraction,
) -> Box<[TermId]> {
    let preimage = preimages(&abstraction.witness);
    let mut renamed_apps: Vec<TermId> = ground_images(terms, abstraction.roots())
        .into_iter()
        .filter(|&node| matches!(terms.get(node), TermData::App(head, _) if preimage.contains_key(head)))
        .collect();
    renamed_apps.sort_unstable();
    let mut builder = InstanceBuilder {
        witness: &abstraction.witness,
        indices: HashMap::default(),
        noted: HashSet::default(),
        out: Vec::new(),
    };
    for &app in &renamed_apps {
        let TermData::App(head, args) = terms.get(app) else {
            continue;
        };
        let Some((symbol, result, arg_sorts)) = preimage.get(head) else {
            continue;
        };
        match (symbol.name(), args.as_slice(), arg_sorts.as_slice()) {
            ("select", &[_, index], [array, _]) => builder.note_index(array, index),
            ("store", &[_, index, _], _) => builder.note_index(result, index),
            _ => {}
        }
    }
    for &app in &renamed_apps {
        let TermData::App(head, args) = terms.get(app).clone() else {
            continue;
        };
        let Some((symbol, result, arg_sorts)) = preimage.get(&head) else {
            continue;
        };
        match (symbol.name(), args.as_slice()) {
            ("store", &[base, index, value]) => {
                builder.write(terms, result, app, base, index, value);
            }
            ("const-array", &[value]) => builder.constant(terms, result, app, value),
            (name, _) => builder.constructor(terms, name, result, arg_sorts, app, &args),
        }
        if builder.is_over_cap() {
            return Box::default();
        }
    }
    builder.out.into_boxed_slice()
}

/// Linear in the ground DAG plus [`MAX_AXIOM_INSTANCES`]: an index is noted
/// in O(1), and each loop that emits an instance per noted index stops as
/// soon as the cap is exceeded, so an overflowing problem interns at most one
/// instance past the cap before the rung falls back to the pure renaming.
struct InstanceBuilder<'a> {
    witness: &'a RenamingWitness,
    /// Ground index images read or written, keyed by the ORIGINAL array sort,
    /// each list in first-noted order.
    indices: HashMap<Sort, Vec<TermId>>,
    /// The `(array sort, index)` pairs already listed in `indices`.
    noted: HashSet<(Sort, TermId)>,
    out: Vec<TermId>,
}

impl InstanceBuilder<'_> {
    fn note_index(&mut self, array: &Sort, index: TermId) {
        if self.noted.insert((array.clone(), index)) {
            self.indices.entry(array.clone()).or_default().push(index);
        }
    }

    fn is_over_cap(&self) -> bool {
        self.out.len() > MAX_AXIOM_INSTANCES
    }

    /// The fresh `select` at the original array sort `array`, if the
    /// renaming minted one, with its image result sort.
    fn reader(&self, terms: &TermStore, array: &Sort) -> Option<(Symbol, Sort)> {
        let (index, element) = (array.array_index()?, array.array_element()?);
        let key = (
            Symbol::named("select"),
            element.clone(),
            vec![array.clone(), index.clone()],
        );
        let fresh = self.witness.symbols.get(&key)?.clone();
        Some((fresh, self.witness.mapped_sort(terms, element)?))
    }

    fn indices_at(&self, array: &Sort) -> Vec<TermId> {
        let at = self.indices.get(array).map_or(&[][..], Vec::as_slice);
        at.iter().take(MAX_AXIOM_INSTANCES + 1).copied().collect()
    }

    fn write(
        &mut self,
        terms: &mut TermStore,
        array: &Sort,
        write: TermId,
        base: TermId,
        index: TermId,
        value: TermId,
    ) {
        let Some((select, element)) = self.reader(terms, array) else {
            return;
        };
        let hit = terms.mk_app(select.clone(), [write, index], element.clone());
        self.out.push(equality(terms, hit, value));
        for other in self.indices_at(array) {
            if self.is_over_cap() {
                return;
            }
            if other == index {
                continue;
            }
            let same = equality(terms, index, other);
            let read = terms.mk_app(select.clone(), [write, other], element.clone());
            let below = terms.mk_app(select.clone(), [base, other], element.clone());
            let differ = equality(terms, read, below);
            let miss = terms.mk_app(Symbol::named("or"), [same, differ], Sort::Bool);
            self.out.push(miss);
        }
    }

    fn constant(&mut self, terms: &mut TermStore, array: &Sort, constant: TermId, value: TermId) {
        let Some((select, element)) = self.reader(terms, array) else {
            return;
        };
        for index in self.indices_at(array) {
            if self.is_over_cap() {
                return;
            }
            let read = terms.mk_app(select.clone(), [constant, index], element.clone());
            self.out.push(equality(terms, read, value));
        }
    }

    /// Selector-over-constructor instances when `name` is a registered
    /// constructor of the carrier `carrier`; nothing otherwise.
    fn constructor(
        &mut self,
        terms: &mut TermStore,
        name: &str,
        carrier: &Sort,
        field_sorts: &[Sort],
        application: TermId,
        args: &[TermId],
    ) {
        let Some(fields) = terms.constructor_field_names(name).map(<[String]>::to_vec) else {
            return;
        };
        if fields.len() != args.len() || fields.len() != field_sorts.len() {
            return;
        }
        for ((field, field_sort), &arg) in fields.iter().zip(field_sorts).zip(args) {
            let key = (
                Symbol::named(field.as_str()),
                field_sort.clone(),
                vec![carrier.clone()],
            );
            let Some(selector) = self.witness.symbols.get(&key).cloned() else {
                continue;
            };
            let arg_sort = terms.sort(arg).clone();
            let projected = terms.mk_app(selector, [application], arg_sort);
            self.out.push(equality(terms, projected, arg));
        }
    }
}

/// `(= lhs rhs)` in the TermId order `mk_eq` interns (the only orientation
/// the solver's equality-atom lookups find), through the RAW constructor so
/// nothing is folded away. The checker accepts either orientation.
fn equality(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    let args = if lhs < rhs { [lhs, rhs] } else { [rhs, lhs] };
    terms.mk_app(Symbol::named("="), args, Sort::Bool)
}
