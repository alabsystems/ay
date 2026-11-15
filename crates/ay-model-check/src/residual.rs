// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Residual joint-satisfiability decision for FREE datatype-element arrays
//! (#free-dt-array-residual).
//!
//! ## The gap this closes
//!
//! A `Sat` model over a datatype-carrying array problem can leave some array
//! leaves genuinely UNPINNED ("free"): the model-checker-consumer arrays-of-structs /
//! `Vec<Struct>` VCs constrain their backing/input arrays only by mutual
//! aliasing `(= a b)` and element reads `(= scalar (fld (select a i)))`. The
//! independent gate cannot resolve such a leaf to a concrete value (there is
//! nothing to resolve it TO), so every assertion touching it is `Unevaluable`
//! and [`crate::confirm_model`] fails closed — converting a whole CLASS of
//! valid `sat` answers into `unknown` (the g4 "Site-3" wall).
//!
//! ## The decision
//!
//! When the ONLY unevaluable residue consists of constraints over free
//! datatype-element array variables of exactly two shapes —
//!
//! * alias equalities `(= a b)` between two free array variables, and
//! * ground element reads `(= <ground> (select a i))` or bounded named
//!   selector paths over that read, whose index and ground side evaluate
//!   under the fixed partial model —
//!
//! then union-find the alias classes and collect, per class, the
//! `(index-value, slot) -> value` REQUIREMENTS from the residue plus the
//! PINNED reads over class members the evaluator did resolve (see below). The
//! requirements must agree at every `(class, index, field-path)` slot.
//! Whole-element and ancestor values are reconciled with descendant values
//! by exact constructor projection, and each node must fit one real declared
//! constructor. Bounded synthesis can still refuse a satisfiable requirement.
//! The decision then MATERIALIZES that proof as one bounded
//! `(default, finite-store)` value per alias class, overlays those values on
//! every class member, and runs the ordinary independent model checker again
//! with residual admission disabled. `ConfirmedSat` is returned only when the
//! fresh replay computes every original assertion to `Bool(true)`; otherwise
//! the blanket `CannotConfirm` stands.
//!
//! ## Soundness argument (why `true` here cannot fabricate a `sat`)
//!
//! This decision runs only after the main scan proved every non-residual
//! assertion `Bool(true)` (or a model-independent tautology) under the pinned
//! partial model. An assertion the evaluator computed `true` used ONLY (a)
//! model-pinned leaf values and (b) committed application pins adopted into
//! the evaluator's `uf_graph` / `select_graph`; its truth is therefore
//! preserved by ANY assignment of values to leaves whose computed term
//! values it did not change. The only pin sites that can commit a value for
//! a term DEPENDING on a free array without evaluating it are `select` reads
//! (`eval_select_via_model`) and selector-shaped unary applications
//! (`eval_selector_via_model`); the walk below enumerates every such site
//! over the classes and either LOCALIZES its committed value into the
//! per-(class, index, slot) entry map (direct `select`/selector-chain reads)
//! or refuses. Explicit extension: give every member of an alias class the
//! SAME array value, whose element at each constrained index-value is the
//! whole-element entry if present, else a fitting constructor applied to the
//! field entries with the remaining fields filled by bounded canonical
//! inhabitants. Its default is another bounded canonical datatype inhabitant.
//! Every residual alias then holds
//! (identical values), every residual read holds (selector projection of a
//! matching constructor), every pinned read keeps its committed value
//! (entry-consistency was checked), and every previously-true assertion
//! keeps its computed truth. The FRESH replay checks those claims rather than
//! relying on this argument alone. Hence the formula is satisfiable and
//! `ConfirmedSat` is correct. The map is `Sat -> {Sat, Unknown}` only: a
//! failure from any construction or replay check keeps today's fail-closed
//! verdict.
//!
//! Committed pins are never TRUSTED to discharge residue: a residual
//! requirement is discharged only by consistency of the FORMULA's own ground
//! values, and a pin can only cause additional refusal (or coincide). This
//! preserves the Site-3 hard constraint — the solver's committed
//! store-chains/values for free arrays are cross-validated, never adopted
//! as evidence on their own.
//!
//! ## Fail-closed guards (each `false` = keep `CannotConfirm`)
//!
//! 1. Any residual assertion beyond the two shapes above (disequalities,
//!    stores, testers, read-vs-read equalities, quantifiers, ...) refuses.
//!    Boolean structure is admitted only conservatively: `and` over
//!    classified conjuncts; `or` where some disjunct classifies and every
//!    other disjunct is concretely `false` or ignorable (an `or` is true as
//!    soon as the classified disjunct is made true); `=>` with every
//!    antecedent concretely `true`.
//! 2. OCCURRENCE GUARD: a class member may occur in the assertion DAG only
//!    as the array operand of a `select` or as a side of one of the
//!    classified alias equalities. Any other occurrence (inside a `store`,
//!    an `ite` branch, a UF argument, a non-classified equality, ...)
//!    refuses — those contexts could constrain the array in ways this
//!    fragment does not model.
//! 3. PIN LOCALIZATION: every `select` over a class member and every
//!    selector-shaped unary application whose argument depends on a class
//!    member is probed AFTER classification (the evaluator's pin graphs only
//!    grow and computed values are stable, so a probe seen `Unevaluable` at
//!    the end proves no pin over that term was ever consulted). A probe that
//!    yields a value is localized into the entry map when the term is a
//!    `(select m i)` or authenticated selector path with an evaluable index,
//!    including every committed ancestor prefix, and refuses otherwise.
//! 4. The witness is local to this PROVED residual fragment. It never adopts
//!    the solver's canonical const-array or committed store chain (the former
//!    was proven unsound on `qf_abv_incremental_false_unsat`). Defaults and
//!    unconstrained fields are synthesized from the DECLARED sorts under hard
//!    depth/work bounds, and every synthesized array is replayed through a
//!    fresh evaluator before it has any authority.
//! 5. Classification, occurrence traversal, alias members, entries, semantic
//!    index comparisons, and witness synthesis all have explicit hard bounds.
//!    Exhaustion is `CannotConfirm`, never a partial witness.

use std::collections::{HashMap, HashSet};

use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};

use crate::dt_axiom::DtResolve;
use crate::{is_datatype_tautology_with, EvalOutcome, Evaluator, ModelValue, ModelView};

mod path;
mod witness;
pub(super) use witness::MAX_WITNESS_ENTRIES;
#[cfg(test)]
pub(super) use witness::MAX_WITNESS_VALUE_WORK;
use witness::{account_entry_values, materialize_and_replay, AccessStep, Entry, Slot};
pub use witness::{ArrayCompletion, CompletedArrayAssignment, ModelConfirmation};

/// Recursion bound for the residual-constraint classifier (top-level Boolean
/// structure only; residual assertions are shallow in practice).
pub(super) const MAX_CLASSIFY_DEPTH: usize = 64;

/// Maximum total immediate-argument work admitted by residual classification.
///
/// This bounds both traversal and the temporary argument snapshots needed to
/// recurse without borrowing the term store through a mutable classifier call.
pub(super) const MAX_CLASSIFY_WORK: usize = 16_384;

/// Maximum alias edges admitted by one residual witness.
pub(super) const MAX_WITNESS_ALIASES: usize = 512;

/// Maximum free array leaves completed by one residual witness.
pub(super) const MAX_WITNESS_MEMBERS: usize = 256;

/// Maximum assertion-DAG nodes inspected by the occurrence guard.
pub(super) const MAX_OCCURRENCE_NODES: usize = 16_384;

/// Decide whether the unevaluable `residue` is exactly the free-datatype-array
/// fragment AND jointly satisfiable. Retain the exact replayed extension;
/// `None` keeps the fail-closed `CannotConfirm` outcome.
pub(crate) fn free_dt_array_residue_extends<'a>(
    terms: &'a TermStore,
    model: &'a dyn ModelView,
    ev: &Evaluator<'_>,
    assertions: &'a [TermId],
    residue: &[TermId],
    resolve: &DtResolve<'_>,
) -> Option<ArrayCompletion<'a>> {
    let mut cx = Classifier {
        terms,
        model,
        ev,
        resolve,
        aliases: Vec::new(),
        alias_eq_terms: Vec::new(),
        entries: Vec::new(),
        classify_work: 0,
        witness_value_work: 0,
    };
    for &a in residue {
        if !cx.classify(a, 0) {
            return None;
        }
    }
    if cx.aliases.is_empty() && cx.entries.is_empty() {
        // Nothing was classified (e.g. every residual assertion meanwhile
        // re-evaluated `true`): not the free-dt-array fragment — keep today's
        // fail-closed behaviour rather than widen the gate's contract.
        return None;
    }
    let alias_eqs: HashSet<TermId> = cx.alias_eq_terms.iter().copied().collect();

    // Union-find the alias classes (each recorded edge is between two free
    // array variables of the SAME sort, checked at classification).
    let mut uf: HashMap<TermId, TermId> = HashMap::new();
    let mut members: HashSet<TermId> = HashSet::new();
    for &(l, r) in &cx.aliases {
        if members.insert(l) && members.len() > MAX_WITNESS_MEMBERS {
            return None;
        }
        if members.insert(r) && members.len() > MAX_WITNESS_MEMBERS {
            return None;
        }
        union(&mut uf, l, r);
    }
    for e in &cx.entries {
        if members.insert(e.array) && members.len() > MAX_WITNESS_MEMBERS {
            return None;
        }
    }

    // Occurrence guard over the whole assertion DAG, including quantified bodies, and
    // collection of every pin SITE over the classes.
    let mut select_sites: Vec<TermId> = Vec::new();
    // Every prefix is retained separately, including pinned ancestor values.
    let mut chain_sites: Vec<(TermId, TermId, TermId, Slot)> = Vec::new();
    let mut other_read_sites: Vec<TermId> = Vec::new();
    let mut store_edges = path::StoreEdges::default();
    let mut contains_memo: HashMap<TermId, bool> = HashMap::new();
    if assertions.len() > MAX_OCCURRENCE_NODES {
        return None;
    }
    let mut stack: Vec<TermId> = assertions.to_vec();
    let mut seen: HashSet<TermId> = HashSet::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if seen.len() > MAX_OCCURRENCE_NODES {
            return None;
        }
        match terms.get(t) {
            TermData::App(sym, args) => {
                if !pending_nodes_fit(seen.len(), stack.len(), args.len(), MAX_OCCURRENCE_NODES) {
                    return None;
                }
                let is_select = matches!(sym, Symbol::Named(name) if name == "select")
                    && !terms.is_declared_function("select")
                    && args.len() == 2;
                let blessed_eq = alias_eqs.contains(&t);
                if is_select && members.contains(&args[0]) {
                    select_sites.push(t);
                } else if is_select && contains_member(terms, t, &members, &mut contains_memo)? {
                    // Nested selects have the same committed per-read fallback
                    // as direct reads. Preserve every such pin, including reads
                    // in already-true assertions and unselected Boolean arms.
                    match cx.parse_read_with_stores(t) {
                        Some(read) if members.contains(&read.array) => {
                            store_edges.admit(read.store_edges, &mut cx)?;
                            chain_sites.push((t, read.array, read.index, read.slot));
                        }
                        _ => other_read_sites.push(t),
                    }
                }
                // Selector-shaped unary application whose argument depends on
                // a member: the ONE pin site that can commit a value without
                // evaluating its argument (`eval_selector_via_model`).
                if let (Symbol::Named(name), [arg]) = (sym, args.as_slice()) {
                    let Some(contains) = contains_member(terms, *arg, &members, &mut contains_memo)
                    else {
                        return None;
                    };
                    if contains {
                        let Some(selector_shaped) = cx.selector_shaped(name, *arg) else {
                            return None;
                        };
                        if selector_shaped {
                            match cx.parse_read_with_stores(t) {
                                Some(read) if members.contains(&read.array) => {
                                    store_edges.admit(read.store_edges, &mut cx)?;
                                    chain_sites.push((t, read.array, read.index, read.slot));
                                }
                                _ => other_read_sites.push(t),
                            }
                        }
                    }
                }
                // Authenticate a consuming read before descending into its
                // missed stores. Check EVERY incoming use even for seen DAG
                // children, so one valid miss never blesses a store equation.
                for (pos, &child) in args.iter().enumerate() {
                    let allowed_store_edge = store_edges.permits(t, child, pos);
                    if members.contains(&child)
                        && !((is_select && pos == 0) || blessed_eq || allowed_store_edge)
                    {
                        return None;
                    }
                    if path::is_store(terms, child)
                        && contains_member(terms, child, &members, &mut contains_memo)?
                        && !allowed_store_edge
                    {
                        return None;
                    }
                }
                stack.extend(args.iter().copied());
            }
            // Finite quantifier bodies now evaluate in the gate and may
            // constrain this extension. The generic walk includes their bodies
            // (but not solver-search triggers), conservatively retaining pins.
            data => {
                let Some(child_count) = term_child_count(data) else {
                    return None;
                };
                if !pending_nodes_fit(seen.len(), stack.len(), child_count, MAX_OCCURRENCE_NODES) {
                    return None;
                }
                let mut escaped = false;
                if for_each_term_child(data, |c| {
                    if members.contains(&c)
                        || (path::is_store(terms, c)
                            && contains_member(terms, c, &members, &mut contains_memo)
                                != Some(false))
                    {
                        escaped = true;
                    }
                    stack.push(c);
                })
                .is_none()
                {
                    return None;
                }
                if escaped {
                    return None; // member under a non-App context (ite/not/let)
                }
            }
        }
    }

    if cx.classify_work > MAX_CLASSIFY_WORK {
        return None; // an exhausted selector census must never hide a pin
    }
    // Probe every pin site LAST (final pin-graph state). A resolvable direct
    // read is LOCALIZED as an entry; anything else resolvable refuses.
    for t in select_sites {
        let TermData::App(_, args) = terms.get(t) else {
            return None; // unreachable by construction
        };
        let (arr, idx_term) = (args[0], args[1]);
        if let EvalOutcome::Value(v) = ev.evaluate(t) {
            let EvalOutcome::Value(index) = ev.evaluate(idx_term) else {
                return None; // pinned read at an unkeyable index
            };
            let Sort::Array(array_sort) = terms.sort(arr) else {
                return None;
            };
            if terms.sort(idx_term) != &array_sort.index_sort
                || terms.sort(t) != &array_sort.element_sort
                || ev
                    .ensure_value_inhabits_sort(&index, &array_sort.index_sort)
                    .is_err()
                || ev
                    .ensure_value_inhabits_sort(&v, &array_sort.element_sort)
                    .is_err()
            {
                return None;
            }
            if !cx.push_entry(Entry {
                array: arr,
                index,
                slot: Slot::Whole,
                value: v,
            }) {
                return None;
            }
        }
    }
    for (t, m, idx_term, slot) in chain_sites {
        if let EvalOutcome::Value(v) = ev.evaluate(t) {
            let EvalOutcome::Value(index) = ev.evaluate(idx_term) else {
                return None; // pinned field read at an unkeyable index
            };
            let Sort::Array(array_sort) = terms.sort(m) else {
                return None;
            };
            if terms.sort(idx_term) != &array_sort.index_sort
                || ev
                    .ensure_value_inhabits_sort(&index, &array_sort.index_sort)
                    .is_err()
                || ev.ensure_value_inhabits_sort(&v, terms.sort(t)).is_err()
            {
                return None;
            }
            if !cx.push_entry(Entry {
                array: m,
                index,
                slot,
                value: v,
            }) {
                return None;
            }
        }
    }
    for t in other_read_sites {
        if matches!(ev.evaluate(t), EvalOutcome::Value(_)) {
            return None; // committed pin that cannot be localized
        }
    }

    let mut member_roots: HashMap<TermId, TermId> = HashMap::new();
    for &member in &members {
        let root = find(&mut uf, member);
        member_roots.insert(member, root);
    }
    materialize_and_replay(
        terms,
        model,
        ev,
        assertions,
        resolve,
        member_roots,
        std::mem::take(&mut cx.entries),
        cx.witness_value_work,
    )
}

/// Classification state: the alias edges, the classified alias-equality terms
/// (with separately authenticated store-miss receiver edges), and the entry map
/// (requirements now; pinned reads are appended by the probe phase).
struct Classifier<'a> {
    terms: &'a TermStore,
    model: &'a dyn ModelView,
    ev: &'a Evaluator<'a>,
    resolve: &'a DtResolve<'a>,
    aliases: Vec<(TermId, TermId)>,
    alias_eq_terms: Vec<TermId>,
    entries: Vec<Entry>,
    classify_work: usize,
    witness_value_work: usize,
}

impl<'a> Classifier<'a> {
    fn spend_classify_work(&mut self, amount: usize) -> bool {
        let Some(next) = self.classify_work.checked_add(amount) else {
            self.classify_work = MAX_CLASSIFY_WORK + 1;
            return false;
        };
        if next > MAX_CLASSIFY_WORK {
            self.classify_work = MAX_CLASSIFY_WORK + 1;
            return false;
        }
        self.classify_work = next;
        true
    }

    fn push_alias(&mut self, equality: TermId, left: TermId, right: TermId) -> bool {
        if self.aliases.len() >= MAX_WITNESS_ALIASES {
            return false;
        }
        self.aliases.push((left, right));
        self.alias_eq_terms.push(equality);
        true
    }

    fn push_entry(&mut self, entry: Entry) -> bool {
        if self.entries.len() >= MAX_WITNESS_ENTRIES {
            return false;
        }
        if !account_entry_values(
            &mut self.witness_value_work,
            &entry.index,
            &entry.value,
            &entry.slot,
        ) {
            return false;
        }
        self.entries.push(entry);
        true
    }

    /// Classify one residual assertion/conjunct. `true` = admitted (either
    /// satisfied by the pinned partial model or recorded as an allowed
    /// free-dt-array constraint); `false` = refuse the whole decision.
    fn classify(&mut self, t: TermId, depth: usize) -> bool {
        if depth > MAX_CLASSIFY_DEPTH || !self.spend_classify_work(1) {
            return false;
        }
        let app_header = match self.terms.get(t) {
            TermData::App(sym, args) => Some((sym.name().to_string(), args.len())),
            _ => None,
        };
        if app_header
            .as_ref()
            .is_some_and(|(_, argument_count)| !self.spend_classify_work(*argument_count))
        {
            return false;
        }
        // A term that meanwhile evaluates `true` needs no residual constraint;
        // one that evaluates `false`/non-Bool refuses (never confirm over a
        // computed refutation). A model-independent tautology holds in every
        // model, including every extension.
        match self.ev.evaluate(t) {
            EvalOutcome::Value(ModelValue::Bool(true)) => return true,
            EvalOutcome::Value(_) => return false,
            EvalOutcome::Unevaluable(_) => {}
        }
        if is_datatype_tautology_with(self.terms, t, self.resolve) {
            return true;
        }
        let Some((name, _)) = app_header else {
            return false;
        };
        let args = match self.terms.get(t) {
            TermData::App(_, args) => args.clone(),
            _ => return false,
        };
        match name.as_str() {
            "and" => args.iter().all(|&c| self.classify(c, depth + 1)),
            // `or`: satisfied outright if some disjunct is concretely true;
            // otherwise ONE unevaluable disjunct is classified (the extension
            // makes it true, which makes the `or` true REGARDLESS of the other
            // disjuncts — their truth is not needed, and any of their member
            // reads still pass through the occurrence guard and pin probes).
            // A disjunct trial that fails is rolled back and the next tried.
            "or" => {
                let mut open: Vec<TermId> = Vec::new();
                for &d in &args {
                    match self.ev.evaluate(d) {
                        EvalOutcome::Value(ModelValue::Bool(true)) => return true,
                        EvalOutcome::Value(ModelValue::Bool(false)) => {}
                        EvalOutcome::Value(_) => return false,
                        EvalOutcome::Unevaluable(_) => open.push(d),
                    }
                }
                for d in open {
                    let snap = (
                        self.aliases.len(),
                        self.alias_eq_terms.len(),
                        self.entries.len(),
                        self.witness_value_work,
                    );
                    if self.classify(d, depth + 1) {
                        return true;
                    }
                    self.aliases.truncate(snap.0);
                    self.alias_eq_terms.truncate(snap.1);
                    self.entries.truncate(snap.2);
                    self.witness_value_work = snap.3;
                }
                false
            }
            // `=>`: admissible only when every antecedent concretely evaluates
            // `true` (then the implication reduces to its consequent).
            "=>" if args.len() >= 2 => {
                let (last, init) = args.split_last().expect("len >= 2");
                for &p in init {
                    match self.ev.evaluate(p) {
                        EvalOutcome::Value(ModelValue::Bool(false)) => return true,
                        EvalOutcome::Value(ModelValue::Bool(true)) => {}
                        _ => return false,
                    }
                }
                self.classify(*last, depth + 1)
            }
            "=" if args.len() == 2 => self.classify_eq(t, args[0], args[1]),
            _ => false,
        }
    }

    /// Classify an unevaluable binary equality: a free-array alias or a ground
    /// element read. Anything else refuses.
    fn classify_eq(&mut self, t: TermId, l: TermId, r: TermId) -> bool {
        // Alias `(= a b)`: both sides free array variables of the same sort.
        if let (Some(sl), Some(sr)) = (self.free_dt_array_var(l), self.free_dt_array_var(r)) {
            if sl != sr {
                return false;
            }
            if l != r {
                return self.push_alias(t, l, r);
            }
            return true;
        }
        // Element read: one side a free read chain, the other ground.
        for (read_side, ground_side) in [(l, r), (r, l)] {
            let Some((array, idx_term, slot)) = self.parse_free_read(read_side) else {
                continue;
            };
            // The read must be genuinely unresolvable at this point — a read
            // the model commits a value for is folded in by the probe phase,
            // not here (and would have made the equality evaluable anyway).
            if matches!(self.ev.evaluate(read_side), EvalOutcome::Value(_)) {
                return false;
            }
            let EvalOutcome::Value(index) = self.ev.evaluate(idx_term) else {
                return false;
            };
            let EvalOutcome::Value(value) = self.ev.evaluate(ground_side) else {
                return false;
            };
            let read_sort = self.terms.sort(read_side);
            if !path::metadata::sort_work(self.terms.sort(ground_side), 0, &mut |n| {
                self.spend_classify_work(n)
            }) {
                return false;
            }
            if read_sort != self.terms.sort(ground_side)
                || self
                    .ev
                    .ensure_value_inhabits_sort(&index, self.terms.sort(idx_term))
                    .is_err()
                || self
                    .ev
                    .ensure_value_inhabits_sort(&value, read_sort)
                    .is_err()
            {
                return false;
            }
            return self.push_entry(Entry {
                array,
                index,
                slot,
                value,
            });
        }
        false
    }

    /// `t` as a FREE datatype-element array variable: a `Var` leaf of sort
    /// `(Array _ DT)` the model does not pin. Returns its sort.
    fn free_dt_array_var(&mut self, t: TermId) -> Option<&'a Sort> {
        if !matches!(self.terms.get(t), TermData::Var(_, _)) {
            return None;
        }
        let sort = self.terms.sort(t);
        if !path::metadata::sort_work(sort, 0, &mut |n| self.spend_classify_work(n)) {
            return None;
        }
        let Sort::Array(arr) = sort else {
            return None;
        };
        if !matches!(&arr.element_sort, Sort::Datatype(_)) {
            path::metadata::datatype(&arr.element_sort, self.resolve, &mut |n| {
                self.spend_classify_work(n)
            })?;
        }
        if self.model.leaf_value(t).is_some() {
            return None; // pinned ⇒ not free ⇒ out of this fragment
        }
        Some(sort)
    }

    /// Whether `(name arg)` is selector-shaped: `arg` is datatype-sorted and
    /// `name` is a field of that datatype — the exact precondition of the
    /// evaluator's `eval_selector_via_model` pin site.
    fn selector_shaped(&mut self, name: &str, arg: TermId) -> Option<bool> {
        let Some(dt) =
            path::metadata::datatype_shape(self.terms.sort(arg), self.resolve, &mut |n| {
                self.spend_classify_work(n)
            })?
        else {
            return Some(false);
        };
        Some(
            dt.constructors
                .iter()
                .any(|c| c.fields.iter().any(|f| f.name == name)),
        )
    }
}

/// Visit immediate term children without cloning an application or let vector.
///
/// `TermData` is non-exhaustive across the crate boundary. An unknown future
/// variant returns `None`, so this proof-oriented path fails closed until its
/// child semantics are reviewed explicitly.
pub(crate) fn for_each_term_child(data: &TermData, mut visit: impl FnMut(TermId)) -> Option<()> {
    match data {
        TermData::Const(_) | TermData::Var(_, _) => {}
        TermData::App(_, arguments) => {
            for &argument in arguments {
                visit(argument);
            }
        }
        TermData::Let(bindings, body) => {
            for (_, value) in bindings {
                visit(*value);
            }
            visit(*body);
        }
        TermData::Not(argument) => visit(*argument),
        TermData::Ite(condition, then_term, else_term) => {
            visit(*condition);
            visit(*then_term);
            visit(*else_term);
        }
        TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => visit(*body),
        _ => return None,
    }
    Some(())
}

pub(crate) fn term_child_count(data: &TermData) -> Option<usize> {
    match data {
        TermData::Const(_) | TermData::Var(_, _) => Some(0),
        TermData::App(_, arguments) => Some(arguments.len()),
        TermData::Let(bindings, _) => bindings.len().checked_add(1),
        TermData::Not(_) | TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => Some(1),
        TermData::Ite(_, _, _) => Some(3),
        _ => None,
    }
}

fn pending_nodes_fit(seen: usize, pending: usize, additional: usize, maximum: usize) -> bool {
    seen.checked_add(pending)
        .and_then(|count| count.checked_add(additional))
        .is_some_and(|count| count <= maximum)
}

/// Whether `t`'s subtree mentions a class member (memoized, iterative — no
/// native-stack recursion; quantifier bodies included, since over-approximating
/// containment is only ever conservative here).
fn contains_member(
    terms: &TermStore,
    t: TermId,
    members: &HashSet<TermId>,
    memo: &mut HashMap<TermId, bool>,
) -> Option<bool> {
    contains_member_bounded(terms, t, members, memo, MAX_OCCURRENCE_NODES)
}

/// Bounded implementation of [`contains_member`]. The memoized nodes and
/// pending post-order frames share one checked budget: a hostile wide term
/// must not enqueue an unbounded child list before the memo-size guard can
/// observe it.
fn contains_member_bounded(
    terms: &TermStore,
    t: TermId,
    members: &HashSet<TermId>,
    memo: &mut HashMap<TermId, bool>,
    max_nodes: usize,
) -> Option<bool> {
    if let Some(&cached) = memo.get(&t) {
        return Some(cached);
    }
    if memo.len().checked_add(1)? > max_nodes {
        return None;
    }
    // Explicit post-order: (node, children_expanded).
    let mut stack: Vec<(TermId, bool)> = vec![(t, false)];
    while let Some((cur, expanded)) = stack.pop() {
        if memo.contains_key(&cur) {
            continue;
        }
        if members.contains(&cur) {
            if memo.len().checked_add(stack.len())?.checked_add(1)? > max_nodes {
                return None;
            }
            memo.insert(cur, true);
            continue;
        }
        if expanded {
            let mut found = false;
            if for_each_term_child(terms.get(cur), |child| {
                found |= memo.get(&child).copied().unwrap_or(false);
            })
            .is_none()
            {
                return None;
            }
            if memo.len().checked_add(stack.len())?.checked_add(1)? > max_nodes {
                return None;
            }
            memo.insert(cur, found);
        } else {
            let child_count = term_child_count(terms.get(cur))?;
            let pending_after_expand = memo
                .len()
                .checked_add(stack.len())?
                .checked_add(1)?
                .checked_add(child_count)?;
            if pending_after_expand > max_nodes {
                return None;
            }
            stack.push((cur, true));
            for_each_term_child(terms.get(cur), |child| {
                if !memo.contains_key(&child) {
                    stack.push((child, false));
                }
            })?;
        }
    }
    Some(memo.get(&t).copied().unwrap_or(false))
}

#[cfg(test)]
mod contains_member_tests {
    use super::*;

    #[test]
    fn pending_post_order_frames_share_the_hard_node_cap() {
        let mut terms = TermStore::new();
        let member = terms.mk_var("member", Sort::Bool);
        let left = terms.mk_var("left", Sort::Bool);
        let right = terms.mk_var("right", Sort::Bool);
        let wide = terms.mk_app(Symbol::named("wide"), &[member, left, right], Sort::Bool);
        let members = HashSet::from([member]);

        let mut at_limit = HashMap::new();
        assert_eq!(
            contains_member_bounded(&terms, wide, &members, &mut at_limit, 4),
            Some(true)
        );

        let mut over_limit = HashMap::new();
        assert_eq!(
            contains_member_bounded(&terms, wide, &members, &mut over_limit, 3),
            None,
            "the expanded parent plus three pending children exceed the cap"
        );
        assert!(
            over_limit.is_empty(),
            "capacity refusal must happen before a partial memo is installed"
        );
    }

    #[test]
    fn existing_memo_entries_consume_the_shared_node_cap() {
        let mut terms = TermStore::new();
        let cached = terms.mk_var("cached", Sort::Bool);
        let member = terms.mk_var("member", Sort::Bool);
        let members = HashSet::from([member]);
        let mut memo = HashMap::from([(cached, false)]);

        assert_eq!(
            contains_member_bounded(&terms, member, &members, &mut memo, 1),
            None
        );
        assert_eq!(memo, HashMap::from([(cached, false)]));
    }
}

/// Tiny union-find over `TermId` (path-halving find, union by direct link).
fn find(uf: &mut HashMap<TermId, TermId>, t: TermId) -> TermId {
    let mut cur = t;
    loop {
        let parent = *uf.get(&cur).unwrap_or(&cur);
        if parent == cur {
            return cur;
        }
        let grand = *uf.get(&parent).unwrap_or(&parent);
        uf.insert(cur, grand);
        cur = grand;
    }
}

fn union(uf: &mut HashMap<TermId, TermId>, a: TermId, b: TermId) {
    let ra = find(uf, a);
    let rb = find(uf, b);
    if ra != rb {
        uf.insert(ra, rb);
    }
}
