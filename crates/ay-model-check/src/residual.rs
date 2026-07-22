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
//! * ground element reads `(= <ground> (select a i))` /
//!   `(= <ground> (fld (select a i)))` whose index and ground side evaluate
//!   under the fixed partial model —
//!
//! then union-find the alias classes and collect, per class, the
//! `(index-value, slot) -> value` REQUIREMENTS from the residue plus the
//! PINNED reads over class members the evaluator did resolve (see below). The
//! residue is jointly satisfiable iff no two collected entries force
//! different values at one `(class, index, field)` slot — whole-element
//! values are reconciled with field values by exact constructor projection,
//! and the constrained fields of one element must fit a single constructor.
//! In that case the confirmed partial model EXTENDS to a full model, so
//! `ConfirmedSat` is returned; otherwise the blanket `CannotConfirm` stands.
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
//! whole-element entry if present, else the common constructor applied to
//! the field entries with the remaining fields arbitrary — SMT sorts are
//! non-empty, so such values exist. Every residual alias then holds
//! (identical values), every residual read holds (selector projection of a
//! matching constructor), every pinned read keeps its committed value
//! (entry-consistency was checked), and every previously-true assertion
//! keeps its computed truth. Hence the formula is satisfiable and
//! `ConfirmedSat` is correct. The map is `Sat -> {Sat, Unknown}` only: a
//! `false` from any check keeps today's fail-closed verdict.
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
//!    direct `(select m i)` / `(fld (select m i))` read with an evaluable
//!    index, and refuses otherwise.
//! 4. Canonical const-array completion is deliberately NOT used anywhere
//!    (proven unsound on `qf_abv_incremental_false_unsat`): no value is ever
//!    fabricated for a free array — the decision is purely about joint
//!    satisfiability of the residual constraint set.

use std::collections::{HashMap, HashSet};

use ay_core::term::{Symbol, TermData};
use ay_core::{DatatypeSort, Sort, TermId, TermStore};

use crate::dt_axiom::DtResolve;
use crate::{is_datatype_tautology_with, value_eq, EvalOutcome, Evaluator, ModelValue, ModelView};

/// Recursion bound for the residual-constraint classifier (top-level Boolean
/// structure only; residual assertions are shallow in practice).
const MAX_CLASSIFY_DEPTH: usize = 64;

/// Which slot of an array element an entry constrains.
#[derive(Clone, PartialEq, Eq)]
enum Slot {
    /// The whole element: `(= <ground> (select a i))` or a pinned select.
    Whole,
    /// One selector field: `(= <ground> (fld (select a i)))` or a pinned
    /// selector-chain read.
    Field(String),
}

/// One entry of the joint constraint map: `(array, index-value, slot) ->
/// value`, from either a residual requirement or a pinned read.
struct Entry {
    array: TermId,
    index: ModelValue,
    slot: Slot,
    value: ModelValue,
}

/// Decide whether the unevaluable `residue` is exactly the free-datatype-array
/// fragment AND jointly satisfiable, so the confirmed partial model provably
/// extends to a full model. `true` ⇒ the caller may return `ConfirmedSat`;
/// `false` ⇒ keep the fail-closed `CannotConfirm`.
pub(crate) fn free_dt_array_residue_extends(
    terms: &TermStore,
    model: &dyn ModelView,
    ev: &Evaluator<'_>,
    assertions: &[TermId],
    residue: &[TermId],
    resolve: &DtResolve<'_>,
) -> bool {
    let mut cx = Classifier {
        terms,
        model,
        ev,
        resolve,
        aliases: Vec::new(),
        alias_eq_terms: Vec::new(),
        entries: Vec::new(),
    };
    for &a in residue {
        if !cx.classify(a, 0) {
            return false;
        }
    }
    if cx.aliases.is_empty() && cx.entries.is_empty() {
        // Nothing was classified (e.g. every residual assertion meanwhile
        // re-evaluated `true`): not the free-dt-array fragment — keep today's
        // fail-closed behaviour rather than widen the gate's contract.
        return false;
    }
    let alias_eqs: HashSet<TermId> = cx.alias_eq_terms.iter().copied().collect();

    // Union-find the alias classes (each recorded edge is between two free
    // array variables of the SAME sort, checked at classification).
    let mut uf: HashMap<TermId, TermId> = HashMap::new();
    let mut members: HashSet<TermId> = HashSet::new();
    for &(l, r) in &cx.aliases {
        members.insert(l);
        members.insert(r);
        union(&mut uf, l, r);
    }
    for e in &cx.entries {
        members.insert(e.array);
    }

    // Occurrence guard over the whole (non-quantifier) assertion DAG, and
    // collection of every pin SITE over the classes.
    let mut select_sites: Vec<TermId> = Vec::new();
    // (site, inner array member, inner index term, field name)
    let mut chain_sites: Vec<(TermId, TermId, TermId, String)> = Vec::new();
    let mut other_selector_sites: Vec<TermId> = Vec::new();
    let mut contains_memo: HashMap<TermId, bool> = HashMap::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    let mut seen: HashSet<TermId> = HashSet::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::App(sym, args) => {
                let is_select = sym.name() == "select" && args.len() == 2;
                let blessed_eq = alias_eqs.contains(&t);
                for (pos, &c) in args.iter().enumerate() {
                    if members.contains(&c) && !((is_select && pos == 0) || blessed_eq) {
                        return false; // member escapes the blessed contexts
                    }
                }
                if is_select && members.contains(&args[0]) {
                    select_sites.push(t);
                }
                // Selector-shaped unary application whose argument depends on
                // a member: the ONE pin site that can commit a value without
                // evaluating its argument (`eval_selector_via_model`).
                if let (Symbol::Named(name), [arg]) = (sym, args.as_slice()) {
                    if cx.selector_shaped(name, *arg)
                        && contains_member(terms, *arg, &members, &mut contains_memo)
                    {
                        match cx.direct_chain(*arg, name) {
                            Some((m, i)) => chain_sites.push((t, m, i, name.clone())),
                            None => other_selector_sites.push(t),
                        }
                    }
                }
                stack.extend(args.iter().copied());
            }
            // Quantifier bodies are never evaluated by the gate (the evaluator
            // fails at the quantifier node itself, adopting no pins), so they
            // cannot constrain the extension; do not descend.
            TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {}
            _ => {
                for c in terms.children(t) {
                    if members.contains(&c) {
                        return false; // member under a non-App context (ite/not/let)
                    }
                    stack.push(c);
                }
            }
        }
    }

    // Probe every pin site LAST (final pin-graph state). A resolvable direct
    // read is LOCALIZED as an entry; anything else resolvable refuses.
    for t in select_sites {
        let TermData::App(_, args) = terms.get(t) else {
            return false; // unreachable by construction
        };
        let (arr, idx_term) = (args[0], args[1]);
        if let EvalOutcome::Value(v) = ev.evaluate(t) {
            let EvalOutcome::Value(index) = ev.evaluate(idx_term) else {
                return false; // pinned read at an unkeyable index
            };
            cx.entries.push(Entry {
                array: arr,
                index,
                slot: Slot::Whole,
                value: v,
            });
        }
    }
    for (t, m, idx_term, fld) in chain_sites {
        if let EvalOutcome::Value(v) = ev.evaluate(t) {
            let EvalOutcome::Value(index) = ev.evaluate(idx_term) else {
                return false; // pinned field read at an unkeyable index
            };
            cx.entries.push(Entry {
                array: m,
                index,
                slot: Slot::Field(fld),
                value: v,
            });
        }
    }
    for t in other_selector_sites {
        if matches!(ev.evaluate(t), EvalOutcome::Value(_)) {
            return false; // committed pin that cannot be localized
        }
    }

    // Joint satisfiability of the entry map: group by (class, index-value)
    // and check that no two entries force different values at one slot.
    let entries = std::mem::take(&mut cx.entries);
    let keyed: Vec<(TermId, &Entry)> = entries
        .iter()
        .map(|e| (find(&mut uf, e.array), e))
        .collect();
    let mut grouped: Vec<usize> = (0..keyed.len()).collect();
    // For each group representative, gather its group and check consistency.
    let mut done: Vec<bool> = vec![false; keyed.len()];
    for gi in grouped.drain(..) {
        if done[gi] {
            continue;
        }
        let (root, first) = keyed[gi];
        let mut group: Vec<&Entry> = Vec::new();
        for (j, &(r2, e2)) in keyed.iter().enumerate() {
            if r2 != root {
                continue;
            }
            match value_eq(&first.index, &e2.index) {
                Ok(true) => {
                    group.push(e2);
                    done[j] = true;
                }
                Ok(false) => {}
                Err(_) => return false, // incomparable index values
            }
        }
        // Whole entries must all agree; field entries must agree per field.
        let mut whole: Option<&ModelValue> = None;
        let mut fields: Vec<(&str, &ModelValue)> = Vec::new();
        for e in &group {
            match &e.slot {
                Slot::Whole => match whole {
                    None => whole = Some(&e.value),
                    Some(w) => {
                        if !matches!(value_eq(w, &e.value), Ok(true)) {
                            return false; // conflicting whole-element values
                        }
                    }
                },
                Slot::Field(f) => {
                    if let Some((_, prev)) = fields.iter().find(|(g, _)| *g == f.as_str()) {
                        if !matches!(value_eq(prev, &e.value), Ok(true)) {
                            return false; // conflicting values at one field
                        }
                    } else {
                        fields.push((f.as_str(), &e.value));
                    }
                }
            }
        }
        if fields.is_empty() {
            continue;
        }
        let Some(dt) = cx.element_dt_of_array(root) else {
            return false;
        };
        match whole {
            // Whole + fields: reconcile by EXACT constructor projection.
            Some(ModelValue::Datatype { ctor, args }) => {
                let Some(cons) = dt.constructors.iter().find(|c| c.name == *ctor) else {
                    return false;
                };
                for (f, v) in &fields {
                    let Some(pos) = cons.fields.iter().position(|cf| cf.name == *f) else {
                        return false; // field not of the element's constructor
                    };
                    let Some(actual) = args.get(pos) else {
                        return false;
                    };
                    if !matches!(value_eq(actual, v), Ok(true)) {
                        return false; // field value contradicts the element
                    }
                }
            }
            // An opaque element token cannot be projected — refuse.
            Some(_) => return false,
            // Fields only: they must fit a single constructor.
            None => {
                let fits_one_ctor = dt.constructors.iter().any(|c| {
                    fields
                        .iter()
                        .all(|(f, _)| c.fields.iter().any(|cf| cf.name == *f))
                });
                if !fits_one_ctor {
                    return false;
                }
            }
        }
    }

    true
}

/// Classification state: the alias edges, the classified alias-equality terms
/// (the ONLY blessed non-`select` occurrence context), and the entry map
/// (requirements now; pinned reads are appended by the probe phase).
struct Classifier<'a> {
    terms: &'a TermStore,
    model: &'a dyn ModelView,
    ev: &'a Evaluator<'a>,
    resolve: &'a DtResolve<'a>,
    aliases: Vec<(TermId, TermId)>,
    alias_eq_terms: Vec<TermId>,
    entries: Vec<Entry>,
}

impl Classifier<'_> {
    /// Classify one residual assertion/conjunct. `true` = admitted (either
    /// satisfied by the pinned partial model or recorded as an allowed
    /// free-dt-array constraint); `false` = refuse the whole decision.
    fn classify(&mut self, t: TermId, depth: usize) -> bool {
        if depth > MAX_CLASSIFY_DEPTH {
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
        let (name, args) = match self.terms.get(t) {
            TermData::App(sym, args) => (sym.name().to_string(), args.clone()),
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
                    );
                    if self.classify(d, depth + 1) {
                        return true;
                    }
                    self.aliases.truncate(snap.0);
                    self.alias_eq_terms.truncate(snap.1);
                    self.entries.truncate(snap.2);
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
                self.aliases.push((l, r));
                self.alias_eq_terms.push(t);
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
            // A whole-element requirement must be a datatype-shaped value
            // (structured or an opaque element token) — anything else is
            // ill-typed for a datatype element.
            if matches!(slot, Slot::Whole)
                && !matches!(
                    value,
                    ModelValue::Datatype { .. } | ModelValue::Uninterpreted(_)
                )
            {
                return false;
            }
            self.entries.push(Entry {
                array,
                index,
                slot,
                value,
            });
            return true;
        }
        false
    }

    /// `t` as a FREE datatype-element array variable: a `Var` leaf of sort
    /// `(Array _ DT)` the model does not pin. Returns its sort.
    fn free_dt_array_var(&self, t: TermId) -> Option<Sort> {
        if !matches!(self.terms.get(t), TermData::Var(_, _)) {
            return None;
        }
        let sort = self.terms.sort(t).clone();
        let Sort::Array(arr) = &sort else {
            return None;
        };
        element_dt(&arr.element_sort, self.resolve)?;
        if self.model.leaf_value(t).is_some() {
            return None; // pinned ⇒ not free ⇒ out of this fragment
        }
        Some(sort)
    }

    /// Parse `(select a i)` / `(fld (select a i))` over a free array variable.
    fn parse_free_read(&self, t: TermId) -> Option<(TermId, TermId, Slot)> {
        match self.terms.get(t) {
            TermData::App(sym, args) if sym.name() == "select" && args.len() == 2 => {
                let (a, i) = (args[0], args[1]);
                self.free_dt_array_var(a)?;
                Some((a, i, Slot::Whole))
            }
            TermData::App(Symbol::Named(name), args) if args.len() == 1 => {
                let (a, i) = self.direct_chain(args[0], name)?;
                Some((a, i, Slot::Field(name.clone())))
            }
            _ => None,
        }
    }

    /// `arg` as the inner read of a DIRECT selector chain `(name (select m i))`
    /// over a free member array whose element datatype declares field `name`.
    fn direct_chain(&self, arg: TermId, name: &str) -> Option<(TermId, TermId)> {
        let TermData::App(isym, iargs) = self.terms.get(arg) else {
            return None;
        };
        if isym.name() != "select" || iargs.len() != 2 {
            return None;
        }
        let (a, i) = (iargs[0], iargs[1]);
        let sort = self.free_dt_array_var(a)?;
        let Sort::Array(arr) = &sort else {
            return None;
        };
        let dt = element_dt(&arr.element_sort, self.resolve)?;
        dt.constructors
            .iter()
            .any(|c| c.fields.iter().any(|f| f.name == *name))
            .then_some((a, i))
    }

    /// Whether `(name arg)` is selector-shaped: `arg` is datatype-sorted and
    /// `name` is a field of that datatype — the exact precondition of the
    /// evaluator's `eval_selector_via_model` pin site.
    fn selector_shaped(&self, name: &str, arg: TermId) -> bool {
        let Some(dt) = element_dt(self.terms.sort(arg), self.resolve) else {
            return false;
        };
        dt.constructors
            .iter()
            .any(|c| c.fields.iter().any(|f| f.name == name))
    }

    /// The element datatype of the array sort of `array_var` (a class member).
    fn element_dt_of_array(&self, array_var: TermId) -> Option<DatatypeSort> {
        let Sort::Array(arr) = self.terms.sort(array_var) else {
            return None;
        };
        element_dt(&arr.element_sort, self.resolve)
    }
}

/// Resolve a sort to its datatype definition (native or registry-abstracted).
fn element_dt(sort: &Sort, resolve: &DtResolve<'_>) -> Option<DatatypeSort> {
    match sort {
        Sort::Datatype(dt) => Some(dt.clone()),
        Sort::Uninterpreted(name) => resolve(name),
        _ => None,
    }
}

/// Whether `t`'s subtree mentions a class member (memoized, iterative — no
/// native-stack recursion; quantifier bodies included, since over-approximating
/// containment is only ever conservative here).
fn contains_member(
    terms: &TermStore,
    t: TermId,
    members: &HashSet<TermId>,
    memo: &mut HashMap<TermId, bool>,
) -> bool {
    // Explicit post-order: (node, children_expanded).
    let mut stack: Vec<(TermId, bool)> = vec![(t, false)];
    while let Some((cur, expanded)) = stack.pop() {
        if memo.contains_key(&cur) {
            continue;
        }
        if members.contains(&cur) {
            memo.insert(cur, true);
            continue;
        }
        if expanded {
            let found = terms
                .children(cur)
                .iter()
                .any(|c| memo.get(c).copied().unwrap_or(false));
            memo.insert(cur, found);
        } else {
            stack.push((cur, true));
            for &c in &terms.children(cur) {
                if !memo.contains_key(&c) {
                    stack.push((c, false));
                }
            }
        }
    }
    memo.get(&t).copied().unwrap_or(false)
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
