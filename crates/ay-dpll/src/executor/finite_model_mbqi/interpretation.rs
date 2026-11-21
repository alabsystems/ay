// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The completed candidate interpretation the quantified model check fixes
//! (roadmap component QM, model-check half).
//!
//! The legacy finite-sort pass pins only the free finite-sorted constants of
//! the quantifier bodies. The generic check fixes more of the candidate model:
//!
//! * every free scalar constant of a body (`Bool`, bit-vector, floating-point,
//!   `RoundingMode`, `Int`, `Real`) by a literal equality;
//! * every free constant of an uninterpreted sort by the PARTITION the model
//!   puts it in: one representative constant per universe element, the others
//!   equated to it, the representatives pairwise distinct;
//! * every uninterpreted function applied in a body by a finite TABLE plus an
//!   ELSE value ("model completion"): the rows are the model's values at the
//!   ground applications the problem mentions, the else value is the first
//!   row's value (the default of the result sort when there is no row).
//!
//! Tables are not pins. They are SUBSTITUTED: every application `f(t̄)` in a
//! matrix, in the residual and in a certification instance becomes
//! `ite(t̄ = k̄₁, v₁, ite(…, else))`, so every auxiliary query and the residual
//! speak about the same structure `P ∧ f = T_f`. The staged output model then
//! receives each table verbatim (see `witness.rs`), which is the structure
//! the checked UNSATs were about.
//!
//! Soundness never depends on how complete this is. A constant left unpinned
//! or a function left unsubstituted is a symbol the auxiliary queries leave
//! free, so their refutations quantify over it and stay valid; it can only
//! cost a decision.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Sort, Symbol, TermData, TermId, TermStore};

use super::{finite_value_term, trace, AuthoredUniversal};
use crate::executor::model::{EvalValue, Model};
use crate::executor::rm_domain::{is_rm_sort, rm_literal_term};
use crate::executor::Executor;

/// Cap on pins so a huge ground slice cannot blow up the sub-queries.
const MAX_PINS: usize = 256;
/// Cap on the rows of one table, and on the number of tables.
pub(super) const MAX_TABLE_ROWS: usize = 256;
const MAX_TABLES: usize = 64;

/// One uninterpreted function fixed to a finite table plus an else value.
///
/// Keys and values are literal terms or pinned representatives, so the
/// substituted `ite` chain denotes one function in every model of the pins.
#[derive(Clone)]
pub(super) struct UfTable {
    pub(super) symbol: Symbol,
    pub(super) arg_sorts: Vec<Sort>,
    pub(super) result_sort: Sort,
    /// Every observed point, including values equal to the present default.
    /// Alternative defaults must retain those points as observations.
    pub(super) rows: Vec<(Vec<TermId>, TermId)>,
    pub(super) default: TermId,
}

/// The fixed part of the candidate model one certificate pass works under.
#[derive(Clone, Default)]
pub(super) struct Interpretation {
    pub(super) symbolic: crate::executor::model::SymbolicUfModel,
    pub(super) symbolic_owner: Option<crate::executor::model::SymbolicAdmission>,
    /// Ground equalities (and representative disequalities) true in the
    /// candidate model.
    pub(super) pins: Vec<TermId>,
    /// Constants the candidate left unvalued and the pins completed.
    pub(super) completions: Vec<(TermId, EvalValue)>,
    pub(super) tables: Vec<UfTable>,
    pub(super) index: HashMap<Symbol, usize>,
    /// Representatives of uninterpreted-sort elements, per sort.
    reps: HashMap<Sort, Vec<TermId>>,
}

impl Interpretation {
    /// A total-model proposal for numeric functions with finitely many
    /// exceptional values. Using the first observed value as the else value
    /// can keep adding zero-valued rows forever. Retain every observed row
    /// and propose zero outside them; the ordinary authored and residual
    /// checks must still certify this exact interpretation before publishing.
    pub(super) fn with_zero_numeric_defaults(&self, terms: &mut TermStore) -> Option<Self> {
        fn zero(terms: &mut TermStore, sort: &Sort) -> Option<TermId> {
            match sort {
                Sort::Int => Some(terms.mk_int(0.into())),
                Sort::Real => {
                    Some(terms.mk_rational(num_rational::BigRational::from_integer(0.into())))
                }
                _ => None,
            }
        }

        if !self
            .tables
            .iter()
            .any(|table| zero(terms, &table.result_sort).is_some_and(|zero| table.default != zero))
        {
            return None;
        }
        let mut candidate = self.clone();
        for table in &mut candidate.tables {
            if let Some(zero) = zero(terms, &table.result_sort) {
                table.default = zero;
            }
        }
        Some(candidate)
    }

    /// One additional total-model candidate for quantified relations. Ground
    /// search often leaves an unobserved relation false, which cannot satisfy
    /// a reflexivity law on fresh carrier elements. A constant true function
    /// is only a proposal: every original quantified and residual obligation
    /// must still pass the ordinary checks before it can be published.
    pub(super) fn with_true_boolean_tables(&self, terms: &mut TermStore) -> Option<Self> {
        let truth = terms.mk_bool(true);
        if !self.tables.iter().any(|table| {
            table.result_sort == Sort::Bool
                && (table.default != truth || table.rows.iter().any(|(_, value)| *value != truth))
        }) {
            return None;
        }
        let mut candidate = self.clone();
        for table in &mut candidate.tables {
            if table.result_sort == Sort::Bool {
                table.rows.clear();
                table.default = truth;
            }
        }
        Some(candidate)
    }

    /// Preserve the existing scalar-table candidate before attempting the
    /// additional closed-array candidate. These are term data, not authority.
    pub(super) fn without_array_defaults(&self) -> Option<Self> {
        if !self
            .tables
            .iter()
            .any(|table| matches!(table.result_sort, Sort::Array(_)))
        {
            return None;
        }
        let mut original = self.clone();
        original
            .tables
            .retain(|table| !matches!(table.result_sort, Sort::Array(_)));
        original.index = original
            .tables
            .iter()
            .enumerate()
            .map(|(idx, table)| (table.symbol.clone(), idx))
            .collect();
        Some(original)
    }

    /// The pinned representatives of `sort` (empty for other sorts).
    pub(super) fn representatives(&self, sort: &Sort) -> &[TermId] {
        self.reps.get(sort).map_or(&[], Vec::as_slice)
    }

    /// `term` with every tabled application replaced by its table.
    pub(super) fn substitute(&self, terms: &mut TermStore, term: TermId) -> TermId {
        if self.tables.is_empty() {
            return term;
        }
        let mut memo: HashMap<TermId, TermId> = HashMap::default();
        self.substitute_memo(terms, term, &mut memo)
    }

    fn substitute_memo(
        &self,
        terms: &mut TermStore,
        term: TermId,
        memo: &mut HashMap<TermId, TermId>,
    ) -> TermId {
        if let Some(&done) = memo.get(&term) {
            return done;
        }
        let rebuilt = match terms.get(term).clone() {
            TermData::App(sym, args) => {
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&arg| self.substitute_memo(terms, arg, memo))
                    .collect();
                match self.index.get(&sym).map(|&i| &self.tables[i]) {
                    Some(table) if table.arg_sorts.len() == new_args.len() => {
                        table_application(terms, table, &new_args)
                    }
                    _ if new_args == args => term,
                    // Replacing an array-valued UF can expose a closed array.
                    // Rebuild the typed read through the ordinary constructor,
                    // whose read-over-const/store reductions preserve exactly
                    // the same array semantics as frontend elaboration.
                    _ if matches!(&sym, Symbol::Named(name) if name == "select")
                        && new_args.len() == 2
                        && terms.sort(new_args[0]).array_index()
                            == Some(terms.sort(new_args[1]))
                        && terms.sort(new_args[0]).array_element() == Some(terms.sort(term)) =>
                    {
                        terms.mk_select(new_args[0], new_args[1])
                    }
                    _ => {
                        let sort = terms.sort(term).clone();
                        terms.mk_app(sym, new_args, sort)
                    }
                }
            }
            TermData::Not(inner) => {
                let new_inner = self.substitute_memo(terms, inner, memo);
                if new_inner == inner {
                    term
                } else {
                    terms.mk_not(new_inner)
                }
            }
            TermData::Ite(c, t, e) => {
                let (nc, nt, ne) = (
                    self.substitute_memo(terms, c, memo),
                    self.substitute_memo(terms, t, memo),
                    self.substitute_memo(terms, e, memo),
                );
                if (nc, nt, ne) == (c, t, e) {
                    term
                } else {
                    terms.mk_ite(nc, nt, ne)
                }
            }
            // Leaves, and binders: a quantified vector is refused by every
            // checked probe, so an unsubstituted binder can only decline.
            _ => term,
        };
        memo.insert(term, rebuilt);
        rebuilt
    }
}

/// `ite(args = k̄₁, v₁, ite(…, default))` for one table.
fn table_application(terms: &mut TermStore, table: &UfTable, args: &[TermId]) -> TermId {
    let mut body = table.default;
    for (keys, value) in table
        .rows
        .iter()
        .rev()
        .filter(|(_, value)| *value != table.default)
    {
        let conjuncts: Vec<TermId> = args
            .iter()
            .zip(keys)
            .map(|(&arg, &key)| terms.mk_eq(arg, key))
            .collect();
        let condition = if conjuncts.len() == 1 {
            conjuncts[0]
        } else {
            terms.mk_and(conjuncts)
        };
        body = terms.mk_ite(condition, *value, body);
    }
    body
}

/// Literal term for a scalar value, or `None`.
pub(super) fn scalar_value_term(
    terms: &mut TermStore,
    sort: &Sort,
    value: &EvalValue,
) -> Option<TermId> {
    match (sort, value) {
        (Sort::Int, EvalValue::Rational(r)) if r.is_integer() => Some(terms.mk_int(r.to_integer())),
        (Sort::Real, EvalValue::Rational(r)) => Some(terms.mk_rational(r.clone())),
        (sort, EvalValue::Element(name)) if is_rm_sort(sort) => {
            ay_fp::RoundingMode::from_name(name).map(|mode| rm_literal_term(terms, mode))
        }
        _ => finite_value_term(terms, sort, value),
    }
}

/// Whether the model check can fix a value of `sort`: a scalar with literals,
/// or an uninterpreted sort through its representatives.
pub(super) fn is_fixable_sort(executor: &Executor, sort: &Sort) -> bool {
    match sort {
        Sort::Bool | Sort::Int | Sort::Real | Sort::BitVec(_) | Sort::FloatingPoint(..) => true,
        Sort::Uninterpreted(_) => is_rm_sort(sort) || executor.datatype_sort_name(sort).is_none(),
        _ => false,
    }
}

pub(super) fn is_element_sort(executor: &Executor, sort: &Sort) -> bool {
    matches!(sort, Sort::Uninterpreted(_))
        && !is_rm_sort(sort)
        && executor.datatype_sort_name(sort).is_none()
}

/// What one walk over the quantifier bodies found.
#[derive(Default)]
struct BodySymbols {
    leaves: Vec<TermId>,
    functions: Vec<Symbol>,
}

/// Collect the free `Var` leaves and the applied uninterpreted functions of
/// one quantifier-free body.
fn collect_body_symbols(
    terms: &TermStore,
    term: TermId,
    bound: &HashSet<String>,
    ufs: &HashSet<String>,
    out: &mut BodySymbols,
    seen: &mut HashSet<TermId>,
) {
    if !seen.insert(term) {
        return;
    }
    match terms.get(term) {
        TermData::Var(name, _) if !bound.contains(name) => out.leaves.push(term),
        TermData::App(sym, args) => {
            if !args.is_empty() && ufs.contains(sym.name()) && !out.functions.contains(sym) {
                out.functions.push(sym.clone());
            }
            for &arg in args {
                collect_body_symbols(terms, arg, bound, ufs, out, seen);
            }
        }
        TermData::Not(inner) => collect_body_symbols(terms, *inner, bound, ufs, out, seen),
        TermData::Ite(c, t, e) => {
            for sub in [*c, *t, *e] {
                collect_body_symbols(terms, sub, bound, ufs, out, seen);
            }
        }
        _ => {}
    }
}

/// Ground applications of `functions` reachable from `roots` without entering
/// a binder.
fn ground_applications(
    terms: &TermStore,
    roots: &[TermId],
    functions: &[Symbol],
) -> HashMap<Symbol, Vec<TermId>> {
    let mut found: HashMap<Symbol, Vec<TermId>> = HashMap::default();
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut pending = roots.to_vec();
    while let Some(term) = pending.pop() {
        if !seen.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::App(sym, args) => {
                if !args.is_empty() && functions.contains(sym) {
                    found.entry(sym.clone()).or_default().push(term);
                }
                pending.extend(args.iter().copied());
            }
            TermData::Not(inner) => pending.push(*inner),
            TermData::Ite(c, t, e) => pending.extend([*c, *t, *e]),
            TermData::Let(bindings, body) => {
                pending.extend(bindings.iter().map(|(_, value)| *value));
                pending.push(*body);
            }
            _ => {}
        }
    }
    for apps in found.values_mut() {
        apps.sort_unstable();
    }
    found
}

impl Executor {
    /// Identities of the ordinary free uninterpreted functions of the query.
    fn model_check_uf_identities(&self) -> HashSet<String> {
        let mut out = HashSet::default();
        for (surface_name, info) in self.ctx.symbol_iter() {
            if !info.arg_sorts.is_empty()
                && self.is_ordinary_free_primary_declaration(surface_name, info)
            {
                out.insert(
                    self.ctx
                        .symbol_identity_name(surface_name, info)
                        .to_string(),
                );
            }
        }
        out
    }

    /// Build the generic interpretation for one certificate pass, or `None`
    /// when there is no candidate model.
    pub(super) fn model_check_interpretation(
        &mut self,
        universals: &[AuthoredUniversal],
        roots: &[TermId],
    ) -> Option<Interpretation> {
        let model = self.last_model.clone()?;
        let bound: HashSet<String> = universals
            .iter()
            .flat_map(|leaf| leaf.vars.iter().map(|(name, _)| name.clone()))
            .collect();
        let ufs = self.model_check_uf_identities();
        let mut symbols = BodySymbols::default();
        let mut seen = HashSet::default();
        for leaf in universals {
            collect_body_symbols(
                &self.ctx.terms,
                leaf.body,
                &bound,
                &ufs,
                &mut symbols,
                &mut seen,
            );
        }
        symbols.leaves.sort_unstable();
        symbols.leaves.dedup();
        let mut scope: Vec<TermId> = roots.to_vec();
        scope.extend(self.ctx.assertions.iter().copied());
        let apps = ground_applications(&self.ctx.terms, &scope, &symbols.functions);

        let mut interp = Interpretation::default();
        // Representatives first: table keys and values name them.
        let mut element_terms = symbols.leaves.clone();
        for app in apps.values().flatten() {
            if let TermData::App(_, args) = self.ctx.terms.get(*app) {
                element_terms.extend(args.iter().copied());
            }
            element_terms.push(*app);
        }
        self.model_check_representatives(&model, &element_terms, &mut interp);
        for &leaf in &symbols.leaves {
            self.model_check_scalar_pin(&model, leaf, &mut interp);
        }
        if interp.pins.len() > MAX_PINS {
            trace(|| format!("qmc: {} pins exceed the cap", interp.pins.len()));
            return None;
        }
        for symbol in symbols.functions.iter().take(MAX_TABLES) {
            let Some(applications) = apps.get(symbol) else {
                self.model_check_table(&model, symbol, &[], universals, &mut interp);
                continue;
            };
            self.model_check_table(&model, symbol, applications, universals, &mut interp);
        }
        trace(|| {
            format!(
                "qmc: interpretation pins={} completions={} tables={} functions={}",
                interp.pins.len(),
                interp.completions.len(),
                interp.tables.len(),
                symbols.functions.len()
            )
        });
        Some(interp)
    }

    /// Group the uninterpreted-sort `Var` terms among `candidates` by their
    /// model element; pin each to its group's representative and the
    /// representatives of one sort pairwise distinct.
    fn model_check_representatives(
        &mut self,
        model: &Model,
        candidates: &[TermId],
        interp: &mut Interpretation,
    ) {
        let mut groups: Vec<(Sort, String, Vec<TermId>)> = Vec::new();
        let mut sorted: Vec<TermId> = candidates
            .iter()
            .copied()
            .filter(|&t| matches!(self.ctx.terms.get(t), TermData::Var(..)))
            .collect();
        sorted.sort_unstable();
        sorted.dedup();
        for term in sorted {
            let sort = self.ctx.terms.sort(term).clone();
            if !is_element_sort(self, &sort) {
                continue;
            }
            let EvalValue::Element(element) = self.evaluate_term(model, term) else {
                continue;
            };
            match groups
                .iter_mut()
                .find(|(s, e, _)| *s == sort && *e == element)
            {
                Some((_, _, members)) => members.push(term),
                None => groups.push((sort, element, vec![term])),
            }
        }
        for (sort, _, members) in groups {
            let rep = members[0];
            for &other in &members[1..] {
                let pin = self.ctx.terms.mk_eq(other, rep);
                interp.pins.push(pin);
            }
            interp.reps.entry(sort).or_default().push(rep);
        }
        let mut sorts: Vec<Sort> = interp.reps.keys().cloned().collect();
        sorts.sort_by_key(|sort| format!("{sort:?}"));
        for sort in sorts {
            let reps = interp.representatives(&sort).to_vec();
            if reps.len() > 1 {
                let distinct = self.ctx.terms.mk_distinct(reps);
                interp.pins.push(distinct);
            }
        }
    }

    /// Pin one scalar leaf to its model value, completing an unvalued one.
    fn model_check_scalar_pin(&mut self, model: &Model, leaf: TermId, interp: &mut Interpretation) {
        let sort = self.ctx.terms.sort(leaf).clone();
        if is_element_sort(self, &sort) || !is_fixable_sort(self, &sort) {
            return;
        }
        let mut value = self.evaluate_term(model, leaf);
        let mut completed = false;
        if matches!(value, EvalValue::Unknown) {
            let Some(default) = self.unconstrained_default_value(&sort) else {
                return;
            };
            value = default;
            completed = true;
        }
        let Some(value_term) = scalar_value_term(&mut self.ctx.terms, &sort, &value) else {
            trace(|| format!("qmc: no literal for {sort:?} value {value:?}"));
            return;
        };
        let pin = self.ctx.terms.mk_eq(leaf, value_term);
        interp.pins.push(pin);
        if completed {
            interp.completions.push((leaf, value));
        }
    }
}
