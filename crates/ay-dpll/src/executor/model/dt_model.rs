// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Datatype model extraction helpers (#5412).
//!
//! Translates DT-sorted variable values from opaque UF representative names
//! (`@SortName!N`) to proper constructor expressions (`Green`, `(Some #x42)`).

use std::cell::RefCell;

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{quote_symbol, Sort, TermId, TermStore};
use num_rational::BigRational;

use crate::executor_format::{format_default_value, format_sort};

use super::{EvalValue, Executor, Model};

thread_local! {
    /// Per-thread override map consulted at the top of [`Executor::evaluate_term`].
    ///
    /// While the materialized datatype re-evaluator ([`Executor::dt_mat_eval`]) is
    /// running, this holds the concrete value of every datatype selector
    /// application / recognizer subterm that the model reaches through a
    /// constructor assignment (real theory-model values, or the SAME default the
    /// model printer presents for an unconstrained field). With the boundary
    /// subterms pinned, the WHOLE assertion is ground and is finished by ay's
    /// existing complete term evaluator — every string/BV/int/seq predicate is
    /// handled correctly with no op-by-op reimplementation. The map is empty (and
    /// the override is a no-op) outside `dt_mat_eval`.
    static DT_FIELD_OVERRIDE: RefCell<Option<HashMap<TermId, EvalValue>>> =
        const { RefCell::new(None) };

    /// Bound terms installed specifically for contextual evaluation (currently
    /// runtime `lambda-array` beta reduction).
    ///
    /// `DT_FIELD_OVERRIDE` is also used by datatype materialization, so its
    /// presence alone cannot tell application evaluators that a TermId's value
    /// depends on a binder environment. This stack provides that distinction.
    /// Nested bindings are retained newest-last and restored by length.  Keep
    /// their values in a layer separate from `DT_FIELD_OVERRIDE`: datatype
    /// materializer pins are ambient model facts, while these values belong to
    /// one lexical beta environment.
    static SCOPED_TERM_BINDINGS: RefCell<Vec<(TermId, EvalValue)>> =
        const { RefCell::new(Vec::new()) };
}

/// Look up a materialized override value for `term_id`, if the datatype-field
/// re-evaluator is currently active and has pinned this subterm. Consulted at the
/// very top of [`Executor::evaluate_term`] so the ordinary evaluator sees the
/// concrete field value instead of `Unknown` for a selector/recognizer it cannot
/// otherwise resolve.
pub(super) fn dt_field_override_lookup(term_id: TermId) -> Option<EvalValue> {
    DT_FIELD_OVERRIDE.with(|cell| {
        cell.borrow()
            .as_ref()
            .and_then(|m| m.get(&term_id).cloned())
    })
}

/// Look up the active value of `term_id` under layered evaluator overrides.
///
/// The newest exact lexical binding wins.  An ambient datatype-materializer
/// pin may be reused only for a term that is independent of every active
/// lexical binding; otherwise the same `TermId` could leak a value computed in
/// a different beta environment.
pub(super) fn active_term_override_lookup(terms: &TermStore, term_id: TermId) -> Option<EvalValue> {
    let scoped = SCOPED_TERM_BINDINGS.with(|cell| {
        cell.borrow()
            .iter()
            .rev()
            .find_map(|(bound, value)| (*bound == term_id).then(|| value.clone()))
    });
    if scoped.is_some() {
        return scoped;
    }
    if term_depends_on_scoped_binding(terms, term_id) {
        return None;
    }
    dt_field_override_lookup(term_id)
}

/// Whether the datatype-field materialization override is currently installed.
///
/// While active, a fixed `TermId` may evaluate to DIFFERENT values across
/// materialization or lexical beta contexts, so the `evaluate_term` result
/// memo must be DISABLED for the entire nested evaluation — otherwise a value
/// cached in one context could be returned in another.
pub(super) fn dt_field_override_active() -> bool {
    DT_FIELD_OVERRIDE.with(|cell| cell.borrow().is_some())
        || SCOPED_TERM_BINDINGS.with(|cell| !cell.borrow().is_empty())
}

/// RAII guard that installs an override map for the duration of a `dt_mat_eval`
/// call (or the dt-egraph assignment self-check) and restores the previous one
/// (supporting re-entrancy) on drop.
pub(super) struct OverrideGuard {
    prev: Option<HashMap<TermId, EvalValue>>,
}

impl OverrideGuard {
    pub(super) fn install(map: HashMap<TermId, EvalValue>) -> Self {
        let prev = DT_FIELD_OVERRIDE.with(|cell| cell.borrow_mut().replace(map));
        OverrideGuard { prev }
    }
}

impl Drop for OverrideGuard {
    fn drop(&mut self) {
        DT_FIELD_OVERRIDE.with(|cell| {
            *cell.borrow_mut() = self.prev.take();
        });
    }
}

/// Restores the contextual-binding stack on every exit, including unwinding.
struct ScopedBindingGuard {
    restore_len: usize,
}

impl ScopedBindingGuard {
    fn install(term: TermId, value: EvalValue) -> Self {
        let restore_len = SCOPED_TERM_BINDINGS.with(|cell| {
            let mut bindings = cell.borrow_mut();
            let len = bindings.len();
            bindings.push((term, value));
            len
        });
        Self { restore_len }
    }
}

impl Drop for ScopedBindingGuard {
    fn drop(&mut self) {
        SCOPED_TERM_BINDINGS.with(|cell| cell.borrow_mut().truncate(self.restore_len));
    }
}

/// Whether contextual term bindings are currently installed.
pub(super) fn scoped_term_binding_active() -> bool {
    SCOPED_TERM_BINDINGS.with(|cell| !cell.borrow().is_empty())
}

/// Whether `root` syntactically depends on any active contextual binding.
///
/// A context-free per-TermId model pin is reusable only when this returns
/// false. A conservative positive result merely loses evaluator completeness;
/// it can never admit a value from the wrong beta environment.
pub(super) fn term_depends_on_scoped_binding(terms: &TermStore, root: TermId) -> bool {
    let bindings: HashSet<TermId> =
        SCOPED_TERM_BINDINGS.with(|cell| cell.borrow().iter().map(|(term, _)| *term).collect());
    if bindings.is_empty() {
        return false;
    }
    let mut stack = vec![root];
    let mut seen = HashSet::default();
    while let Some(term) = stack.pop() {
        if bindings.contains(&term) {
            return true;
        }
        if seen.insert(term) {
            stack.extend(terms.children(term));
        }
    }
    false
}

/// Evaluate `f` with one additional concrete term binding.
///
/// Recursive [`Executor::evaluate_term`] calls see this context-local value,
/// bypass the ordinary `(model, term)` memo, and restore the previous context
/// on every exit (including unwinding).  Lexical bindings deliberately remain
/// separate from ambient datatype-materializer pins so dependent terms cannot
/// inherit pins computed outside this beta environment.
pub(super) fn with_scoped_term_override<R>(
    term: TermId,
    value: EvalValue,
    f: impl FnOnce() -> R,
) -> R {
    let _binding_guard = ScopedBindingGuard::install(term, value);
    f()
}

/// Install ambient materializer pins for a focused layered-override regression.
#[cfg(test)]
pub(super) fn with_dt_field_overrides_for_test<R>(
    overrides: HashMap<TermId, EvalValue>,
    f: impl FnOnce() -> R,
) -> R {
    let _guard = OverrideGuard::install(overrides);
    f()
}

impl Executor {
    /// Check whether a symbol is a datatype-internal symbol (constructor, tester,
    /// or selector) that should be excluded from `get-model` output (#5412).
    pub(in crate::executor) fn is_dt_internal_symbol(&self, name: &str) -> bool {
        // Parametric-instance members are registered under their SURFACE name with
        // an instance-mangled `internal_name`; exclude them from model output.
        if self
            .ctx
            .symbol_info(name)
            .is_some_and(|i| i.internal_name.is_some())
        {
            return true;
        }
        if self.ctx.is_constructor(name).is_some() {
            return true;
        }
        if let Some(ctor) = name.strip_prefix("is-") {
            if self.ctx.is_constructor(ctor).is_some() {
                return true;
            }
        }
        self.ctx
            .ctor_selectors_iter()
            .any(|(_ctor, selectors)| selectors.iter().any(|sel| sel == name))
    }

    /// User-facing surface name of a (possibly instance-mangled) datatype
    /// constructor/selector internal name, for model / `get-value` output.
    pub(super) fn dt_surface<'a>(&'a self, name: &'a str) -> &'a str {
        self.ctx.dt_surface_name(name).unwrap_or(name)
    }

    /// Resolve a DT-sorted variable's value to a constructor expression (#5412).
    ///
    /// Uses two strategies:
    /// 1. SAT model: Check tester proposition truth values (works for pure DT solver)
    /// 2. EUF model: Check equivalence classes (works for combined DT+UF solvers)
    ///
    /// For nullary constructors (e.g., `Green`), returns the constructor name.
    /// For non-nullary constructors (e.g., `Some`), evaluates selector arguments
    /// to produce e.g. `(Some #x42)`.
    pub(super) fn resolve_dt_value(
        &self,
        sort_name: &str,
        var_term_id: TermId,
        model: &Model,
    ) -> Option<String> {
        // Single source (#mv-dt-single-source): when the DT lane exported its
        // e-graph, the per-class assignment is authoritative for EVERY printed
        // datatype value — `(get-model)`, `(get-value)`, and the totalization
        // committed cases all read it, so they cannot diverge. `None` (no
        // export / poisoned class / unresolvable fresh term) falls through to
        // the strategies below. This MUST stay first: the top-level printer
        // (output.rs) and the independent gate's leaf resolution both consult
        // the e-graph assignment first, so any other order here would let
        // `(get-value)` / array-element rendering diverge from `(get-model)`.
        if let Some(v) = self.dt_egraph_value(model, var_term_id) {
            return Some(v);
        }
        // Total-datatype-model construction (#dt-total-model): the constructed
        // ground value for this term — the SAME value every validator
        // evaluated — rendered as a round-trippable surface term. Falls
        // through to the legacy per-leaf resolution when absent.
        if let Some(mv) = model.dt_ground.get(&var_term_id) {
            if let Some(s) = self.format_gate_model_value(mv, self.ctx.terms.sort(var_term_id)) {
                return Some(s);
            }
        }
        for (dt_name, constructors) in self.ctx.datatype_iter() {
            if dt_name != sort_name {
                continue;
            }
            // Strategy 1: Check tester propositions in SAT model.
            // DT axiom injection creates (is-CtorName var) terms; if the SAT model
            // assigns a tester to true, that identifies the constructor.
            // Collect ALL tester values first because the combined DT+BV solver
            // may not enforce mutual exclusivity of testers in the SAT model.
            // If multiple testers are true, prefer the one that was explicitly
            // asserted by the user.
            let mut tester_results: Vec<(&str, bool)> = Vec::new();
            for ctor_name in constructors {
                let tester_name = format!("is-{ctor_name}");
                for idx in 0..self.ctx.terms.len() {
                    let tid = TermId(idx as u32);
                    if let TermData::App(sym, args) = self.ctx.terms.get(tid) {
                        if sym.name() == tester_name && args.len() == 1 && args[0] == var_term_id {
                            let is_asserted = self.ctx.assertions.contains(&tid);
                            tester_results.push((ctor_name, is_asserted));
                            break;
                        }
                    }
                }
            }
            // Prefer explicitly asserted testers; fall back to SAT model true.
            if let Some((ctor_name, _)) = tester_results.iter().find(|&&(_, asserted)| asserted) {
                return Some(self.format_dt_ctor_value(ctor_name, var_term_id, model));
            }
            // Fall back: pick the first tester that's true in the SAT model.
            for ctor_name in constructors {
                let tester_name = format!("is-{ctor_name}");
                for idx in 0..self.ctx.terms.len() {
                    let tid = TermId(idx as u32);
                    if let TermData::App(sym, args) = self.ctx.terms.get(tid) {
                        if sym.name() == tester_name && args.len() == 1 && args[0] == var_term_id {
                            if self.term_value(&model.sat_model, &model.term_to_var, tid)
                                == Some(true)
                            {
                                return Some(self.format_dt_ctor_value(
                                    ctor_name,
                                    var_term_id,
                                    model,
                                ));
                            }
                            break;
                        }
                    }
                }
            }

            // Strategy 2: For combined DT+UF solvers with EUF model, match by
            // equivalence class (nullary constructors share the same element name).
            if let Some(ref euf_model) = model.euf_model {
                if let Some(elem) = euf_model.term_values.get(&var_term_id) {
                    for ctor_name in constructors {
                        if let Some(info) = self.ctx.symbol_info(ctor_name) {
                            if info.arg_sorts.is_empty() {
                                if let Some(ctor_term_id) = info.term {
                                    if euf_model.term_values.get(&ctor_term_id) == Some(elem) {
                                        return Some(ctor_name.clone());
                                    }
                                }
                            }
                        }
                    }
                }
            }

            // Strategy 3: Single-constructor DTs always use that constructor.
            // This handles nested DT values where no tester term exists in the
            // term store (e.g., `(val x)` returning a `Pair` with only `mkpair`) (#5432).
            if constructors.len() == 1 {
                return Some(self.format_dt_ctor_value(&constructors[0], var_term_id, model));
            }

            // Strategy 4: Check assertion equalities for constructor values (#5450).
            // In pure QF_DT, selector values like `(val m1)` may be constrained by
            // assertions like `(= (val m1) Green)`. If the assertion's other side
            // evaluates to a known constructor name, return that constructor.
            if let Some(EvalValue::Element(ref elem)) =
                self.extract_value_from_asserted_equalities(model, var_term_id)
            {
                if constructors.iter().any(|c| c == elem) {
                    return Some(elem.clone());
                }
            }

            // No constructor determined — the value is fully unconstrained /
            // under-determined. Render a concrete canonical default constructor
            // rather than leaking the internal `@Sort!n` representative, which is
            // not a valid SMT-LIB term (z3 rejects it as an unknown constant).
            // Every constrained / tester-determined value returned via the
            // strategies above is unaffected (#model-witness-no-skolem).
            return self.datatype_canonical_value(sort_name, &mut Vec::new());
        }
        None
    }

    /// Find the constructor argument term for a DT-sorted variable at a given
    /// field position from an asserted equality `(= var (Ctor a0 a1 ...))` (#5450).
    ///
    /// In pure QF_DT (no theory model for selector applications), the only place
    /// a field value lives is the constructor application on the other side of an
    /// asserted equality. This returns the argument term-id at `field_idx` when
    /// the equality holds in the SAT model, so the caller can evaluate the
    /// concrete argument (e.g. the `42` in `(= b (MkBox 42))`) directly.
    pub(super) fn constructor_arg_from_asserted_eq(
        &self,
        var_term_id: TermId,
        ctor_name: &str,
        field_idx: usize,
        model: &Model,
    ) -> Option<TermId> {
        for &assertion in &self.ctx.assertions {
            let TermData::App(sym, args) = self.ctx.terms.get(assertion) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            // The equality must hold to be relied upon. A top-level `=`
            // assertion is unconditionally asserted true, so default to true
            // when the SAT model has no entry (recovered/dummy model) (#5450).
            let eq_true = self
                .term_value(&model.sat_model, &model.term_to_var, assertion)
                .unwrap_or(true);
            if !eq_true {
                continue;
            }
            let other = if args[0] == var_term_id {
                args[1]
            } else if args[1] == var_term_id {
                args[0]
            } else {
                continue;
            };
            // The other side must be an application of the same constructor.
            if let TermData::App(other_sym, ctor_args) = self.ctx.terms.get(other) {
                if other_sym.name() == ctor_name && field_idx < ctor_args.len() {
                    return Some(ctor_args[field_idx]);
                }
            }
        }
        None
    }

    /// Format a DT constructor value with evaluated selector arguments.
    ///
    /// Looks up selector application terms `(sel var)` in the term store and
    /// resolves their values from theory-specific models (BV, LIA, LRA, EUF).
    fn format_dt_ctor_value(&self, ctor_name: &str, var_term_id: TermId, model: &Model) -> String {
        let selectors = self.ctx.constructor_selectors(ctor_name).unwrap_or(&[]);
        if selectors.is_empty() {
            return self.dt_surface(ctor_name).to_string();
        }
        // Non-nullary: find selector application terms and look up their values
        // directly in the theory models. evaluate_term doesn't handle unrecognized
        // function apps (like selectors) in BV/LIA models, so we look up directly.
        let mut arg_strs = Vec::new();
        for (field_idx, sel_name) in selectors.iter().enumerate() {
            // (0) The term is ITSELF a constructor application `(Ctor a0 a1 ...)`
            // — e.g. a constant bound by eager single-constructor datatype
            // elimination. Its field values ARE the constructor arguments. The
            // `(sel var)` applications were folded away at elaboration
            // (`sel_i(C(..)) -> a_i`), so the per-selector store scan below would
            // not find them; read the argument term directly.
            let direct_field: Option<TermId> = match self.ctx.terms.get(var_term_id) {
                TermData::App(sym, cargs) if sym.name() == ctor_name && field_idx < cargs.len() => {
                    Some(cargs[field_idx])
                }
                _ => None,
            };
            if let Some(field_term) = direct_field {
                if let Some(s) = self.format_field_term_value(field_term, model) {
                    arg_strs.push(s);
                    continue;
                }
            }
            // Prefer the concrete argument from an asserted equality
            // `(= var (Ctor a0 a1 ...))`. In pure QF_DT this is the only source
            // of truth for field values, since no theory model tracks selector
            // applications (#5450).
            if let Some(arg_tid) =
                self.constructor_arg_from_asserted_eq(var_term_id, ctor_name, field_idx, model)
            {
                let arg_sort = self.ctx.terms.sort(arg_tid);
                if let Sort::Uninterpreted(sort_name) = arg_sort {
                    if let Some(resolved) = self.resolve_dt_value(sort_name, arg_tid, model) {
                        arg_strs.push(resolved);
                        continue;
                    }
                }
                // An array-sorted field must render as a `store`-chain that
                // satisfies its asserted `(select (sel var) i) = v` constraints,
                // not the bare const-array default (#model-array-witness).
                if matches!(arg_sort, Sort::Array(_)) {
                    if let Some(value) = self.format_array_witness_value(model, arg_tid, arg_sort) {
                        arg_strs.push(value);
                        continue;
                    }
                }
                let val = self.lookup_term_value(model, arg_tid);
                if !matches!(val, EvalValue::Unknown) {
                    arg_strs.push(self.format_eval_value(&val, arg_tid));
                    continue;
                }
            }
            let mut found = false;
            for idx in 0..self.ctx.terms.len() {
                let tid = TermId(idx as u32);
                if let TermData::App(sym, args) = self.ctx.terms.get(tid) {
                    if sym.name() == sel_name.as_str() && args.len() == 1 && args[0] == var_term_id
                    {
                        let sel_sort = self.ctx.terms.sort(tid);
                        // For DT-sorted selectors, recursively resolve to a
                        // constructor expression instead of returning the opaque
                        // element name like `@Pair!0` (#5432).
                        if let Sort::Uninterpreted(sort_name) = sel_sort {
                            if let Some(resolved) = self.resolve_dt_value(sort_name, tid, model) {
                                arg_strs.push(resolved);
                                found = true;
                                break;
                            }
                        }
                        // Array-sorted field: render a `store`-chain that
                        // satisfies its asserted `(select (sel var) i) = v`
                        // constraints (the selector application `tid` IS the
                        // array term read by those selects) instead of the
                        // const-array default (#model-array-witness).
                        if matches!(sel_sort, Sort::Array(_)) {
                            if let Some(value) =
                                self.format_array_witness_value(model, tid, sel_sort)
                            {
                                arg_strs.push(value);
                                found = true;
                                break;
                            }
                        }
                        let mut val = self.lookup_term_value(model, tid);
                        // #5506: For Int-sorted selectors with no LIA model value,
                        // scan assertions for inequality/equality constraints and
                        // pick a satisfying integer value instead of defaulting to 0.
                        if matches!(val, EvalValue::Unknown) && matches!(sel_sort, Sort::Int) {
                            if let Some(v) = self.extract_int_from_assertion_bounds(tid) {
                                val = EvalValue::Rational(BigRational::from(v));
                            }
                        }
                        // #1766: Same for Real-sorted selectors with no LRA model value.
                        if matches!(val, EvalValue::Unknown) && matches!(sel_sort, Sort::Real) {
                            if let Some(v) = self.extract_real_from_assertion_bounds(tid) {
                                val = EvalValue::Rational(v);
                            }
                        }
                        // For DT-sorted selectors whose value is unknown or an
                        // opaque internal name (`@Color!0`), render a concrete
                        // canonical default constructor of the field sort instead
                        // of leaking the `@Sort!n` skolem. `canonical_default_value`
                        // prefers a nullary constructor but also handles no-nullary
                        // recursive datatypes (#5450, #model-witness-no-skolem).
                        if self.datatype_sort_name(sel_sort).is_some() {
                            let needs_default = match &val {
                                EvalValue::Unknown => true,
                                EvalValue::Element(elem) => elem.starts_with('@'),
                                _ => false,
                            };
                            if needs_default {
                                arg_strs.push(self.canonical_default_value(sel_sort));
                                found = true;
                                break;
                            }
                        }
                        arg_strs.push(self.format_eval_value(&val, tid));
                        found = true;
                        break;
                    }
                }
            }
            if !found {
                // The field's sort MUST come from THIS constructor's declaration,
                // not from `symbol_sort(sel_name)`: a selector name like `fld_data`
                // is SHARED across datatypes (`Vec_PbTerm`, `Vec_bv40`,
                // `Vec_PbConstraint` all declare `fld_data`), so the global
                // symbol-sort lookup can resolve to a SIBLING datatype's field sort
                // (e.g. `Array _ (_ BitVec 40)` instead of `Array _ PbTerm`),
                // emitting an ill-sorted canonical default that z3 rejects
                // (#dt-shared-selector-field-sort). Take the field sort by index
                // from the constructor's own selector info.
                let field_sort = self
                    .ctx
                    .constructor_selector_info(ctor_name)
                    .and_then(|fields| fields.get(field_idx))
                    .map(|(_, fs)| fs.clone())
                    .or_else(|| self.ctx.symbol_sort(sel_name).cloned());
                if let Some(sel_sort) = field_sort {
                    // A skolem-free concrete default for the field's sort
                    // (datatype -> canonical constructor, array -> const default,
                    // scalar -> scalar default), never an `@Sort!n` representative.
                    arg_strs.push(self.canonical_default_value(&sel_sort));
                } else {
                    arg_strs.push("?".to_string());
                }
            }
        }
        format!("({} {})", self.dt_surface(ctor_name), arg_strs.join(" "))
    }

    /// Evaluate a constructor-argument TERM (the term that supplies a field's
    /// value) to its model string, returning `None` when it cannot be resolved.
    ///
    /// Used when a datatype value is a literal constructor application
    /// `(Ctor a0 a1 ...)` (e.g. from eager single-constructor elimination): each
    /// `a_i` is read here rather than through a `(sel var)` selector application
    /// (which the fold removed). Mirrors the per-selector resolution: a
    /// datatype-sorted field recurses to a constructor expression; an Int/Real
    /// field constrained only by inequalities is satisfied from the assertion
    /// bounds instead of defaulting.
    fn format_field_term_value(&self, field_term: TermId, model: &Model) -> Option<String> {
        if let Sort::Uninterpreted(sort_name) = self.ctx.terms.sort(field_term) {
            if let Some(resolved) = self.resolve_dt_value(sort_name, field_term, model) {
                return Some(resolved);
            }
        }
        // An array-sorted field renders as a `store`-chain satisfying its
        // asserted `(select field i) = v` constraints (#model-array-witness).
        let field_sort = self.ctx.terms.sort(field_term);
        if matches!(field_sort, Sort::Array(_)) {
            return self.format_array_witness_value(model, field_term, field_sort);
        }
        let mut val = self.lookup_term_value(model, field_term);
        if matches!(val, EvalValue::Unknown) {
            match self.ctx.terms.sort(field_term) {
                Sort::Int => {
                    if let Some(v) = self.extract_int_from_assertion_bounds(field_term) {
                        val = EvalValue::Rational(BigRational::from(v));
                    }
                }
                Sort::Real => {
                    if let Some(v) = self.extract_real_from_assertion_bounds(field_term) {
                        val = EvalValue::Rational(v);
                    }
                }
                _ => {}
            }
        }
        (!matches!(val, EvalValue::Unknown)).then(|| self.format_eval_value(&val, field_term))
    }

    /// Look up a term's value directly from theory models.
    ///
    /// Unlike `evaluate_term`, this checks BV/LIA/LRA/EUF models by TermId
    /// without trying to evaluate the term recursively. This is needed for
    /// DT selector applications whose TermIds are mapped in theory models
    /// but whose function names are not recognized by `evaluate_term`.
    pub(super) fn lookup_term_value(&self, model: &Model, term_id: TermId) -> EvalValue {
        self.lookup_term_value_inner(model, term_id, true)
    }

    /// [`Self::lookup_term_value`] WITHOUT the total-datatype-model pin read.
    ///
    /// The single-source e-graph assignment builder (#mv-dt-single-source)
    /// derives every value from the solver e-graph plus the raw theory
    /// models; reading another completion engine's fabricated defaults
    /// (`Model::dt_pins`, #dt-total-model) into that derivation would let the
    /// two engines' free-slack choices collide (observed: repair-loop
    /// separation failures on deep free Nat classes) and defeat the
    /// single-source property the MV printer depends on.
    pub(super) fn lookup_term_value_no_dt_pins(&self, model: &Model, term_id: TermId) -> EvalValue {
        self.lookup_term_value_inner(model, term_id, false)
    }

    fn lookup_term_value_inner(
        &self,
        model: &Model,
        term_id: TermId,
        use_dt_pins: bool,
    ) -> EvalValue {
        // Every direct source below is keyed only by the ambient TermId. Under
        // beta reduction, fail closed for a dependent term: this helper is
        // commonly reached only after recursive evaluation returned Unknown,
        // so re-entering it here could recurse. Reusing an ambient pin would
        // also conflate distinct lambda instances.
        if term_depends_on_scoped_binding(&self.ctx.terms, term_id) {
            return EvalValue::Unknown;
        }
        // A literal constant denotes itself. The by-TermId theory-model rows
        // below can carry a stale/defaulted value for a literal the theory
        // never tracked as a variable (observed: the eager DT lane's LIA
        // extraction mapping `Const(Int(1))` to 0), and the e-graph value
        // assignment reads ctor-argument scalars through this helper — a
        // junk row must never override the literal (#mv-dt-single-source).
        if matches!(self.ctx.terms.get(term_id), TermData::Const(_)) {
            return self.evaluate_term(model, term_id);
        }
        // Total-datatype-model pins (#dt-total-model): the constructed value
        // is authoritative for every pinned term, and it must be read HERE as
        // well as in `evaluate_term` — this lookup otherwise reads the raw
        // EUF `@Sort!n` representative for a datatype-sorted term, which
        // string-compares unequal against a co-class term's pinned canonical
        // value and would make the materialized re-evaluator demote a
        // genuinely-consistent model.
        if use_dt_pins && !model.dt_pins.is_empty() {
            if let Some(pin) = model.dt_pins.get(&term_id) {
                return pin.clone();
            }
        }
        let sort = self.ctx.terms.sort(term_id);

        // Check BV model for BitVec-sorted terms.
        if let Sort::BitVec(bv) = sort {
            if let Some(ref bv_model) = model.bv_model {
                if let Some(val) = bv_model.values.get(&term_id) {
                    return EvalValue::BitVec {
                        value: val.clone(),
                        width: bv.width,
                    };
                }
            }
        }

        // Check LIA model for Int-sorted terms.
        if matches!(sort, Sort::Int) {
            if let Some(ref lia_model) = model.lia_model {
                if let Some(val) = lia_model.values.get(&term_id) {
                    return EvalValue::Rational(BigRational::from(val.clone()));
                }
            }
        }

        // Check LRA model for Real-sorted terms (and Int fallback).
        if matches!(sort, Sort::Int | Sort::Real) {
            if let Some(ref lra_model) = model.lra_model {
                if let Some(val) = lra_model.values.get(&term_id) {
                    return EvalValue::Rational(val.clone());
                }
            }
        }

        // Check EUF model for uninterpreted sorts.
        if let Some(ref euf_model) = model.euf_model {
            if let Some(elem) = euf_model.term_values.get(&term_id) {
                return EvalValue::Element(elem.clone());
            }
        }

        // Check Bool in SAT model.
        if matches!(sort, Sort::Bool) {
            if let Some(val) = self.term_value(&model.sat_model, &model.term_to_var, term_id) {
                return EvalValue::Bool(val);
            }
        }

        // For pure DT logic (no LIA/LRA/BV theory solver), selector values
        // are not tracked by any theory model. Extract the value from assertion
        // equalities like `(= (sel x) constant)` that are true in the SAT model (#5432).
        if let Some(val) = self.extract_value_from_asserted_equalities(model, term_id) {
            return val;
        }

        // Fall back to recursive evaluation for computed values.
        self.evaluate_term(model, term_id)
    }

    /// Extract a term's value from assertion equalities in the SAT model.
    ///
    /// Scans assertions for `(= term_id expr)` or `(= expr term_id)` patterns
    /// where the equality holds true in the SAT model. Evaluates the other side
    /// of the equality to obtain the value. This handles the pure DT case where
    /// no arithmetic theory solver is active (#5432).
    pub(super) fn extract_value_from_asserted_equalities(
        &self,
        model: &Model,
        term_id: TermId,
    ) -> Option<EvalValue> {
        // A constant is its own value; never resolve it through an equality.
        // Otherwise `(= (sel x) 1)` would make the constant `1` "resolve" back
        // to `(sel x)`, creating a selector<->constant evaluation cycle (#5450).
        if let TermData::Const(_) = self.ctx.terms.get(term_id) {
            let val = self.evaluate_term(model, term_id);
            return (!matches!(val, EvalValue::Unknown)).then_some(val);
        }
        for &assertion in &self.ctx.assertions {
            // Look for equalities involving term_id
            if let TermData::App(sym, args) = self.ctx.terms.get(assertion) {
                if sym.name() == "=" && args.len() == 2 {
                    // Check if this equality is true in the SAT model. A
                    // top-level `=` assertion is unconditionally asserted true,
                    // so when the SAT model has no entry for it (e.g. a recovered
                    // model after the trivially-true fast path), default to true
                    // rather than false (#5450).
                    let eq_true = self
                        .term_value(&model.sat_model, &model.term_to_var, assertion)
                        .unwrap_or(true);
                    if !eq_true {
                        continue;
                    }
                    // Match (= term_id other) or (= other term_id)
                    let other = if args[0] == term_id {
                        args[1]
                    } else if args[1] == term_id {
                        args[0]
                    } else {
                        continue;
                    };
                    // Evaluate the other side — constants evaluate directly
                    let val = self.evaluate_term(model, other);
                    if !matches!(val, EvalValue::Unknown) {
                        return Some(val);
                    }
                    // Nullary DT constructors are stored as TermData::Var
                    // (#1745). In pure QF_DT (no EUF model), evaluate_term
                    // returns Unknown for them. Recognize them directly.
                    if let TermData::Var(name, _) = self.ctx.terms.get(other) {
                        if self.ctx.is_constructor(name).is_some() {
                            return Some(EvalValue::Element(name.clone()));
                        }
                    }
                }
            }
        }
        None
    }

    /// Resolve a selector application `(sel var)` through an asserted equality
    /// `(= var (Ctor a0 a1 ...))` by plucking the constructor argument at the
    /// selector's field position (#5450).
    ///
    /// In pure QF_DT no theory model tracks selector applications, so the field
    /// value must come from the constructor term on the other side of an asserted
    /// equality. `sel_name` must be a selector of the constructor used; the field
    /// index is determined from the constructor's declared selector order.
    /// Returns `None` when `name`/`args` is not such a selector application or no
    /// matching asserted constructor equality holds in the SAT model.
    pub(super) fn eval_selector_via_constructor(
        &self,
        model: &Model,
        sel_name: &str,
        args: &[TermId],
    ) -> Option<EvalValue> {
        if args.len() != 1 {
            return None;
        }
        // Recursion guard: DT axiom injection creates derived selector/equality
        // terms (e.g. `(= (tail X) (cons a (tail Y)))`) that can form cyclic
        // resolution chains. Bound the nesting depth and return `None` (meaning
        // "cannot determine here") past the limit so the caller falls back to
        // its other strategies instead of looping forever (#5450). Returning
        // `None` is sound — it never invents a value.
        use std::cell::Cell;
        thread_local!(static SELVIA_DEPTH: Cell<u32> = const { Cell::new(0) });
        struct DepthGuard;
        impl Drop for DepthGuard {
            fn drop(&mut self) {
                SELVIA_DEPTH.with(|c| c.set(c.get().saturating_sub(1)));
            }
        }
        let depth = SELVIA_DEPTH.with(|c| {
            let v = c.get();
            c.set(v + 1);
            v
        });
        let _guard = DepthGuard;
        if depth >= 32 {
            return None;
        }
        let var_term_id = args[0];
        // Find which constructor owns this selector and at what field index.
        for (ctor_name, selectors) in self.ctx.ctor_selectors_iter() {
            let Some(field_idx) = selectors.iter().position(|s| s == sel_name) else {
                continue;
            };
            if let Some(arg_tid) =
                self.constructor_arg_from_asserted_eq(var_term_id, ctor_name, field_idx, model)
            {
                let val = self.lookup_term_value(model, arg_tid);
                if !matches!(val, EvalValue::Unknown) {
                    return Some(val);
                }
            }
        }
        None
    }

    /// Sort name of a datatype sort, else `None`.
    ///
    /// Declared datatypes surface either as `Sort::Uninterpreted(name)`
    /// (resolved against the datatype registry) or the inline `Sort::Datatype`
    /// form.
    pub(in crate::executor) fn datatype_sort_name(&self, sort: &Sort) -> Option<String> {
        match sort {
            Sort::Datatype(dt) => Some(dt.name.clone()),
            Sort::Uninterpreted(name) => self
                .ctx
                .datatype_iter()
                .any(|(n, _)| n == name)
                .then(|| name.clone()),
            _ => None,
        }
    }

    /// A concrete, skolem-free canonical default value of any sort, as SMT-LIB
    /// text — for rendering a fully unconstrained / under-determined model value
    /// (#model-witness-no-skolem).
    ///
    /// A datatype sort picks a canonical constructor (a nullary one if present,
    /// else the first constructor applied to canonical default field values,
    /// recursively); an array recurses into its element sort; every other sort
    /// uses its scalar default. Never emits an internal `@Sort!n` representative,
    /// which z3 rejects as an unknown constant.
    pub(super) fn canonical_default_value(&self, sort: &Sort) -> String {
        let mut visited = Vec::new();
        self.canonical_default_value_guarded(sort, &mut visited)
    }

    fn canonical_default_value_guarded(&self, sort: &Sort, visited: &mut Vec<String>) -> String {
        match sort {
            Sort::Array(arr) => format!(
                "((as const {}) {})",
                format_sort(sort),
                self.canonical_default_value_guarded(&arr.element_sort, visited)
            ),
            Sort::Datatype(dt) => self
                .datatype_canonical_value(&dt.name, visited)
                .unwrap_or_else(|| format_default_value(sort)),
            Sort::Uninterpreted(name) => self
                .datatype_canonical_value(name, visited)
                .unwrap_or_else(|| format_default_value(sort)),
            _ => format_default_value(sort),
        }
    }

    /// Canonical constructor value of a datatype `sort_name`: a nullary
    /// constructor if one exists, else the first constructor applied to canonical
    /// default field values (recursively). `visited` breaks recursion through
    /// self-referential field sorts. `None` when `sort_name` is not a declared
    /// datatype.
    pub(super) fn datatype_canonical_value(
        &self,
        sort_name: &str,
        visited: &mut Vec<String>,
    ) -> Option<String> {
        let constructors: Vec<String> = self
            .ctx
            .datatype_iter()
            .find(|(n, _)| *n == sort_name)
            .map(|(_, cs)| cs.to_vec())?;

        // Prefer a nullary constructor — the simplest canonical inhabitant, and
        // always safe under recursion.
        for ctor in &constructors {
            if self
                .ctx
                .constructor_selector_info(ctor)
                .map_or(true, |fields| fields.is_empty())
            {
                return Some(self.dt_surface(ctor).to_string());
            }
        }

        // No nullary constructor and this sort is already on the recursion path
        // (a non-well-founded / degenerate datatype): best-effort first
        // constructor name to terminate without looping.
        if visited.iter().any(|s| s == sort_name) {
            return constructors.first().map(|c| self.dt_surface(c).to_string());
        }
        visited.push(sort_name.to_string());

        // Pick a well-founded constructor: prefer one whose field sorts do not
        // re-enter a datatype already on the recursion path (e.g. `leaf` over
        // `node` for a `Tree`), so the recursion terminates at a finite ground
        // term. Fall back to the first constructor otherwise.
        let choice = constructors
            .iter()
            .find(|ctor| {
                self.ctx
                    .constructor_selector_info(ctor)
                    .map_or(false, |fields| {
                        !fields
                            .iter()
                            .any(|(_, fs)| Self::sort_revisits_datatype(fs, visited))
                    })
            })
            .or_else(|| constructors.first());

        let result = choice.map(|ctor| {
            let fields = self.ctx.constructor_selector_info(ctor).unwrap_or(&[]);
            if fields.is_empty() {
                self.dt_surface(ctor).to_string()
            } else {
                let args: Vec<String> = fields
                    .iter()
                    .map(|(_, field_sort)| {
                        self.canonical_default_value_guarded(field_sort, visited)
                    })
                    .collect();
                format!("({} {})", self.dt_surface(ctor), args.join(" "))
            }
        });
        visited.pop();
        result
    }

    /// Whether `sort` references (directly, or through an array element sort) a
    /// datatype whose name is already on the canonical-default recursion path.
    fn sort_revisits_datatype(sort: &Sort, visited: &[String]) -> bool {
        match sort {
            Sort::Datatype(dt) => visited.iter().any(|s| s == &dt.name),
            Sort::Uninterpreted(name) => visited.iter().any(|s| s == name),
            Sort::Array(arr) => Self::sort_revisits_datatype(&arr.element_sort, visited),
            _ => false,
        }
    }

    // Arithmetic bound extraction methods are in dt_bounds.rs.

    /// Resolve a datatype-sorted term `term` to the constructor that the
    /// candidate model assigns it, returning `(ctor_name, sort_name)`.
    ///
    /// Used by the materialized datatype re-evaluator (`dt_mat_eval`) to walk a
    /// selector chain through the model's actual constructor assignment, even
    /// when the field values themselves are left unconstrained. Returns `None`
    /// when the sort is not a datatype or the constructor is undetermined.
    /// PHASE 1 CENSUS (#dt-array-model-census): the SOLE certification boundary
    /// for a datatype-carrying-array SAT. Reconstructs the datatype-array fragment
    /// of `model` and returns `true` ONLY when it is provably consistent + fully
    /// decidable — a positive concrete witness that the returned SAT is genuine.
    /// Otherwise `false` (the caller degrades to a sound `unknown`).
    ///
    /// Sound BY CONSTRUCTION and can ONLY fail to `unknown`, never to a false SAT:
    /// - Array cells are keyed by the MODEL-EVALUATED index VALUE (not the
    ///   syntactic index term), so datatype-valued SELECT-CONGRUENCE at a
    ///   DERIVED-equal index and constructor-INDEX injectivity hold automatically
    ///   (`bvadd i c = bvadd j c` under `i=j` collapse to one key; `mk(a)=mk(b)`
    ///   iff the reconstructed index tuples are equal).
    /// - Array IDENTITY is taken from the MODEL: a union-find over array terms that
    ///   unions (a) every UNCONDITIONALLY-asserted top-level array equality
    ///   `(= X Y)` and (b) two array-valued selects `(select A i)`,`(select A' j)`
    ///   whose bases are already identified and whose indices EVALUATE equal — the
    ///   latter derives NESTED inner-array identity from the model's index values
    ///   (so the reverted escape-a's syntactic-grouping gap is closed).
    /// - Within an identity class, two datatype-valued reads at the SAME evaluated
    ///   index that reconstruct to DIFFERENT canonical values are a
    ///   select-congruence CONFLICT -> reject. An UNDECIDABLE index or a needed but
    ///   undecidable value -> reject (fail-closed; an extraction gap is never a
    ///   certification). An asserted DISTINCT/`(not (= X Y))` whose operands
    ///   reconstruct to equal maps (no differing witnessed cell) -> reject.
    ///
    /// Runs AFTER the strict per-assertion oracle (which validated the scalar/BV
    /// and decidable-datatype assertions), so a `true` means the model satisfies
    /// the whole datatype-array fragment.
    pub(in crate::executor) fn datatype_array_census_certifies(&self, model: &Model) -> bool {
        /// Reconstruction depth for datatype canonical values.
        const CANON_DEPTH: u32 = 20;
        let datatype_ctors: HashSet<String> = self
            .ctx
            .datatype_iter()
            .map(|(n, _)| n.to_string())
            .collect();
        if datatype_ctors.is_empty() {
            return false;
        }

        // A sort that (recursively, through arrays) carries a declared datatype.
        let carries_dt =
            |sort: &Sort| -> bool { self.census_sort_carries_dt(sort, &datatype_ctors) };
        // Is the array `arr` a datatype-carrying array?
        let is_dt_array = |arr: TermId, exec: &Self| -> bool {
            matches!(exec.ctx.terms.sort(arr), Sort::Array(a)
                if exec.census_sort_carries_dt(&a.index_sort, &datatype_ctors)
                    || exec.census_sort_carries_dt(&a.element_sort, &datatype_ctors))
        };

        // (1) Model array-identity: reachable terms, union-find over model-true
        // array equalities + derived nested-select identity, and the observed
        // cell function per identity class. Shared verbatim with the general
        // select-congruence gate so the two never diverge.
        let (reachable, uf, class_cells) = self.census_build_identity(model);

        // The census is the certification boundary for datatype-ELEMENT arrays
        // (select-congruence over datatype VALUES). A problem whose only
        // datatype-carrying arrays are datatype-INDEXED (with a scalar element)
        // has no datatype-value congruence obligation for the census to discharge;
        // certifying it here would short-circuit the model completion the normal
        // bypass path performs, yielding a model the independent gate cannot
        // confirm (a genuine SAT wrongly degraded). Defer those to the existing
        // gate/bypass. (#dt-array-census-element-only)
        let has_dt_element_array = reachable.iter().any(|&t| {
            matches!(self.ctx.terms.sort(t), Sort::Array(a)
                if self.census_sort_carries_dt(&a.element_sort, &datatype_ctors))
        });
        if !has_dt_element_array {
            return false;
        }

        // (2) Group datatype-carrying-array selects by (identity class, evaluated
        // index). A select whose index is undecidable fails closed.
        let mut groups: HashMap<(TermId, String), Vec<TermId>> = HashMap::default();
        for &t in &reachable {
            let (array, index) = match self.ctx.terms.get(t) {
                TermData::App(sym, args) if sym.name() == "select" && args.len() == 2 => {
                    (args[0], args[1])
                }
                _ => continue,
            };
            if !is_dt_array(array, self) {
                continue;
            }
            let Some(idx_key) = self.census_index_key(model, index) else {
                if std::env::var_os("AY_CENSUS_TRACE").is_some() {
                    eprintln!(
                        "c census-reject undecidable-index sort={}",
                        self.ctx.terms.sort(index)
                    );
                }
                return false; // undecidable index over a datatype-carrying array
            };
            let cls = Self::census_find(&uf, array);
            groups.entry((cls, idx_key)).or_default().push(t);
        }
        // Select-congruence: every 2+ group's reads must all be pairwise
        // COMPATIBLE — completable to one shared value. Compatibility (not
        // string-equal canonicals) is the sound notion for values that carry
        // arrays: two array fields agree iff they never disagree on a COMMON
        // observed cell; disjoint / unconstrained cells complete freely. A
        // definite incompatibility (differing ctor, differing scalar, or a
        // common cell that conflicts) is a real congruence violation; an
        // undecidable comparison fails closed to `unknown`.
        for reads in groups.values() {
            if reads.len() < 2 {
                continue;
            }
            for i in 0..reads.len() {
                for j in (i + 1)..reads.len() {
                    match self.census_compatible(
                        model,
                        reads[i],
                        reads[j],
                        &class_cells,
                        &uf,
                        CANON_DEPTH,
                    ) {
                        Some(true) => {}
                        Some(false) => {
                            if std::env::var_os("AY_CENSUS_TRACE").is_some() {
                                eprintln!(
                                    "c census-reject congruence-conflict {} vs {}",
                                    self.census_value_key(model, reads[i], CANON_DEPTH)
                                        .unwrap_or_else(|| "?".into()),
                                    self.census_value_key(model, reads[j], CANON_DEPTH)
                                        .unwrap_or_else(|| "?".into()),
                                );
                            }
                            return false; // congruence conflict (definite)
                        }
                        None => {
                            if std::env::var_os("AY_CENSUS_TRACE").is_some() {
                                eprintln!(
                                    "c census-reject undecidable-value sort={}",
                                    self.ctx.terms.sort(reads[i]),
                                );
                            }
                            return false; // undecidable comparison -> fail closed
                        }
                    }
                }
            }
        }

        // (3) Validate asserted DISTINCT / (not (= X Y)) over datatype-carrying
        // arrays: each operand pair must have a WITNESSED differing cell (a common
        // evaluated index at which the reconstructed values differ). If two
        // operands' observed cells agree on every common key, the model cannot be
        // shown to satisfy the disequality -> fail closed.
        for &a in &self.ctx.assertions {
            let operands: Vec<TermId> = match self.ctx.terms.get(a) {
                TermData::App(sym, args) if sym.name() == "distinct" => args.clone(),
                TermData::Not(inner) => match self.ctx.terms.get(*inner) {
                    TermData::App(s2, a2) if s2.name() == "=" && a2.len() == 2 => a2.clone(),
                    _ => continue,
                },
                _ => continue,
            };
            let dt_operands: Vec<TermId> = operands
                .into_iter()
                .filter(|&o| {
                    carries_dt(self.ctx.terms.sort(o)) && self.ctx.terms.sort(o).is_array()
                })
                .collect();
            for i in 0..dt_operands.len() {
                for j in (i + 1)..dt_operands.len() {
                    if !self.census_arrays_witnessed_distinct(
                        model,
                        dt_operands[i],
                        dt_operands[j],
                        &uf,
                        &groups,
                        &class_cells,
                        CANON_DEPTH,
                    ) {
                        return false;
                    }
                }
            }
        }

        true
    }

    /// Build the model's array-identity structure, shared by the datatype census
    /// and the general select-congruence gate: `(reachable, uf, class_cells)`.
    ///
    /// - `reachable`: every term reachable from the assertions (App/Not/Ite/Let).
    /// - `uf`: union-find over array-sorted terms — unions every reachable array
    ///   equality the MODEL committed to TRUE (top-level asserted OR a nested
    ///   literal the SAT assignment set true), then fixpoint-unions array-valued
    ///   selects `(select A i)` whose base is already identified and whose index
    ///   is model-equal (derives nested inner-array identity). A model-FALSE or
    ///   undetermined equality does not force identity, so it is not unioned.
    /// - `class_cells`: per identity-class rep, the `(evaluated-index key, select
    ///   term)` cells actually read on that class.
    fn census_build_identity(
        &self,
        model: &Model,
    ) -> (
        HashSet<TermId>,
        HashMap<TermId, TermId>,
        HashMap<TermId, Vec<(String, TermId)>>,
    ) {
        let mut reachable: HashSet<TermId> = Default::default();
        {
            let mut stack: Vec<TermId> = self.ctx.assertions.clone();
            while let Some(t) = stack.pop() {
                if !reachable.insert(t) {
                    continue;
                }
                match self.ctx.terms.get(t) {
                    TermData::App(_, args) => stack.extend(args.iter().copied()),
                    TermData::Not(inner) => stack.push(*inner),
                    TermData::Ite(c, th, el) => {
                        stack.push(*c);
                        stack.push(*th);
                        stack.push(*el);
                    }
                    TermData::Let(bindings, body) => {
                        stack.push(*body);
                        for (_, v) in bindings {
                            stack.push(*v);
                        }
                    }
                    _ => {}
                }
            }
        }

        let mut uf: HashMap<TermId, TermId> = HashMap::default();
        let mut union = |uf: &mut HashMap<TermId, TermId>, x: TermId, y: TermId| {
            let rx = Self::census_find(uf, x);
            let ry = Self::census_find(uf, y);
            if rx != ry {
                uf.insert(rx, ry);
            }
        };
        for &t in &reachable {
            if let TermData::App(sym, args) = self.ctx.terms.get(t) {
                if sym.name() == "="
                    && args.len() == 2
                    && matches!(self.ctx.terms.sort(args[0]), Sort::Array(_))
                    && self.sat_term_assigned_true(model, t)
                {
                    union(&mut uf, args[0], args[1]);
                }
            }
        }
        let mut arr_selects: Vec<(TermId, TermId, TermId)> = Vec::new(); // (select, base, index)
        for &t in &reachable {
            if let TermData::App(sym, args) = self.ctx.terms.get(t) {
                if sym.name() == "select"
                    && args.len() == 2
                    && matches!(self.ctx.terms.sort(t), Sort::Array(_))
                {
                    arr_selects.push((t, args[0], args[1]));
                }
            }
        }
        let arr_sel_idx: Vec<Option<String>> = arr_selects
            .iter()
            .map(|&(_, _, idx)| self.census_index_key(model, idx))
            .collect();
        // Fixpoint-union array-valued selects that read the SAME inner array:
        // equal base identity class AND equal evaluated index. Grouped by
        // (base-class rep, index key) each round — O(N) per round — instead of the
        // naive O(N^2) pairwise scan (which cost ~140s on the 1259-array aterm
        // instance). Semantically identical: every select sharing a group is
        // unioned to that group's representative, so the final classes match.
        loop {
            let mut changed = false;
            let mut groups: HashMap<(TermId, &str), TermId> = HashMap::default();
            for (i, &(sel, base, _)) in arr_selects.iter().enumerate() {
                let Some(k) = arr_sel_idx[i].as_deref() else {
                    continue;
                };
                let key = (Self::census_find(&uf, base), k);
                match groups.get(&key) {
                    Some(&rep) => {
                        if Self::census_find(&uf, sel) != Self::census_find(&uf, rep) {
                            union(&mut uf, sel, rep);
                            changed = true;
                        }
                    }
                    None => {
                        groups.insert(key, sel);
                    }
                }
            }
            if !changed {
                break;
            }
        }

        let mut class_cells: HashMap<TermId, Vec<(String, TermId)>> = HashMap::default();
        for &t in &reachable {
            if let TermData::App(sym, args) = self.ctx.terms.get(t) {
                if sym.name() == "select" && args.len() == 2 {
                    if let Some(k) = self.census_index_key(model, args[1]) {
                        let cls = Self::census_find(&uf, args[0]);
                        class_cells.entry(cls).or_default().push((k, t));
                    }
                }
            }
        }
        (reachable, uf, class_cells)
    }

    /// General model-based SELECT-CONGRUENCE gate — the sound backstop for the
    /// eager array encoding's derived-equal-index hole for ANY element sort
    /// (uninterpreted, scalar, datatype). Returns `true` iff the candidate model
    /// DEFINITELY violates select-congruence: two reads on the same array
    /// identity class at the same evaluated index whose element values are
    /// provably incompatible (`census_compatible == Some(false)`). The caller
    /// degrades such a SAT to a sound `unknown`.
    ///
    /// This is degrade-on-PROVEN-violation (not certify): a genuine SAT model is
    /// select-congruent on its read cells, so it never trips; only a model the
    /// eager encoding left congruence-inconsistent (the pre-existing
    /// `declare-sort E` array false-SAT class) is caught. Undecidable comparisons
    /// do NOT trip it — completeness is preserved for everything except the
    /// specific inconsistency.
    pub(in crate::executor) fn array_select_congruence_violated(&self, model: &Model) -> bool {
        const CANON_DEPTH: u32 = 20;
        let (_reachable, uf, class_cells) = self.census_build_identity(model);
        // Group ALL selects by (identity class, evaluated index).
        let mut cells: HashMap<(TermId, String), Vec<TermId>> = HashMap::default();
        for (cls, list) in &class_cells {
            for (k, t) in list {
                cells.entry((*cls, k.clone())).or_default().push(*t);
            }
        }
        for reads in cells.values() {
            if reads.len() < 2 {
                continue;
            }
            for i in 0..reads.len() {
                for j in (i + 1)..reads.len() {
                    if self.census_compatible(
                        model,
                        reads[i],
                        reads[j],
                        &class_cells,
                        &uf,
                        CANON_DEPTH,
                    ) == Some(false)
                    {
                        if std::env::var_os("AY_CENSUS_TRACE").is_some() {
                            eprintln!(
                                "c select-cong-violation {} vs {}",
                                self.census_value_key(model, reads[i], CANON_DEPTH)
                                    .unwrap_or_else(|| "?".into()),
                                self.census_value_key(model, reads[j], CANON_DEPTH)
                                    .unwrap_or_else(|| "?".into()),
                            );
                        }
                        return true; // proven select-congruence violation
                    }
                }
            }
        }
        false
    }

    /// Phase 2 CEGAR (#dt-array-cegar): distill the array select-congruence
    /// LEMMA that `model` violates — the theory tautology the deepening loop
    /// installs to prune the spurious model and re-solve. Finds the FIRST
    /// (identity class, evaluated index) cell holding two reads whose element
    /// values are definitely incompatible (`census_compatible == Some(false)`)
    /// and returns `(=> (and (= A B) (= i j)) (= (select A i) (select B j)))`
    /// for that pair. `None` when the model has no fixable congruence violation
    /// or the offending terms cannot form a same-sort equality.
    pub(in crate::executor) fn census_congruence_cegar_lemma(
        &mut self,
        model: &Model,
    ) -> Option<TermId> {
        const CANON_DEPTH: u32 = 20;
        // Phase A (immutable analysis): locate the first violating read pair.
        let pair = {
            let (_reachable, uf, class_cells) = self.census_build_identity(model);
            let mut cells: HashMap<(TermId, String), Vec<TermId>> = HashMap::default();
            for (cls, list) in &class_cells {
                for (k, t) in list {
                    cells.entry((*cls, k.clone())).or_default().push(*t);
                }
            }
            let mut found: Option<(TermId, TermId)> = None;
            'outer: for reads in cells.values() {
                if reads.len() < 2 {
                    continue;
                }
                for a in 0..reads.len() {
                    for b in (a + 1)..reads.len() {
                        if self.census_compatible(
                            model,
                            reads[a],
                            reads[b],
                            &class_cells,
                            &uf,
                            CANON_DEPTH,
                        ) == Some(false)
                        {
                            found = Some((reads[a], reads[b]));
                            break 'outer;
                        }
                    }
                }
            }
            found
        };
        let (r1, r2) = pair?;
        // Phase B (mutable construction): build the congruence lemma.
        self.build_select_congruence_lemma(model, r1, r2)
    }

    /// Strict-oracle CEGAR distillation (#dt-array-cegar): build the
    /// select-congruence tautology for the read pair of a strict-oracle-rejected
    /// (dis)equality `(= r1 r2)`. Thin visibility wrapper over
    /// [`Self::build_select_congruence_lemma`] — `None` unless both operands are
    /// binary `select`s forming same-sort equalities.
    pub(in crate::executor) fn strict_oracle_select_congruence_lemma(
        &mut self,
        model: &Model,
        r1: TermId,
        r2: TermId,
    ) -> Option<TermId> {
        self.build_select_congruence_lemma(model, r1, r2)
    }

    /// Build the array select-congruence tautology for two reads
    /// `r1 = (select A i)`, `r2 = (select B j)`:
    /// `(=> (and (= A B) (= i j)) (= r1 r2))` (dropping the `(= A B)` conjunct
    /// when `A` and `B` are the same term). `None` if either operand is not a
    /// binary `select` or the equalities are not same-sort.
    fn build_select_congruence_lemma(
        &mut self,
        model: &Model,
        r1: TermId,
        r2: TermId,
    ) -> Option<TermId> {
        let (a, i) = match self.ctx.terms.get(r1) {
            TermData::App(s, args) if s.name() == "select" && args.len() == 2 => (args[0], args[1]),
            _ => return None,
        };
        let (b, j) = match self.ctx.terms.get(r2) {
            TermData::App(s, args) if s.name() == "select" && args.len() == 2 => (args[0], args[1]),
            _ => return None,
        };
        if self.ctx.terms.sort(r1) != self.ctx.terms.sort(r2)
            || self.ctx.terms.sort(i) != self.ctx.terms.sort(j)
        {
            return None;
        }
        // Consequent: for a scalar/array read a direct `(= r1 r2)`; for a
        // DATATYPE-valued read, DECOMPOSE into its per-selector field equalities
        // (recursively). Equating two datatype VALUES makes the eager DT route
        // unroll the whole constructor/selector/injectivity axiom set for those
        // values — a multi-x clause blowup that memouts on large instances (the
        // aterm `Transition`-array census conflict). Each `(= (sel r1)(sel r2))`
        // under the shared antecedent is itself a selector-congruence tautology,
        // so the decomposition is verdict-preserving, and its leaves are BV/array
        // equalities the encoder already handles cheaply.
        let consequent = self.build_congruence_consequent(model, r1, r2, 8)?;
        let idx_eq = self.ctx.terms.mk_eq(i, j);
        let antecedent = if a == b {
            idx_eq
        } else {
            if self.ctx.terms.sort(a) != self.ctx.terms.sort(b) {
                return None;
            }
            let arr_eq = self.ctx.terms.mk_eq(a, b);
            self.ctx.terms.mk_and(vec![arr_eq, idx_eq])
        };
        Some(self.ctx.terms.mk_implies(antecedent, consequent))
    }

    /// Congruence consequent for two model-equal reads. A scalar/array leaf
    /// yields `(= r1 r2)` directly; a DATATYPE value yields the conjunction of
    /// its model-constructor selector-projection equalities (recursively to
    /// `depth`), so the emitted lemma bottoms out in BV/array equalities the
    /// eager encoder handles without unrolling a datatype-VALUE equality. Falls
    /// back to `(= r1 r2)` when the constructor is undecidable or a selector app
    /// is missing. Sound: each `(= (sel r1)(sel r2))` is a selector-congruence
    /// consequence of `r1 = r2`, so the decomposition preserves the verdict.
    fn build_congruence_consequent(
        &mut self,
        model: &Model,
        r1: TermId,
        r2: TermId,
        depth: u32,
    ) -> Option<TermId> {
        if self.ctx.terms.sort(r1) != self.ctx.terms.sort(r2) {
            return None;
        }
        let sort = self.ctx.terms.sort(r1).clone();
        let is_dt = matches!(&sort, Sort::Datatype(dt) if self.ctx.datatype_iter().any(|(n,_)| n==dt.name.as_str()))
            || matches!(&sort, Sort::Uninterpreted(n) if self.ctx.datatype_iter().any(|(d,_)| d==n.as_str()));
        if is_dt && depth > 0 {
            // Model constructor + its selector applications (all read-only).
            let pairs: Option<Vec<(TermId, TermId)>> =
                self.dt_constructor_of(model, r1).and_then(|(ctor, _)| {
                    let sels = self
                        .ctx
                        .constructor_selectors(&ctor)
                        .map(|s| s.to_vec())
                        .unwrap_or_default();
                    let mut pairs = Vec::with_capacity(sels.len());
                    for sel in sels {
                        let f1 = self.find_dt_selector_app(&sel, r1)?;
                        let f2 = self.find_dt_selector_app(&sel, r2)?;
                        pairs.push((f1, f2));
                    }
                    (!pairs.is_empty()).then_some(pairs)
                });
            if let Some(pairs) = pairs {
                let mut parts = Vec::with_capacity(pairs.len());
                for (f1, f2) in pairs {
                    parts.push(self.build_congruence_consequent(model, f1, f2, depth - 1)?);
                }
                return Some(self.ctx.terms.mk_and(parts));
            }
            // Constructor undecidable / selectors missing -> full equality.
        }
        Some(self.ctx.terms.mk_eq(r1, r2))
    }

    /// Union-find find (no compression; read-only over `uf`).
    fn census_find(uf: &HashMap<TermId, TermId>, x: TermId) -> TermId {
        let mut r = x;
        while let Some(&p) = uf.get(&r) {
            if p == r {
                break;
            }
            r = p;
        }
        r
    }

    /// A sort that (recursively through arrays and datatype fields) carries a
    /// declared datatype with an ARRAY-sorted constructor field — the
    /// `Slice{ptr,len,data}` shape. Rendering such a value into a committed
    /// array CELL forces the renderer to spell out the nested array field, and
    /// the per-term spelling cannot see cells observed through a CONGRUENT
    /// field term (`(dat (select A i))` vs `(dat (select A j))` under `i = j`),
    /// so the cell fabricates a collapsed const-default field the strict
    /// arrays oracle then correctly rejects (#dt-array-model-census). Callers
    /// use this to leave such arrays to the observation-based census instead
    /// of materializing unfaithful cells.
    pub(super) fn sort_carries_array_field_datatype(&self, sort: &Sort) -> bool {
        fn walk(exec: &Executor, sort: &Sort, visited: &mut Vec<String>) -> bool {
            let dt_name = match sort {
                Sort::Array(a) => {
                    return walk(exec, &a.index_sort, visited)
                        || walk(exec, &a.element_sort, visited);
                }
                Sort::Datatype(dt) => dt.name.clone(),
                Sort::Uninterpreted(n) => n.clone(),
                _ => return false,
            };
            let Some((_, ctors)) = exec.ctx.datatype_iter().find(|(n, _)| *n == dt_name) else {
                return false;
            };
            if visited.iter().any(|v| v == &dt_name) {
                return false;
            }
            visited.push(dt_name);
            let ctors: Vec<String> = ctors.to_vec();
            let hit = ctors.iter().any(|ctor| {
                exec.ctx
                    .constructor_selector_info(ctor)
                    .is_some_and(|fields| {
                        fields.iter().any(|(_, fsort)| {
                            matches!(fsort, Sort::Array(_)) || walk(exec, fsort, visited)
                        })
                    })
            });
            visited.pop();
            hit
        }
        let mut visited = Vec::new();
        walk(self, sort, &mut visited)
    }

    /// A sort that (recursively through arrays) carries a declared datatype.
    fn census_sort_carries_dt(&self, sort: &Sort, dts: &HashSet<String>) -> bool {
        match sort {
            Sort::Datatype(dt) => dts.contains(&dt.name),
            Sort::Uninterpreted(n) => dts.contains(n.as_str()),
            Sort::Array(a) => {
                self.census_sort_carries_dt(&a.index_sort, dts)
                    || self.census_sort_carries_dt(&a.element_sort, dts)
            }
            _ => false,
        }
    }

    /// Canonical model key of an INDEX term: a datatype index reconstructs to its
    /// canonical constructor tuple; a scalar index to its evaluated value. `None`
    /// if the model does not determine it (fail-closed at the call site).
    fn census_index_key(&self, model: &Model, index: TermId) -> Option<String> {
        self.census_value_key(model, index, 20)
    }

    /// Recursive canonical model key of a term — the census `RValue` tree
    /// flattened to a string: a datatype value reconstructs to its constructor
    /// tuple `(ctor field..)` with EACH field recursively keyed (INCLUDING
    /// array-typed fields, which `dt_mat_canonical` bailed on with `None`); an
    /// array to a const/store/identity canonical; a scalar/uninterpreted leaf to
    /// its evaluated value. `None` when the model does not determine it
    /// (fail-closed at the call site). Two terms are model-equal iff their keys
    /// are equal (over-approximate for bare-array fields — same syntactic term ⇒
    /// same key; a false inequality can only over-reject to a sound `unknown`,
    /// never certify a false SAT).
    fn census_value_key(&self, model: &Model, term: TermId, depth: u32) -> Option<String> {
        if depth == 0 {
            return None;
        }
        let sort = self.ctx.terms.sort(term).clone();
        if let Sort::Array(_) = sort {
            return self.census_array_canonical(model, term, depth);
        }
        let is_dt = matches!(&sort, Sort::Datatype(dt) if self.ctx.datatype_iter().any(|(n,_)| n==dt.name.as_str()))
            || matches!(&sort, Sort::Uninterpreted(n) if self.ctx.datatype_iter().any(|(d,_)| d==n.as_str()));
        if is_dt {
            // Literal constructor application: head + recursively-keyed args.
            if let TermData::App(sym, args) = self.ctx.terms.get(term) {
                if let Some((_dt, ctor)) = self.ctx.is_constructor(sym.name()) {
                    let args_v: Vec<TermId> = args.clone();
                    let mut parts = vec![ctor];
                    for arg in args_v {
                        parts.push(self.census_value_key(model, arg, depth - 1)?);
                    }
                    return Some(format!("({})", parts.join(" ")));
                }
            }
            // Datatype-sorted variable / selector result: read the model's
            // constructor, then each field via its selector application.
            let (ctor, _) = self.dt_constructor_of(model, term)?;
            let selectors: Vec<String> = self
                .ctx
                .constructor_selectors(&ctor)
                .map(|s| s.to_vec())
                .unwrap_or_default();
            if selectors.is_empty() {
                return Some(ctor);
            }
            let mut parts = vec![ctor];
            for sel in selectors {
                let sel_app = self.find_dt_selector_app(&sel, term)?;
                parts.push(self.census_value_key(model, sel_app, depth - 1)?);
            }
            return Some(format!("({})", parts.join(" ")));
        }
        // A read the preprocessor substituted away (its live twin carries the
        // bits) evaluates Unknown by TermId; the asserted equality that PINS it
        // (`(= (ptr (select A j)) #xFF)`) still defines its model value — the
        // same resolution `concrete_select_pairs` uses for the strict oracle.
        let v = match self.evaluate_term(model, term) {
            EvalValue::Unknown => self
                .extract_value_from_asserted_equalities(model, term)
                .unwrap_or(EvalValue::Unknown),
            v => v,
        };
        match v {
            EvalValue::BitVec { value, width } => Some(format!("bv{width}:{value}")),
            EvalValue::Bool(b) => Some(format!("b:{b}")),
            EvalValue::Rational(r) => Some(format!("r:{r}")),
            EvalValue::Element(e) => Some(format!("e:{e}")),
            _ => None,
        }
    }

    /// Canonical of an ARRAY term under the model: a const-array to
    /// `const(<fill>)`, a store to `store(<base>,<idx>,<val>)`, a nested
    /// `(select B k)` to `sel(<B id>,<eval k>)` (same base term + evaluated index ⇒
    /// same inner array, by array congruence), and any other bare/computed array
    /// to an identity marker `arr#<term id>`. SOUND: identity-by-term over-rejects
    /// (degrades) two model-equal but syntactically-distinct arrays, never
    /// under-rejects. Used to key datatype ARRAY fields (e.g. `Slice.data`).
    fn census_array_canonical(&self, model: &Model, arr: TermId, depth: u32) -> Option<String> {
        if depth == 0 {
            return None;
        }
        if let Some(fill) = self.ctx.terms.get_const_array(arr) {
            return Some(format!(
                "const({})",
                self.census_value_key(model, fill, depth - 1)?
            ));
        }
        if let TermData::App(sym, args) = self.ctx.terms.get(arr) {
            if sym.name() == "store" && args.len() == 3 {
                let base = self.census_array_canonical(model, args[0], depth - 1)?;
                let idx = self.census_index_key(model, args[1])?;
                let val = self.census_value_key(model, args[2], depth - 1)?;
                return Some(format!("store({base},{idx},{val})"));
            }
            if sym.name() == "select" && args.len() == 2 {
                let idx = self.census_index_key(model, args[1])?;
                return Some(format!("sel({},{})", args[0].0, idx));
            }
        }
        Some(format!("arr#{}", arr.0))
    }

    /// Whether arrays `x`,`y` are WITNESSED distinct under the model: some common
    /// evaluated index at which their reconstructed cell values differ. Uses the
    /// already-built `groups` (class,idx -> reads) — for each idx-key observed on
    /// BOTH classes, compares the reconstructed value. Returns false (fail-closed)
    /// when they agree on every common observed key.
    fn census_arrays_witnessed_distinct(
        &self,
        model: &Model,
        x: TermId,
        y: TermId,
        uf: &HashMap<TermId, TermId>,
        groups: &HashMap<(TermId, String), Vec<TermId>>,
        class_cells: &HashMap<TermId, Vec<(String, TermId)>>,
        depth: u32,
    ) -> bool {
        let cx = Self::census_find(uf, x);
        let cy = Self::census_find(uf, y);
        if cx == cy {
            return false; // same identity class -> provably NOT distinct
        }
        // Common observed index keys.
        let mut keys_x: HashSet<String> = Default::default();
        for (cls, k) in groups.keys() {
            if *cls == cx {
                keys_x.insert(k.clone());
            }
        }
        for (cls, k) in groups.keys() {
            if *cls != cy || !keys_x.contains(k) {
                continue;
            }
            let vx = groups
                .get(&(cx, k.clone()))
                .and_then(|r| r.first())
                .copied();
            let vy = groups
                .get(&(cy, k.clone()))
                .and_then(|r| r.first())
                .copied();
            if let (Some(a), Some(b)) = (vx, vy) {
                // A distinct is witnessed only by a DEFINITE incompatibility at a
                // common cell — `census_compatible == Some(false)`. String
                // inequality of canonicals would over-witness (two model-equal
                // array fields carry distinct `arr#id` markers), certifying a
                // disequality the model does not actually satisfy — a false SAT.
                if self.census_compatible(model, a, b, class_cells, uf, depth) == Some(false) {
                    return true; // witnessed difference (definite)
                }
            }
        }
        // No witnessed differing cell among common observed indices. The distinct
        // is STILL satisfiable when the two (different-identity-class) arrays can
        // differ at an UNOBSERVED index — which they always can if the index
        // domain has a free slot beyond the observed keys (an infinite index
        // sort, or a finite one not fully pinned). A completion that differs
        // there satisfies the disequality, so certifying is sound (the union-find
        // already excluded genuinely-equal arrays via `cx == cy` above, including
        // transitively-equated ones). Fixes over-refutation of `(distinct v3 v5)`
        // over unconstrained datatype-element arrays (#dt-array-distinct-freeslot).
        if self.census_index_domain_has_free_slot(x, &keys_x) {
            return true;
        }
        false
    }

    /// Whether array `arr`'s index domain has a value NOT among the `observed`
    /// keys — a slot at which two different-identity arrays can be completed to
    /// differ. True for an infinite index sort (Int/Real); for a finite BitVec
    /// index only when its `2^width` slots exceed the observed count.
    /// Conservative (`false`) for index sorts of unknown cardinality, so a
    /// disequality is never spuriously certified there.
    fn census_index_domain_has_free_slot(&self, arr: TermId, observed: &HashSet<String>) -> bool {
        match self.ctx.terms.sort(arr) {
            Sort::Array(a) => match &a.index_sort {
                Sort::Int | Sort::Real => true,
                Sort::BitVec(bv) => {
                    bv.width >= 63 || (observed.len() as u128) < (1u128 << bv.width)
                }
                _ => false,
            },
            _ => false,
        }
    }

    /// Structural model-COMPATIBILITY of two terms: `Some(true)` iff the model's
    /// partial assignment can be completed with both denoting the SAME value,
    /// `Some(false)` iff they are DEFINITELY unequal (differing constructor,
    /// differing scalar/EUF value, or a common observed array cell that
    /// conflicts), `None` if a needed value is undecidable (caller fails closed).
    ///
    /// This is the sound notion of "select-congruent" for values carrying
    /// arrays: two array fields are compatible unless they disagree on a cell
    /// BOTH were observed at — disjoint / unread cells complete freely, so two
    /// unconstrained `Slice.data` arrays are compatible rather than falsely
    /// conflicting on their `arr#id` identity. Certifying on compatibility is
    /// sound because a satisfying completion demonstrably exists; only cells the
    /// model already pins can force `Some(false)`.
    fn census_compatible(
        &self,
        model: &Model,
        t1: TermId,
        t2: TermId,
        class_cells: &HashMap<TermId, Vec<(String, TermId)>>,
        uf: &HashMap<TermId, TermId>,
        depth: u32,
    ) -> Option<bool> {
        if depth == 0 {
            return None; // recursion budget exhausted -> undecidable, fail closed
        }
        let sort = self.ctx.terms.sort(t1).clone();
        // Arrays: compatible unless a COMMON observed cell (or overlapping
        // const-default) conflicts.
        if let Sort::Array(_) = sort {
            let (c1, d1) = self.census_collect_cells(model, t1, class_cells, uf, depth);
            let (c2, d2) = self.census_collect_cells(model, t2, class_cells, uf, depth);
            for (k, v1) in &c1 {
                if let Some(v2) = c2.get(k).copied().or(d2) {
                    if self.census_compatible(model, *v1, v2, class_cells, uf, depth - 1)? == false
                    {
                        return Some(false);
                    }
                }
            }
            if let Some(dv1) = d1 {
                for (k, v2) in &c2 {
                    if c1.contains_key(k) {
                        continue;
                    }
                    if self.census_compatible(model, dv1, *v2, class_cells, uf, depth - 1)? == false
                    {
                        return Some(false);
                    }
                }
                if let Some(dv2) = d2 {
                    if self.census_compatible(model, dv1, dv2, class_cells, uf, depth - 1)? == false
                    {
                        return Some(false);
                    }
                }
            }
            return Some(true);
        }
        // Datatype values: same constructor, then each field pairwise compatible.
        let is_dt = matches!(&sort, Sort::Datatype(dt) if self.ctx.datatype_iter().any(|(n,_)| n==dt.name.as_str()))
            || matches!(&sort, Sort::Uninterpreted(n) if self.ctx.datatype_iter().any(|(d,_)| d==n.as_str()));
        if is_dt {
            let (c1, _) = self.dt_constructor_of(model, t1)?;
            let (c2, _) = self.dt_constructor_of(model, t2)?;
            if c1 != c2 {
                return Some(false); // different constructors -> definitely unequal
            }
            let selectors: Vec<String> = self
                .ctx
                .constructor_selectors(&c1)
                .map(|s| s.to_vec())
                .unwrap_or_default();
            for sel in selectors {
                let dbg = std::env::var_os("AY_CENSUS_TRACE").is_some();
                let (Some(a1), Some(a2)) = (
                    self.find_dt_selector_app(&sel, t1),
                    self.find_dt_selector_app(&sel, t2),
                ) else {
                    if dbg {
                        eprintln!(
                            "c census-dbg no-selector-app sel={sel} t1={} t2={}",
                            t1.0, t2.0
                        );
                    }
                    return None;
                };
                let r = self.census_compatible(model, a1, a2, class_cells, uf, depth - 1);
                if dbg && r.is_none() {
                    eprintln!(
                        "c census-dbg field-undecidable sel={sel} a1={} ({}) a2={} ({})",
                        a1.0,
                        self.format_term(a1),
                        a2.0,
                        self.format_term(a2)
                    );
                }
                if !r? {
                    return Some(false);
                }
            }
            return Some(true);
        }
        // Scalar / EUF leaf: compare evaluated values (undecidable -> None).
        let dbg = std::env::var_os("AY_CENSUS_TRACE").is_some();
        let k1 = self.census_value_key(model, t1, depth);
        let k2 = self.census_value_key(model, t2, depth);
        if dbg && (k1.is_none() || k2.is_none()) {
            eprintln!(
                "c census-dbg leaf-undecidable t1={} ({}) k1={:?} t2={} ({}) k2={:?}",
                t1.0,
                self.format_term(t1),
                k1,
                t2.0,
                self.format_term(t2),
                k2
            );
        }
        Some(k1? == k2?)
    }

    /// Observed cell function of an array term under the model: `(cells, default)`
    /// where `cells` maps an evaluated-index key to a value term and `default` is
    /// a const-array fill (if the array is/reduces to `((as const ..) f)`).
    /// Combines the array's syntactic `store`/const structure with every
    /// `(select S k)` read on its identity class. Used by `census_compatible` to
    /// compare two array fields cell-by-cell.
    fn census_collect_cells(
        &self,
        model: &Model,
        arr: TermId,
        class_cells: &HashMap<TermId, Vec<(String, TermId)>>,
        uf: &HashMap<TermId, TermId>,
        depth: u32,
    ) -> (HashMap<String, TermId>, Option<TermId>) {
        let mut cells: HashMap<String, TermId> = HashMap::default();
        let mut default: Option<TermId> = None;
        // Walk the syntactic store/const chain: outermost store wins each index.
        let mut cur = arr;
        for _ in 0..depth.min(64) {
            if let Some(fill) = self.ctx.terms.get_const_array(cur) {
                default = Some(fill);
                break;
            }
            if let TermData::App(sym, args) = self.ctx.terms.get(cur) {
                if sym.name() == "store" && args.len() == 3 {
                    if let Some(k) = self.census_index_key(model, args[1]) {
                        cells.entry(k).or_insert(args[2]);
                    }
                    cur = args[0];
                    continue;
                }
            }
            break;
        }
        // Observed selects on the array's (and the reduced base's) identity class.
        for base in [arr, cur] {
            let cls = Self::census_find(uf, base);
            if let Some(list) = class_cells.get(&cls) {
                for (k, t) in list {
                    cells.entry(k.clone()).or_insert(*t);
                }
            }
        }
        (cells, default)
    }

    pub(super) fn dt_constructor_of(
        &self,
        model: &Model,
        term: TermId,
    ) -> Option<(String, String)> {
        // A literal constructor application is its own answer.
        if let TermData::App(sym, _) = self.ctx.terms.get(term) {
            if let Some((dt_name, ctor_name)) = self.ctx.is_constructor(sym.name()) {
                return Some((ctor_name, dt_name));
            }
        }
        let sort_name = match self.ctx.terms.sort(term) {
            Sort::Uninterpreted(s) => s.clone(),
            Sort::Datatype(dt) => dt.name.clone(),
            _ => return None,
        };
        let constructors: Vec<String> = self
            .ctx
            .datatype_iter()
            .find(|(dt, _)| *dt == sort_name)
            .map(|(_, ctors)| ctors.to_vec())
            .unwrap_or_default();
        if constructors.is_empty() {
            return None;
        }
        // Sole-constructor datatypes always use that constructor (the recognizer
        // is a tautology); this is what makes BUG B's `(_ is c2)` definitive.
        if constructors.len() == 1 {
            return Some((constructors[0].clone(), sort_name));
        }
        // Multiple constructors: require an unambiguous model-true tester.
        let mut chosen: Option<String> = None;
        for c in &constructors {
            if self.dt_tester_true(model, c, term) {
                if chosen.is_some() {
                    return None; // ambiguous
                }
                chosen = Some(c.clone());
            }
        }
        chosen.map(|c| (c, sort_name))
    }

    /// True if `(is-ctor term)` is asserted or true in the SAT model.
    fn dt_tester_true(&self, model: &Model, ctor: &str, term: TermId) -> bool {
        let tester = format!("is-{ctor}");
        for idx in 0..self.ctx.terms.len() {
            let tid = TermId(idx as u32);
            if let TermData::App(sym, args) = self.ctx.terms.get(tid) {
                if sym.name() == tester && args.len() == 1 && args[0] == term {
                    if self.ctx.assertions.contains(&tid) {
                        return true;
                    }
                    return self.term_value(&model.sat_model, &model.term_to_var, tid)
                        == Some(true);
                }
            }
        }
        false
    }

    /// Find the term that supplies the value of field `field_idx` of `ctor`
    /// applied to the datatype term `dt_term`, under the candidate model.
    ///
    /// Two sources, in order of authority:
    /// 1. An asserted constructor equality `(= dt_term (ctor a0 a1 ...))` — the
    ///    argument `a{field_idx}` IS the field value (BUG C / nested chains).
    /// 2. The selector application `(sel dt_term)` found in the term store — its
    ///    model value is the field value (BUG C2's BV field via the BV model).
    ///
    /// `dt_term` may itself be a literal constructor application, in which case
    /// the argument is read off directly.
    fn dt_field_value_term(
        &self,
        model: &Model,
        dt_term: TermId,
        ctor: &str,
        field_idx: usize,
    ) -> Option<TermId> {
        // Literal constructor application: read the field argument directly.
        if let TermData::App(sym, args) = self.ctx.terms.get(dt_term) {
            if sym.name() == ctor && field_idx < args.len() {
                return Some(args[field_idx]);
            }
        }
        // Asserted constructor equality.
        if let Some(arg_tid) =
            self.constructor_arg_from_asserted_eq(dt_term, ctor, field_idx, model)
        {
            return Some(arg_tid);
        }
        None
    }

    /// Materialized datatype re-evaluator.
    ///
    /// Re-evaluates `term` against the candidate model the way the model PRINTER
    /// presents it: every datatype selector application `(sel x)` is resolved by
    /// walking `x`'s assigned constructor and reading off the field value
    /// (recursively, so deep selector chains propagate). A field the theory model
    /// leaves unconstrained materializes to the SAME default the printer emits
    /// (String -> "", BV -> #x0, Int -> 0), because that is the value the model
    /// actually exhibits. Recognizers `(is-ctor x)` evaluate to whether `x`'s
    /// constructor is `ctor`.
    ///
    /// **Design (full-evaluator route).** Rather than re-implementing every
    /// operator over materialized field values (an op-by-op approach is always
    /// incomplete — it missed `str.substr`/`str.at`/`str.indexof`/`str.replace`/
    /// the `str.prefixof`/`str.suffixof`/`str.contains`/`str.<=` family, etc.),
    /// we MATERIALIZE only the datatype boundary subterms — selector applications
    /// `(sel x)` and recognizers `(is-ctor x)` — to concrete values, pin them in a
    /// per-thread override map ([`DT_FIELD_OVERRIDE`]), and then evaluate the WHOLE
    /// `term` with ay's existing complete evaluator [`Executor::evaluate_term`].
    /// Because every boundary value is pinned, the assertion is fully ground and
    /// the ordinary evaluator finishes it correctly for ALL theories (strings, BV,
    /// arithmetic, sequences) with no per-operator code here.
    ///
    /// This is purely a SOUNDNESS gate: it never invents constraints. When it
    /// reduces an asserted atom to `Bool(false)`, the candidate model genuinely
    /// falsifies that atom (it is internally inconsistent), so the caller must
    /// degrade SAT -> Unknown. When it returns `Unknown` (any boundary subterm
    /// could not be materialized to a concrete value), the gate stays silent (no
    /// demotion) so a model-extraction gap is never mistaken for a violation.
    pub(super) fn dt_mat_eval(&self, model: &Model, term: TermId, depth: u32) -> EvalValue {
        if depth == 0 {
            return EvalValue::Unknown;
        }
        // Materialize every datatype boundary subterm (selector / recognizer) to a
        // concrete value. If ANY of them cannot be materialized, fail closed:
        // return Unknown so no demotion happens on an extraction gap.
        let mut overrides: HashMap<TermId, EvalValue> = HashMap::default();
        if !self.collect_dt_field_overrides(model, term, depth, &mut overrides) {
            return EvalValue::Unknown;
        }
        // Pin the boundary values and let the full evaluator finish the assertion.
        let _guard = OverrideGuard::install(overrides);
        let result = self.evaluate_term(model, term);
        if std::env::var_os("AY_PHASE_TRACE").is_some() && matches!(result, EvalValue::Bool(false))
        {
            if let TermData::App(sym, args) = self.ctx.terms.get(term) {
                if matches!(sym.name(), "=" | "distinct") && args.len() == 2 {
                    let a = self.dt_mat_canonical(model, args[0], 64);
                    let b = self.dt_mat_canonical(model, args[1], 64);
                    eprintln!("c phase-trace dt-mat-false lhs={a:?} rhs={b:?}");
                }
            }
        }
        result
    }

    /// Walk `term`, materializing every datatype selector application / recognizer
    /// subterm to a concrete value and recording it in `overrides`. Returns `true`
    /// when every boundary subterm encountered was materialized to a concrete
    /// (non-`Unknown`) value; returns `false` as soon as one cannot be resolved, so
    /// `dt_mat_eval` fails closed.
    ///
    /// Boundary subterms are NOT descended into past their materialization: once a
    /// selector application is pinned to a value, the evaluator never recurses into
    /// its datatype argument, so we don't need to. We DO descend into the ordinary
    /// arguments of non-boundary applications to find boundary subterms nested
    /// inside them (e.g. the `(s d0)` inside `(str.++ (s d0) "x")`).
    fn collect_dt_field_overrides(
        &self,
        model: &Model,
        term: TermId,
        depth: u32,
        overrides: &mut HashMap<TermId, EvalValue>,
    ) -> bool {
        if depth == 0 {
            return false;
        }
        match self.ctx.terms.get(term) {
            // Recognizer `(is-ctor x)`: true iff x's assigned constructor is ctor.
            TermData::App(sym, args)
                if args.len() == 1
                    && sym
                        .name()
                        .strip_prefix("is-")
                        .is_some_and(|c| self.ctx.is_constructor(c).is_some()) =>
            {
                let ctor = sym.name().strip_prefix("is-").unwrap().to_string();
                match self.dt_constructor_of(model, args[0]) {
                    Some((assigned, _)) => {
                        overrides.insert(term, EvalValue::Bool(assigned == ctor));
                        true
                    }
                    None => false,
                }
            }
            // Selector application `(sel x)`: resolve through x's constructor to a
            // concrete field value and pin it.
            TermData::App(sym, args)
                if args.len() == 1
                    && self
                        .ctx
                        .ctor_selectors_iter()
                        .any(|(_c, sels)| sels.iter().any(|s| s == sym.name())) =>
            {
                let v = self.dt_mat_eval_selector(model, sym.name(), args[0], term, depth);
                // Coerce to the selector's declared sort. A combined DT solver may
                // store an Int/Real/BV/Bool field in the EUF model as an
                // `EvalValue::Element("1")` string; the full evaluator needs the
                // proper scalar variant (`Rational(1)`) for arithmetic/BV ops to
                // reduce instead of returning Unknown.
                let v = self.coerce_eval_to_term_sort(v, term);
                if matches!(v, EvalValue::Unknown) {
                    return false;
                }
                overrides.insert(term, v);
                true
            }
            // Datatype `=` / `distinct` where at least one operand is a CONSTRUCTOR
            // APPLICATION literal (e.g. `(= d0 (mk "aa" 7))`, `(distinct (mk u0 5)
            // (mk u1 5))`). The full evaluator cannot decide datatype equality (it
            // reads EUF element identity the eager DT route does not maintain), so
            // we resolve each operand to a canonical, fully-materialized ground form
            // (constructor + materialized field values, defaults included) and pin
            // the resulting Bool. This validates datatype equalities NESTED inside
            // boolean structure, which the top-level `DtOracle` cannot reach.
            //
            // The constructor-literal anchor is deliberate: it keeps the demotion
            // tied to a concretely-shaped operand. A bare `(= d0 d1)`/`(distinct d0
            // d1)` between two unconstrained datatype VARIABLES is left to the model
            // (a distinct completion usually exists), so we do not over-demote it to
            // Unknown by fabricating colliding field defaults.
            TermData::App(sym, args)
                if matches!(sym.name(), "=" | "distinct")
                    && args.len() == 2
                    && (self.is_constructor_app(args[0]) || self.is_constructor_app(args[1]))
                    && (self.dt_term_is_datatype_related(args[0])
                        || self.dt_term_is_datatype_related(args[1])) =>
            {
                let (Some(a), Some(b)) = (
                    self.dt_mat_canonical(model, args[0], depth - 1),
                    self.dt_mat_canonical(model, args[1], depth - 1),
                ) else {
                    return false;
                };
                let eq = a == b;
                let v = if sym.name() == "=" { eq } else { !eq };
                overrides.insert(term, EvalValue::Bool(v));
                true
            }
            // Ordinary application: recurse into every argument.
            TermData::App(_sym, args) => args
                .iter()
                .all(|&a| self.collect_dt_field_overrides(model, a, depth - 1, overrides)),
            TermData::Not(inner) => {
                self.collect_dt_field_overrides(model, *inner, depth - 1, overrides)
            }
            TermData::Ite(c, t, e) => {
                self.collect_dt_field_overrides(model, *c, depth - 1, overrides)
                    && self.collect_dt_field_overrides(model, *t, depth - 1, overrides)
                    && self.collect_dt_field_overrides(model, *e, depth - 1, overrides)
            }
            TermData::Let(bindings, body) => {
                bindings
                    .iter()
                    .all(|(_, v)| self.collect_dt_field_overrides(model, *v, depth - 1, overrides))
                    && self.collect_dt_field_overrides(model, *body, depth - 1, overrides)
            }
            // Plain variable leaf: if the theory model leaves it unconstrained, the
            // model PRINTER still presents it with a canonical default (String -> "",
            // BV -> #x0, Int -> 0, Bool -> false). Pin that SAME default so the
            // re-evaluation faithfully reflects the model AY actually exhibits. This
            // is what makes a sibling-variable contradiction like
            // `(= (str.++ u0 "b" (s d2)) u0)` (an unconstrained string `u0` printed
            // as "") definitively false. Sound: the gate only ever demotes
            // SAT -> Unknown, and we materialize a leaf only when the evaluator
            // genuinely could not resolve it (so the printed default is the model's
            // exhibited value). A datatype-sorted leaf has no scalar default here
            // (handled by the DtOracle) and is left for the evaluator.
            TermData::Var(_, _) => {
                if matches!(self.evaluate_term(model, term), EvalValue::Unknown) {
                    // Only the data sorts with an unambiguous printer default; Bool
                    // is deliberately excluded (an eliminated/irrelevant Bool var is a
                    // genuine don't-care, not a fixed exhibited value, so pinning it
                    // to `false` could over-demote a valid disjunction).
                    let def = match self.ctx.terms.sort(term) {
                        Sort::String => EvalValue::String(String::new()),
                        Sort::BitVec(bv) => EvalValue::BitVec {
                            value: num_bigint::BigInt::from(0),
                            width: bv.width,
                        },
                        Sort::Int | Sort::Real => {
                            EvalValue::Rational(BigRational::from(num_bigint::BigInt::from(0)))
                        }
                        _ => EvalValue::Unknown,
                    };
                    if !matches!(def, EvalValue::Unknown) {
                        overrides.insert(term, def);
                    }
                }
                true
            }
            // Constant leaf: the evaluator resolves it exactly.
            _ => true,
        }
    }

    /// Materialize a single selector application `(sel dt_term)`.
    fn dt_mat_eval_selector(
        &self,
        model: &Model,
        sel_name: &str,
        dt_term: TermId,
        sel_app: TermId,
        depth: u32,
    ) -> EvalValue {
        // Determine dt_term's constructor; the selector must belong to it.
        let Some((ctor, _sort)) = self.dt_constructor_of(model, dt_term) else {
            return EvalValue::Unknown;
        };
        let selectors = self.ctx.constructor_selectors(&ctor).unwrap_or(&[]);
        let field_idx = selectors.iter().position(|s| s == sel_name);
        // (1) When the selector BELONGS to dt_term's constructor, resolve the
        // field value TERM and recurse the materialized eval into it (handles
        // nested datatype field chains, e.g. `(ib (tm v0))`, where the field is
        // itself a datatype value). When the selector belongs to a DIFFERENT
        // constructor (`field_idx` is None — e.g. `(ts v)` with `v = tleaf`),
        // SMT-LIB leaves `(sel x)` unspecified-but-FIXED: the model still
        // exhibits a single value for it. Skip step (1) and fall through to the
        // model value / printer default below — that is the value the candidate
        // model actually presents, so re-evaluating against it faithfully
        // demotes a self-contradicting SAT (e.g. `(= (str.len (str.++ (ts v)
        // "bb")) 0)`, unsat for every value of `(ts v)`) to Unknown rather than
        // failing open. Sound: this only ever turns SAT into Unknown.
        if let Some(field_idx) = field_idx {
            if let Some(field_term) = self.dt_field_value_term(model, dt_term, &ctor, field_idx) {
                let v = self.dt_mat_eval(model, field_term, depth - 1);
                if !matches!(v, EvalValue::Unknown) {
                    return v;
                }
            }
        }
        // (2) The selector application's OWN model value. This is the value the
        // printer reads for this field (`format_dt_ctor_value` calls
        // `lookup_term_value` on `(sel x)`): a LIA/LRA/BV model entry, or an
        // asserted `(= (sel x) c)`. Catches genuinely-constrained fields such as
        // `(= (n d) 7)` or `(= (mb m) #x3)`, so we do NOT over-demote them.
        let looked_up = self.lookup_term_value(model, sel_app);
        if !matches!(looked_up, EvalValue::Unknown) {
            return looked_up;
        }
        // (3) Field value left unconstrained by every model: materialize the SAME
        // default the printer presents (String -> "", BV -> #x0, Int -> 0). This
        // is the value the candidate model actually exhibits and is what makes a
        // string-field assertion like BUG A self-contradicting.
        self.dt_default_field_value(sel_app)
    }

    /// Coerce a materialized field value to the declared sort of `term`.
    ///
    /// A combined DT solver may surface a scalar field through the EUF model as an
    /// `EvalValue::Element("1")` (the value rendered as a string), or as a numeric
    /// `Rational` for a BV field. The full term evaluator dispatches on the
    /// `EvalValue` variant, so an Int field carried as `Element` would make every
    /// enclosing arithmetic op return `Unknown`. Re-parse the rendered value into
    /// the variant the sort requires. A value already in the right variant is
    /// returned unchanged. Returns `Unknown` when the rendered value cannot be
    /// reconciled with the sort (fail closed — no demotion on a malformed value).
    fn coerce_eval_to_term_sort(&self, value: EvalValue, term: TermId) -> EvalValue {
        let sort = self.ctx.terms.sort(term).clone();
        match (&sort, &value) {
            // Already the correct variant.
            (Sort::Int | Sort::Real, EvalValue::Rational(_))
            | (Sort::String, EvalValue::String(_))
            | (Sort::BitVec(_), EvalValue::BitVec { .. })
            | (Sort::Bool, EvalValue::Bool(_)) => value,
            // Element / string-rendered scalar: re-parse into the sort's variant.
            (Sort::Int | Sort::Real | Sort::BitVec(_) | Sort::Bool, EvalValue::Element(s)) => {
                self.parse_model_value_string(s, &Some(sort))
            }
            // BV field that arrived as a plain integer.
            (Sort::BitVec(bv), EvalValue::Rational(r)) if r.is_integer() => EvalValue::BitVec {
                value: r.to_integer(),
                width: bv.width,
            },
            // Datatype / uninterpreted / other: leave as-is (the DtOracle handles
            // datatype equality; element identity is meaningful there).
            _ => value,
        }
    }

    /// True if `term` is a constructor application literal `(Ctor a0 a1 ...)`.
    fn is_constructor_app(&self, term: TermId) -> bool {
        matches!(self.ctx.terms.get(term), TermData::App(sym, _)
            if self.ctx.is_constructor(sym.name()).is_some())
    }

    /// True if `term` is datatype-sorted or a constructor application — i.e. the
    /// kind of operand whose `=`/`distinct` the full evaluator cannot decide and
    /// which `dt_mat_canonical` must resolve.
    fn dt_term_is_datatype_related(&self, term: TermId) -> bool {
        if matches!(
            self.ctx.terms.sort(term),
            Sort::Datatype(_) | Sort::Uninterpreted(_)
        ) && self.dt_sort_name_of(term).is_some()
        {
            return true;
        }
        matches!(self.ctx.terms.get(term), TermData::App(sym, _)
            if self.ctx.is_constructor(sym.name()).is_some())
    }

    /// The datatype sort name of `term`, if it is datatype-sorted.
    fn dt_sort_name_of(&self, term: TermId) -> Option<String> {
        match self.ctx.terms.sort(term) {
            Sort::Datatype(dt) => Some(dt.name.clone()),
            Sort::Uninterpreted(s) if self.ctx.datatype_iter().any(|(dt, _)| dt == s.as_str()) => {
                Some(s.clone())
            }
            _ => None,
        }
    }

    /// Structural constructor depth of the datatype VALUE the candidate model
    /// assigns `term` — the interpretation ay's internal acyclicity
    /// instrumentation (`__ay_dt_depth_<dt>`, see
    /// `dt_acyclicity_depth_axioms_up_to`) is evaluated under at
    /// model-validation time (#dt-depth-structural): `depth(v) = 0` when the
    /// value has no datatype-sorted field (e.g. `nil`), else
    /// `1 + max(depth(field))` over its datatype-sorted fields.
    ///
    /// This interpretation is a genuine FUNCTION OF THE VALUE and satisfies
    /// every injected depth axiom by construction on FINITE values:
    /// * monotonicity `depth(C(.. a ..)) >= depth(a) + 1` — the constructor's
    ///   depth is `1 + max(..)`, which dominates each field's `depth + 1`;
    /// * asserted-equality congruence `depth(x) = depth(C(args))` — both sides
    ///   resolve through the SAME asserted-constructor-equality machinery
    ///   (`dt_asserted_ctor_app`) to the same constructor tree.
    ///
    /// FAIL-CLOSED: returns `None` whenever the value cannot be resolved to a
    /// finite constructor tree — an undetermined/ambiguous constructor, an
    /// unresolvable field, or a CYCLIC constructor chain (fuel exhaustion; a
    /// cyclic value has NO finite depth). The caller then falls back to the raw
    /// committed theory values (exactly today's behavior), so a cyclic witness
    /// keeps its term-level depth contradiction (`depth(x) = depth(cons(.. x))`
    /// vs `depth(cons(.. x)) >= depth(x) + 1`) and can NEVER be validated
    /// through a fabricated depth.
    pub(super) fn dt_structural_depth(
        &self,
        model: &Model,
        term: TermId,
        fuel: u32,
    ) -> Option<num_bigint::BigInt> {
        if fuel == 0 {
            return None; // cyclic or unresolvably deep: no finite depth
        }
        if let TermData::App(sym, args) = self.ctx.terms.get(term) {
            let head = sym.name().to_string();
            let args = args.clone();
            // Literal constructor application `(Ctor a0 a1 ...)`: read the
            // datatype-sorted argument terms off directly.
            if self.ctx.is_constructor(&head).is_some() {
                let mut depth = num_bigint::BigInt::from(0);
                for &a in &args {
                    if self.dt_sort_name_of(a).is_none() {
                        continue; // scalar field: carries no depth axiom
                    }
                    let cand = self.dt_structural_depth(model, a, fuel - 1)? + 1;
                    if cand > depth {
                        depth = cand;
                    }
                }
                return Some(depth);
            }
            // Selector application `(sel y)`: resolve `y` to the constructor
            // APPLICATION it is asserted equal to and recurse into the
            // matching field argument. Deliberately CHEAP: only the literal /
            // asserted-equality resolution is used — NO term-store tester
            // scans (`dt_constructor_of` is O(|terms|) per call and blows
            // validation up on large dt-carrying-array problems).
            if args.len() == 1
                && self
                    .ctx
                    .ctor_selectors_iter()
                    .any(|(_c, sels)| sels.iter().any(|s| *s == head))
            {
                let dt_arg = args[0];
                let ctor_app = if self.is_constructor_app(dt_arg) {
                    dt_arg
                } else {
                    self.dt_asserted_ctor_app(model, dt_arg)?
                };
                let TermData::App(csym, cargs) = self.ctx.terms.get(ctor_app) else {
                    return None;
                };
                let (_dt, ctor) = self.ctx.is_constructor(csym.name())?;
                let cargs = cargs.clone();
                let selectors = self.ctx.constructor_selectors(&ctor)?;
                let field_idx = selectors.iter().position(|s| *s == head)?;
                let field_term = *cargs.get(field_idx)?;
                return self.dt_structural_depth(model, field_term, fuel - 1);
            }
        }
        // Datatype-sorted variable / other term: resolve it to the constructor
        // APPLICATION it is asserted equal to (`(= term (C args))` holding in
        // the SAT model — the source of truth in pure QF_DT, mirroring
        // `constructor_arg_from_asserted_eq`) and recurse into the application
        // itself so the fields are the equality's own arguments. A cyclic
        // chain (`x = cons(1, x)`) recurses back into `term` and exhausts the
        // fuel -> `None` (fail closed, no finite depth).
        self.dt_sort_name_of(term)?;
        let ctor_app = self.dt_asserted_ctor_app(model, term)?;
        self.dt_structural_depth(model, ctor_app, fuel - 1)
    }

    /// The constructor APPLICATION term asserted equal to `term` — a top-level
    /// asserted `(= term (C ...))` holding in the SAT model — when every such
    /// asserted equality agrees on the constructor. `None` otherwise (including
    /// on constructor disagreement: fail closed, an inconsistent model must not
    /// get a fabricated depth). Companion to `constructor_arg_from_asserted_eq`.
    fn dt_asserted_ctor_app(&self, model: &Model, term: TermId) -> Option<TermId> {
        let mut found: Option<(String, TermId)> = None;
        for &assertion in &self.ctx.assertions {
            let TermData::App(sym, args) = self.ctx.terms.get(assertion) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            // A top-level `=` assertion is unconditionally asserted true, so
            // default to true when the SAT model has no entry (#5450).
            let eq_true = self
                .term_value(&model.sat_model, &model.term_to_var, assertion)
                .unwrap_or(true);
            if !eq_true {
                continue;
            }
            let other = if args[0] == term {
                args[1]
            } else if args[1] == term {
                args[0]
            } else {
                continue;
            };
            let TermData::App(osym, _) = self.ctx.terms.get(other) else {
                continue;
            };
            let Some((_dt, ctor)) = self.ctx.is_constructor(osym.name()) else {
                continue;
            };
            match &found {
                Some((c, _)) if *c != ctor => return None, // disagreement
                Some(_) => {}
                None => found = Some((ctor, other)),
            }
        }
        found.map(|(_, t)| t)
    }

    /// Resolve a datatype-sorted term (or constructor application) to a canonical,
    /// fully-materialized ground string under the model: the assigned constructor
    /// followed by each field's materialized value (theory-model value, asserted
    /// constructor-equality argument, or the SAME printer default for an
    /// unconstrained field). Canonical: two terms with the same model value produce
    /// byte-identical strings, distinct values produce distinct strings.
    ///
    /// Returns `None` only when the constructor itself cannot be determined (an
    /// ambiguous/undetermined multi-constructor datatype), so the materialized
    /// equality is left undecided (fail closed). Fields ALWAYS materialize (to a
    /// default if unconstrained), matching what the model printer exhibits.
    fn dt_mat_canonical(&self, model: &Model, term: TermId, depth: u32) -> Option<String> {
        if depth == 0 {
            return None;
        }
        // Literal constructor application `(Ctor a0 a1 ...)`: head + resolved args.
        if let TermData::App(sym, args) = self.ctx.terms.get(term) {
            if let Some((_dt, ctor)) = self.ctx.is_constructor(sym.name()) {
                let mut parts = Vec::with_capacity(args.len());
                for &arg in args {
                    parts.push(self.dt_mat_canonical_field(model, arg, depth - 1)?);
                }
                return Some(if parts.is_empty() {
                    ctor
                } else {
                    format!("({} {})", ctor, parts.join(" "))
                });
            }
        }
        // Datatype-sorted variable / selector-result: walk its assigned
        // constructor and read off each field via its selector application.
        let (ctor, _) = self.dt_constructor_of(model, term)?;
        let selectors = self.ctx.constructor_selectors(&ctor).unwrap_or(&[]);
        if selectors.is_empty() {
            return Some(ctor);
        }
        let mut parts = Vec::with_capacity(selectors.len());
        for sel in selectors {
            let sel_name = sel.clone();
            // The selector application `(sel term)` carries the field's sort and is
            // the handle the field value is read through.
            let sel_app = self.find_dt_selector_app(&sel_name, term);
            // A datatype-sorted field recurses; a scalar field materializes (with a
            // printer default if unconstrained).
            let part = match sel_app {
                Some(app) if self.dt_term_is_datatype_related(app) => {
                    self.dt_mat_canonical(model, app, depth - 1)?
                }
                Some(app) => {
                    let raw = self.dt_mat_eval_selector(model, &sel_name, term, app, depth - 1);
                    let v = match self.coerce_eval_to_term_sort(raw, app) {
                        EvalValue::Unknown => self.dt_default_field_value(app),
                        v => v,
                    };
                    // Genuinely unavailable field (e.g. an ARRAY-sorted slice
                    // backing store the model does not pin, and which has no
                    // scalar printer default): fail CLOSED. Rendering it as the
                    // `(_ ay.value-unavailable t<id>)` placeholder embeds the
                    // TermId, so two DISTINCT unavailable fields at corresponding
                    // positions produce distinct strings and fabricate an
                    // inequality — a model-EXTRACTION gap mistaken for a
                    // violation, which this oracle's contract forbids
                    // ("returns Unknown ... so a model-extraction gap is never
                    // mistaken for a violation"). Returning None leaves the
                    // enclosing datatype equality undecided -> dt_mat_eval yields
                    // Unknown -> no demotion. SOUND: an unconstrained field can
                    // be completed to make the equality hold, so the model is not
                    // provably inconsistent. (#dt-mat-unavailable-field)
                    if matches!(v, EvalValue::Unknown) {
                        return None;
                    }
                    self.format_eval_value(&v, app)
                }
                None => return None,
            };
            parts.push(part);
        }
        Some(format!("({} {})", ctor, parts.join(" ")))
    }

    /// Canonicalize a constructor ARGUMENT term (`(Ctor arg ...)`): a datatype arg
    /// recurses; a scalar arg is evaluated/defaulted to its printed form.
    fn dt_mat_canonical_field(&self, model: &Model, arg: TermId, depth: u32) -> Option<String> {
        if self.dt_term_is_datatype_related(arg) {
            return self.dt_mat_canonical(model, arg, depth);
        }
        // Scalar field: evaluate; default to the printer value if unresolved.
        let v = match self.evaluate_term(model, arg) {
            EvalValue::Unknown => self.dt_default_field_value(arg),
            v => v,
        };
        // Genuinely unavailable field (an ARRAY-sorted / non-scalar operand the
        // model does not pin): fail closed rather than emit the TermId-tagged
        // placeholder, which would fabricate an inequality between two unavailable
        // fields. See the sibling site in `dt_mat_canonical`
        // (#dt-mat-unavailable-field).
        if matches!(v, EvalValue::Unknown) {
            return None;
        }
        Some(self.format_eval_value(&v, arg))
    }

    /// Find the selector application term `(sel arg)` in the term store.
    pub(super) fn find_dt_selector_app(&self, sel: &str, arg: TermId) -> Option<TermId> {
        for idx in 0..self.ctx.terms.len() {
            let tid = TermId(idx as u32);
            if let TermData::App(sym, args) = self.ctx.terms.get(tid) {
                if sym.name() == sel && args.len() == 1 && args[0] == arg {
                    return Some(tid);
                }
            }
        }
        None
    }

    /// The default value the model printer presents for an unconstrained field of
    /// the given (selector-application) term: empty string, zero bitvector, zero
    /// integer/real. Returns `Unknown` for sorts with no canonical default.
    fn dt_default_field_value(&self, sel_app: TermId) -> EvalValue {
        match self.ctx.terms.sort(sel_app) {
            Sort::String => EvalValue::String(String::new()),
            Sort::BitVec(bv) => EvalValue::BitVec {
                value: num_bigint::BigInt::from(0),
                width: bv.width,
            },
            Sort::Int | Sort::Real => {
                EvalValue::Rational(BigRational::from(num_bigint::BigInt::from(0)))
            }
            Sort::Bool => EvalValue::Bool(false),
            _ => EvalValue::Unknown,
        }
    }

    /// True if `term` contains a datatype selector application, recognizer, or a
    /// datatype `=`/`distinct` over datatype-related operands. Any of these means
    /// the materialized re-evaluator (`dt_mat_eval`) can decide a soundness
    /// violation the ordinary evaluator and the top-level `DtOracle` cannot reach
    /// (the latter only sees TOP-LEVEL datatype equalities, not ones nested inside
    /// boolean structure).
    pub(super) fn term_mentions_dt_field(&self, term: TermId) -> bool {
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![term];
        let mut budget = 4096u32;
        while let Some(t) = stack.pop() {
            if budget == 0 {
                return true; // be conservative if we run out of budget
            }
            budget -= 1;
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    let nm = sym.name();
                    let is_sel = self
                        .ctx
                        .ctor_selectors_iter()
                        .any(|(_c, sels)| sels.iter().any(|s| s == nm));
                    let is_recognizer = nm
                        .strip_prefix("is-")
                        .is_some_and(|c| self.ctx.is_constructor(c).is_some());
                    let is_constructor = self.ctx.is_constructor(nm).is_some();
                    // A datatype (dis)equality with a CONSTRUCTOR-LITERAL operand —
                    // decidable by the materialized canonicalizer (mirrors the
                    // collection guard; a bare var-vs-var (dis)equality is left to
                    // the model / top-level DtOracle).
                    let is_dt_eq = matches!(nm, "=" | "distinct")
                        && args.len() == 2
                        && (self.is_constructor_app(args[0]) || self.is_constructor_app(args[1]))
                        && (self.dt_term_is_datatype_related(args[0])
                            || self.dt_term_is_datatype_related(args[1]));
                    if is_sel || is_recognizer || is_constructor || is_dt_eq {
                        return true;
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                TermData::Let(bindings, body) => {
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                    stack.push(*body);
                }
                _ => {}
            }
        }
        false
    }

    /// Total `define-fun` interpretations for every datatype SELECTOR in the
    /// problem signature, for `(get-model)` (#mv-total-selectors).
    ///
    /// SMT-LIB selectors are PARTIAL: a benchmark may apply a selector to a
    /// value built by a different constructor, and a model that only assigns
    /// the user constants leaves that application uninterpreted — a model
    /// validator then rejects the whole model (Dolmen: `partial-dstr`). The
    /// remedy (as validated against the pinned 2025 Dolmen) is a TOTAL
    /// interpretation per selector:
    ///
    /// ```text
    /// (define-fun car ((@p0 list)) tree
    ///   (ite ((_ is cons) @p0) (car @p0) <wrong-ctor cases / default>))
    /// ```
    ///
    /// The right-constructor arm defers to the BUILTIN selector semantics (the
    /// definition is non-recursive, so the self-reference resolves to the
    /// builtin projection). Faithfulness on the WRONG-constructor arm: every
    /// selector application `(sel t)` in the term store whose argument's model
    /// value is NOT built by an owning constructor gets an explicit
    /// `(= @p0 <arg-value>)` branch carrying the INTERNAL model's committed
    /// value for that application — the value the always-on model gate checked
    /// — so the printed function agrees with the internal model on every
    /// constrained case. Only genuinely unconstrained wrong-constructor inputs
    /// fall through to the arbitrary-but-well-typed canonical default (model
    /// COMPLETION of unconstrained points, never an override of committed ones,
    /// #no-fabricated-model-values).
    ///
    /// Skipped (emission only — solving is unaffected): parametric datatype
    /// instances (their members carry instance-mangled internal names; one
    /// monomorphic `define-fun` under the shared surface name cannot represent
    /// several instances at once) and selector names shared across DIFFERENT
    /// datatypes (two same-name definitions would conflict).
    ///
    /// FAIL-CLOSED (#mv-total-selector-fail-closed): a selector with a
    /// committed case that cannot be faithfully represented — unrenderable or
    /// abstract (`@`) branch key, unrenderable committed value, or two
    /// CONFLICTING committed values for one key — has its WHOLE definition
    /// omitted. A missing total definition reads as a partial function to a
    /// model validator (0 points, non-voiding, confirmed against the pinned
    /// 2025 Dolmen); a total definition whose default arm silently covers a
    /// committed point with a fabricated value reads as a wrong model
    /// (voiding, M4 F1/F2). Same principle when the e-graph assignment's
    /// structural self-check fails: ALL totalizations are withheld.
    pub(super) fn total_selector_definitions(&self, model: &Model) -> Vec<String> {
        struct SelInfo {
            dt_name: String,
            ret_sort: Sort,
            ctors: Vec<String>,
            skip: bool,
        }
        // Insertion-ordered (name, info) list; datatype_iter order is
        // deterministic and small, so linear find is fine.
        let mut sel_infos: Vec<(String, SelInfo)> = Vec::new();
        for (dt_name, ctors) in self.ctx.datatype_iter() {
            // A parametric INSTANCE registers members under mangled internal
            // names with a surface mapping — skip the whole instance.
            if ctors.iter().any(|c| self.ctx.dt_surface_name(c).is_some()) {
                continue;
            }
            for ctor in ctors {
                let Some(fields) = self.ctx.constructor_selector_info(ctor) else {
                    continue;
                };
                for (sel, ret_sort) in fields {
                    if let Some((_, info)) = sel_infos.iter_mut().find(|(n, _)| n == sel) {
                        if info.dt_name != dt_name || info.ret_sort != *ret_sort {
                            // Same selector name under a different datatype (or
                            // conflicting field sort): no single definition can
                            // be emitted under this name.
                            info.skip = true;
                        } else {
                            // Shared by several constructors of ONE datatype:
                            // the tester arm becomes a disjunction.
                            info.ctors.push(ctor.clone());
                        }
                    } else {
                        sel_infos.push((
                            sel.clone(),
                            SelInfo {
                                dt_name: dt_name.to_string(),
                                ret_sort: ret_sort.clone(),
                                ctors: vec![ctor.clone()],
                                skip: false,
                            },
                        ));
                    }
                }
            }
        }
        if sel_infos.is_empty() {
            return Vec::new();
        }

        // Committed wrong-constructor cases, one pass over the term store:
        // sel_name -> [(rendered argument value, rendered application value)].
        //
        // Values come from the SAME engine as every other printed value: the
        // single-source e-graph assignment when the DT lane exported one
        // (#mv-dt-single-source), else the per-term `(get-value)` core. Either
        // way the branch key/value pair matches what `(get-value)` answers on
        // the same terms — that invariant is what makes the totalization
        // faithful.
        //
        // FAIL-CLOSED (#mv-total-selector-fail-closed, M4 F1/F2): a committed
        // case that cannot be represented — unrenderable key or value, an
        // abstract `@` leak in the KEY, or two conflicting committed values
        // for one key — DROPS THE WHOLE DEFINITION for that selector instead
        // of letting the emitted TOTAL function silently cover the committed
        // point with the canonical-default arm (a fabricated value). A missing
        // total definition is at worst `E:partial-dstr` to the validator
        // (0 points, non-voiding); a fabricated committed point is
        // `E:bad-model` (voiding).
        let egraph = self.dt_egraph_available(model);
        if egraph && !self.dt_egraph_self_check_ok(model) {
            // The assignment could not be re-validated structurally: withhold
            // every total selector definition (fail-closed partial model)
            // rather than emit totalizations whose committed cases the
            // validator could refute (#mv-dt-single-source).
            return Vec::new();
        }
        let mut wrong_cases: HashMap<String, Vec<(String, String)>> = HashMap::default();
        let mut dropped: HashSet<String> = HashSet::default();
        for raw in 0..self.ctx.terms.len() {
            let tid = TermId(raw as u32);
            let TermData::App(sym, args) = self.ctx.terms.get(tid) else {
                continue;
            };
            if args.len() != 1 {
                continue;
            }
            let name = sym.name();
            if dropped.contains(name) {
                continue;
            }
            let Some((_, info)) = sel_infos.iter().find(|(n, _)| n == name) else {
                continue;
            };
            if info.skip
                || self
                    .datatype_sort_name(self.ctx.terms.sort(args[0]))
                    .as_deref()
                    != Some(info.dt_name.as_str())
            {
                continue;
            }
            // An argument committed to an OWNING constructor is covered by the
            // tester arm (which is evaluated first). With the e-graph
            // assignment the constructor is read directly off the class.
            if let Some(cls_ctor) = self.dt_egraph_class_ctor(model, args[0]) {
                if info.ctors.iter().any(|c| *c == cls_ctor) {
                    continue;
                }
            }
            let arg_val = if egraph {
                self.dt_egraph_value(model, args[0])
            } else {
                self.term_value_string(model, args[0]).ok()
            };
            let Some(arg_str) = arg_val else {
                // A committed case with no representable key cannot be part of
                // a faithful total definition — drop the definition.
                if std::env::var_os("AY_PHASE_TRACE").is_some() {
                    eprintln!(
                        "c phase-trace mv-total-sel-drop sel={name} reason=arg-unrenderable tid={} arg={}",
                        tid.0, args[0].0
                    );
                }
                dropped.insert(name.to_string());
                continue;
            };
            if arg_str.contains('@') {
                // Abstract/skolem leak in the branch KEY: not expressible as a
                // reliable `(= @p0 …)` guard — fail closed (M4 F2; the former
                // silent case-skip let the default arm override a committed
                // gate-checked value: a voiding channel).
                if std::env::var_os("AY_PHASE_TRACE").is_some() {
                    eprintln!(
                        "c phase-trace mv-total-sel-drop sel={name} reason=abstract-key tid={} arg_str={arg_str}",
                        tid.0
                    );
                }
                dropped.insert(name.to_string());
                continue;
            }
            // Legacy owning-constructor detection by rendered head (kept as a
            // backstop for the non-e-graph path).
            let head = sexpr_head(&arg_str);
            if info.ctors.iter().any(|c| self.dt_surface(c) == head) {
                continue;
            }
            let app_val = if egraph && self.datatype_sort_name(&info.ret_sort).is_some() {
                self.dt_egraph_value(model, tid)
            } else {
                self.term_value_string(model, tid).ok()
            };
            let Some(val_str) = app_val else {
                if std::env::var_os("AY_PHASE_TRACE").is_some() {
                    eprintln!(
                        "c phase-trace mv-total-sel-drop sel={name} reason=value-unrenderable tid={} arg_str={arg_str}",
                        tid.0
                    );
                }
                dropped.insert(name.to_string());
                continue;
            };
            let cases = wrong_cases.entry(name.to_string()).or_default();
            match cases.iter().find(|(a, _)| *a == arg_str) {
                Some((_, prev)) if *prev != val_str => {
                    // Two committed values for ONE argument value is a
                    // model-coherence violation; printing either would
                    // contradict the internal model on the other application.
                    // Surface it loudly and drop the definition (fail-closed;
                    // the former keep-the-first silently printed a value
                    // contradicting the internal model).
                    tracing::warn!(
                        selector = name,
                        arg = %arg_str,
                        "conflicting committed selector values for one argument \
                         value; dropping the selector's total definition"
                    );
                    if std::env::var_os("AY_PHASE_TRACE").is_some() {
                        eprintln!(
                            "c phase-trace mv-total-sel-drop sel={name} reason=conflict tid={} arg_str={arg_str} val={val_str} prev={prev}",
                            tid.0
                        );
                    }
                    dropped.insert(name.to_string());
                }
                Some(_) => {}
                None => cases.push((arg_str, val_str)),
            }
        }

        let mut names: Vec<&String> = sel_infos
            .iter()
            .filter(|(n, i)| !i.skip && !dropped.contains(n.as_str()))
            .map(|(n, _)| n)
            .collect();
        names.sort();
        let mut defs: Vec<String> = Vec::with_capacity(names.len());
        for name in names {
            let (_, info) = sel_infos
                .iter()
                .find(|(n, _)| n == name)
                .expect("name collected from sel_infos above");
            // A selector shared by EVERY constructor of its datatype is already
            // TOTAL: the tester disjunction is exhaustive, so a wrong-ctor arm
            // is unreachable and any default it carried would be pure
            // fabrication (a single-constructor `(mkbox (arr ...) ...)` field
            // accessor must not print a `((as const ...) 0)` arm the model
            // never uses, #model-array-witness). Emit the builtin-deferral
            // body directly. Guarded on no committed wrong-ctor cases, which
            // cannot exist when the owning set is exhaustive.
            let exhaustive = self
                .ctx
                .datatype_iter()
                .find(|(n, _)| *n == info.dt_name)
                .is_some_and(|(_, ctors)| {
                    ctors.iter().all(|c| info.ctors.iter().any(|ic| ic == c))
                });
            if exhaustive && wrong_cases.get(name).map_or(true, |c| c.is_empty()) {
                defs.push(format!(
                    "  (define-fun {sel} ((@p0 {dt})) {ret} ({sel} @p0))",
                    sel = quote_symbol(name),
                    dt = quote_symbol(&info.dt_name),
                    ret = format_sort(&info.ret_sort),
                ));
                continue;
            }
            // else-chain: committed wrong-constructor cases first, canonical
            // default innermost.
            let mut els = self.canonical_default_value(&info.ret_sort);
            if let Some(cases) = wrong_cases.get(name) {
                for (arg, val) in cases.iter().rev() {
                    els = format!("(ite (= @p0 {arg}) {val} {els})");
                }
            }
            let tester = |c: &String| format!("((_ is {}) @p0)", quote_symbol(self.dt_surface(c)));
            let cond = if info.ctors.len() == 1 {
                tester(&info.ctors[0])
            } else {
                format!(
                    "(or {})",
                    info.ctors.iter().map(tester).collect::<Vec<_>>().join(" ")
                )
            };
            defs.push(format!(
                "  (define-fun {sel} ((@p0 {dt})) {ret} (ite {cond} ({sel} @p0) {els}))",
                sel = quote_symbol(name),
                dt = quote_symbol(&info.dt_name),
                ret = format_sort(&info.ret_sort),
            ));
        }
        defs
    }
}

/// Head symbol of a rendered s-expression value: `(cons a b)` -> `cons`,
/// `null` -> `null`. Only used to recognize owning-constructor heads (a
/// mis-parse is shadowed by the tester arm, see
/// [`Executor::total_selector_definitions`]).
fn sexpr_head(s: &str) -> &str {
    let t = s.trim();
    let t = t.strip_prefix('(').unwrap_or(t).trim_start();
    let end = t
        .find(|c: char| c.is_whitespace() || c == ')' || c == '(')
        .unwrap_or(t.len());
    &t[..end]
}
