// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bridge between the solver and the INDEPENDENT, fail-closed model-check gate
//! ([`ay_model_check`]).
//!
//! After `check-sat` produces `Sat` with a model, the gate re-evaluates every
//! assertion under that model with a *separate*, solver-independent evaluator.
//! The two non-confirming verdicts are treated differently, unconditionally
//! (no environment variable changes this):
//!
//! * [`GateVerdict::ModelViolates`] — the gate ground-evaluated an assertion
//!   under the emitted model to `false`. That is a CONCRETE REFUTATION of the
//!   witness, so the `Sat` is ALWAYS downgraded to `Unknown` (fail closed).
//!   The (untrusted) search engine can therefore never ship a refuted model
//!   as `sat`.
//! * [`GateVerdict::CannotConfirm`] — the gate could not ground-evaluate some
//!   fragment (FP, quantifiers, infinite-domain UF, ...). That is evaluator
//!   INCOMPLETENESS, not a refutation; the verdict is kept and the gap is
//!   recorded in the statistics (monitored).
//!
//! This module reuses the model's existing per-leaf value lookups
//! ([`Executor::evaluate_var`] and [`Executor::parse_model_value_string`]) ONLY
//! to populate leaf values for the gate's [`ModelView`]. The compositional
//! evaluation of every operator is done by the gate itself, in its own crate,
//! so the independence is at the operator/composition level — exactly where the
//! historical wrong-`sat` bugs lived.

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::time::Duration;

use ay_core::kani_compat::DetHashMap;
use ay_core::term::TermData;
use ay_core::time::Instant;
use ay_core::{Sort, TermId, TermStore};
use ay_model_check::{ArrayValue, EvalOutcome, Evaluator, GateVerdict, ModelValue, ModelView};

use super::{EvalValue, Model};
use crate::ematching::contains_quantifier;
use crate::executor::Executor;
use crate::executor_types::{SolveResult, UnknownReason};
use crate::logic_detection::LogicCategory;

/// Which sort kind a leaf-defining equality must produce.
#[derive(Clone, Copy, PartialEq, Eq)]
enum DefKind {
    Array,
    Datatype,
}

/// The [`IndependentModelView`] resolution caches, shareable across the views
/// the SAT-emission funnel builds over ONE fixed `(assertions, model)` pair
/// (#gate-view-cache, perf-only).
///
/// The independent gate and the authoritative-failclosed gate each build a
/// fresh view; without sharing, the second gate re-derives the identical
/// `def_index` and re-resolves every array/datatype leaf from scratch — on a
/// flattened store-chain problem (storecomm `sf`) that repeated resolution is
/// quadratic. Every cached entry is a pure function of the fixed model (see
/// the field docs on [`IndependentModelView`]), so sharing changes how OFTEN a
/// resolution is computed, never its result — and it shares only GATE-side
/// caches between two GATE-side consumers, so the strict-vs-independent
/// evaluator separation is untouched.
#[derive(Clone)]
struct SharedViewCaches {
    resolved: Rc<RefCell<HashMap<TermId, ModelValue>>>,
    resolved_none: Rc<RefCell<HashSet<TermId>>>,
    def_index: Rc<RefCell<Option<HashMap<TermId, Vec<TermId>>>>>,
}

impl SharedViewCaches {
    fn fresh() -> Self {
        SharedViewCaches {
            resolved: Rc::new(RefCell::new(HashMap::new())),
            resolved_none: Rc::new(RefCell::new(HashSet::new())),
            def_index: Rc::new(RefCell::new(None)),
        }
    }
}

thread_local! {
    /// The active shared-view-cache scope, if any (see [`GateViewCacheSession`]).
    static ACTIVE_VIEW_CACHES: RefCell<Option<SharedViewCaches>> = const { RefCell::new(None) };
}

/// RAII scope over which every [`IndependentModelView`] shares one set of
/// resolution caches (#gate-view-cache).
///
/// SAFETY CONTRACT (caller-enforced): the session must only span a region over
/// which the assertion set and the model are BOTH fixed — in practice the
/// read-only independent + authoritative gate sequence in
/// [`emit_sat_verdict`](crate::executor::model::sat_emit). Views built outside
/// any session keep today's behavior exactly (fresh caches per view).
pub(in crate::executor) struct GateViewCacheSession {
    prev: Option<SharedViewCaches>,
}

impl GateViewCacheSession {
    pub(in crate::executor) fn new() -> Self {
        let prev = ACTIVE_VIEW_CACHES.with(|c| c.borrow_mut().replace(SharedViewCaches::fresh()));
        GateViewCacheSession { prev }
    }
}

impl Drop for GateViewCacheSession {
    fn drop(&mut self) {
        ACTIVE_VIEW_CACHES.with(|c| *c.borrow_mut() = self.prev.take());
    }
}

/// A [`ModelView`] over a solved [`Model`], reading only LEAF values.
struct IndependentModelView<'a> {
    exec: &'a Executor,
    model: &'a Model,
    /// Array variables currently being resolved through their definitional
    /// equality — guards against cyclic/mutual array definitions (e.g.
    /// `(= a b)` with `(= b a)`), which would otherwise recurse forever.
    resolving: RefCell<HashSet<TermId>>,
    /// Memo of fully-resolved array leaves. A nested datatype-carrying array
    /// (a `Vec` of `Vec`s: constraints of terms) is otherwise re-resolved
    /// exponentially — each `select` reconstructs the whole store-chain, whose
    /// elements are themselves arrays. A resolved `Some` value is the array's
    /// value under the FIXED model, independent of the resolution stack, so it
    /// is safe to cache. (`Rc`-shared across the funnel's views inside a
    /// [`GateViewCacheSession`], #gate-view-cache.)
    resolved: Rc<RefCell<HashMap<TermId, ModelValue>>>,
    /// Memo of leaves whose resolution FAILED (`None`) with ZERO cycle-guard
    /// re-entries observed during the whole resolution frame
    /// (#gate-none-cache). A `None` computed without any `resolving` re-entry
    /// never consulted the in-flight stack, so it is as stack-independent as a
    /// `Some` — a fresh top-level resolution deterministically reproduces it.
    /// A `None` whose frame DID observe a cycle re-entry (`cycle_hits`
    /// advanced) may depend on which ancestors were in flight, so it is never
    /// cached — exactly the case the pre-existing "don't cache None" rule was
    /// protecting. Without this cache, every assertion over an UNRESOLVABLE
    /// defined-array chain (storecomm `sf`: `a_{n} = store(a_{n-1}, i, e)`
    /// with a free base) re-resolves the whole chain, which is quadratic.
    resolved_none: Rc<RefCell<HashSet<TermId>>>,
    /// Count of cycle-guard re-entries (failed `resolving` inserts) in this
    /// view, used by the `resolved_none` frame-purity check above.
    cycle_hits: Cell<u64>,
    /// Lazily-built, model-fixed index of asserted array/datatype definitional
    /// equalities: maps each side of a `(= l r)` (reached along an
    /// unconditionally-asserted path — top-level, `and`-conjunct, model-selected
    /// `ite` branch, or model-unique non-false `or` disjunct) to the OTHER side.
    /// Built ONCE (the model is fixed), so the model-aware branch/disjunct
    /// selection is not re-walked per leaf. `None` until first use.
    /// (`Rc`-shared across the funnel's views inside a
    /// [`GateViewCacheSession`], #gate-view-cache.)
    def_index: Rc<RefCell<Option<HashMap<TermId, Vec<TermId>>>>>,
    /// Guards reentrancy while [`Self::ensure_def_index`] is building: during the
    /// build, definitional-equality lookups return empty so the branch/disjunct
    /// conditions (bool/bv discriminators, independent of array defs) evaluate
    /// without recursing back into a half-built index.
    building_index: Cell<bool>,
}

impl ModelView for IndependentModelView<'_> {
    fn leaf_value(&self, t: TermId) -> Option<ModelValue> {
        let sort = self.exec.ctx.terms.sort(t).clone();
        match &sort {
            // Array leaves: see `array_leaf` — prefer the array's defining
            // equality (evaluated by the gate itself) over the theory-internal
            // array model, which can be polluted by model completion.
            Sort::Array(arr) => self.array_leaf(t, &arr.index_sort, &arr.element_sort),
            // Datatype leaves (native or UF-abstracted): prefer the leaf's
            // asserted definitional equality to a constructor expression,
            // evaluated by the gate itself, so a tester/selector over the leaf
            // sees the full constructor value instead of an opaque token. Fall
            // back to the theory leaf lookup when there is no definition.
            _ if self.exec.datatype_sort_name(&sort).is_some() => {
                // FAIL-CLOSED BACKSTOP (#mv-gate-reads-printed-dt): the model
                // PRINTER's single source of truth for a datatype-sorted
                // constant is `dt_egraph_value` — the concrete constructor tree
                // it emits into `(get-model)` and hands to the external
                // validator (output.rs checks it FIRST, unconditionally, for
                // every DT-sorted const). The gate must re-evaluate THAT exact
                // tree, not a representative token: reading an abstract
                // `@nat!N`/`@list!N`/`@tree!N` here makes an assertion over the
                // printed structure `Unevaluable` (a monitored coverage gap),
                // so a printed reconstruction that STRUCTURALLY FALSIFIES an
                // assertion — the mutually-recursive-datatype ModelUnsat class
                // (Barrett nat/list/tree) — slips past as `sat`. Parsing the
                // rendered value back into a gate value and evaluating it under
                // the same structural selector-projection semantics the
                // validator uses turns such a witness into an enforced
                // `ModelViolates` (Sat → Unknown). Faithful by construction:
                // whenever `dt_egraph_value` is `Some`, the printer emits
                // exactly this value; when it is `None` (poisoned / no export /
                // combined lanes) the leaf falls through to the unchanged
                // resolution chain below, so no currently-confirmed model can
                // regress.
                //
                // PERF CONFINEMENT (STAGE 1, #mv-backstop-selector-bearing):
                // the printed-value re-read is CONFINED to SELECTOR-BEARING
                // datatypes — the only shape the ModelUnsat class occurs in
                // (mutually-recursive nat/list/tree). An ENUM-ONLY datatype
                // (all-nullary, e.g. the Bouvier `vlsat` Petri-net markings —
                // hundreds of nullary constants) is resolved correctly by the
                // native nullary-constructor / theory-leaf path below WITHOUT
                // the backstop (those models were validator-VALID pre-backstop),
                // and running the backstop's legacy `resolve_dt_value`
                // reconstruction (an O(terms) tester scan) over each of its
                // hundreds of enum constants — once per gate leaf, and again in
                // `gate_emit_reconstructions` — was a ~39x model-EMIT regression
                // (vlsat3_h00 1.38s→53s) that risked TIMING OUT the heavy enum
                // instances (AY's margin over SMTInterpol). Skipping it there is
                // sound (enum leaves never take the recursive-tree path) and
                // restores the pre-backstop emit time.
                let dt_selector_bearing = self.exec.selector_bearing_datatype(&sort);
                if dt_selector_bearing {
                    if let Some(rendered) = self.exec.dt_egraph_value(self.model, t) {
                        if let Some(v) = self.exec.parse_rendered_dt_value(&rendered, &sort) {
                            return Some(v);
                        }
                    }
                }
                // A NULLARY constructor lowered to a bare leaf (e.g. `None`
                // emitted as a `Sort::Uninterpreted` constant whose NAME is the
                // constructor) denotes exactly that constructor value — resolve
                // it to the full `Datatype` value so testers/`=` over it evaluate
                // (an opaque token would be incomparable to a `Datatype`).
                if let Some(v) = self.nullary_constructor_leaf(t, &sort) {
                    return Some(v);
                }
                // Total-datatype-model construction (#dt-total-model): the
                // constructed ground value for this leaf, identical to the
                // value the solver-side validators evaluated and the printer
                // emits, so the gate confirms/refutes the SAME witness.
                if let Some(mv) = self.model.dt_ground.get(&t) {
                    return Some(mv.clone());
                }
                if let Some(v) = self.datatype_leaf(t) {
                    return Some(v);
                }
                if let Some(v) = self.reconstruct_datatype_value(t, 0) {
                    return Some(v);
                }
                // Legacy printer resolution (#mv-gate-reads-printed-dt): a
                // datatype const the gate's own reconstruction cannot pin is
                // still PRINTED — the printer falls to `resolve_dt_value`'s
                // tester / EUF-class strategies (Uninterpreted-lowered datatype
                // sorts, output.rs). The gate must re-check THAT printed
                // constructor tree, or a legacy-emitted witness that
                // structurally falsifies an assertion ships as `sat` (the v2
                // nat/list/tree ModelUnsat: `x1 = (succ zero)` printed against
                // `(not (= x1 (succ zero)))`). Parse the printed value so it is
                // caught as `ModelViolates`; the printer emits this SAME value,
                // so a valid witness re-checks true and never regresses.
                if dt_selector_bearing {
                    if let Sort::Uninterpreted(sort_name) = &sort {
                        if let Some(rendered) = self.exec.resolve_dt_value(sort_name, t, self.model)
                        {
                            if let Some(v) = self.exec.parse_rendered_dt_value(&rendered, &sort) {
                                return Some(v);
                            }
                        }
                    }
                }
                let ev = self.exec.evaluate_var(self.model, t, &sort);
                eval_value_to_model_value(&ev, &sort)
            }
            // Every scalar / seq / uninterpreted leaf is resolved by the model's
            // existing leaf lookup, then converted into a gate value.
            _ => {
                let ev = self.exec.evaluate_var(self.model, t, &sort);
                eval_value_to_model_value(&ev, &sort)
            }
        }
    }

    /// Datatype registry for datatypes abstracted to `Sort::Uninterpreted(name)`
    /// (the eager DtAufbv path lowers a declared datatype to an uninterpreted
    /// sort, so `(fld_rhs x)` / `(is-C x)` / `(C ..)` carry `Uninterpreted`, not
    /// `Sort::Datatype`). Rebuild the `DatatypeSort` from the front-end's
    /// declaration tables so the gate's evaluator can project selectors, decide
    /// testers, and build constructor values faithfully — the completeness that
    /// lets it CONFIRM a valid datatype-carrying model AND REFUTE a
    /// constructor-injectivity violation (#g4-gate-dt-registry).
    fn datatype_def(&self, name: &str) -> Option<ay_core::DatatypeSort> {
        self.exec.dt_registry_lookup(name)
    }

    /// The model's committed value for the uninterpreted-function application
    /// `t`. The gate calls this only for applications it cannot evaluate
    /// structurally (i.e. genuine UF applications and under-specified datatype
    /// operations); it keys them by evaluated argument VALUES and enforces
    /// single-valuedness itself, so returning the per-application committed
    /// value here (analogous to a leaf) is what lets the gate expose a model
    /// that collapsed two congruent applications' arguments (#uflia-uf-collapse).
    ///
    /// Reads the value through the solver's own model evaluator — the same
    /// value a `get-value ((f ...))` would report — and converts it into a gate
    /// value. Anything the evaluator cannot pin (Unknown) leaves the leaf
    /// unpinned so the gate fails closed. This does NOT trust the per-application
    /// pins for the final verdict: the gate's `uf_graph` collapses equal-argument
    /// applications to one value, so inconsistent pins are surfaced, not honoured.
    fn uf_app_value(&self, t: TermId) -> Option<ModelValue> {
        // Only meaningful for applications; a bare leaf goes through
        // `leaf_value`. Guard defensively so this can never fabricate a value
        // for a non-application term.
        if !matches!(self.exec.ctx.terms.get(t), TermData::App(_, _)) {
            return None;
        }
        // Total-datatype-model construction (#dt-total-model): a
        // datatype-sorted application (e.g. a wrong-constructor selector
        // chain) the construction phase resolved carries its constructed
        // STRUCTURED value — never the canonical Element token, which the
        // gate could not compare against a `Datatype` value.
        if let Some(mv) = self.model.dt_ground.get(&t) {
            return Some(mv.clone());
        }
        let sort = self.exec.ctx.terms.sort(t).clone();
        // Single-source e-graph assignment (#mv-dt-single-source x
        // #mv-gate-reads-printed-dt, mv-rerun-20260718 regression): when the
        // DT lane exported its e-graph, `construct_total_datatype_model`
        // STEPS ASIDE, so `dt_ground` has no structured value for a
        // wrong-constructor selector chain — but the assignment DOES commit a
        // per-class value for it (the very value the printer's total selector
        // definitions emit and Dolmen re-checks). Without this, the chain
        // resolves to an opaque EUF `Element` token below and every equality
        // against a structured `Datatype` value observes as "incomparable" —
        // the gate then CannotConfirm a witness it should confirm (166
        // Barrett QF_DT sats fail-closed to unknown; bisected to merge
        // 547590f8, both parents sat). Parse the SAME rendered value the
        // printer emits into a structured value, exactly as `leaf_value`
        // already does for datatype leaves. FAIL-CLOSED: `dt_egraph_value`
        // never fabricates (no assignment / poisoned class / failed
        // self-check => `None`), and an unparseable rendering leaves the
        // application unpinned as today.
        if self.exec.datatype_sort_name(&sort).is_some() {
            if let Some(rendered) = self.exec.dt_egraph_value(self.model, t) {
                if let Some(v) = self.exec.parse_rendered_dt_value(&rendered, &sort) {
                    return Some(v);
                }
            }
        }
        let ev = self.exec.evaluate_term(self.model, t);
        eval_value_to_model_value(&ev, &sort)
    }

    /// The model's committed value for an array-`select` read `t` = `(select A
    /// i)`. The gate calls this ONLY when it could not resolve `A` to a concrete
    /// `(default, finite-store)` interpretation (a partial/unreconstructable
    /// array leaf) — the analogue of [`uf_app_value`](Self::uf_app_value).
    ///
    /// FAITHFULNESS: the value is read through the array theory's OWN read
    /// evaluator ([`Executor::evaluate_select`]), which resolves the read against
    /// the reconstructed `array_model` (store-chain / const-array / stored
    /// entries / trusted default) — the SAME interpretation `get-model` serialises
    /// — and returns `Unknown` when the model cannot resolve it. It deliberately
    /// does NOT use the whole-term evaluator ([`Executor::evaluate_term`]), whose
    /// `select` case falls back to the LIA/BV *opaque* value for the select TERM;
    /// under AUFLIA that opaque value can DISAGREE with the emitted array (a
    /// `(select A i)` the LIA solver treated as an unconstrained variable), so
    /// trusting it here could confirm — or spuriously refute — a read whose
    /// emitted-array value differs. Reading only the array interpretation keeps
    /// the gate checking the EMITTED witness, and fails closed otherwise.
    ///
    /// The gate keys reads by `(array-term, index-value)` and enforces
    /// single-valuedness itself, so this per-read value is only ever a leaf the
    /// McCarthy-consistency graph then reconciles — surfacing, not honouring, an
    /// array model that pins two coincident reads to different values
    /// (#array-select-collapse). Guarded to a genuine binary `select`.
    fn array_select_value(&self, t: TermId) -> Option<ModelValue> {
        let TermData::App(sym, args) = self.exec.ctx.terms.get(t) else {
            return None;
        };
        if sym.name() != "select" || args.len() != 2 {
            return None;
        }
        let (array, index) = (args[0], args[1]);
        let sort = self.exec.ctx.terms.sort(t).clone();
        let ev = self.exec.evaluate_select(self.model, array, index);
        eval_value_to_model_value(&ev, &sort)
    }
}

impl<'a> IndependentModelView<'a> {
    /// Build a view over `(exec, model)`. Inside a [`GateViewCacheSession`]
    /// the resolution caches are the session's shared ones (#gate-view-cache);
    /// otherwise the view gets fresh caches — today's behavior exactly. The
    /// `resolving` cycle-guard stack is always per-view (it tracks in-flight
    /// frames, never results).
    fn new(exec: &'a Executor, model: &'a Model) -> Self {
        let caches = ACTIVE_VIEW_CACHES
            .with(|c| c.borrow().clone())
            .unwrap_or_else(SharedViewCaches::fresh);
        IndependentModelView {
            exec,
            model,
            resolving: RefCell::new(HashSet::new()),
            resolved: caches.resolved,
            resolved_none: caches.resolved_none,
            cycle_hits: Cell::new(0),
            def_index: caches.def_index,
            building_index: Cell::new(false),
        }
    }
}

impl IndependentModelView<'_> {
    /// Resolve an array-variable leaf.
    ///
    /// An array variable is rarely a true free leaf: it is usually *defined* by
    /// an assertion `(= a <array-expr>)`. We resolve such a leaf by evaluating
    /// `<array-expr>` with the gate's OWN evaluator — this is both faithful to
    /// the formula and independent of the theory's internal array model (which
    /// at gate-time can carry a model-completion default that contradicts the
    /// asserted equality, producing a spurious violation). Only when there is no
    /// definition do we fall back to the reconstructed array model.
    ///
    /// A cycle guard breaks mutual/self definitions: on re-entry for the same
    /// array term we return `None` (so that sub-expression is unevaluable and
    /// the resolution falls through soundly).
    fn array_leaf(&self, t: TermId, index_sort: &Sort, element_sort: &Sort) -> Option<ModelValue> {
        if let Some(cached) = self.resolved.borrow().get(&t) {
            return Some(cached.clone());
        }
        if self.resolved_none.borrow().contains(&t) {
            return None; // cached stack-independent failure (#gate-none-cache)
        }
        if !self.resolving.borrow_mut().insert(t) {
            self.cycle_hits.set(self.cycle_hits.get() + 1);
            return None; // cycle
        }
        let hits_before = self.cycle_hits.get();
        let result = self.array_leaf_inner(t, index_sort, element_sort);
        self.resolving.borrow_mut().remove(&t);
        match &result {
            Some(v) => {
                self.resolved.borrow_mut().insert(t, v.clone());
            }
            // A failure whose frame observed NO cycle re-entry never consulted
            // the in-flight stack, so it is a pure function of the fixed model
            // — cacheable (#gate-none-cache). A post-cycle failure is not.
            None if self.cycle_hits.get() == hits_before => {
                self.resolved_none.borrow_mut().insert(t);
            }
            None => {}
        }
        result
    }

    fn array_leaf_inner(
        &self,
        t: TermId,
        index_sort: &Sort,
        element_sort: &Sort,
    ) -> Option<ModelValue> {
        if self
            .model
            .array_model
            .as_ref()
            .is_some_and(|arrays| arrays.read_conflicted.contains(&t))
        {
            return None;
        }
        // 1. Definitional equality `(= t <array-expr>)`: evaluate the defining
        //    expression compositionally with the gate's own evaluator. A leaf can
        //    carry SEVERAL asserted definitions (e.g. a fresh `(= d (const-array
        //    x))` plus alias equalities `(= d other!fld_data)`); they are all
        //    asserted EQUAL, so ANY that the gate can fully evaluate yields the
        //    array's value — try them in order and take the first that resolves to
        //    a concrete array. Consistency between the alternatives is still
        //    enforced: each OTHER definition is itself a top-level assertion the
        //    gate ground-checks, so two definitions that disagree under the model
        //    produce a `ModelViolates` there (never suppressed here).
        for def in self.array_definitions(t) {
            let ev = Evaluator::new(&self.exec.ctx.terms, self);
            if let EvalOutcome::Value(v @ ModelValue::Array(_)) = ev.evaluate(def) {
                return Some(v);
            }
            // else: try the next definition / fall through to the reconstructed
            // model (branch 2 below).
        }

        // 2. Fallback: the array theory's reconstructed model entry.
        if let Some(v) = self.array_from_model(t, index_sort, element_sort) {
            return Some(v);
        }

        // 3. EXTENSIONALITY-COVERING MERGE. An array leaf the theory model does
        //    not reconstruct, but which is asserted EQUAL to other array leaves
        //    (a mutual SSA-copy class `(= a b)`, `(= b c)`), is resolved by
        //    giving the WHOLE class ONE shared canonical array value: the fixed
        //    canonical default of the element sort (a deterministic function of
        //    the sort, identical for every member) plus the merged committed
        //    direct-select reads of the class. Because every member then denotes
        //    the IDENTICAL array, `select(a,i)` and `select(b,i)` read the same
        //    value at every index, so the asserted equalities confirm.
        //
        //    SOUND: the members are asserted mutually equal, so a model in which
        //    they are the identical array satisfies those equalities; the shared
        //    default only sets indices in NO committed read (hence in no other
        //    constraint besides the extensionality), and the gate still
        //    re-checks every assertion, so any real conflict ⇒ `ModelViolates`.
        //    Guards: only array-`Var == Var` equalities that are top-level or
        //    top-level-`and` conjuncts join the class (never `or`/`ite`/`not`);
        //    a committed-read VALUE conflict between members fails the whole
        //    class closed; the default is a fixed function of the element sort.
        //
        //    NOTE (#seed-1213-case-187): a printed-witness fallback was tried
        //    here and REVERTED — parsing back the printer's total array and
        //    refuting against it is UNSOUND, because the printer fabricates a
        //    single canonical default for the array's unread indices, so a
        //    satisfiable `(distinct -3 (select a z) (select a x))` with z != x
        //    and `a` genuinely unpinned would be falsely refuted (both reads
        //    collapse to the fabricated default). A refutation is only sound
        //    when it holds in EVERY completion of the unpinned leaf; that
        //    "for-all-completions" reasoning is the job of the authoritative
        //    congruent-read fail-closed gate, not this per-leaf resolver. Case
        //    187 is fixed by CONSTRUCTION (same-array read-congruence
        //    propagation in ay-arrays), so no wrong model reaches here for that
        //    class; an unpinned leaf stays a coverage gap (keeps `sat`).
        self.array_extensionality_value(t, index_sort, element_sort)
    }

    /// Branch 2 of [`array_leaf_inner`]: the array theory's reconstructed model
    /// entry for `t`, or `None` if partial/absent.
    fn array_from_model(
        &self,
        t: TermId,
        index_sort: &Sort,
        element_sort: &Sort,
    ) -> Option<ModelValue> {
        let array_model = self.model.array_model.as_ref()?;
        // Extraction dropped at least one disputed cell.  Neither an existing
        // default nor a later completion may turn that deliberately-partial
        // interpretation into independent evidence for a total array.
        if array_model.read_conflicted.contains(&t) {
            return None;
        }
        let interp = array_model.array_values.get(&t)?;
        let default_str = interp.default.as_ref()?; // a partial array fails closed
        let default = self.parse_leaf(default_str, element_sort)?;
        let mut store = Vec::with_capacity(interp.stores.len());
        // ArrayInterpretation is authoritative/newest first, whereas the
        // independent evaluator's ArrayValue is oldest first (and selects by
        // scanning in reverse). Reverse at this representation boundary so a
        // repeated store index keeps the same winner the solver/emitter use.
        for (k_s, v_s) in interp.stores.iter().rev() {
            let key = self.parse_leaf(k_s, index_sort)?;
            let val = self.parse_leaf(v_s, element_sort)?;
            store.push((key, val));
        }
        Some(ModelValue::Array(Box::new(ArrayValue { default, store })))
    }

    /// Branch 3 of [`array_leaf_inner`]: the extensionality-covering shared value
    /// for `t`'s asserted-equality class. Returns `None` when `t` is not in a
    /// nontrivial array-`Var==Var` class, when the class carries an asserted
    /// read the model does not pin, or when any two pinned values disagree
    /// (fail closed).
    fn array_extensionality_value(
        &self,
        t: TermId,
        index_sort: &Sort,
        element_sort: &Sort,
    ) -> Option<ModelValue> {
        let class = self.array_equality_class(t);
        if class.len() < 2 {
            return None; // not an extensionality case
        }
        if self.model.array_model.as_ref().is_some_and(|arrays| {
            class
                .iter()
                .any(|member| arrays.read_conflicted.contains(member))
        }) {
            return None;
        }
        // 3a. ADOPT AN EMITTED ENTRY (#ext-class-adopt-emitted). The members
        //    are asserted mutually equal, so a member's COMPLETE emitted
        //    array-model entry is already the interpretation `(get-model)`
        //    serializes for the whole class — adopt it instead of
        //    manufacturing anything (this reads the emitted witness and
        //    fabricates nothing). Two complete entries that disagree mean the
        //    emitted model is not single-valued on the class ⇒ fail closed.
        let mut adopted: Option<ModelValue> = None;
        for &m in &class {
            if let Some(v) = self.array_from_model(m, index_sort, element_sort) {
                match &adopted {
                    Some(prev) if !values_equal(prev, &v) => return None, // ⇒ fail closed
                    Some(_) => {}
                    None => adopted = Some(v),
                }
            }
        }
        // 3b. Merge the class's committed reads (fail-closed on a value
        //    conflict at one index): (i) the array theory's per-member store
        //    entries; (ii) every ASSERTED direct `select` over a class member
        //    (#ext-class-read-cover), keyed by its model-evaluated index, with
        //    its model-committed value. (ii) enforces this branch's own
        //    soundness condition — "the shared default only sets indices in NO
        //    committed read" — so an asserted read the model does not pin
        //    fails the class CLOSED (resolution degrades to the monitored
        //    `CannotConfirm` coverage-gap posture) instead of fabricating a
        //    default value the constraints may contradict. A fabricated value
        //    is not evidence about the emitted witness, so it must never
        //    ground a `ModelViolates` refutation.
        let mut store: Vec<(ModelValue, ModelValue)> = Vec::new();
        for &m in &class {
            let Some(am) = self.model.array_model.as_ref() else {
                continue;
            };
            let Some(interp) = am.array_values.get(&m) else {
                continue;
            };
            let mut seen_member_keys: Vec<ModelValue> = Vec::new();
            for (k_s, v_s) in &interp.stores {
                let key = self.parse_leaf(k_s, index_sort)?;
                // Interpretation stores are authoritative/newest first. An
                // older duplicate is shadowed within this member and is not a
                // second committed read (nor a cross-member conflict).
                if seen_member_keys.iter().any(|seen| values_equal(seen, &key)) {
                    continue;
                }
                seen_member_keys.push(key.clone());
                let val = self.parse_leaf(v_s, element_sort)?;
                if let Some((_, prev)) = store.iter().find(|(k, _)| values_equal(k, &key)) {
                    if !values_equal(prev, &val) {
                        return None; // committed read conflict ⇒ fail closed
                    }
                } else {
                    store.push((key, val));
                }
            }
        }
        // (ii): walk the assertions' subterms for direct reads of a member.
        {
            let terms = &self.exec.ctx.terms;
            let mut stack: Vec<TermId> = self.exec.ctx.assertions.to_vec();
            let mut seen: HashSet<TermId> = HashSet::new();
            while let Some(cur) = stack.pop() {
                if !seen.insert(cur) {
                    continue;
                }
                match terms.get(cur) {
                    TermData::App(sym, args) => {
                        if sym.name() == "select" && args.len() == 2 && class.contains(&args[0]) {
                            let idx_ev = self.exec.evaluate_term(self.model, args[1]);
                            let key = eval_value_to_model_value(&idx_ev, index_sort)?;
                            let val = self.committed_read_value(cur, element_sort)?;
                            if let Some((_, prev)) =
                                store.iter().find(|(k, _)| values_equal(k, &key))
                            {
                                if !values_equal(prev, &val) {
                                    return None; // committed read conflict ⇒ fail closed
                                }
                            } else {
                                store.push((key, val));
                            }
                        }
                        stack.extend(args.iter().copied());
                    }
                    TermData::Not(inner) => stack.push(*inner),
                    TermData::Ite(c, a, b) => {
                        stack.push(*c);
                        stack.push(*a);
                        stack.push(*b);
                    }
                    _ => {}
                }
            }
        }
        // An adopted entry is TOTAL, so the merged committed reads must agree
        // with it at every index; a disagreement means the emitted model
        // contradicts its own committed reads ⇒ fail closed.
        if let Some(ModelValue::Array(base)) = adopted {
            for (k, v) in &store {
                let at = base
                    .store
                    .iter()
                    .rev()
                    .find(|(bk, _)| values_equal(bk, k))
                    .map(|(_, bv)| bv)
                    .unwrap_or(&base.default);
                if !values_equal(at, v) {
                    return None; // reads contradict the emitted entry ⇒ fail closed
                }
            }
            return Some(ModelValue::Array(base));
        }
        let default = self.canonical_model_value(element_sort)?;
        Some(ModelValue::Array(Box::new(ArrayValue { default, store })))
    }

    /// The model-committed value of one asserted read `sel = (select a i)`
    /// over an extensionality-class member: the solver evaluator's structural
    /// value when it resolves, cross-checked against — or, when structural
    /// evaluation cannot resolve, taken from — the read's committed OPAQUE
    /// per-term value in the EUF/LIA views (a select the array theory never
    /// materialized is committed there as a plain term value). `None` (⇒ the
    /// class fails closed) when the model pins nothing, or pins two
    /// disagreeing values (an internally inconsistent model must not ground
    /// either a confirmation or a refutation).
    fn committed_read_value(&self, sel: TermId, element_sort: &Sort) -> Option<ModelValue> {
        let structural = {
            let ev = self.exec.evaluate_term(self.model, sel);
            eval_value_to_model_value(&ev, element_sort)
        };
        let opaque = self
            .model
            .euf_model
            .as_ref()
            .and_then(|e| e.term_values.get(&sel))
            .and_then(|s| self.parse_leaf(s, element_sort))
            .or_else(|| match element_sort {
                Sort::Int => self
                    .model
                    .lia_model
                    .as_ref()
                    .and_then(|l| l.values.get(&sel))
                    .map(|v| ModelValue::Int(v.clone())),
                _ => None,
            });
        match (structural, opaque) {
            (Some(a), Some(b)) => values_equal(&a, &b).then_some(a), // disagree ⇒ fail closed
            (Some(a), None) => Some(a),
            (None, Some(b)) => Some(b),
            (None, None) => None,
        }
    }

    /// The asserted array-`Var == Var` equality class of `t` (reflexive-transitive
    /// closure), joining ONLY top-level or top-level-`and`-conjunct equalities
    /// between two array-sorted variables — never conditional (`or`/`ite`/`not`).
    fn array_equality_class(&self, t: TermId) -> Vec<TermId> {
        let terms = &self.exec.ctx.terms;
        // Gather all qualifying array Var==Var equalities as undirected edges.
        let mut edges: Vec<(TermId, TermId)> = Vec::new();
        let mut stack: Vec<(TermId, u32)> = self
            .exec
            .ctx
            .assertions
            .iter()
            .map(|&a| (a, 32u32))
            .collect();
        while let Some((cand, depth)) = stack.pop() {
            if depth == 0 {
                continue;
            }
            match terms.get(cand) {
                TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                    let (l, r) = (args[0], args[1]);
                    if l != r
                        && matches!(terms.sort(l), Sort::Array(_))
                        && matches!(terms.get(l), TermData::Var(_, _))
                        && matches!(terms.get(r), TermData::Var(_, _))
                    {
                        edges.push((l, r));
                    }
                }
                TermData::App(sym, args) if sym.name() == "and" => {
                    for &c in args {
                        stack.push((c, depth - 1));
                    }
                }
                _ => {}
            }
        }
        // BFS the closure from `t`.
        let mut class = vec![t];
        let mut i = 0;
        while i < class.len() {
            let cur = class[i];
            for &(a, b) in &edges {
                let other = if a == cur {
                    Some(b)
                } else if b == cur {
                    Some(a)
                } else {
                    None
                };
                if let Some(o) = other {
                    if !class.contains(&o) {
                        class.push(o);
                    }
                }
            }
            i += 1;
        }
        class
    }

    /// A fixed, deterministic canonical model value for `sort` — the shared
    /// default of an extensionality class. A pure function of the sort, so every
    /// class member gets the IDENTICAL default (a prerequisite for the members to
    /// denote the same array). `None` for sorts with no canonical ground value.
    fn canonical_model_value(&self, sort: &Sort) -> Option<ModelValue> {
        match sort {
            Sort::Bool => Some(ModelValue::Bool(false)),
            Sort::Int => Some(ModelValue::Int(num_bigint::BigInt::from(0))),
            Sort::Real => Some(ModelValue::Real(num_rational::BigRational::from(
                num_bigint::BigInt::from(0),
            ))),
            Sort::BitVec(w) => Some(ModelValue::bitvec(num_bigint::BigInt::from(0), w.width)),
            Sort::String => Some(ModelValue::Str(String::new())),
            Sort::Array(arr) => {
                let default = self.canonical_model_value(&arr.element_sort)?;
                Some(ModelValue::Array(Box::new(ArrayValue {
                    default,
                    store: Vec::new(),
                })))
            }
            _ => {
                // Datatype (native or UF-abstracted): the canonical constructor
                // value (a nullary constructor if present, else the first
                // constructor applied to canonical field values).
                let name = self.exec.datatype_sort_name(sort)?;
                self.canonical_datatype_value(&name, &mut Vec::new())
            }
        }
    }

    /// Canonical [`ModelValue::Datatype`] for datatype `name`: a nullary
    /// constructor if one exists, else the first constructor applied to canonical
    /// field values (recursively). `visited` breaks self-referential field sorts.
    fn canonical_datatype_value(
        &self,
        name: &str,
        visited: &mut Vec<String>,
    ) -> Option<ModelValue> {
        if visited.iter().any(|v| v == name) {
            return None; // unbounded recursion through a self-referential field
        }
        visited.push(name.to_string());
        let (_, ctor_names) = self.exec.ctx.datatype_iter().find(|(dt, _)| *dt == name)?;
        // Prefer a nullary constructor.
        let chosen = ctor_names
            .iter()
            .find(|cn| {
                self.exec
                    .ctx
                    .constructor_selector_info(cn)
                    .map_or(false, |f| f.is_empty())
            })
            .or_else(|| ctor_names.first())?
            .clone();
        let fields = self.exec.ctx.constructor_selector_info(&chosen)?.to_vec();
        let mut args = Vec::with_capacity(fields.len());
        for (_fname, fsort) in &fields {
            let v = match fsort {
                Sort::Bool => ModelValue::Bool(false),
                Sort::Int => ModelValue::Int(num_bigint::BigInt::from(0)),
                Sort::Real => {
                    ModelValue::Real(num_rational::BigRational::from(num_bigint::BigInt::from(0)))
                }
                Sort::BitVec(w) => ModelValue::bitvec(num_bigint::BigInt::from(0), w.width),
                Sort::String => ModelValue::Str(String::new()),
                Sort::Array(arr) => {
                    let default = self.canonical_field_value(&arr.element_sort, visited)?;
                    ModelValue::Array(Box::new(ArrayValue {
                        default,
                        store: Vec::new(),
                    }))
                }
                _ => {
                    let dtn = self.exec.datatype_sort_name(fsort)?;
                    self.canonical_datatype_value(&dtn, visited)?
                }
            };
            args.push(v);
        }
        visited.pop();
        Some(ModelValue::Datatype { ctor: chosen, args })
    }

    fn canonical_field_value(&self, sort: &Sort, visited: &mut Vec<String>) -> Option<ModelValue> {
        match sort {
            Sort::Bool => Some(ModelValue::Bool(false)),
            Sort::Int => Some(ModelValue::Int(num_bigint::BigInt::from(0))),
            Sort::Real => Some(ModelValue::Real(num_rational::BigRational::from(
                num_bigint::BigInt::from(0),
            ))),
            Sort::BitVec(w) => Some(ModelValue::bitvec(num_bigint::BigInt::from(0), w.width)),
            Sort::String => Some(ModelValue::Str(String::new())),
            Sort::Array(arr) => {
                let default = self.canonical_field_value(&arr.element_sort, visited)?;
                Some(ModelValue::Array(Box::new(ArrayValue {
                    default,
                    store: Vec::new(),
                })))
            }
            _ => {
                let dtn = self.exec.datatype_sort_name(sort)?;
                self.canonical_datatype_value(&dtn, visited)
            }
        }
    }

    /// Find an asserted `(= t <array-expr>)` / `(= <array-expr> t)` that
    /// *defines* the array variable `t`, returning the array expression.
    ///
    /// The equality may be a TOP-LEVEL assertion OR a direct CONJUNCT of a
    /// top-level `(and ...)` — the eager encoder emits a `Vec::push` as one
    /// asserted `and` whose conjuncts are the SSA field updates (`(= v!fld_data
    /// (store ...))`, `(= v!fld_len ...)`, ...). Each conjunct of a top-level
    /// `and` is UNCONDITIONALLY asserted, so resolving `t` through it is faithful
    /// to the formula — and it is essential: the theory's RECONSTRUCTED array
    /// interpretation for such a push target can carry a completion default that
    /// contradicts the asserted store-chain (a wrong `default`), which is exactly
    /// the spurious `ModelViolates` this definitional resolution exists to avoid.
    /// Collect ALL asserted definitions `(= t <array-expr>)` of the array leaf
    /// `t`, descending ONLY through nested `and` conjunctions — every conjunct of
    /// a (conjunct of a) top-level `and` is UNCONDITIONALLY asserted, so a
    /// definition found there holds in the model. Never descends `or`/`ite`/`not`
    /// (conditional), so no conditionally-held equality is mistaken for a
    /// definition. The caller tries them in order and takes the first the gate
    /// can fully evaluate (they are all asserted equal).
    fn array_definitions(&self, t: TermId) -> Vec<TermId> {
        self.definitions_for(t, DefKind::Array)
    }

    /// All asserted definitional partners of leaf `t` whose sort matches `kind`,
    /// read from the memoized [`Self::ensure_def_index`]. (Both sides of every
    /// asserted array/datatype `(= l r)` are indexed, so this returns `t`'s
    /// entailed-equal partners — leaf aliases and `store`/`const-array` exprs.)
    fn definitions_for(&self, t: TermId, kind: DefKind) -> Vec<TermId> {
        self.ensure_def_index();
        let idx = self.def_index.borrow();
        let Some(map) = idx.as_ref() else {
            return Vec::new();
        };
        let Some(partners) = map.get(&t) else {
            return Vec::new();
        };
        partners
            .iter()
            .copied()
            .filter(|&p| self.sort_is_kind(self.exec.ctx.terms.sort(p), kind))
            .collect()
    }

    /// Build the model-fixed definitional-equality index ONCE. A single walk over
    /// every assertion records — along UNCONDITIONALLY-asserted paths only — both
    /// sides of each array/datatype equality `(= l r)` as mutual defining partners.
    ///
    /// Asserted paths: the top-level assertion; every conjunct of an `and`; the
    /// model-SELECTED branch of an `ite`/`if`; and the model-UNIQUE non-false
    /// disjunct of an `or` (all other disjuncts provably `false` under the fixed
    /// model, so the survivor is entailed — the exact analogue of the `ite`
    /// branch, applied to the origin-stream field-decomposition axioms
    /// `(or <discriminator> (and (= f1 sel1) ...))`). Never descends `not` or a
    /// disjunction with two non-false arms (undetermined). Built once because the
    /// model is fixed, so the (potentially expensive) branch/disjunct evaluation
    /// is not repeated per resolved leaf.
    ///
    /// SOUND: every recorded equality is unconditionally entailed by the
    /// assertions in THIS model, so aliasing a leaf to its partner's value cannot
    /// widen the model; and the gate independently re-checks every assertion
    /// (including each `or`/`ite`), so a mis-selected branch can only surface as a
    /// `ModelViolates` (→ Unknown), never confirm a wrong witness. (#g3-or-entailed-def)
    fn ensure_def_index(&self) {
        if self.def_index.borrow().is_some() || self.building_index.get() {
            return;
        }
        self.building_index.set(true);
        let mut map: HashMap<TermId, Vec<TermId>> = HashMap::new();
        let assertions = self.exec.ctx.assertions.clone();
        for assertion in assertions {
            self.index_walk(assertion, 32, &mut map);
        }
        self.building_index.set(false);
        *self.def_index.borrow_mut() = Some(map);
        // Discard any array/datatype leaf values MEMOIZED during the build: they
        // were computed with the index empty (branch conditions only need
        // bool/bv leaves, but a defensive clear guarantees no under-resolved
        // value leaks into the real resolution that now has the full index).
        // The negative cache is cleared for the same reason: a leaf that
        // FAILED against the half-built index may resolve against the full one
        // (#gate-none-cache).
        self.resolved.borrow_mut().clear();
        self.resolved_none.borrow_mut().clear();
    }

    /// Record every array/datatype equality reachable from `cand` along an
    /// unconditionally-asserted path into `map` (both directions). See
    /// [`Self::ensure_def_index`] for the soundness argument.
    fn index_walk(&self, cand: TermId, depth: u32, map: &mut HashMap<TermId, Vec<TermId>>) {
        if depth == 0 {
            return;
        }
        // Record a `(= l r)` where the operands are array/datatype sorted.
        if let TermData::App(sym, args) = self.exec.ctx.terms.get(cand) {
            if sym.name() == "=" && args.len() == 2 {
                let (l, r) = (args[0], args[1]);
                if l != r {
                    let ls = self.exec.ctx.terms.sort(l).clone();
                    if matches!(ls, Sort::Array(_)) || self.exec.datatype_sort_name(&ls).is_some() {
                        map.entry(l).or_default().push(r);
                        map.entry(r).or_default().push(l);
                    }
                }
            }
        }
        match self.exec.ctx.terms.get(cand) {
            TermData::App(sym, args) if sym.name() == "and" => {
                let args = args.clone();
                for c in args {
                    self.index_walk(c, depth - 1, map);
                }
            }
            // Model-selected branch of a conditional: the asserted branch.
            TermData::App(sym, args)
                if (sym.name() == "ite" || sym.name() == "if") && args.len() == 3 =>
            {
                if let Some(b) = self.eval_bool_cond(args[0]) {
                    let branch = if b { args[1] } else { args[2] };
                    self.index_walk(branch, depth - 1, map);
                }
            }
            TermData::Ite(c, then_b, else_b) => {
                let (c, then_b, else_b) = (*c, *then_b, *else_b);
                if let Some(b) = self.eval_bool_cond(c) {
                    let branch = if b { then_b } else { else_b };
                    self.index_walk(branch, depth - 1, map);
                }
            }
            // Model-entailed disjunct of an asserted `or`. The `or` holds, so if
            // every disjunct BUT ONE is AUTHORITATIVELY false, that one is
            // entailed. "Authoritatively false" = evaluates `Some(false)` AND is
            // array/datatype-FREE, so its falsity is a fact about pinned
            // bool/bv/int leaves that no array/datatype reconstruction can flip.
            //
            // A disjunct that DOES carry an array/datatype subterm is NEVER
            // counted as authoritatively false — its `Some(false)` may be a
            // SPURIOUS artifact of the very reconstruction inconsistency this
            // index repairs (an unaliased field leaf). So it always remains a
            // survivor. The origin-stream field-decomposition axiom
            // `(or <discriminator-bool> (and (= f1 sel1) ...))` is exactly this:
            // the discriminator is an authoritatively-false bool, and the
            // field-equality `and` — spuriously false because its field leaves
            // are reconstructed inconsistently — is the sole survivor, hence
            // entailed, so its conjunct equalities are recorded as defs.
            //
            // SOUND: we descend a disjunct only when ALL OTHER disjuncts are
            // GENUINELY (reconstruction-independently) false, so it is truly
            // entailed; a pure-bool `or` all of whose disjuncts are false yields
            // ZERO survivors (nothing recorded), so we can never manufacture a
            // satisfying alias for a genuinely-violated disjunction — and the gate
            // still re-checks every assertion. (#g3-or-entailed-def)
            TermData::App(sym, args) if sym.name() == "or" && !args.is_empty() => {
                let args = args.clone();
                let mut survivor: Option<TermId> = None;
                let mut unique = true;
                for &d in &args {
                    if self.term_is_array_dt_free(d) && self.eval_bool_cond(d) == Some(false) {
                        continue; // authoritatively false: cannot be the asserted disjunct
                    }
                    if survivor.is_some() {
                        unique = false; // >= 2 possible survivors: undetermined
                        break;
                    }
                    survivor = Some(d);
                }
                if unique {
                    if let Some(d) = survivor {
                        self.index_walk(d, depth - 1, map);
                    }
                }
            }
            _ => {}
        }
    }

    /// Whether `term` contains NO array-sorted or datatype-sorted subterm (so its
    /// value is a fact about pinned bool/bv/int/real leaves that no
    /// array/datatype reconstruction can flip). Short-circuits on the first
    /// array/datatype subterm found. Used by the `or`-entailment rule in
    /// [`Self::index_walk`] to decide which disjuncts are AUTHORITATIVELY false.
    fn term_is_array_dt_free(&self, term: TermId) -> bool {
        let sort = self.exec.ctx.terms.sort(term);
        if matches!(sort, Sort::Array(_)) || self.exec.datatype_sort_name(sort).is_some() {
            return false;
        }
        for child in self.exec.ctx.terms.children(term) {
            if !self.term_is_array_dt_free(child) {
                return false;
            }
        }
        true
    }

    /// Evaluate a Boolean condition under the model with the gate's own evaluator.
    fn eval_bool_cond(&self, c: TermId) -> Option<bool> {
        let ev = Evaluator::new(&self.exec.ctx.terms, self);
        match ev.evaluate(c) {
            EvalOutcome::Value(ModelValue::Bool(b)) => Some(b),
            _ => None,
        }
    }

    fn sort_is_kind(&self, sort: &Sort, kind: DefKind) -> bool {
        match kind {
            DefKind::Array => matches!(sort, Sort::Array(_)),
            DefKind::Datatype => self.exec.datatype_sort_name(sort).is_some(),
        }
    }

    /// Resolve a DATATYPE-sorted leaf `t` through its definitional equality
    /// `(= t <ctor-expr>)` — the analogue of [`array_leaf`](Self::array_leaf).
    ///
    /// The eager DtAufbv route emits a datatype local as a fresh
    /// `Sort::Uninterpreted` leaf whose value is fixed by an asserted equality to
    /// a constructor expression (often an `ite` over `Some`/`None` branches). The
    /// theory model only pins it to an OPAQUE element token (no field structure),
    /// so a tester/selector over the leaf is unevaluable. Resolving the leaf
    /// through its asserted definition — evaluated by the gate's OWN evaluator
    /// under the model — recovers the full [`ModelValue::Datatype`] faithfully:
    /// the equality is UNCONDITIONALLY asserted (top-level or `and`-conjunct;
    /// conditional `ite` branches are descended only for the model-selected
    /// branch), so the value is the one the model commits, and the gate still
    /// re-checks every assertion (a wrong definition ⇒ `ModelViolates`). Cycles
    /// (mutual definitions) fail closed via the shared `resolving` guard.
    /// If leaf `t` is a bare variable whose NAME is a NULLARY constructor of its
    /// datatype `sort`, return that constructor's [`ModelValue::Datatype`]. Sound:
    /// the eager lowering emits a datatype's nullary constructor as a fresh
    /// constant of that name (no separate declaration shadows it), so the term IS
    /// that constructor value — and any model satisfying the assertions agrees.
    fn nullary_constructor_leaf(&self, t: TermId, sort: &Sort) -> Option<ModelValue> {
        let TermData::Var(name, _) = self.exec.ctx.terms.get(t) else {
            return None;
        };
        let dt_name = self.exec.datatype_sort_name(sort)?;
        let (_, ctor_names) = self
            .exec
            .ctx
            .datatype_iter()
            .find(|(dt, _)| *dt == dt_name)?;
        if !ctor_names.iter().any(|c| c == name) {
            return None;
        }
        // It is a constructor NAME of this datatype; require it to be nullary.
        if self.exec.ctx.constructor_selector_info(name)?.is_empty() {
            Some(ModelValue::Datatype {
                ctor: name.clone(),
                args: Vec::new(),
            })
        } else {
            None
        }
    }

    /// Reconstruct a [`ModelValue::Datatype`] for a datatype-sorted term `t` from
    /// the model's COMMITTED constructor (Fix B / Site 5). Used when neither a
    /// definitional equality nor a nullary-constructor name pins the leaf, but the
    /// model still commits it to a constructor (a sole-constructor datatype, or a
    /// multi-constructor one with a unique model-true tester `(is-C t)`).
    ///
    /// FAITHFUL: the constructor is the one [`Executor::dt_constructor_of`] reads
    /// from the model (asserted / model-true tester, or the sole constructor);
    /// each field is resolved through the model — a scalar/BV field from the
    /// selector application's committed value, an array field via `array_leaf`, a
    /// nested datatype via recursion. Fail-closed if the constructor is
    /// undeterminable or ANY field is unresolvable, and the gate re-checks every
    /// assertion, so a wrong reconstruction is caught as `ModelViolates`.
    fn reconstruct_datatype_value(&self, t: TermId, depth: u32) -> Option<ModelValue> {
        if depth > 24 {
            return None;
        }
        if !self.resolving.borrow_mut().insert(t) {
            self.cycle_hits.set(self.cycle_hits.get() + 1);
            return None; // cycle
        }
        let result = self.reconstruct_datatype_value_inner(t, depth);
        self.resolving.borrow_mut().remove(&t);
        // NOTE: no #gate-none-cache here — the result is `depth`-dependent
        // (the recursion cutoff above), so a failure is not a pure function of
        // the term alone.
        result
    }

    fn reconstruct_datatype_value_inner(&self, t: TermId, depth: u32) -> Option<ModelValue> {
        let (ctor, _dt_name) = self.exec.dt_constructor_of(self.model, t)?;
        let fields = self.exec.ctx.constructor_selector_info(&ctor)?.to_vec();
        let mut args = Vec::with_capacity(fields.len());
        for (fname, fsort) in &fields {
            // The selector application `(fname t)`, if present in the term store,
            // carries the field's committed value.
            let sel_app = self.exec.find_dt_selector_app(fname, t);
            let v = match fsort {
                Sort::Array(arr) => {
                    // Resolve the array field through the array leaf machinery.
                    let sa = sel_app?;
                    self.array_leaf(sa, &arr.index_sort, &arr.element_sort)?
                }
                _ if self.exec.datatype_sort_name(fsort).is_some() => {
                    // Nested datatype field: recurse on the selector application.
                    let sa = sel_app?;
                    if let Some(v) = self.datatype_leaf(sa) {
                        v
                    } else {
                        self.reconstruct_datatype_value(sa, depth + 1)?
                    }
                }
                _ => {
                    // Scalar / BV field: the selector application's committed value.
                    let sa = sel_app?;
                    let ev = self.exec.evaluate_term(self.model, sa);
                    eval_value_to_model_value(&ev, fsort)?
                }
            };
            args.push(v);
        }
        Some(ModelValue::Datatype { ctor, args })
    }

    fn datatype_leaf(&self, t: TermId) -> Option<ModelValue> {
        if let Some(cached) = self.resolved.borrow().get(&t) {
            return Some(cached.clone());
        }
        if self.resolved_none.borrow().contains(&t) {
            return None; // cached stack-independent failure (#gate-none-cache)
        }
        if !self.resolving.borrow_mut().insert(t) {
            self.cycle_hits.set(self.cycle_hits.get() + 1);
            return None; // cycle
        }
        let hits_before = self.cycle_hits.get();
        let defs = self.definitions_for(t, DefKind::Datatype);
        let mut result = None;
        for def in defs {
            let ev = Evaluator::new(&self.exec.ctx.terms, self);
            if let EvalOutcome::Value(v @ ModelValue::Datatype { .. }) = ev.evaluate(def) {
                result = Some(v);
                break;
            }
        }
        self.resolving.borrow_mut().remove(&t);
        match &result {
            Some(v) => {
                self.resolved.borrow_mut().insert(t, v.clone());
            }
            // Same frame-purity rule as `array_leaf` (#gate-none-cache).
            None if self.cycle_hits.get() == hits_before => {
                self.resolved_none.borrow_mut().insert(t);
            }
            None => {}
        }
        result
    }

    /// Parse a model-emitted value string for the given sort into a gate value,
    /// reusing the solver's own parser (a pure leaf-value helper).
    fn parse_leaf(&self, s: &str, sort: &Sort) -> Option<ModelValue> {
        let ev = self.exec.parse_model_value_string(s, &Some(sort.clone()));
        eval_value_to_model_value(&ev, sort)
    }
}

/// Conservative structural equality of two gate [`ModelValue`]s, used only to
/// detect a committed-read VALUE conflict when merging an extensionality class.
/// Returns `false` on any shape it does not compare exactly (incl. floats /
/// mismatched shapes), which fails the merge CLOSED — a sound direction (it can
/// only make the gate more conservative, never confirm a wider model).
fn values_equal(a: &ModelValue, b: &ModelValue) -> bool {
    use ModelValue as V;
    match (a, b) {
        (V::Bool(x), V::Bool(y)) => x == y,
        (V::Int(x), V::Int(y)) => x == y,
        (V::Real(x), V::Real(y)) => x == y,
        (
            V::BitVec {
                width: w1,
                value: v1,
            },
            V::BitVec {
                width: w2,
                value: v2,
            },
        ) => w1 == w2 && v1 == v2,
        (V::Str(x), V::Str(y)) => x == y,
        (V::Uninterpreted(x), V::Uninterpreted(y)) => x == y,
        (V::Array(x), V::Array(y)) => {
            values_equal(&x.default, &y.default)
                && x.store.len() == y.store.len()
                && x.store
                    .iter()
                    .zip(y.store.iter())
                    .all(|((ka, va), (kb, vb))| values_equal(ka, kb) && values_equal(va, vb))
        }
        (V::Datatype { ctor: c1, args: a1 }, V::Datatype { ctor: c2, args: a2 }) => {
            c1 == c2
                && a1.len() == a2.len()
                && a1.iter().zip(a2.iter()).all(|(x, y)| values_equal(x, y))
        }
        _ => false,
    }
}

/// Convert a solver [`EvalValue`] (a leaf value) into a gate [`ModelValue`].
///
/// `sort` disambiguates a numeric `Rational` between `Int` and `Real` and gives
/// the element sort for sequences. Anything the gate cannot faithfully
/// represent (floating point, unknown, a non-integer in an Int context) becomes
/// `None`, which makes the leaf unpinned and the gate fail closed.
fn eval_value_to_model_value(ev: &EvalValue, sort: &Sort) -> Option<ModelValue> {
    match ev {
        EvalValue::Bool(b) => Some(ModelValue::Bool(*b)),
        EvalValue::Rational(r) => match sort {
            Sort::Int => {
                if r.is_integer() {
                    Some(ModelValue::Int(r.to_integer()))
                } else {
                    None
                }
            }
            Sort::Real => Some(ModelValue::Real(r.clone())),
            _ => None,
        },
        EvalValue::BitVec { value, width } => Some(ModelValue::bitvec(value.clone(), *width)),
        EvalValue::String(s) => Some(ModelValue::Str(s.clone())),
        EvalValue::Element(e) => Some(ModelValue::Uninterpreted(e.clone())),
        EvalValue::Seq(elems) => {
            let elem_sort = sort.seq_element()?;
            let mut out = Vec::with_capacity(elems.len());
            for e in elems {
                out.push(eval_value_to_model_value(e, elem_sort)?);
            }
            Some(ModelValue::Seq(out))
        }
        // Exact NRA algebraic value (irrational witness): the gate's
        // ModelValue is rational-only, so the leaf is unpinned and the gate
        // fails closed (CannotConfirm) — never a wrong confirmation.
        EvalValue::Algebraic(_) => None,
        // Floating point is intentionally not modelled by the gate; Unknown is
        // an unpinned leaf. Both fail closed.
        EvalValue::Fp(_) | EvalValue::Unknown => None,
    }
}

/// A parsed S-expression: an atom (a whitespace/paren-delimited token, or a
/// `"…"` / `|…|` quoted unit) or a parenthesised list. Used only to re-read a
/// rendered datatype value the model printer emitted, so it is deliberately
/// minimal — it does not model comments, datums beyond the printer's output, or
/// SMT-LIB syntax it never emits.
enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

impl Sexp {
    /// Render back to canonical `(head arg …)` / bare-atom text, so a non-datatype
    /// (scalar/bitvector/string) field can be handed to the solver's leaf parser.
    fn render(&self) -> String {
        match self {
            Sexp::Atom(a) => a.clone(),
            Sexp::List(items) => {
                let parts: Vec<String> = items.iter().map(Sexp::render).collect();
                format!("({})", parts.join(" "))
            }
        }
    }
}

/// Parse ONE S-expression off the front of `cur`, advancing `cur` past it (and
/// past leading whitespace). Returns `None` on malformed input (unbalanced
/// parens, empty). Never panics.
fn parse_sexp(cur: &mut &str) -> Option<Sexp> {
    *cur = cur.trim_start();
    let bytes = cur.as_bytes();
    let first = *bytes.first()?;
    if first == b'(' {
        *cur = &cur[1..];
        let mut items = Vec::new();
        loop {
            *cur = cur.trim_start();
            match cur.as_bytes().first()? {
                b')' => {
                    *cur = &cur[1..];
                    return Some(Sexp::List(items));
                }
                _ => items.push(parse_sexp(cur)?),
            }
        }
    }
    if first == b')' {
        return None;
    }
    Some(Sexp::Atom(parse_atom(cur)))
}

/// Consume one atom off the front of `cur`: a `"…"` string literal (SMT-LIB
/// `""` escape), a `|…|` quoted symbol, or a run of characters up to the next
/// whitespace or paren. Assumes `cur` does not start with `(`, `)`, or
/// whitespace.
fn parse_atom(cur: &mut &str) -> String {
    let bytes = cur.as_bytes();
    if bytes[0] == b'"' {
        // String literal: scan to the closing quote, treating "" as an escaped
        // quote (not a terminator).
        let mut i = 1;
        while i < bytes.len() {
            if bytes[i] == b'"' {
                if bytes.get(i + 1) == Some(&b'"') {
                    i += 2;
                    continue;
                }
                i += 1; // include closing quote
                break;
            }
            i += 1;
        }
        let atom = cur[..i].to_string();
        *cur = &cur[i..];
        return atom;
    }
    if bytes[0] == b'|' {
        // Quoted symbol: scan to the closing '|'.
        let mut i = 1;
        while i < bytes.len() && bytes[i] != b'|' {
            i += 1;
        }
        if i < bytes.len() {
            i += 1; // include closing '|'
        }
        let atom = cur[..i].to_string();
        *cur = &cur[i..];
        return atom;
    }
    let end = cur
        .find(|c: char| c.is_whitespace() || c == '(' || c == ')')
        .unwrap_or(cur.len());
    let atom = cur[..end].to_string();
    *cur = &cur[end..];
    atom
}

/// Pure, contract-carrying decision core of the independent SAT gate — the SMT
/// twin of the SAT-side Verified-SAT-Gate (`decision_sat_self_checked` in
/// `crates/ay/src/cmd_pb.rs`, proven in `decision_sat_vig_realbody.rs`).
///
/// DIRECTIONAL SOUNDNESS: the gate keeps a `Sat` verdict (`true`) EXACTLY when the
/// incoming verdict was `Sat` AND the model was independently `confirmed`, OR
/// enforcement is deliberately not engaged (`!enforce` — statically the case only
/// for the monitored `CannotConfirm` coverage-gap arm; the `ModelViolates`
/// refutation arm passes `enforce = true` unconditionally, see
/// [`Executor::apply_independent_model_gate`]). Consequences, both
/// machine-checkable: it can NEVER manufacture `Sat` from a non-`Sat` verdict
/// (`result ==> was_sat`), and once enforcement is on it NEVER keeps an
/// unconfirmed model (`result && enforce ==> confirmed`). The gate only ever maps
/// `Sat -> {Sat, Unknown}`, never toward unsoundness.
///
/// The `` contract is inert in the stock build
/// (`deductive_verify` is unset, so no `trust` dependency and zero codegen) and is
/// discharged by the stage2 deductive-checks pipeline; the P1 soundness proof and its
/// refuted `no_check` control live in
/// the development proof harness.
fn gate_keeps_sat(was_sat: bool, confirmed: bool, enforce: bool) -> bool {
    was_sat && (confirmed || !enforce)
}

/// Compact human display of an [`EvalValue`] for the soundness-gate alarm's
/// falsifying-assignment line. Best-effort and debug-only — never parsed.
fn eval_value_display(v: &EvalValue) -> String {
    match v {
        EvalValue::Bool(b) => b.to_string(),
        EvalValue::Element(s) => s.clone(),
        EvalValue::Rational(r) => {
            if r.is_integer() {
                r.to_integer().to_string()
            } else {
                r.to_string()
            }
        }
        EvalValue::BitVec { value, width } => format!("(_ bv{value} {width})"),
        EvalValue::Fp(_) => "<fp>".to_string(),
        EvalValue::String(s) => format!("{s:?}"),
        EvalValue::Seq(_) => "<seq>".to_string(),
        EvalValue::Algebraic(_) => "<algebraic>".to_string(),
        EvalValue::Unknown => "?".to_string(),
    }
}

/// Enforcement at the [`GateVerdict::ModelViolates`] call site is
/// UNCONDITIONAL: a concrete ground refutation of the emitted witness always
/// downgrades `Sat` to `Unknown` — there is no env var or runtime opt-out
/// (the pre-2026-07 `AY_MODEL_CHECK_STRICT` monitor-by-default posture was a
/// rollout stopgap and is removed). Pinned by
/// `tests/smt_model_gate_conformance.rs`.
const ENFORCE_ON_REFUTATION: bool = true;

/// Result of the three-valued congruent-read evaluation
/// ([`Executor::congruent_read_eval`]): a concrete value, an opaque
/// uninterpreted read keyed by `(array leaf, concrete index value)`, or
/// indeterminate.
#[derive(Debug, Clone)]
enum CongruentReadEval {
    /// Concrete ground value from the ordinary model evaluator.
    Val(EvalValue),
    /// Unpinned read `(select leaf i)` with concrete index value — equal to
    /// any other read with the identical key in every model completion.
    Read(TermId, EvalValue),
    /// No definite verdict.
    Indet,
}

impl Executor {
    /// Rebuild the `DatatypeSort` for a datatype declared as `Sort::Datatype`
    /// OR abstracted to `Sort::Uninterpreted(name)` (the eager DtAufbv lowering)
    /// from the front-end declaration tables. Shared by the independent gate's
    /// `datatype_def` and the model-independent tautology checks.
    pub(in crate::executor) fn dt_registry_lookup(
        &self,
        name: &str,
    ) -> Option<ay_core::DatatypeSort> {
        let (_, ctor_names) = self.ctx.datatype_iter().find(|(dt, _)| *dt == name)?;
        let constructors = ctor_names
            .iter()
            .map(|cn| {
                let fields = self
                    .ctx
                    .constructor_selector_info(cn)
                    .unwrap_or(&[])
                    .iter()
                    .map(|(fname, fsort)| ay_core::DatatypeField::new(fname.clone(), fsort.clone()))
                    .collect();
                ay_core::DatatypeConstructor::new(cn.clone(), fields)
            })
            .collect();
        Some(ay_core::DatatypeSort::new(name, constructors))
    }

    /// Parse a RENDERED datatype value string — as produced by the model
    /// printer's single-source [`Executor::dt_egraph_value`] (e.g. `(cons (node
    /// null) null)`, `(succ (succ zero))`, or a bare nullary `zero`) — into the
    /// independent gate's [`ModelValue`], so the gate re-evaluates EXACTLY the
    /// constructor tree that will be printed and handed to the external
    /// validator (#mv-gate-reads-printed-dt).
    ///
    /// FAIL-CLOSED: any token that does not resolve to a declared constructor of
    /// the expected datatype sort (or a scalar field the solver's own leaf
    /// parser cannot read) yields `None`, which leaves the leaf UNPINNED so the
    /// gate fails closed (a coverage gap, never a wrong confirmation). The input
    /// is emitted by ay's OWN renderer, so it is well-formed; the parser is
    /// deliberately total and never panics.
    pub(in crate::executor) fn parse_rendered_dt_value(
        &self,
        s: &str,
        sort: &Sort,
    ) -> Option<ModelValue> {
        let mut cur = s;
        let sx = parse_sexp(&mut cur)?;
        // Reject trailing garbage after one complete value.
        if !cur.trim_start().is_empty() {
            return None;
        }
        self.sexp_to_model_value(&sx, sort)
    }

    /// Interpret a parsed S-expression as a [`ModelValue`] of the given sort:
    /// datatype sorts recurse structurally over the constructor's declared field
    /// sorts; every other (scalar / bitvector / string / …) field is rendered
    /// back to text and read by the solver's own leaf parser.
    fn sexp_to_model_value(&self, sx: &Sexp, sort: &Sort) -> Option<ModelValue> {
        if self.datatype_sort_name(sort).is_some() {
            return self.sexp_to_dt_value(sx, sort);
        }
        let text = sx.render();
        let ev = self.parse_model_value_string(&text, &Some(sort.clone()));
        eval_value_to_model_value(&ev, sort)
    }

    /// Interpret a parsed S-expression as a datatype [`ModelValue`] of `sort`.
    /// The head token must name a declared constructor of the sort's datatype
    /// (matched by SURFACE name so the printer's rendering round-trips), and the
    /// argument count must equal that constructor's field count; each argument
    /// recurses on the field's declared sort. The stored `ctor` is the INTERNAL
    /// constructor name, which is the name the gate evaluator's registry
    /// (`dt_registry_lookup`) and its tester/selector matching use.
    fn sexp_to_dt_value(&self, sx: &Sexp, sort: &Sort) -> Option<ModelValue> {
        let dt_name = self.datatype_sort_name(sort)?;
        let (head, arg_sexps): (&str, &[Sexp]) = match sx {
            Sexp::Atom(a) => (a.as_str(), &[]),
            Sexp::List(items) => {
                let Some(Sexp::Atom(h)) = items.first() else {
                    return None;
                };
                (h.as_str(), &items[1..])
            }
        };
        let (_dt, ctor_names) = self.ctx.datatype_iter().find(|(dt, _)| *dt == dt_name)?;
        let internal = ctor_names
            .iter()
            .find(|c| self.dt_surface(c) == head || c.as_str() == head)?
            .clone();
        let fields = self.ctx.constructor_selector_info(&internal)?.to_vec();
        if fields.len() != arg_sexps.len() {
            return None;
        }
        let mut args = Vec::with_capacity(fields.len());
        for ((_fname, fsort), asx) in fields.iter().zip(arg_sexps.iter()) {
            args.push(self.sexp_to_model_value(asx, fsort)?);
        }
        Some(ModelValue::Datatype {
            ctor: internal,
            args,
        })
    }

    /// Whether `term` is a MODEL-INDEPENDENT datatype/Boolean tautology (true in
    /// every model) per ay-model-check's normalizer, resolving datatypes via the
    /// ctx registry. A `true` result is a proof the assertion holds in every
    /// model, so a theory-model reconstruction that happens to evaluate it false
    /// (a ROW2 / read-over-equality congruence gap the independent gate proves
    /// away) is NOT a genuine refutation — used to avoid spuriously degrading a
    /// SAT on such an assertion. Model-independent, so it can never confirm a
    /// non-tautology as true. (#g4-dt-taut)
    pub(in crate::executor) fn term_is_datatype_tautology(&self, term: TermId) -> bool {
        ay_model_check::is_datatype_tautology_with(&self.ctx.terms, term, &|name| {
            self.dt_registry_lookup(name)
        })
    }
    /// Run the independent gate over the current `Sat` model and assertions.
    pub(in crate::executor) fn confirm_sat_with_independent_gate(&self) -> GateVerdict {
        let Some(model) = self.last_model.as_ref() else {
            return GateVerdict::CannotConfirm {
                reason: "no model was produced".to_string(),
            };
        };
        let view = IndependentModelView::new(self, model);
        // Build the definitional-equality index NOW, while the resolution stack
        // (`resolving`/`resolved`) is empty, so branch/disjunct selection is
        // deterministic and not perturbed by an in-flight leaf resolution.
        view.ensure_def_index();
        if std::env::var_os("AY_G3_GATE_DUMP").is_some() {
            self.dump_gate_diagnostics(&view);
        }
        // A DT certificate validates the whole snapshot against its completed
        // model M', while the retained emission candidate M intentionally did
        // not witness the universals.  Independently check every ground
        // assertion in M, but leave the already-certified universals to the
        // quantified gate's deterministic certificate deferral below.  Without
        // an active grant, the full assertion set is checked exactly as before.
        let ground_assertions: Vec<TermId> = if self.dt_cert_grant_active {
            self.ctx
                .assertions
                .iter()
                .copied()
                .filter(|&assertion| !contains_quantifier(&self.ctx.terms, assertion))
                .collect()
        } else {
            Vec::new()
        };
        let assertions = if self.dt_cert_grant_active {
            ground_assertions.as_slice()
        } else {
            self.ctx.assertions.as_slice()
        };
        ay_model_check::confirm_model(&self.ctx.terms, &view, assertions)
    }

    /// Emission-side entailed reconstruction, shared with the model PRINTER.
    ///
    /// For every user-declared datatype- or array-sorted constant, resolve it to
    /// the SAME entailed [`ModelValue`] the independent gate used to CONFIRM this
    /// model — through the identical [`IndependentModelView`] + `def_index`
    /// machinery (`leaf_value`, which folds in the datatype-leaf definitional
    /// resolution, Fix-B constructor reconstruction, and array store-chain /
    /// extensionality resolution) — and format it as a round-trippable SMT-LIB
    /// term via [`Executor::format_gate_model_value`].
    ///
    /// The printer's own per-leaf datatype/array materialization resolves each
    /// leaf INDEPENDENTLY (its own tester/selector scan and branch selection),
    /// which on a datatype-carrying-array VC can (a) leave a field leaf
    /// `Unknown` — emitted as the explicit unavailable marker — and (b) pick
    /// per-leaf values that are individually plausible but MUTUALLY incoherent
    /// (a `(= x <ctor-expr>)` whose fields disagree with another leaf's), so the
    /// emitted model fails to re-check. This reconstruction is the model the gate
    /// actually confirmed, so the values it yields are jointly consistent with
    /// the assertions.
    ///
    /// FAIL-CLOSED: only inserts a value the reconstruction fully resolves to a
    /// concrete, marker-free SMT-LIB term. A leaf the gate leaves opaque (a free
    /// datatype leaf with no committed constructor, an unrepresentable skolem) is
    /// OMITTED, so the caller keeps its existing behavior — never a fabricated
    /// default (#no-fabricated-model-values). A single [`IndependentModelView`]
    /// is built and its `def_index` computed ONCE for the whole map.
    pub(in crate::executor) fn gate_emit_reconstructions(
        &self,
        model: &Model,
    ) -> HashMap<TermId, String> {
        let mut out = HashMap::new();
        // Nothing to reconstruct unless a datatype- or array-sorted constant is
        // declared — skip building the view/def_index entirely on pure
        // scalar (BV/LIA/…) models, whose `(get-model)` is unaffected.
        let has_dt_or_array = self.ctx.symbol_iter().any(|(name, info)| {
            info.arg_sorts.is_empty()
                && info.term.is_some()
                && !self.is_dt_internal_symbol(name)
                && (self.datatype_sort_name(&info.sort).is_some()
                    || matches!(info.sort, Sort::Array(_)))
        });
        if !has_dt_or_array {
            return out;
        }
        let view = IndependentModelView::new(self, model);
        view.ensure_def_index();
        for (name, info) in self.ctx.symbol_iter() {
            if !info.arg_sorts.is_empty() {
                continue;
            }
            if self.is_dt_internal_symbol(name) {
                continue;
            }
            let Some(term_id) = info.term else {
                continue;
            };
            let is_dt = self.datatype_sort_name(&info.sort).is_some();
            let is_array = matches!(info.sort, Sort::Array(_));
            if !is_dt && !is_array {
                continue;
            }
            // Use the FULL gate Evaluator, not a bare `leaf_value`: a declared
            // symbol's term is not always a `Var` (preprocessing can rewrite it to
            // an alias / constructor application), and only the compositional
            // Evaluator follows that structure to a concrete value — a raw
            // `leaf_value` would treat the rewritten term as an opaque leaf and
            // return a representative token. The Evaluator drives every leaf
            // through this same view's `leaf_value`, so the entailed def_index
            // resolution and datatype/array reconstruction still apply.
            if let EvalOutcome::Value(mv) =
                ay_model_check::evaluate_term(&self.ctx.terms, &view, term_id)
            {
                if let Some(s) = self.format_gate_model_value(&mv, &info.sort) {
                    if !s.contains("value-unavailable") {
                        out.insert(term_id, s);
                    }
                }
            }
        }
        out
    }

    /// DEBUG-ONLY (AY_G3_GATE_DUMP): print each assertion's gate outcome AFTER
    /// the datatype-tautology normalizer, plus reconstructed leaf values for the
    /// operands of each false/uneval field-decomposition assertion.
    fn dump_gate_diagnostics(&self, view: &IndependentModelView<'_>) {
        let mut n_false = 0usize;
        let mut n_uneval = 0usize;
        for &assertion in &self.ctx.assertions {
            let out = ay_model_check::evaluate_term(&self.ctx.terms, view, assertion);
            let taut = self.term_is_datatype_tautology(assertion);
            let label = match &out {
                EvalOutcome::Value(ModelValue::Bool(true)) => continue,
                EvalOutcome::Value(ModelValue::Bool(false)) => {
                    if taut {
                        continue;
                    }
                    n_false += 1;
                    "FALSE-non-taut"
                }
                EvalOutcome::Value(_) => "NONBOOL",
                EvalOutcome::Unevaluable(_) => {
                    if taut {
                        continue;
                    }
                    n_uneval += 1;
                    "UNEVAL-non-taut"
                }
            };
            eprintln!(
                "AY_G3_GATE_DUMP [{label}] assertion={} reason={:?} :: {}",
                assertion.index(),
                out,
                self.format_term(assertion)
            );
            // Dump reconstructed leaf values for every var mentioned.
            let mut leaves = Vec::new();
            self.collect_leaf_vars(assertion, &mut leaves);
            leaves.sort_by_key(|t| t.index());
            leaves.dedup();
            for leaf in leaves {
                let v = ay_model_check::evaluate_term(&self.ctx.terms, view, leaf);
                eprintln!(
                    "    leaf {} = {} => {:?}",
                    leaf.index(),
                    self.format_term(leaf),
                    v
                );
            }
        }
        eprintln!("AY_G3_GATE_DUMP SUMMARY: n_false={n_false} n_uneval={n_uneval}");
    }

    /// Collect the free variable/leaf term ids referenced by `term` (DEBUG).
    fn collect_leaf_vars(&self, term: TermId, out: &mut Vec<TermId>) {
        match self.ctx.terms.get(term) {
            TermData::Var(_, _) | TermData::Const(_) => out.push(term),
            _ => {
                for child in self.ctx.terms.children(term) {
                    self.collect_leaf_vars(child, out);
                }
            }
        }
    }

    /// Apply the independent, fail-closed model-check gate to a `check-sat`
    /// result. Only `Sat` is gated; every other verdict is returned untouched.
    ///
    /// ENFORCEMENT IS UNCONDITIONAL for a refutation, monitoring for a coverage
    /// gap — no environment variable changes either posture:
    ///
    /// * [`GateVerdict::ModelViolates`] — the emitted model ground-falsifies an
    ///   assertion: a concrete, independently-derived refutation of the witness.
    ///   Downgrading `Sat` to `Unknown` on a concrete refutation is ALWAYS sound
    ///   (`unknown` is never a wrong answer), so the downgrade is enforced
    ///   unconditionally. This is the permanent guarantee that no wrong-model
    ///   class — present or future — ships as `sat`.
    /// * [`GateVerdict::CannotConfirm`] — the gate could not ground-evaluate
    ///   some fragment. That is evaluator INCOMPLETENESS, not a refutation;
    ///   enforcing it would permanently degrade fragments that can never be
    ///   ground-model-checked (FP, quantifiers, infinite-domain UF) for zero
    ///   soundness gain, so this arm records the gap and keeps the verdict.
    ///
    /// The gate never alters a verdict toward unsoundness — at most
    /// `Sat` → `Unknown`.
    pub(in crate::executor) fn apply_independent_model_gate(
        &mut self,
        result: SolveResult,
    ) -> SolveResult {
        if result != SolveResult::Sat {
            return result;
        }
        // The only way to disable the gate is the programmatic
        // `set_independent_model_gate(false)` API (debugging/tests); the former
        // `AY_NO_MODEL_CHECK_GATE` env-var bypass is removed — no environment
        // variable may turn off a soundness gate.
        if !self.independent_model_gate_enabled() {
            return result;
        }
        // Nothing to independently re-check without a model (trivially-SAT /
        // empty-assertion paths are already validated upstream): leave the
        // verdict untouched rather than manufacture an Unknown.
        if self.last_model.is_none() {
            return result;
        }

        match self.confirm_sat_with_independent_gate() {
            GateVerdict::ConfirmedSat => {
                self.last_statistics
                    .set_string("model_check_gate.result", "confirmed-sat");
                result
            }
            GateVerdict::ModelViolates { assertion } => {
                let term = self.format_term(assertion);
                // LOUD, always-visible alarm + falsifying assignment (stderr +
                // structured trace): a theory-search path produced an invalid
                // model. Emitted while `last_model` is still live (the downgrade
                // below clears it).
                if std::env::var_os("AY_MODEL_REJECT_DUMP").is_some() {
                    eprintln!("[reject-site] apply_independent_model_gate");
                }
                self.report_caught_invalid_model(assertion, &term);
                // DIAGNOSTIC ONLY (`AY_MODEL_REJECT_DUMP=1`; default off is
                // byte-identical). The gate names the TOP-LEVEL assertion, which
                // on a single-`assert` benchmark is the whole conjunction — an
                // unusable census signal. Re-run the SAME evaluator over the
                // FLATTENED conjuncts to name the one that actually computed
                // false. WRITE-ONLY: no verdict path reads it, and the
                // enforcement below is untouched.
                if std::env::var_os("AY_MODEL_REJECT_DUMP").is_some() {
                    self.dump_violated_flat_conjuncts(assertion);
                }
                self.last_statistics
                    .set_string("model_check_gate.result", "model-violates");
                self.last_statistics
                    .set_string("model_check_gate.violated_assertion", term);
                // #qfax-cegar: this rejection is the same evidence class the
                // strict-oracle hook feeds on — derive the sound
                // pattern-blocking clause here too, so the dispatch's
                // stage-4 refinement fires on gate-caught violations
                // (previously only strict-oracle rejections derived).
                self.derive_qfax_refinement_clause(assertion);
                self.last_rejected_array_assertion = Some(assertion);
                // #uflia-cong-repair-arm: a UFLIA-lane refutation is the exact
                // trigger for the reactive congruence-repair re-solve. Record
                // it (scoped to the UFLIA lane so no other theory's refutation
                // arms a wasteful retry); `check_sat_guarded` reads this to arm
                // `discover_congruence_repair_eqs` and re-solve ONCE. This only
                // redirects search on a re-solve the gate is about to reject
                // anyway — the downgrade below is unaffected.
                if self.uflia_congruence_lane {
                    self.uflia_congruence_gate_rejected = true;
                }
                // #abv-subst-model-retry: a refutation of a model built by the
                // substitution-carrying eager BV lane arms the single
                // preprocessing-free re-solve (`check_sat_guarded`), the same
                // reactive pattern as the UFLIA arm above. Scoped to
                // `bv_subst_lane` so no other theory's refutation triggers a
                // wasteful retry; the unconditional downgrade below is
                // unaffected.
                if self.bv_subst_lane {
                    self.bv_subst_model_rejected = true;
                }
                // ENFORCED, UNCONDITIONALLY. A `ModelViolates` means the gate's
                // own evaluator ground-falsified an assertion under the EMITTED
                // `last_model` — a concrete refutation of the witness. Shipping
                // a refuted witness as `sat` is exactly the wrong-model bug
                // class this gate exists to stop, and the 2026-07-02 SMT-COMP
                // QF_AX sweep showed it happening in the wild: the storeinv
                // `_np_` false-SATs (`:status unsat` answered `sat`) are
                // precisely runs where this gate fired `model-violates` and was
                // ignored under the former monitor-by-default stance. Degrading
                // to Unknown can never flip a verdict toward unsoundness. There
                // is deliberately NO env-var opt-out (the transient
                // `AY_MODEL_CHECK_MONITOR`/`AY_MODEL_CHECK_STRICT` switches are
                // removed). Route the keep/downgrade decision through the
                // contract-carrying gate core (a `ModelViolates` is
                // unconfirmed: confirmed = false; enforcement is statically
                // on): the machine-checked P1 contract
                // (`result && enforce ==> confirmed`, discharged in
                // proofs/deductive_checks/smt_model_gate_realbody.rs) guarantees the
                // core can never keep an unconfirmed model here.
                if gate_keeps_sat(true, /* confirmed = */ false, ENFORCE_ON_REFUTATION) {
                    result
                } else {
                    self.downgrade_sat_after_gate(
                        "model-not-independently-confirmed: an assertion is falsified by the model",
                    );
                    SolveResult::Unknown
                }
            }
            GateVerdict::CannotConfirm { reason } => {
                self.last_statistics
                    .set_string("model_check_gate.result", "cannot-confirm");
                self.last_statistics
                    .set_string("model_check_gate.cannot_confirm_reason", reason.clone());
                // MONITORED, deliberately — and this is a DIFFERENT KIND of
                // verdict from `ModelViolates`, not a weaker copy of it. A
                // `CannotConfirm` is a COVERAGE gap: the gate's evaluator could
                // not ground-evaluate some fragment (FP, quantifiers,
                // uninterpreted functions, UF-elaborated datatypes). Nothing
                // was refuted; the solver's own (stricter, theory-aware)
                // validation already passed. Some of these fragments can NEVER
                // be ground-model-checked (FP, quantifiers, infinite-domain
                // UF), so enforcing a downgrade here would be a permanent
                // completeness loss for zero soundness gain — evaluator
                // incompleteness must not masquerade as a refutation. The
                // gate's soundness value is the unconditionally-enforced
                // `ModelViolates` path above, which is unaffected: record the
                // gap and keep the verdict.
                tracing::debug!(
                    reason = %reason,
                    "independent model-check gate could not confirm SAT \
                     (evaluator coverage gap, not a refutation); keeping verdict"
                );
                result
            }
        }
    }

    /// DIAGNOSTIC ONLY (`AY_MODEL_REJECT_DUMP=1`): name the FLATTENED
    /// conjuncts of a gate-refuted assertion that the gate's own evaluator
    /// computes `false`. Pure re-evaluation through the same
    /// [`IndependentModelView`]; nothing is mutated and no verdict path reads
    /// the output.
    fn dump_violated_flat_conjuncts(&self, assertion: TermId) {
        let Some(model) = self.last_model.as_ref() else {
            return;
        };
        let view = IndependentModelView::new(self, model);
        view.ensure_def_index();
        let mut flat: Vec<TermId> = Vec::new();
        let mut stack = vec![assertion];
        while let Some(t) = stack.pop() {
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) if sym.name() == "and" => {
                    stack.extend(args.iter().rev().copied());
                }
                _ => flat.push(t),
            }
            if flat.len() > 100_000 {
                break;
            }
        }
        // ONE shared evaluator over the whole flattened window: the gate's
        // UF/select single-valuedness is a CROSS-conjunct property (it keys
        // applications by evaluated argument values over the entire run), so
        // re-checking conjuncts one at a time would lose exactly the
        // inconsistency that refuted the model. Peel off each violated
        // conjunct and re-run to enumerate a few.
        let mut window: Vec<TermId> = flat;
        for _ in 0..8 {
            match ay_model_check::confirm_model(&self.ctx.terms, &view, &window) {
                GateVerdict::ModelViolates { assertion: bad } => {
                    let text = self.format_term(bad);
                    let text: String = text.chars().take(300).collect();
                    eprintln!("[gate-false-conjunct] {text}");
                    window.retain(|&t| t != bad);
                }
                _ => break,
            }
        }
    }

    /// Common bookkeeping for downgrading a gate-rejected `Sat` to `Unknown`.
    fn downgrade_sat_after_gate(&mut self, detail: &str) {
        self.last_model = None;
        self.last_unknown_reason = Some(UnknownReason::Incomplete);
        self.last_statistics
            .set_string("unknown.reason", UnknownReason::Incomplete.to_string());
        self.last_statistics
            .set_string("unknown.phase", "independent-model-check-gate");
        self.last_statistics.set_string("unknown.detail", detail);
    }

    /// LOUD, always-visible soundness alarm: a gate caught a model that
    /// FALSIFIES an assertion (a [`GateVerdict::ModelViolates`]). That means an
    /// (untrusted) theory-search path produced an INVALID model — a genuine
    /// internal bug — even though AY then fail-closes `Sat -> Unknown` (SOUND).
    ///
    /// Printed to STDERR (never stdout, so the `sat`/`unsat`/`unknown` verdict
    /// line stays machine-parseable) with the falsifying assignment, so the
    /// offending theory can be debugged, AND as a structured `tracing::warn!`.
    /// Suppress the stderr banner with `AY_QUIET_SOUNDNESS_GATE=1` for
    /// noise-sensitive batch/fuzz runs (the trace record still fires). MUST be
    /// called BEFORE [`downgrade_sat_after_gate`](Self::downgrade_sat_after_gate),
    /// which clears `last_model`.
    pub(in crate::executor) fn report_caught_invalid_model(
        &self,
        assertion: TermId,
        assertion_str: &str,
    ) {
        let assignment = self.format_falsifying_assignment(assertion);
        let logic = self.logic().unwrap_or("(unset)");
        tracing::warn!(
            logic = %logic,
            assertion = %assertion_str,
            assignment = %assignment,
            "SOUNDNESS GATE caught an invalid model: a theory-search path produced \
             a model that falsifies an assertion; fail-closing Sat -> Unknown"
        );
        if std::env::var_os("AY_QUIET_SOUNDNESS_GATE").is_some() {
            return;
        }
        eprintln!(
            "\n[AY SOUNDNESS GATE] caught an INVALID model — a theory-search path \
             returned a model that falsifies an assertion.\n    \
             AY fail-closed to `unknown` (this is SOUND); it indicates an internal \
             solver bug worth reporting.\n    \
             logic:     {logic}\n    \
             assertion: {assertion_str}\n    \
             falsified under model: {assignment}\n    \
             (set AY_QUIET_SOUNDNESS_GATE=1 to silence this banner)\n"
        );
    }

    /// Format the model's assignment to the scalar leaves of `assertion` — the
    /// concrete values under which the gate found the assertion `false`. Bounded
    /// in recursion depth and leaf count so a pathological formula cannot produce
    /// unbounded output.
    fn format_falsifying_assignment(&self, assertion: TermId) -> String {
        let Some(model) = self.last_model.as_ref() else {
            return "(model unavailable)".to_string();
        };
        let mut leaves = Vec::new();
        let mut seen = HashSet::new();
        self.collect_scalar_leaves(assertion, &mut leaves, &mut seen, 0);
        if leaves.is_empty() {
            return "(no scalar leaves)".to_string();
        }
        let mut parts: Vec<String> = leaves
            .iter()
            .take(16)
            .map(|&leaf| {
                format!(
                    "{} = {}",
                    self.format_term(leaf),
                    eval_value_display(&self.evaluate_term(model, leaf))
                )
            })
            .collect();
        if leaves.len() > 16 {
            parts.push(format!("… (+{} more)", leaves.len() - 16));
        }
        parts.join(", ")
    }

    /// Collect the declared-variable / nullary-application leaves reachable from
    /// `term` (bounded) — the model-assigned scalars whose values drive the
    /// violated assertion's truth value.
    fn collect_scalar_leaves(
        &self,
        term: TermId,
        out: &mut Vec<TermId>,
        seen: &mut HashSet<TermId>,
        depth: u32,
    ) {
        if depth > 48 || out.len() >= 32 || !seen.insert(term) {
            return;
        }
        match self.ctx.terms.get(term) {
            TermData::Var(_, _) => out.push(term),
            TermData::App(_, args) => {
                if args.is_empty() {
                    out.push(term);
                } else {
                    for &a in args {
                        self.collect_scalar_leaves(a, out, seen, depth + 1);
                    }
                }
            }
            TermData::Ite(cond, then_t, else_t) => {
                self.collect_scalar_leaves(*cond, out, seen, depth + 1);
                self.collect_scalar_leaves(*then_t, out, seen, depth + 1);
                self.collect_scalar_leaves(*else_t, out, seen, depth + 1);
            }
            TermData::Not(inner) => self.collect_scalar_leaves(*inner, out, seen, depth + 1),
            _ => {}
        }
    }

    /// AUTHORITATIVE-GROUND FAIL-CLOSED gate (soundness kernel, #sat-chokepoint).
    ///
    /// Inverts the independent gate's [`GateVerdict::CannotConfirm`] fail-OPEN
    /// default to fail-CLOSED for theories whose GROUND evaluation is
    /// authoritative. [`apply_independent_model_gate`](Self::apply_independent_model_gate)
    /// KEEPS a `Sat` on `CannotConfirm` because, for genuinely-incomplete
    /// fragments (FP, quantifiers, infinite-domain UF, incomplete strings), an
    /// unevaluable assertion is evaluator INCOMPLETENESS, not a refutation. But
    /// over a model that pins EVERY scalar leaf an assertion reads, in an
    /// authoritative theory (arrays/LIA/LRA/BV/UF), a well-formed ground
    /// evaluator MUST reduce that assertion to a boolean; a `CannotConfirm` there
    /// means the independent evaluator UNDER-COMPUTED — the model was never
    /// actually confirmed. Keeping the `Sat` is the exact fail-open that shipped
    /// the QF_AX free-base-read / QF_SLIA wrong-SATs.
    ///
    /// This gate re-asks per-assertion: if any assertion the independent
    /// evaluator left unevaluated is authoritatively GROUND
    /// ([`assertion_is_authoritatively_ground`](Self::assertion_is_authoritatively_ground)),
    /// the `Sat` fails CLOSED — downgraded to `Unknown` through the same
    /// contract-carrying [`gate_keeps_sat`] core as the `ModelViolates` arm.
    /// Non-authoritative coverage gaps KEEP the verdict (completeness preserved).
    /// Runs LAST in the [`emit_sat_verdict`](crate::executor::model::sat_emit)
    /// funnel, after the strict and independent gates.
    pub(in crate::executor) fn apply_authoritative_failclosed_gate(
        &mut self,
        result: SolveResult,
    ) -> SolveResult {
        if result != SolveResult::Sat {
            return result;
        }
        if !self.independent_model_gate_enabled() {
            return result;
        }
        // Only the fail-open `CannotConfirm` arm needs this second look: a
        // `ConfirmedSat` needs no further scrutiny and a `ModelViolates` already
        // downgraded upstream. The independent gate records which arm fired.
        if self.last_statistics.get_string("model_check_gate.result") != Some("cannot-confirm") {
            return result;
        }
        let Some(offending) = self.authoritative_ground_unevaluated_assertion() else {
            return result;
        };
        let term = self.format_term(offending);
        tracing::warn!(
            assertion = %term,
            "authoritative-failclosed gate: an authoritatively-ground assertion was left \
             UNEVALUATED by the independent gate — the ground evaluator under-computed a \
             refutation; downgrading SAT to Unknown"
        );
        self.last_statistics
            .set_string("model_check_gate.authoritative_failclosed", "downgraded");
        self.last_statistics
            .set_string("model_check_gate.authoritative_ground_assertion", term);
        // Route the keep/downgrade through the SAME contract-carrying decision
        // core as the `ModelViolates` arm: an authoritatively-ground assertion
        // the evaluator could not confirm is treated as unconfirmed
        // (confirmed = false) with enforcement statically on.
        if gate_keeps_sat(true, /* confirmed = */ false, ENFORCE_ON_REFUTATION) {
            result
        } else {
            self.downgrade_sat_after_gate(
                "authoritative-ground assertion left unevaluated by the independent gate: \
                 ground evaluation is authoritative for this theory, so a coverage gap over a \
                 fully-pinned model is an under-computed refutation",
            );
            SolveResult::Unknown
        }
    }

    /// Find an assertion the INDEPENDENT evaluator left unevaluated (the
    /// `CannotConfirm` coverage-gap signature) that is nonetheless
    /// authoritatively GROUND — the under-computed-refutation signal the
    /// [`apply_authoritative_failclosed_gate`](Self::apply_authoritative_failclosed_gate)
    /// fails closed on. Returns the offending assertion, or `None` when every
    /// coverage gap is a genuine incompleteness (kept as `Sat`).
    fn authoritative_ground_unevaluated_assertion(&self) -> Option<TermId> {
        if !self.logic_is_authoritative_when_ground() {
            return None;
        }
        let model = self.last_model.as_ref()?;
        let view = IndependentModelView::new(self, model);
        // Build the definitional-equality index up front (empty resolution stack),
        // exactly as `confirm_sat_with_independent_gate` does.
        view.ensure_def_index();
        for &assertion in &self.ctx.assertions {
            // Quantified assertions are never authoritatively ground.
            if contains_quantifier(&self.ctx.terms, assertion) {
                continue;
            }
            match ay_model_check::evaluate_term(&self.ctx.terms, &view, assertion) {
                // Confirmed true — not a coverage gap.
                EvalOutcome::Value(ModelValue::Bool(true)) => continue,
                // A ground `false` is a `ModelViolates` the independent gate
                // already accounts for; do not double-handle it here.
                EvalOutcome::Value(ModelValue::Bool(false)) => continue,
                // Non-boolean top value or genuinely unevaluable: the
                // coverage-gap signature the fail-open arm keeps as `Sat`.
                EvalOutcome::Value(_) | EvalOutcome::Unevaluable(_) => {}
            }
            // A model-independent datatype/Boolean tautology holds in EVERY
            // model, so an unevaluated tautology is NOT a refutation — mirror the
            // `confirm_model` guard (#g4-dt-taut-uneval).
            if self.term_is_datatype_tautology(assertion) {
                continue;
            }
            // SOUNDNESS (#storeinv10 wrong-sat): a POSITIVELY-asserted array
            // equality between two `store` chains — `(= (store …) (store …))` —
            // that the INDEPENDENT ground evaluator could not confirm true (we
            // are in the coverage-gap arm; the independent eval above returned
            // non-`true`) IS an under-computed extensionality refutation WHEN the
            // problem also asserts an ARRAY disequality. The storeinv `_np_nf_`
            // family asserts a nested store-swap identity `(= bigstore1 bigstore2)`
            // that secretly forces the base arrays equal (`a1 = a2`),
            // contradicting an asserted `(not (= a1 a2))`; the incomplete
            // ROW/extensionality instantiation never derives that, so the split
            // loop hands back a model in which the solver only "believes"
            // `bigstore1 = bigstore2` via an EUF class merge while the independent
            // evaluator cannot pin the base reads to confirm it. This case must
            // fail closed BEFORE the `self.evaluate_term` carve-out below: that
            // carve-out trusts the solver's OWN (EUF-class) evaluator, which is
            // exactly the unsound signal here (it returns `Bool(true)` for the
            // merged class).
            //
            // The array-disequality co-condition is what keeps genuine SATs of
            // the SAME store-chain-equality shape: `(= (store (store a i v) j x)
            // (store (store a i w) j x)) ∧ (not (= v w))` is sat via `j = i`
            // (element diseq only, no array diseq — not matched); a bare
            // `(= a b)` over free arrays has no `store` operand; an
            // extensionality class with a satisfiable ground read pin is
            // `ConfirmedSat` upstream and never reaches this fail-open arm. The
            // downgrade is to Unknown — always sound, and the sibling storeinv
            // sizes already answer Unknown, bounding the completeness cost.
            if self.is_positive_store_chain_array_equality(assertion)
                && self.assertions_contain_array_disequality()
            {
                return Some(assertion);
            }
            // SOUNDNESS (read-congruence, QF_ALIA seed-1212 wrong-model): an
            // assertion falsified under EVERY completion of the model's
            // unpinned array leaves is a genuine refutation of the emitted
            // witness, no matter which value those leaves later take. The
            // three-valued congruent-read evaluator treats an unpinned
            // `(select a i)` (free array leaf `a`, concrete index value) as an
            // opaque-but-congruent read: two reads with the SAME (leaf, index
            // value) key are EQUAL in every completion. This catches
            // `(distinct c (select a z) (select a x))` under a model with
            // `z = x`, which the plain ground walk fails open on (the select
            // result is not pinned, so the assertion looks non-ground). It
            // must run BEFORE the own-evaluator carve-out below: a for-all-
            // completions `false` outranks any single evaluator's `true`.
            if matches!(
                self.congruent_read_eval(model, assertion, 0),
                CongruentReadEval::Val(EvalValue::Bool(false))
            ) {
                return Some(assertion);
            }
            // COMPLETENESS CARVE-OUT: if the solver's OWN theory evaluator
            // resolves this assertion to `Bool(true)` under the model, the model
            // genuinely satisfies it and the independent evaluator's coverage gap
            // is REAL incompleteness (e.g. a read over a FREE array it cannot
            // materialize, `(= (select a i) v)`), NOT under-computation — keep the
            // `Sat`. The authoritative gate fires only when NEITHER evaluator can
            // confirm the assertion true over a fully-pinned model (the
            // under-computed-refutation signature); a concrete `Bool(false)` the
            // strict gate missed still fails closed here.
            if matches!(self.evaluate_term(model, assertion), EvalValue::Bool(true)) {
                continue;
            }
            if self.assertion_is_authoritatively_ground(model, assertion) {
                return Some(assertion);
            }
        }
        None
    }

    /// NON-STRING-SEQUENCE FAIL-CLOSED gate (soundness kernel, #nonstring-seq-failclose).
    ///
    /// AY's symbolic non-string sequence theory ((Seq Int), (Seq Bool),
    /// (Seq (_ BitVec n)), (Seq Real), …) is systemically UNSOUND on the `Sat`
    /// side: many `seq.*` operations (extract/at/nth/contains/prefixof/suffixof/
    /// indexof/replace and their cross-theory element views) can return `sat` for
    /// an UNSATISFIABLE formula, and the emitted "model" either cannot be produced
    /// (`get-value` errors) or FALSIFIES the very assertions it claims to satisfy.
    /// The independent gate leaves these as a `CannotConfirm` coverage gap
    /// (sequence ground evaluation is deliberately incomplete — see
    /// [`authoritative_sort_class`](Self::authoritative_sort_class)), and the
    /// fail-OPEN `CannotConfirm` arm then KEEPS the wrong `sat`.
    ///
    /// This gate closes that hole SYSTEMICALLY rather than per-axiom: over a `Sat`
    /// the independent gate could not confirm, if ANY asserted constraint
    /// references a non-string sequence term whose truth the independent evaluator
    /// cannot pin to `true` under the emitted model — the exact wrong-`sat`
    /// signature — the `Sat` fails CLOSED to `Unknown`. `unknown` is never a wrong
    /// answer, so an over-conservative downgrade of a genuinely-satisfiable but
    /// unvalidatable non-string-seq problem is acceptable; a wrong `sat` is not.
    ///
    /// STRINGS ARE UNTOUCHED. Strings are the distinct `Sort::String` (and `Char`
    /// is scoped out of the element check), both audits found ZERO string wrong
    /// verdicts, and a pure-string problem never contains a `Sort::Seq(_)` subterm
    /// — so this gate never fires on it. A genuine non-string-seq `Sat` whose model
    /// the independent evaluator CAN confirm true is `ConfirmedSat` upstream and
    /// never reaches this fail-open arm, so it stays `sat`.
    ///
    /// Runs LAST in the [`emit_sat_verdict`](crate::executor::model::sat_emit)
    /// funnel, after the authoritative-failclosed gate.
    pub(in crate::executor) fn apply_nonstring_seq_failclosed_gate(
        &mut self,
        result: SolveResult,
    ) -> SolveResult {
        if result != SolveResult::Sat {
            return result;
        }
        if !self.independent_model_gate_enabled() {
            return result;
        }
        // Only the fail-open `CannotConfirm` arm can ship a wrong non-string-seq
        // `sat`: a `ConfirmedSat` re-evaluated every assertion to `true` (so the
        // model genuinely satisfies the seq constraints), and a `ModelViolates`
        // already downgraded upstream. The independent gate records which arm
        // fired.
        if self.last_statistics.get_string("model_check_gate.result") != Some("cannot-confirm") {
            return result;
        }
        let Some(offending) = self.nonstring_seq_unconfirmed_assertion() else {
            return result;
        };
        let term = self.format_term(offending);
        tracing::warn!(
            assertion = %term,
            "non-string-seq failclosed gate: an assertion referencing a non-string sequence \
             term was left UNCONFIRMED by the independent gate — AY's symbolic non-string \
             sequence theory is unsound on the sat side; downgrading SAT to Unknown"
        );
        self.last_statistics
            .set_string("model_check_gate.nonstring_seq_failclosed", "downgraded");
        self.last_statistics
            .set_string("model_check_gate.nonstring_seq_assertion", term);
        // Route through the SAME contract-carrying decision core as the
        // `ModelViolates` / authoritative-failclosed arms: an unconfirmed
        // non-string-seq assertion is treated as unconfirmed (confirmed = false)
        // with enforcement statically on.
        if gate_keeps_sat(true, /* confirmed = */ false, ENFORCE_ON_REFUTATION) {
            result
        } else {
            self.downgrade_sat_after_gate(
                "non-string-sequence assertion left unconfirmed by the independent gate: \
                 AY's symbolic non-string sequence theory cannot produce and validate a \
                 complete model for this problem, so keeping the `sat` risks a wrong verdict",
            );
            SolveResult::Unknown
        }
    }

    /// Find an assertion that references a NON-STRING sequence LEAF
    /// (a `Sort::Seq(elem)` declared constant/variable with `elem != Char`) and
    /// that the INDEPENDENT evaluator could not confirm `true` under the emitted
    /// model — the wrong-`sat` signature the
    /// [`apply_nonstring_seq_failclosed_gate`](Self::apply_nonstring_seq_failclosed_gate)
    /// fails closed on. Returns the offending assertion, or `None` when every
    /// non-string-seq assertion is either confirmed `true` or a model-independent
    /// tautology (so the `Sat` is a genuine, validatable non-string-seq model).
    fn nonstring_seq_unconfirmed_assertion(&self) -> Option<TermId> {
        let model = self.last_model.as_ref()?;
        // SCOPE — QUANTIFIER-FREE ONLY. The systemic non-string-seq wrong verdicts
        // are all quantifier-free (both audits). In a QUANTIFIED problem, an
        // unconfirmable leaf is the independent gate's DELIBERATE fail-open
        // posture for quantifier/UF incompleteness (E-matching / MBQI /
        // infinite-domain UF — see the `CannotConfirm` docs), NOT a seq-theory
        // wrong sat: e.g. a UF+datatype weakest-precondition query over a
        // `(Seq Int)` argument is DECIDED sat by E-matching, and its seq leaf is
        // simply not ground-reconstructable. Firing there would degrade a genuine
        // UF/quantifier sat and touch reasoning this fix must leave unchanged, so
        // if the problem contains ANY quantifier the gate does not fire.
        if self
            .ctx
            .assertions
            .iter()
            .any(|&a| contains_quantifier(&self.ctx.terms, a))
        {
            return None;
        }
        let view = IndependentModelView::new(self, model);
        // Build the definitional-equality index up front (empty resolution
        // stack), exactly as `confirm_sat_with_independent_gate` does.
        view.ensure_def_index();
        for &assertion in &self.ctx.assertions {
            // SCOPE: only assertions that reference a non-string sequence term.
            // A pure-string / non-sequence assertion has no `Sort::Seq(_)`
            // subterm and is skipped (strings and every other theory unchanged).
            if !self.assertion_references_nonstring_seq(assertion) {
                continue;
            }
            // Confirmed `true` by the INDEPENDENT evaluator: the emitted model
            // genuinely satisfies this seq assertion — keep it (genuine sat).
            if matches!(
                ay_model_check::evaluate_term(&self.ctx.terms, &view, assertion),
                EvalOutcome::Value(ModelValue::Bool(true))
            ) {
                continue;
            }
            // A model-independent datatype/Boolean tautology holds in EVERY model,
            // so an unevaluated tautology is NOT a wrong sat — mirror the
            // `confirm_model` / authoritative-gate tautology guard.
            if self.term_is_datatype_tautology(assertion) {
                continue;
            }
            // Wrong-`sat` signature: a non-string-seq assertion the independent
            // evaluator could not confirm `true`. Fail closed.
            return Some(assertion);
        }
        None
    }

    /// Whether `assertion` references a NON-STRING sequence LEAF: a `Var` or
    /// nullary-application (declared-constant) subterm whose sort is
    /// `Sort::Seq(elem)` with `elem != Char` — a SYMBOLIC sequence the model must
    /// assign a value to.
    ///
    /// This is exactly the systemic wrong-`sat` surface: the audited bugs
    /// (seq.extract/at/nth/contains/prefixof/suffixof/indexof/replace, seq-of-BV,
    /// seq.nth+arith) all constrain the CONTENT of a declared `(Seq …)` constant,
    /// and their wrong `sat` cannot be backed by a model value for that constant
    /// ("no model value available for term of sort (Seq Int)").
    ///
    /// Scoping to a symbolic seq LEAF (not any Seq-sorted subterm) is deliberate:
    /// * strings are the distinct `Sort::String` (never matched) and `(Seq Char)`
    ///   is scoped out, so strings stay untouched;
    /// * a FULLY-GROUND seq problem — e.g. a higher-order `(seq.map f (seq.++
    ///   (seq.unit 1) (seq.unit 2)))` where every sequence is built from literal
    ///   `seq.unit`s and only a FUNCTION/array `f` is symbolic — has NO symbolic
    ///   seq leaf, so a genuine, model-producible sat there stays `sat`. Its
    ///   independent-gate coverage gap is a higher-order/lambda-array gap (the UF
    ///   class the gate rightly keeps open), not the unpinnable-seq-content
    ///   signature this fail-close targets.
    ///
    /// Bounded by a visited set (linear in distinct subterms).
    pub(in crate::executor) fn assertion_references_nonstring_seq(
        &self,
        assertion: TermId,
    ) -> bool {
        let mut stack = vec![assertion];
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            // Only a LEAF (declared constant / variable) counts: a `Var`, or a
            // nullary application (how a `declare-const` may be interned). A
            // compound seq term (`seq.unit`, `seq.++`, `seq.map`, …) is not a
            // model-assigned leaf and does not, by itself, trigger the fail-close.
            let is_leaf = match self.ctx.terms.get(t) {
                TermData::Var(_, _) => true,
                TermData::App(_, args) => args.is_empty(),
                _ => false,
            };
            if is_leaf {
                if let Sort::Seq(elem) = self.ctx.terms.sort(t) {
                    if **elem != Sort::Char {
                        return true;
                    }
                }
            }
            stack.extend(self.ctx.terms.children(t));
        }
        false
    }

    /// SOUNDNESS (#storeinv10 wrong-sat): true iff `t` is an array EQUALITY
    /// `(= A B)` whose two operands are BOTH `store` chains (each a
    /// `TermData::App("store", …)`) and are syntactically distinct. This is the
    /// nested store-swap identity shape of the storeinv `_np_nf_` benchmarks
    /// (`(= bigstore1 bigstore2)`). Used ONLY inside
    /// [`authoritative_ground_unevaluated_assertion`](Self::authoritative_ground_unevaluated_assertion),
    /// where every visited `t` is a top-level (hence positively-asserted)
    /// conjunct the independent evaluator has ALREADY failed to confirm true; a
    /// positive store-chain equality the independent evaluator cannot pin is an
    /// under-computed extensionality refutation, so it fails closed. A bare
    /// `(= a b)` between array VARIABLES has no `store` operand and is
    /// deliberately NOT matched — it is trivially satisfiable and must stay
    /// `Sat`.
    fn is_positive_store_chain_array_equality(&self, t: TermId) -> bool {
        let TermData::App(sym, args) = self.ctx.terms.get(t) else {
            return false;
        };
        if sym.name() != "=" || args.len() != 2 || args[0] == args[1] {
            return false;
        }
        if !matches!(self.ctx.terms.sort(args[0]), Sort::Array(_)) {
            return false;
        }
        args.iter()
            .all(|&x| matches!(self.ctx.terms.get(x), TermData::App(s, _) if s.name() == "store"))
    }

    /// SOUNDNESS (#storeinv10 wrong-sat): true iff any top-level assertion is an
    /// Array-sorted disequality — `(not (= C D))` or `(distinct C D …)` whose
    /// operands have `Sort::Array(_)`. The co-condition for the store-chain
    /// equality fail-close above: the storeinv wrong-sat is a positive
    /// store-swap identity whose forced base-array equality contradicts such a
    /// disequality. Descends through top-level `and` conjuncts so
    /// `(assert (and … (not (= C D))))` counts the same as a bare
    /// `(assert (not (= C D)))`. Well-sortedness gives both `=` operands the same
    /// sort, so probing `args[0]` suffices.
    fn assertions_contain_array_disequality(&self) -> bool {
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::Not(inner) => {
                    if let TermData::App(sym, args) = self.ctx.terms.get(*inner) {
                        if sym.name() == "="
                            && args.len() == 2
                            && matches!(self.ctx.terms.sort(args[0]), Sort::Array(_))
                        {
                            return true;
                        }
                    }
                }
                TermData::App(sym, args) if sym.name() == "distinct" && args.len() >= 2 => {
                    if args
                        .iter()
                        .any(|&x| matches!(self.ctx.terms.sort(x), Sort::Array(_)))
                    {
                        return true;
                    }
                }
                TermData::App(sym, args) if sym.name() == "and" => {
                    stack.extend(args.iter().copied());
                }
                _ => {}
            }
        }
        false
    }

    /// Three-valued ground evaluation with UNINTERPRETED-READ CONGRUENCE
    /// (soundness, read-congruence wrong-model class).
    ///
    /// Like [`evaluate_term`](Self::evaluate_term), but an unpinned
    /// `(select a i)` over a free array LEAF `a` with a concrete index value
    /// becomes an opaque read token keyed by `(a, value(i))` instead of
    /// `Unknown`. Read congruence holds in EVERY completion of the model:
    /// two reads with the same key are equal no matter what value the leaf
    /// array takes. Only DEFINITE verdicts are produced:
    ///
    /// * `Val(Bool(false))` — the assertion is false in every completion of
    ///   the emitted model (a genuine refutation; the caller fails closed).
    /// * `Val(Bool(true))` — true in every completion (never used to confirm;
    ///   the caller only acts on `false`).
    /// * `Indet` — no definite verdict; the caller keeps its existing flow.
    ///
    /// Equality between two concrete scalars uses value equality; between two
    /// reads it is definite only for IDENTICAL keys (same leaf, same index
    /// value). A read vs anything else, or reads over distinct leaves (which
    /// may or may not be equal arrays), is indeterminate — so a `false` can
    /// never be produced from an equality/distinctness that some completion
    /// could satisfy. Depth-bounded.
    fn congruent_read_eval(&self, model: &Model, t: TermId, depth: u32) -> CongruentReadEval {
        use CongruentReadEval::{Indet, Read, Val};
        if depth > 64 {
            return Indet;
        }
        let v = self.evaluate_term(model, t);
        if !matches!(v, EvalValue::Unknown) {
            return Val(v);
        }
        match self.ctx.terms.get(t) {
            TermData::Not(inner) => match self.congruent_read_bool(model, *inner, depth + 1) {
                Some(b) => Val(EvalValue::Bool(!b)),
                None => Indet,
            },
            TermData::Ite(c, th, el) => match self.congruent_read_bool(model, *c, depth + 1) {
                Some(true) => self.congruent_read_eval(model, *th, depth + 1),
                Some(false) => self.congruent_read_eval(model, *el, depth + 1),
                None => Indet,
            },
            TermData::App(sym, args) => match sym.name() {
                "select" if args.len() == 2 => {
                    let idx = self.evaluate_term(model, args[1]);
                    if matches!(idx, EvalValue::Unknown) {
                        return Indet;
                    }
                    // Only a free array LEAF (declared constant) forms a
                    // congruence key; a structural array operand the ground
                    // evaluator could not resolve stays indeterminate.
                    match self.ctx.terms.get(args[0]) {
                        TermData::Var(_, _) => Read(args[0], idx),
                        TermData::App(_, leaf_args) if leaf_args.is_empty() => Read(args[0], idx),
                        _ => Indet,
                    }
                }
                "not" if args.len() == 1 => {
                    match self.congruent_read_bool(model, args[0], depth + 1) {
                        Some(b) => Val(EvalValue::Bool(!b)),
                        None => Indet,
                    }
                }
                "and" | "or" => {
                    let is_and = sym.name() == "and";
                    let mut all_definite = true;
                    for &a in args {
                        match self.congruent_read_bool(model, a, depth + 1) {
                            Some(b) if b != is_and => return Val(EvalValue::Bool(!is_and)),
                            Some(_) => {}
                            None => all_definite = false,
                        }
                    }
                    if all_definite {
                        Val(EvalValue::Bool(is_and))
                    } else {
                        Indet
                    }
                }
                "=>" if args.len() == 2 => {
                    match (
                        self.congruent_read_bool(model, args[0], depth + 1),
                        self.congruent_read_bool(model, args[1], depth + 1),
                    ) {
                        (Some(false), _) | (_, Some(true)) => Val(EvalValue::Bool(true)),
                        (Some(true), Some(false)) => Val(EvalValue::Bool(false)),
                        _ => Indet,
                    }
                }
                "=" if args.len() >= 2 => {
                    let vals: Vec<CongruentReadEval> = args
                        .iter()
                        .map(|&a| self.congruent_read_eval(model, a, depth + 1))
                        .collect();
                    let mut all_equal = true;
                    for w in vals.windows(2) {
                        match Self::congruent_read_equal(&w[0], &w[1]) {
                            Some(false) => return Val(EvalValue::Bool(false)),
                            Some(true) => {}
                            None => all_equal = false,
                        }
                    }
                    if all_equal {
                        Val(EvalValue::Bool(true))
                    } else {
                        Indet
                    }
                }
                "distinct" if args.len() >= 2 => {
                    let vals: Vec<CongruentReadEval> = args
                        .iter()
                        .map(|&a| self.congruent_read_eval(model, a, depth + 1))
                        .collect();
                    let mut all_unequal = true;
                    for i in 0..vals.len() {
                        for j in (i + 1)..vals.len() {
                            match Self::congruent_read_equal(&vals[i], &vals[j]) {
                                Some(true) => return Val(EvalValue::Bool(false)),
                                Some(false) => {}
                                None => all_unequal = false,
                            }
                        }
                    }
                    if all_unequal {
                        Val(EvalValue::Bool(true))
                    } else {
                        Indet
                    }
                }
                _ => Indet,
            },
            _ => Indet,
        }
    }

    /// Boolean projection of [`congruent_read_eval`](Self::congruent_read_eval).
    fn congruent_read_bool(&self, model: &Model, t: TermId, depth: u32) -> Option<bool> {
        match self.congruent_read_eval(model, t, depth) {
            CongruentReadEval::Val(EvalValue::Bool(b)) => Some(b),
            _ => None,
        }
    }

    /// Definite equality between two congruent-read evaluations.
    ///
    /// `Some(true)`/`Some(false)` only when the verdict holds in EVERY
    /// completion of the model; `None` otherwise. Definite inequality is
    /// restricted to unambiguous concrete scalar kinds (Bool / Rational /
    /// BitVec / String); `Element`, `Fp`, `Seq`, `Algebraic` stay conservative
    /// on the unequal side.
    fn congruent_read_equal(a: &CongruentReadEval, b: &CongruentReadEval) -> Option<bool> {
        use CongruentReadEval::{Read, Val};
        match (a, b) {
            (Val(x), Val(y)) => {
                if matches!(x, EvalValue::Unknown) || matches!(y, EvalValue::Unknown) {
                    return None;
                }
                if x == y {
                    return Some(true);
                }
                let definite_kind = |v: &EvalValue| {
                    matches!(
                        v,
                        EvalValue::Bool(_)
                            | EvalValue::Rational(_)
                            | EvalValue::BitVec { .. }
                            | EvalValue::String(_)
                    )
                };
                if definite_kind(x) && definite_kind(y) {
                    Some(false)
                } else {
                    None
                }
            }
            (Read(r1, i1), Read(r2, i2)) => {
                if r1 == r2 && !matches!(i1, EvalValue::Unknown) && i1 == i2 {
                    Some(true)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Whether the declared logic is one where GROUND evaluation is
    /// AUTHORITATIVE — i.e. a fully-pinned model that fails to reduce an
    /// assertion indicates evaluator under-computation, not theory
    /// incompleteness. Restricted to quantifier-free array / LIA / LRA / BV / UF
    /// combinations; FP, strings, sequences/sets/maps, and nonlinear arithmetic
    /// are DELIBERATELY excluded (their ground evaluators are legitimately
    /// incomplete, so a `CannotConfirm` there must keep the verdict).
    fn logic_is_authoritative_when_ground(&self) -> bool {
        let Some(logic) = self.logic() else {
            return false;
        };
        // A stored accepted-but-unmapped declared logic (a z3-recognized token
        // AY does not map to a category, e.g. `QF_UFO` — recognized via the
        // "UF" substring, starts with `QF_`, misses every exclusion below) must
        // NOT extend ground-authoritative model-gate trust to arbitrary content.
        // Any `Other`-category logic (incl. the fail-closed combined four) is
        // non-authoritative here; the token routed through content detection, so
        // trust must be earned by the detected fragment, not the raw token.
        if matches!(LogicCategory::from_logic(logic), LogicCategory::Other) {
            return false;
        }
        // Quantified logics (E-matching / CEGQI incompleteness) are not
        // authoritative when ground.
        if !logic.starts_with("QF_") {
            return false;
        }
        // Incomplete/non-ground-authoritative fragments.
        if logic.contains("FP")
            || logic.contains("SEQ")
            || logic.contains("SET")
            || logic.contains("MULTISET")
            || logic.contains("MAP")
        {
            return false;
        }
        // Strings (`QF_S`, `QF_SLIA`, `QF_SNIA`, ...): `str.*` operators have
        // incomplete ground evaluation.
        if logic.starts_with("QF_S") {
            return false;
        }
        // Nonlinear arithmetic (`NIA`/`NRA`/`NIRA`): incomplete.
        if logic.contains("NIA") || logic.contains("NRA") || logic.contains("NIRA") {
            return false;
        }
        true
    }

    /// Whether `assertion` is STRUCTURALLY GROUND in an authoritative theory
    /// under `model`: every scalar leaf it reads (declared constant/variable,
    /// array `select` result, uninterpreted-function application) resolves to a
    /// concrete value the solver's own evaluator committed.
    ///
    /// SURGICAL by construction: it fires ONLY on the boolean/arithmetic/BV +
    /// concrete-`select`-read fragment. Any array-valued or datatype-valued
    /// subterm OTHER than the array operand of a scalar `select` (e.g. a raw
    /// `(= a b)` array equality or a bare store chain), or any FP / string /
    /// sequence subterm, makes the assertion NON-authoritative-ground here
    /// (returns `false` → keep `Sat`), so partial-reconstruction genuine SATs —
    /// like `extensionality_class_with_ground_read_pin_confirms_sat`, whose
    /// array class the theory only partially materializes — are never downgraded.
    fn assertion_is_authoritatively_ground(&self, model: &Model, assertion: TermId) -> bool {
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![assertion];
        // Require at least one pinned scalar read, so a vacuous walk (e.g. a bare
        // boolean literal) is not mistaken for an authoritative-ground refutation.
        let mut saw_pinned_scalar = false;
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, th, e) => {
                    stack.push(*c);
                    stack.push(*th);
                    stack.push(*e);
                }
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, x)| *x));
                    stack.push(*body);
                }
                // A quantifier makes the assertion non-ground.
                TermData::Forall(..) | TermData::Exists(..) => return false,
                TermData::App(sym, args) => {
                    match sym.name() {
                        // Pure boolean structure: recurse, require nothing here.
                        "and" | "or" | "=>" | "xor" | "not" | "=" | "distinct" | "ite" => {
                            stack.extend(args.iter().copied());
                        }
                        // Authoritative array READ: its scalar result MUST be
                        // pinned. Recurse the index (a scalar leaf); the array
                        // container is subsumed by the read's concreteness.
                        "select" if args.len() == 2 => {
                            if !self.eval_is_concrete_scalar(model, t) {
                                return false;
                            }
                            saw_pinned_scalar = true;
                            stack.push(args[1]);
                        }
                        // Arithmetic/BV composite OR an uninterpreted read.
                        _ => match self.authoritative_sort_class(self.ctx.terms.sort(t)) {
                            SortClass::Scalar => {
                                if !self.eval_is_concrete_scalar(model, t) {
                                    return false;
                                }
                                saw_pinned_scalar = true;
                                stack.extend(args.iter().copied());
                            }
                            // A non-`select` array/datatype-valued subterm, or an
                            // FP/string/seq subterm: outside the surgical
                            // fragment — keep the verdict.
                            SortClass::Container | SortClass::NonAuthoritative => return false,
                        },
                    }
                }
                TermData::Var(_, _) => {
                    match self.authoritative_sort_class(self.ctx.terms.sort(t)) {
                        SortClass::Scalar => {
                            if !self.eval_is_concrete_scalar(model, t) {
                                return false;
                            }
                            saw_pinned_scalar = true;
                        }
                        SortClass::Container | SortClass::NonAuthoritative => return false,
                    }
                }
                // A literal constant is concrete by construction.
                TermData::Const(_) => saw_pinned_scalar = true,
                // Any other childless variant contributes no leaf.
                _ => {}
            }
        }
        saw_pinned_scalar
    }

    /// Classify a sort for the authoritative-ground walk.
    fn authoritative_sort_class(&self, sort: &Sort) -> SortClass {
        match sort {
            Sort::Bool
            | Sort::Int
            | Sort::Real
            | Sort::BitVec(_)
            | Sort::Char
            | Sort::FiniteDomain(_, _) => SortClass::Scalar,
            // A datatype (native or abstracted to `Uninterpreted`) is a
            // container we do not reduce in this surgical fragment.
            Sort::Datatype(_) => SortClass::Container,
            Sort::Uninterpreted(_) => {
                if self.datatype_sort_name(sort).is_some() {
                    SortClass::Container
                } else {
                    SortClass::Scalar
                }
            }
            Sort::Array(_) => SortClass::Container,
            // FP / strings / sequences / regex: ground evaluation is incomplete.
            _ => SortClass::NonAuthoritative,
        }
    }

    /// Whether the solver's own evaluator resolves `t` to a concrete scalar
    /// value under `model` (the "leaf is pinned" test).
    fn eval_is_concrete_scalar(&self, model: &Model, t: TermId) -> bool {
        matches!(
            self.evaluate_term(model, t),
            EvalValue::Bool(_)
                | EvalValue::Element(_)
                | EvalValue::Rational(_)
                | EvalValue::BitVec { .. }
                | EvalValue::Algebraic(_)
        )
    }

    /// QUANTIFIED-ASSERTION fail-closed model gate (#quantified-model-gate).
    ///
    /// The independent evaluator cannot evaluate a quantifier
    /// (`ay_model_check` fails closed on `Forall`/`Exists`), the
    /// `CannotConfirm` arm fails OPEN, the authoritative gate skips quantified
    /// assertions, and the strict all-ground gate disables itself when any
    /// quantifier is present — so historically NO gate ever checked a
    /// universally quantified assertion against the concrete emitted model,
    /// and a `sat` whose model FALSIFIES its own `forall` could ship
    /// (AUFLIA `(forall i. (= (select a i) (f i)))` emitted `f := λ.1` against
    /// an `a` defaulting to 0 — false at every i∉{0}).
    ///
    /// This gate closes the hole SYSTEMICALLY: over a proposed `Sat` with an
    /// emitted model, EVERY quantified assertion conjunct must be either
    /// * CONFIRMED true under the emitted model by an isolated nested solve
    ///   (universal: model-pinned skolemized negation UNSAT — validity over
    ///   every structure, hence truth in the emitted model; existential:
    ///   model-pinned skolemized body SAT under a TOTAL pin set — every free
    ///   symbol forced to its exact model value, so satisfiability IS truth in
    ///   the model; general/alternation shapes go through the QE prepass), or
    /// * REFUTED (the dual verdict) — the emitted witness is invalid: loud
    ///   alarm when the refutation is clean (total pins, no
    ///   uninterpreted-sort binder whose domain the nested solve could
    ///   enlarge beyond the model's finite universe), and in all cases
    ///   `Sat` → `Unknown`, or
    /// * neither — FAIL CLOSED to `Unknown`. `unknown` is never a wrong
    ///   answer; an unvalidatable quantified `sat` witness must not ship.
    ///
    /// Runs in the [`emit_sat_verdict`](crate::executor::model::sat_emit)
    /// funnel after the non-string-seq gate, over the funnel's scoped combined
    /// assertion set (so `check-sat-assuming` roots are covered). Zero cost on
    /// quantifier-free problems (keyed on `contains_quantifier`).
    pub(in crate::executor) fn apply_quantified_model_failclosed_gate(
        &mut self,
        result: SolveResult,
    ) -> SolveResult {
        if result != SolveResult::Sat {
            return result;
        }
        if !self.independent_model_gate_enabled() {
            return result;
        }
        // Nested isolated solves must never recurse into this gate.
        if self.in_quantified_model_gate {
            return result;
        }
        // Without an emitted model there is no witness to validate here; the
        // other funnel gates and the validation-evidence postcondition own
        // that case (mirrors the independent gate's no-model posture).
        if self.last_model.is_none() {
            return result;
        }
        // The all-or-nothing DT certificate already checked every snapshot
        // universal against its completed model M'.  The retained emission
        // candidate M intentionally contains only the ground core, which the
        // preceding strict and independent gates still checked.  Record the
        // certificate handoff explicitly and do not let the independent gate's
        // ground-core `ConfirmedSat` marker short-circuit this provenance.
        if self.dt_cert_grant_active {
            self.last_statistics
                .set_string("model_check_gate.quantified", "deferred-certified-dt");
            return result;
        }
        // `ConfirmedSat` means the independent evaluator pinned EVERY
        // assertion (quantified included, e.g. via a true ground disjunct) to
        // `true` — nothing left to check.
        if self.last_statistics.get_string("model_check_gate.result") == Some("confirmed-sat") {
            return result;
        }

        // Collect the quantified LEAF conjuncts of the scoped assertion set
        // (each `(and …)` assertion is true iff all its leaf conjuncts are).
        let assertions = self.ctx.assertions.clone();
        let mut candidates: Vec<TermId> = Vec::new();
        for &assertion in &assertions {
            if !contains_quantifier(&self.ctx.terms, assertion) {
                continue;
            }
            let mut conjuncts = Vec::new();
            crate::executor::quantifier_loop::collect_and_conjuncts(
                &self.ctx.terms,
                assertion,
                &mut conjuncts,
            );
            if conjuncts.is_empty() {
                conjuncts.push(assertion);
            }
            for c in conjuncts {
                let is_and_node = matches!(
                    self.ctx.terms.get(c),
                    TermData::App(sym, _) if sym.name() == "and"
                );
                if !is_and_node
                    && contains_quantifier(&self.ctx.terms, c)
                    && !candidates.contains(&c)
                {
                    candidates.push(c);
                }
            }
        }
        if candidates.is_empty() {
            return result;
        }

        // One shared wall budget PER CHECK-SAT for every nested confirm (an
        // axiom-heavy problem must not multiply the budget per assertion),
        // never extending an already-tighter outer deadline. Nested solves
        // pollute `last_statistics`; snapshot and restore so the emitted
        // statistics describe the OUTER solve, then record this gate's own
        // verdict keys.
        let saved_deadline = self.solve_deadline.get();
        let budget = Instant::now() + Duration::from_secs(2);
        self.set_deadline(match saved_deadline {
            Some(d) if d < budget => Some(d),
            _ => Some(budget),
        });
        let saved_statistics = self.last_statistics.clone();
        self.in_quantified_model_gate = true;
        let mut failure: Option<(TermId, QuantifiedModelCheck)> = None;
        let mut deferred_any = false;
        for &conjunct in &candidates {
            if self.solve_deadline.expired() {
                if self.quantified_conjunct_defer_eligible(conjunct) {
                    // Out of budget, but the witness prints no interpretation
                    // for any of this conjunct's functions — the same
                    // deferral the full check would reach on indeterminate.
                    deferred_any = true;
                    continue;
                }
                failure = Some((
                    conjunct,
                    QuantifiedModelCheck::Indeterminate("gate budget exhausted"),
                ));
                break;
            }
            match self.check_quantified_conjunct_against_model(conjunct) {
                QuantifiedModelCheck::Confirmed => {}
                QuantifiedModelCheck::Deferred => deferred_any = true,
                other => {
                    failure = Some((conjunct, other));
                    break;
                }
            }
        }
        self.in_quantified_model_gate = false;
        self.set_deadline(saved_deadline);
        self.last_statistics = saved_statistics;

        match failure {
            None
            | Some((_, QuantifiedModelCheck::Confirmed))
            | Some((_, QuantifiedModelCheck::Deferred)) => {
                if deferred_any && self.self_check {
                    // FAIL-CLOSED under --self-check (#quantified-deferred-selfcheck).
                    // The self-check contract emits `sat` ONLY when the evaluator
                    // CONFIRMS every authored assertion; anything unverifiable is
                    // `unknown`. A DEFERRED quantified conjunct was NOT confirmed —
                    // the emitted witness pins no interpretation for its functions,
                    // so the `sat` rests on the solving machinery alone, which is
                    // exactly the unsound component on quantified fragments (found
                    // 2026-07-23: 20 UFBV + 1 UFNIRA wintersteiger `fixpoint`
                    // wrong-SATs passing --self-check, while z3, cvc5, and each
                    // file's own `(set-info :status unsat)` all say UNSAT). An
                    // unverified quantifier must degrade to `unknown` here. Default
                    // mode is unchanged: it keeps the completeness-favoring
                    // deferred-`sat` (documented not-sound trade), so this can only
                    // ADD unknowns to the fail-closed mode, never a wrong answer.
                    self.last_statistics.set_string(
                        "model_check_gate.quantified",
                        "deferred-selfcheck-failclosed",
                    );
                    self.downgrade_sat_after_gate(
                        "self-check: a quantified assertion could not be confirmed \
                         against the emitted model (deferred: the witness pins no \
                         interpretation for its functions) — failing closed rather \
                         than trusting the solver's unchecked `sat`",
                    );
                    SolveResult::Unknown
                } else {
                    self.last_statistics.set_string(
                        "model_check_gate.quantified",
                        if deferred_any {
                            // Every checked conjunct passed, but at least one was
                            // DEFERRED: the emitted witness cannot falsify it (no
                            // printed function interpretation, or a closed
                            // model-independent sentence) — the `sat` rests on
                            // the machinery that minted it exactly as before this
                            // gate (refutation paths still ran and found nothing).
                            "deferred"
                        } else {
                            "confirmed"
                        },
                    );
                    result
                }
            }
            Some((conjunct, QuantifiedModelCheck::Refuted { clean })) => {
                let term = self.format_term(conjunct);
                if clean {
                    // A total-substitution refutation is a concrete
                    // counterexample instance: the emitted model falsifies the
                    // quantified assertion — a genuine internal bug worth the
                    // loud alarm (the downgrade below is SOUND regardless).
                    self.report_caught_invalid_model(conjunct, &term);
                }
                self.last_statistics
                    .set_string("model_check_gate.quantified", "refuted");
                self.last_statistics
                    .set_string("model_check_gate.quantified_assertion", term);
                if gate_keeps_sat(true, /* confirmed = */ false, ENFORCE_ON_REFUTATION) {
                    result
                } else {
                    self.downgrade_sat_after_gate(
                        "quantified assertion is falsified by the emitted model",
                    );
                    SolveResult::Unknown
                }
            }
            Some((conjunct, QuantifiedModelCheck::Indeterminate(reason))) => {
                let term = self.format_term(conjunct);
                tracing::debug!(
                    assertion = %term,
                    reason,
                    "quantified model gate could not validate a quantified \
                     assertion against the emitted model; failing closed \
                     Sat -> Unknown"
                );
                self.last_statistics
                    .set_string("model_check_gate.quantified", "fail-closed");
                self.last_statistics
                    .set_string("model_check_gate.quantified_assertion", term);
                self.last_statistics
                    .set_string("model_check_gate.quantified_reason", reason);
                if gate_keeps_sat(true, /* confirmed = */ false, ENFORCE_ON_REFUTATION) {
                    result
                } else {
                    self.downgrade_sat_after_gate(
                        "quantified assertion could not be validated against the emitted \
                         model: no gate evaluates quantifiers, so keeping the `sat` would \
                         ship an unchecked witness",
                    );
                    SolveResult::Unknown
                }
            }
        }
    }

    /// Validate ONE quantified leaf conjunct against the emitted model.
    ///
    /// Strategy (#quantified-model-gate):
    /// 1. Re-evaluate with the independent evaluator — a `true` (e.g. via a
    ///    true ground disjunct around the quantifier) is a genuine confirm.
    /// 2. Reconstruct the printer-visible interpretation of every arity>0
    ///    uninterpreted function occurring in the conjunct (finite EUF table
    ///    rows, `else` = last row — exactly `format_function_table`'s
    ///    semantics) and SUBSTITUTE it for each application, beta-reducing to
    ///    a first-match `ite` chain. A function whose printed interpretation
    ///    cannot be reconstructed EXACTLY stays free (fill-only: that can
    ///    only weaken a confirm into a fail-close, never fabricate one).
    /// 3. Build MODEL PINS: `(= leaf <model-value>)` for every remaining free
    ///    constant leaf whose printed model value is representable as a term
    ///    (Bool/Int/Real/BV/String literals, array store-chains over
    ///    `(as const …)`, uninterpreted-sort elements as shared fresh
    ///    constants asserted pairwise-distinct). `total` records whether
    ///    EVERY free symbol was pinned.
    /// 4. Route by polarity-normalized quantifier prefix:
    ///    * a binder over an uninterpreted sort is EXPANDED over the model's
    ///      finite universe (its exact domain in the emitted model) into a
    ///      conjunction (universal) / disjunction (existential) of instances;
    ///    * universal prefix, QF matrix — nested solve of
    ///      `pins ∧ distinct ∧ ¬matrix[sk⃗]`: UNSAT confirms (validity over
    ///      every structure, including the emitted model, even under PARTIAL
    ///      pins); SAT refutes only when the check is CLEAN (total pins, all
    ///      functions substituted, all uninterpreted-sort binders expanded —
    ///      then nested truth IS truth in the emitted model);
    ///    * existential prefix, QF matrix — nested solve of
    ///      `pins ∧ distinct ∧ matrix[sk⃗]`: UNSAT refutes (no structure at
    ///      all has a witness, so neither does the model); SAT confirms only
    ///      when CLEAN;
    ///    * anything else (alternations, quantifiers under connectives) —
    ///      `pins ∧ distinct ∧ conjunct` through the QE prepass; if
    ///      quantifier-free afterwards, SAT/UNSAT map as in the existential
    ///      route.
    fn check_quantified_conjunct_against_model(
        &mut self,
        conjunct: TermId,
    ) -> QuantifiedModelCheck {
        // (1) Independent-evaluator confirm (quantifier itself is unevaluable,
        // but a surrounding connective can already pin the conjunct true).
        {
            let Some(model) = self.last_model.as_ref() else {
                return QuantifiedModelCheck::Indeterminate("no model");
            };
            let view = IndependentModelView::new(self, model);
            view.ensure_def_index();
            if matches!(
                ay_model_check::evaluate_term(&self.ctx.terms, &view, conjunct),
                EvalOutcome::Value(ModelValue::Bool(true))
            ) {
                return QuantifiedModelCheck::Confirmed;
            }
        }

        // Shared uninterpreted-sort element context (one fresh constant per
        // model universe element, asserted pairwise-distinct exactly as the
        // model holds them).
        let mut elems = QuantifiedGateElements::default();

        // STRICT closedness of the ORIGINAL conjunct (#quantified-model-gate):
        // computed BEFORE ground-value folding and BEFORE UF-interpretation
        // substitution, both of which pour printed-witness content into the
        // term. A sentence that became symbol-free only THROUGH those
        // substitutions is exactly as trustworthy as the witness itself — its
        // falsity IS the witness's falsity — so only this predicate may
        // license the CLOSED deferral in the routes below.
        let model_independent = quantified_gate_model_independent(&self.ctx.terms, conjunct);

        // (1b) EXACT ground-value folding: every maximal binder-free subterm
        // is evaluated under the same independent view the gates check ground
        // assertions with, and replaced by its exact model value (e.g. a
        // binder-independent `(= (bvadd (f y) z) z)` folds to `true`). This is
        // evaluation against the emitted model itself — never sampling — so it
        // is exact in both directions; anything unevaluable is left in place.
        let conjunct = self.quantified_gate_fold_ground_values(conjunct, &mut elems);

        // (1c) Finite-domain binder expansion: Bool and small-width BitVec
        // binders quantify over an exactly-enumerable domain, so
        // `forall`/`exists` over them is EQUIVALENT to the conjunction/
        // disjunction of the instances (capped; past the cap the binder is
        // kept). This decides alternations like `∃x:BV2. ∀y:BV2. …` exactly.
        let conjunct = self.quantified_gate_expand_finite_binders(conjunct);

        // (1d) Folding/expansion can leave the conjunct directly evaluable
        // (e.g. every quantifier expanded away over literals).
        {
            let Some(model) = self.last_model.as_ref() else {
                return QuantifiedModelCheck::Indeterminate("no model");
            };
            let view = IndependentModelView::new(self, model);
            view.ensure_def_index();
            match ay_model_check::evaluate_term(&self.ctx.terms, &view, conjunct) {
                EvalOutcome::Value(ModelValue::Bool(true)) => {
                    return QuantifiedModelCheck::Confirmed;
                }
                EvalOutcome::Value(ModelValue::Bool(false)) => {
                    // Exact evaluation of the (partially folded) conjunct to
                    // FALSE is a direct model refutation.
                    return QuantifiedModelCheck::Refuted { clean: true };
                }
                _ => {}
            }
        }

        // (2) Printer-faithful finite interpretations for the conjunct's
        // remaining (binder-dependent) uninterpreted-function applications.
        // `defer_ok` records that the conjunct HAS uninterpreted-function
        // heads and NONE of them has a printed interpretation: the emitted
        // witness is silent about them, so an INDETERMINATE outcome defers to
        // the pre-existing certificate lane instead of failing closed
        // (refutation outcomes are never relaxed).
        let (interps, defer_ok) = self.quantified_gate_uf_interps(conjunct, &mut elems);
        if std::env::var("AY_DEBUG_QMG").is_ok() {
            let mut names: Vec<&String> = interps.keys().collect();
            names.sort();
            safe_eprintln!("QMG interps built: {names:?} defer_ok={defer_ok}");
        }

        // (4) Polarity-normalized quantifier prefix.
        let mut binders: Vec<(String, Sort)> = Vec::new();
        let mut universal: Option<bool> = None;
        let mut cur = conjunct;
        let mut positive = true;
        loop {
            match self.ctx.terms.get(cur).clone() {
                TermData::Not(inner) => {
                    positive = !positive;
                    cur = inner;
                }
                TermData::Forall(vars, body, _) => {
                    if *universal.get_or_insert(positive) != positive {
                        break;
                    }
                    binders.extend(vars);
                    cur = body;
                }
                TermData::Exists(vars, body, _) => {
                    if *universal.get_or_insert(!positive) == positive {
                        break;
                    }
                    binders.extend(vars);
                    cur = body;
                }
                _ => break,
            }
        }
        let matrix = if positive {
            cur
        } else {
            self.ctx.terms.mk_not(cur)
        };

        let outcome = match universal {
            Some(is_universal) if !contains_quantifier(&self.ctx.terms, matrix) => {
                // Expand each uninterpreted-sort binder over the model's
                // finite universe: in the emitted model that universe IS the
                // binder's whole domain, so the conjunction (universal) /
                // disjunction (existential) of element instances is EXACTLY
                // the quantifier's truth in the model. Capped: past the cap
                // the binder is skolemized instead (confirm-by-UNSAT stays
                // sound; the check is just no longer clean).
                let universe_of = |exec: &Self, sort: &Sort| -> Option<Vec<String>> {
                    let Sort::Uninterpreted(sname) = sort else {
                        return None;
                    };
                    let model = exec.last_model.as_ref()?;
                    match model.euf_model.as_ref() {
                        Some(euf) => match euf.sort_elements.get(sname) {
                            Some(elements) if !elements.is_empty() => Some(elements.clone()),
                            // The EUF model records NO element of this sort:
                            // nothing printed distinguishes any two elements,
                            // so completing the domain as a SINGLETON is
                            // legitimate fill-only completion of the emitted
                            // witness — but only when no term value of the
                            // sort exists either (a stray token would deny
                            // the singleton premise).
                            _ => {
                                let token_prefix = format!("@{sname}!");
                                if euf
                                    .term_values
                                    .values()
                                    .any(|v| v.starts_with(&token_prefix))
                                {
                                    None
                                } else {
                                    Some(vec![format!("@{sname}!0")])
                                }
                            }
                        },
                        // No EUF component at all: no element of any
                        // uninterpreted sort is printed anywhere.
                        None => Some(vec![format!("@{sname}!0")]),
                    }
                };
                let mut instances = vec![matrix];
                let mut skolem_binders: Vec<(String, Sort)> = Vec::new();
                let mut expanded_all_usorts = true;
                for (name, sort) in &binders {
                    let expansion = match universe_of(self, sort) {
                        Some(tokens)
                            if instances.len().saturating_mul(tokens.len())
                                <= QUANTIFIED_GATE_MAX_USORT_INSTANCES =>
                        {
                            Some(tokens)
                        }
                        Some(_) => {
                            expanded_all_usorts = false;
                            None
                        }
                        None => {
                            if matches!(sort, Sort::Uninterpreted(_)) {
                                // No finite universe recorded for the sort —
                                // the binder's model domain is unknown here.
                                expanded_all_usorts = false;
                            }
                            None
                        }
                    };
                    match expansion {
                        Some(tokens) => {
                            let mut next = Vec::with_capacity(instances.len() * tokens.len());
                            for token in &tokens {
                                let elem = elems.term_for(&mut self.ctx.terms, token, sort.clone());
                                let mut subst: DetHashMap<String, TermId> = DetHashMap::default();
                                subst.insert(name.clone(), elem);
                                for &inst in &instances {
                                    next.push(crate::ematching::subst_vars(
                                        &mut self.ctx.terms,
                                        inst,
                                        &subst,
                                    ));
                                }
                            }
                            instances = next;
                        }
                        None => skolem_binders.push((name.clone(), sort.clone())),
                    }
                }
                let combined = if instances.len() == 1 {
                    instances[0]
                } else if is_universal {
                    self.ctx.terms.mk_and(instances)
                } else {
                    self.ctx.terms.mk_or(instances)
                };

                // Skolemize the remaining (polarity-normalized) prefix binders.
                let mut subst: DetHashMap<String, TermId> = DetHashMap::default();
                let mut skolems: HashSet<TermId> = HashSet::default();
                let mut usort_skolem = false;
                for (name, sort) in &skolem_binders {
                    usort_skolem |= sort_mentions_uninterpreted(sort);
                    let fresh = self
                        .ctx
                        .terms
                        .mk_fresh_var(&format!("qmg!{name}"), sort.clone());
                    skolems.insert(fresh);
                    subst.insert(name.clone(), fresh);
                }
                let instance = if subst.is_empty() {
                    combined
                } else {
                    crate::ematching::subst_vars(&mut self.ctx.terms, combined, &subst)
                };

                // Substitute the printer-visible function interpretations,
                // then pin the remaining free constant leaves. Skolems and
                // universe-element constants are the gate's own — never pin
                // them to a value.
                let (instance, ufs_complete) =
                    self.apply_quantified_gate_uf_interps(instance, &interps, &mut elems);
                let mut exclude = skolems;
                exclude.extend(elems.all_terms());
                let pins = self.quantified_gate_model_pins(instance, &mut elems, &exclude);
                let clean = pins.total && ufs_complete && expanded_all_usorts && !usort_skolem;
                let mut nested = pins.equalities.clone();
                nested.extend(elems.distinct_assertions(&mut self.ctx.terms));
                if std::env::var("AY_DEBUG_QMG").is_ok() {
                    safe_eprintln!("QMG instance: {}", self.format_term(instance));
                    for &p in &nested {
                        safe_eprintln!("QMG pin: {}", self.format_term(p));
                    }
                    safe_eprintln!(
                        "QMG clean={clean} total={} ufs_complete={ufs_complete}",
                        pins.total
                    );
                }
                // A CLOSED check: the ORIGINAL conjunct is a genuinely closed
                // sentence over fixed-interpretation domains
                // (`model_independent` — decided before any substitution or
                // folding, so no printed witness content is hiding inside
                // it), AND the check itself pinned nothing, substituted every
                // function (or none exist), and involves no model universe
                // element. Only then can NO printed witness content falsify
                // it; its truth is exactly the verdict machinery's claim. An
                // undecided nested solve then defers instead of failing
                // closed (a decided one still confirms/refutes as usual).
                // `npins=0 ∧ nelems=0` ALONE is NOT closedness: substitution
                // can consume every model symbol and leave nothing to pin —
                // the auflia-model escape class (∀∃ over a printed `f`).
                let closed = model_independent
                    && clean
                    && pins.equalities.is_empty()
                    && elems.by_token.is_empty();
                if is_universal {
                    let target = self.ctx.terms.mk_not(instance);
                    nested.push(target);
                    let r = self.quantified_gate_isolated_solve(nested);
                    if std::env::var("AY_DEBUG_QMG").is_ok() {
                        safe_eprintln!("QMG universal nested result: {r:?}");
                    }
                    match r {
                        SolveResult::Unsat(_) => QuantifiedModelCheck::Confirmed,
                        SolveResult::Sat if clean => QuantifiedModelCheck::Refuted { clean: true },
                        SolveResult::Sat => QuantifiedModelCheck::Indeterminate(
                            "universal negation satisfiable under partial pins",
                        ),
                        SolveResult::Unknown if closed => QuantifiedModelCheck::Deferred,
                        SolveResult::Unknown => {
                            QuantifiedModelCheck::Indeterminate("nested solve undecided")
                        }
                    }
                } else {
                    nested.push(instance);
                    match self.quantified_gate_isolated_solve(nested) {
                        // UNSAT over every structure: the model has no witness
                        // either — a sound refutation even under partial pins.
                        SolveResult::Unsat(_) => QuantifiedModelCheck::Refuted { clean },
                        SolveResult::Sat if clean => QuantifiedModelCheck::Confirmed,
                        SolveResult::Sat => QuantifiedModelCheck::Indeterminate(
                            "existential witness under partial pins",
                        ),
                        SolveResult::Unknown if closed => QuantifiedModelCheck::Deferred,
                        SolveResult::Unknown => {
                            QuantifiedModelCheck::Indeterminate("nested solve undecided")
                        }
                    }
                }
            }
            _ => self.quantified_gate_general_check(
                conjunct,
                &interps,
                &mut elems,
                model_independent,
            ),
        };
        if let QuantifiedModelCheck::Indeterminate(_) = outcome {
            // The witness prints NO interpretation for any of this
            // conjunct's uninterpreted functions, so it asserts nothing
            // the conjunct could falsify through them; an indeterminate
            // check defers to the pre-existing completion-certificate
            // lane (exactly HEAD's trust level). Refutations above were
            // never relaxed.
            if defer_ok {
                return QuantifiedModelCheck::Deferred;
            }
        }
        outcome
    }

    /// General/alternation route: decide `pins ∧ distinct ∧ conjunct` after
    /// the QE prepass, with function interpretations substituted first. Only a
    /// QUANTIFIER-FREE residue is solved (`deep_qe` is an equivalence
    /// transform — the same pass the main pipeline applies to the assertion
    /// set); any residual quantifier fails closed.
    fn quantified_gate_general_check(
        &mut self,
        conjunct: TermId,
        interps: &DetHashMap<String, QuantifiedGateUfInterp>,
        elems: &mut QuantifiedGateElements,
        model_independent: bool,
    ) -> QuantifiedModelCheck {
        let (substituted, ufs_complete) =
            self.apply_quantified_gate_uf_interps(conjunct, interps, elems);
        let exclude: HashSet<TermId> = elems.all_terms();
        let pins = self.quantified_gate_model_pins(substituted, elems, &exclude);
        let usort_binder = self.term_has_uninterpreted_sort_binder(substituted);
        let mut nested = pins.equalities.clone();
        nested.extend(elems.distinct_assertions(&mut self.ctx.terms));
        nested.push(substituted);
        crate::executor::qe_prepass::deep_qe(
            &mut self.ctx.terms,
            &mut nested,
            self.solve_interrupt.as_deref(),
        );
        let clean = pins.total && ufs_complete && !usort_binder;
        // Same CLOSED notion as the prefix route: the ORIGINAL conjunct is a
        // genuinely closed sentence (`model_independent`, decided before any
        // substitution/folding), no pins, everything substituted, no universe
        // elements — only then can no printed witness content falsify it.
        // `npins=0 ∧ nelems=0` alone is NOT closedness: UF-interp
        // substitution and ground folding consume the model symbols and
        // leave nothing to pin — the auflia-model escape class (∀∃
        // alternations, quantifiers under `=>`/`or`/`ite`/`not not`).
        let closed =
            model_independent && clean && pins.equalities.is_empty() && elems.by_token.is_empty();
        if nested
            .iter()
            .any(|&t| contains_quantifier(&self.ctx.terms, t))
        {
            if closed {
                return QuantifiedModelCheck::Deferred;
            }
            return QuantifiedModelCheck::Indeterminate("residual quantifier after QE");
        }
        match self.quantified_gate_isolated_solve(nested) {
            // `pins ∧ conjunct` UNSAT over every structure refutes the model
            // (the model satisfies the pins by construction).
            SolveResult::Unsat(_) => QuantifiedModelCheck::Refuted { clean },
            // With a CLEAN check the conjunct's truth depends only on symbol
            // values every pin forces to the model's, so SAT is truth in the
            // emitted model.
            SolveResult::Sat if clean => QuantifiedModelCheck::Confirmed,
            SolveResult::Sat => {
                QuantifiedModelCheck::Indeterminate("QE residue satisfiable under partial pins")
            }
            SolveResult::Unknown if closed => QuantifiedModelCheck::Deferred,
            SolveResult::Unknown => QuantifiedModelCheck::Indeterminate("nested solve undecided"),
        }
    }

    /// EXACT ground-value folding (#quantified-model-gate): replace every
    /// maximal binder-free subterm of `conjunct` whose value the independent
    /// view can compute with that exact value as a closed term. This is
    /// evaluation against the emitted model itself — the same evaluator every
    /// ground gate anchors on — never sampling, so the fold preserves the
    /// conjunct's truth value in the emitted model exactly. Anything
    /// unevaluable/unconvertible is left in place (fail-close direction:
    /// leftover symbols only make the later confirm harder, never easier).
    ///
    /// A subterm is binder-free iff it contains no `Var` whose name is bound
    /// by ANY quantifier/let inside the conjunct (shadowing a declared
    /// constant with a binder name conservatively blocks folding) and no
    /// quantifier/let node.
    fn quantified_gate_fold_ground_values(
        &mut self,
        conjunct: TermId,
        elems: &mut QuantifiedGateElements,
    ) -> TermId {
        // Binder names appearing anywhere in the conjunct.
        let mut bound: HashSet<String> = HashSet::default();
        {
            let mut stack = vec![conjunct];
            let mut seen: HashSet<TermId> = HashSet::default();
            while let Some(t) = stack.pop() {
                if !seen.insert(t) {
                    continue;
                }
                match self.ctx.terms.get(t) {
                    TermData::Forall(vars, _, _) | TermData::Exists(vars, _, _) => {
                        bound.extend(vars.iter().map(|(n, _)| n.clone()));
                    }
                    TermData::Let(bindings, _) => {
                        bound.extend(bindings.iter().map(|(n, _)| n.clone()));
                    }
                    _ => {}
                }
                stack.extend(self.ctx.terms.children(t));
            }
        }

        // Bottom-up purity: no bound-name Var, no quantifier/let below.
        let mut pure: DetHashMap<TermId, bool> = DetHashMap::default();
        fn is_pure(
            exec: &Executor,
            t: TermId,
            bound: &HashSet<String>,
            pure: &mut DetHashMap<TermId, bool>,
        ) -> bool {
            if let Some(&p) = pure.get(&t) {
                return p;
            }
            let p = match exec.ctx.terms.get(t) {
                TermData::Var(name, _) => !bound.contains(name),
                TermData::Const(_) => true,
                TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..) => false,
                _ => exec
                    .ctx
                    .terms
                    .children(t)
                    .into_iter()
                    .all(|c| is_pure(exec, c, bound, pure)),
            };
            pure.insert(t, p);
            p
        }

        // Maximal pure non-trivial nodes, then their view values.
        let mut candidates: Vec<TermId> = Vec::new();
        {
            let mut stack = vec![conjunct];
            let mut seen: HashSet<TermId> = HashSet::default();
            while let Some(t) = stack.pop() {
                if !seen.insert(t) {
                    continue;
                }
                if is_pure(self, t, &bound, &mut pure) {
                    if !matches!(self.ctx.terms.get(t), TermData::Const(_)) {
                        candidates.push(t);
                    }
                    continue;
                }
                stack.extend(self.ctx.terms.children(t));
            }
        }
        if candidates.is_empty() {
            return conjunct;
        }
        let mut values: DetHashMap<TermId, ModelValue> = DetHashMap::default();
        {
            let Some(model) = self.last_model.as_ref() else {
                return conjunct;
            };
            let view = IndependentModelView::new(self, model);
            view.ensure_def_index();
            for &t in &candidates {
                if let EvalOutcome::Value(v) =
                    ay_model_check::evaluate_term(&self.ctx.terms, &view, t)
                {
                    values.insert(t, v);
                }
            }
        }
        if values.is_empty() {
            return conjunct;
        }

        // Rebuild, replacing each folded node by its value term.
        let mut memo: DetHashMap<TermId, TermId> = DetHashMap::default();
        self.fold_rebuild(conjunct, &values, elems, &mut memo)
    }

    /// Recursive rebuild for [`Self::quantified_gate_fold_ground_values`].
    fn fold_rebuild(
        &mut self,
        term: TermId,
        values: &DetHashMap<TermId, ModelValue>,
        elems: &mut QuantifiedGateElements,
        memo: &mut DetHashMap<TermId, TermId>,
    ) -> TermId {
        if let Some(&t) = memo.get(&term) {
            return t;
        }
        if let Some(mv) = values.get(&term) {
            let sort = self.ctx.terms.sort(term).clone();
            if let Some(value_term) =
                model_value_to_pin_term(&mut self.ctx.terms, &mv.clone(), &sort, elems)
            {
                memo.insert(term, value_term);
                return value_term;
            }
            // Unconvertible value: leave the subtree in place unchanged.
            memo.insert(term, term);
            return term;
        }
        let rebuilt = match self.ctx.terms.get(term).clone() {
            TermData::Const(_) | TermData::Var(..) => term,
            TermData::App(sym, args) => {
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&a| self.fold_rebuild(a, values, elems, memo))
                    .collect();
                if new_args == args {
                    term
                } else {
                    crate::ematching::mk_app_simplified(&mut self.ctx.terms, &sym, new_args, term)
                }
            }
            TermData::Not(inner) => {
                let ni = self.fold_rebuild(inner, values, elems, memo);
                if ni == inner {
                    term
                } else {
                    self.ctx.terms.mk_not(ni)
                }
            }
            TermData::Ite(c, t, e) => {
                let nc = self.fold_rebuild(c, values, elems, memo);
                let nt = self.fold_rebuild(t, values, elems, memo);
                let ne = self.fold_rebuild(e, values, elems, memo);
                if nc == c && nt == t && ne == e {
                    term
                } else {
                    self.ctx.terms.mk_ite(nc, nt, ne)
                }
            }
            TermData::Forall(vars, body, triggers) => {
                let nb = self.fold_rebuild(body, values, elems, memo);
                if nb == body {
                    term
                } else {
                    self.ctx.terms.mk_forall_with_triggers(vars, nb, triggers)
                }
            }
            TermData::Exists(vars, body, triggers) => {
                let nb = self.fold_rebuild(body, values, elems, memo);
                if nb == body {
                    term
                } else {
                    self.ctx.terms.mk_exists_with_triggers(vars, nb, triggers)
                }
            }
            // Let (and future variants): left in place — such nodes were
            // already excluded from folding by the purity walk.
            _ => term,
        };
        memo.insert(term, rebuilt);
        rebuilt
    }

    /// Reconstruct the PRINTER-VISIBLE interpretation of every arity>0
    /// uninterpreted function occurring in `conjunct`, exactly as
    /// `format_function_table` renders it: the resolved EUF table rows in
    /// order with quantifier-phantom rows skipped, the LAST row's result as
    /// the `else` (an empty resolved table renders the sort default). Row
    /// values are re-evaluated through the SAME independent view the gates
    /// check ground assertions with, from each row's source application
    /// (`function_table_terms`).
    ///
    /// ALL-OR-NOTHING per function (#no-fabricated-model-values): any row the
    /// printer would keep that cannot be re-evaluated and term-converted
    /// EXACTLY — or a conflicted/misaligned/oversized table — drops the whole
    /// function from the map, leaving its applications FREE in the nested
    /// solve (which can only weaken a confirm into a fail-close, never
    /// fabricate a refutation: refutes require the CLEAN flag).
    /// Cheap defer-eligibility check (#quantified-model-gate): whether
    /// `conjunct` has at least one declared arity>0 function head and NONE of
    /// its heads has a printed interpretation (no EUF function table) — the
    /// same condition the full check derives, computable without any solving
    /// when the gate budget is already exhausted.
    fn quantified_conjunct_defer_eligible(&self, conjunct: TermId) -> bool {
        let declared: HashSet<String> = self
            .ctx
            .symbol_iter()
            .filter(|(_, info)| !info.arg_sorts.is_empty())
            .map(|(name, info)| self.ctx.symbol_identity_name(name, info).to_string())
            .collect();
        let mut has_head = false;
        let mut stack = vec![conjunct];
        let mut seen: HashSet<TermId> = HashSet::default();
        let euf = self.last_model.as_ref().and_then(|m| m.euf_model.as_ref());
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            if let TermData::App(sym, args) = self.ctx.terms.get(t) {
                if !args.is_empty() && declared.contains(sym.name()) {
                    has_head = true;
                    if euf.is_some_and(|e| e.function_tables.contains_key(sym.name())) {
                        // A printed interpretation exists: not defer-eligible.
                        return false;
                    }
                }
            }
            stack.extend(self.ctx.terms.children(t));
        }
        has_head
    }

    /// Returns the interpretation map plus `defer_ok`: whether the conjunct
    /// HAS at least one uninterpreted-function head and NONE of its heads has
    /// a printed interpretation (no EUF function table).
    fn quantified_gate_uf_interps(
        &mut self,
        conjunct: TermId,
        elems: &mut QuantifiedGateElements,
    ) -> (DetHashMap<String, QuantifiedGateUfInterp>, bool) {
        let mut interps: DetHashMap<String, QuantifiedGateUfInterp> = DetHashMap::default();

        // Declared arity>0 functions and their signatures.
        let declared: HashMap<String, (Vec<Sort>, Sort)> = self
            .ctx
            .symbol_iter()
            .filter(|(_, info)| !info.arg_sorts.is_empty())
            .map(|(name, info)| {
                (
                    self.ctx.symbol_identity_name(name, info).to_string(),
                    (info.arg_sorts.clone(), info.sort.clone()),
                )
            })
            .collect();

        // Function head names occurring in the conjunct.
        let mut heads: Vec<String> = Vec::new();
        let mut stack = vec![conjunct];
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            if let TermData::App(sym, args) = self.ctx.terms.get(t) {
                if !args.is_empty()
                    && declared.contains_key(sym.name())
                    && !heads.iter().any(|h| h == sym.name())
                {
                    heads.push(sym.name().to_string());
                }
            }
            stack.extend(self.ctx.terms.children(t));
        }
        if heads.is_empty() {
            if std::env::var("AY_DEBUG_QMG").is_ok() {
                safe_eprintln!("QMG interp: no declared-function heads in conjunct");
            }
            return (interps, false);
        }

        // Phase A (immutable): re-evaluate each printer-kept row's source
        // application and argument values through the independent view.
        struct RowValues {
            name: String,
            arg_sorts: Vec<Sort>,
            result_sort: Sort,
            rows: Vec<(Vec<QmgRowVal>, QmgRowVal)>,
        }
        let mut collected: Vec<RowValues> = Vec::new();
        // Heads the gate cannot reason about symbolically AT ALL: no printed
        // table, a table the printer itself cannot resolve, or table values
        // outside the gate's term language. If EVERY head of the conjunct is
        // such, an indeterminate check defers to the certificate lane.
        let mut deferable_heads = 0usize;
        {
            let Some(model) = self.last_model.as_ref() else {
                return (interps, false);
            };
            let Some(euf) = model.euf_model.as_ref() else {
                // No EUF component at all: the printer will print NO
                // interpretation for any of these functions.
                if std::env::var("AY_DEBUG_QMG").is_ok() {
                    safe_eprintln!("QMG interp: model has no EUF component");
                }
                return (interps, true);
            };
            let view = IndependentModelView::new(self, model);
            view.ensure_def_index();
            let qmg_debug = std::env::var("AY_DEBUG_QMG").is_ok();
            // Resolve ONE raw table entry the printer's way
            // (`resolve_table_value`): `@?N` placeholders evaluate the term
            // through the printer's own evaluator (array-sorted ones through
            // the independent view, which has an array value language); `@…`
            // tokens are uninterpreted-sort elements verbatim; anything else
            // is an already-concrete literal string resolved in phase B.
            let resolve_entry = |raw: &str, sort: &Sort| -> Option<QmgRowVal> {
                if let Some(id_str) = raw.strip_prefix("@?") {
                    let id = id_str.parse::<u32>().ok()?;
                    let term_id = TermId(id);
                    if matches!(sort, Sort::Array(_)) {
                        match ay_model_check::evaluate_term(&self.ctx.terms, &view, term_id) {
                            EvalOutcome::Value(v) => return Some(QmgRowVal::Model(v)),
                            EvalOutcome::Unevaluable(_) => return None,
                        }
                    }
                    let ev = self.evaluate_term(model, term_id);
                    if matches!(ev, EvalValue::Unknown) {
                        return None;
                    }
                    return Some(QmgRowVal::Eval(ev));
                }
                if raw.starts_with('@') {
                    return Some(QmgRowVal::Token(raw.to_string()));
                }
                Some(QmgRowVal::Literal(raw.to_string()))
            };
            'next_fn: for name in &heads {
                if euf.function_table_conflicts.contains(name) {
                    if qmg_debug {
                        safe_eprintln!("QMG interp {name}: dropped (table conflict)");
                    }
                    continue;
                }
                let Some(table) = euf.function_tables.get(name) else {
                    if qmg_debug {
                        safe_eprintln!("QMG interp {name}: dropped (no table)");
                    }
                    deferable_heads += 1;
                    continue;
                };
                if table.len() > QUANTIFIED_GATE_MAX_UF_ROWS {
                    if qmg_debug {
                        safe_eprintln!("QMG interp {name}: dropped (table too large)");
                    }
                    continue;
                }
                let (arg_sorts, result_sort) = declared[name].clone();
                let mut rows: Vec<(Vec<QmgRowVal>, QmgRowVal)> = Vec::new();
                for (k, (raw_args, raw_result)) in table.iter().enumerate() {
                    // Printer-faithful phantom-row skip.
                    if self.table_entry_is_quantifier_phantom(raw_result, model)
                        || raw_args
                            .iter()
                            .any(|a| self.table_entry_is_quantifier_phantom(a, model))
                    {
                        continue;
                    }
                    if raw_args.len() != arg_sorts.len() {
                        if qmg_debug {
                            safe_eprintln!("QMG interp {name}: dropped (row {k} arity mismatch)");
                        }
                        continue 'next_fn;
                    }
                    let mut arg_values = Vec::with_capacity(raw_args.len());
                    let mut unresolvable = false;
                    for (raw, sort) in raw_args.iter().zip(arg_sorts.iter()) {
                        match resolve_entry(raw, sort) {
                            Some(v) => arg_values.push(v),
                            None => {
                                if qmg_debug {
                                    safe_eprintln!(
                                        "QMG interp {name}: unprintable (row {k} arg unresolvable: {raw})"
                                    );
                                }
                                unresolvable = true;
                                break;
                            }
                        }
                    }
                    if unresolvable {
                        deferable_heads += 1;
                        continue 'next_fn;
                    }
                    let result_value = match resolve_entry(raw_result, &result_sort) {
                        Some(v) => v,
                        None => {
                            if qmg_debug {
                                safe_eprintln!(
                                    "QMG interp {name}: unprintable (row {k} result unresolvable: {raw_result})"
                                );
                            }
                            deferable_heads += 1;
                            continue 'next_fn;
                        }
                    };
                    rows.push((arg_values, result_value));
                }
                collected.push(RowValues {
                    name: name.clone(),
                    arg_sorts,
                    result_sort,
                    rows,
                });
            }
        }

        // Phase B (mutable): convert row values to closed terms. A conversion
        // failure (value outside the gate's term language) leaves the head
        // un-substituted AND counts it deferable — the gate cannot reason
        // about it symbolically at all.
        'convert: for rv in collected {
            let mut rows: Vec<(Vec<TermId>, TermId)> = Vec::with_capacity(rv.rows.len());
            for (arg_values, result_value) in &rv.rows {
                let mut arg_terms = Vec::with_capacity(arg_values.len());
                for (mv, sort) in arg_values.iter().zip(rv.arg_sorts.iter()) {
                    match qmg_row_val_to_term(&mut self.ctx.terms, mv, sort, elems) {
                        Some(t) => arg_terms.push(t),
                        None => {
                            deferable_heads += 1;
                            continue 'convert;
                        }
                    }
                }
                let Some(result_term) =
                    qmg_row_val_to_term(&mut self.ctx.terms, result_value, &rv.result_sort, elems)
                else {
                    deferable_heads += 1;
                    continue 'convert;
                };
                rows.push((arg_terms, result_term));
            }
            // Printer semantics: last resolved row is the `else`; an empty
            // resolved table renders the sort default.
            let else_value = match rows.pop() {
                Some((_, result)) => result,
                None => {
                    match quantified_gate_default_value_term(
                        &mut self.ctx.terms,
                        &rv.result_sort,
                        elems,
                    ) {
                        Some(t) => t,
                        None => {
                            deferable_heads += 1;
                            continue 'convert;
                        }
                    }
                }
            };
            interps.insert(rv.name, QuantifiedGateUfInterp { rows, else_value });
        }
        let defer_ok = !heads.is_empty() && deferable_heads == heads.len();
        (interps, defer_ok)
    }

    /// Finite-domain binder expansion (#quantified-model-gate): rewrite every
    /// quantifier whose binders range over an exactly-enumerable finite sort
    /// (Bool, BitVec of width ≤ 6) into the equivalent conjunction
    /// (`forall`) / disjunction (`exists`) of instances, innermost-first,
    /// capped at [`QUANTIFIED_GATE_MAX_USORT_INSTANCES`] instances per
    /// quantifier (binders past the cap are kept). This is an EQUIVALENCE
    /// (the enumeration covers the whole domain), valid at any polarity.
    fn quantified_gate_expand_finite_binders(&mut self, term: TermId) -> TermId {
        let rebuilt = match self.ctx.terms.get(term).clone() {
            TermData::Const(_) | TermData::Var(..) => return term,
            TermData::App(sym, args) => {
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&a| self.quantified_gate_expand_finite_binders(a))
                    .collect();
                if new_args == args {
                    term
                } else {
                    crate::ematching::mk_app_simplified(&mut self.ctx.terms, &sym, new_args, term)
                }
            }
            TermData::Not(inner) => {
                let ni = self.quantified_gate_expand_finite_binders(inner);
                if ni == inner {
                    term
                } else {
                    self.ctx.terms.mk_not(ni)
                }
            }
            TermData::Ite(c, t, e) => {
                let nc = self.quantified_gate_expand_finite_binders(c);
                let nt = self.quantified_gate_expand_finite_binders(t);
                let ne = self.quantified_gate_expand_finite_binders(e);
                if nc == c && nt == t && ne == e {
                    term
                } else {
                    self.ctx.terms.mk_ite(nc, nt, ne)
                }
            }
            TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                let is_forall = matches!(self.ctx.terms.get(term), TermData::Forall(..));
                let original_body = body;
                let body = self.quantified_gate_expand_finite_binders(body);
                let enumerable = |sort: &Sort| -> Option<u64> {
                    match sort {
                        Sort::Bool => Some(2),
                        Sort::BitVec(w) if w.width <= 6 => Some(1u64 << w.width),
                        _ => None,
                    }
                };
                let mut kept: Vec<(String, Sort)> = Vec::new();
                let mut instances = vec![body];
                for (name, sort) in &vars {
                    // A wide BitVec binder whose matrix is vacuous outside a
                    // literal unsigned range (`∀x. x <u C ⇒ P` / `∃x. x <u C ∧ P`)
                    // quantifies EFFECTIVELY over [0, C): outside the range the
                    // forall-body is literally true (the guard disjunct) and the
                    // exists-body literally false (the guard conjunct), so the
                    // conjunction/disjunction of the in-range instances is
                    // EXACTLY the quantifier's truth — the same equivalence the
                    // small-width expansion uses, with the domain restriction
                    // supplied by the guard instead of the sort. This is the
                    // guarded pointwise-axiom shape verifier encoders emit for
                    // fixed-length collections (`∀i. i <u len ⇒ a[i] = f(i)`
                    // with len already ground-folded to a literal), whose
                    // bv2nat-mixing residue the nested solve cannot decide.
                    let domain = enumerable(sort).or_else(|| {
                        quantified_gate_guard_bounded_bv_domain(
                            &self.ctx.terms,
                            body,
                            name,
                            sort,
                            is_forall,
                        )
                    });
                    let expand = match domain {
                        Some(k)
                            if (instances.len() as u64).saturating_mul(k)
                                <= QUANTIFIED_GATE_MAX_USORT_INSTANCES as u64 =>
                        {
                            Some(k)
                        }
                        _ => None,
                    };
                    match expand {
                        Some(k) => {
                            let mut next = Vec::with_capacity(instances.len() * k as usize);
                            for v in 0..k {
                                let value_term = match sort {
                                    Sort::Bool => self.ctx.terms.mk_bool(v == 1),
                                    Sort::BitVec(w) => self
                                        .ctx
                                        .terms
                                        .mk_bitvec(num_bigint::BigInt::from(v), w.width),
                                    _ => unreachable!("enumerable() only admits Bool/BitVec"),
                                };
                                let mut subst: DetHashMap<String, TermId> = DetHashMap::default();
                                subst.insert(name.clone(), value_term);
                                for &inst in &instances {
                                    next.push(crate::ematching::subst_vars(
                                        &mut self.ctx.terms,
                                        inst,
                                        &subst,
                                    ));
                                }
                            }
                            instances = next;
                        }
                        None => kept.push((name.clone(), sort.clone())),
                    }
                }
                let combined = if instances.len() == 1 {
                    instances[0]
                } else if is_forall {
                    self.ctx.terms.mk_and(instances)
                } else {
                    self.ctx.terms.mk_or(instances)
                };
                if kept.len() == vars.len() {
                    // Nothing expanded; keep the original quantifier node
                    // (with the possibly-rewritten body).
                    if combined == original_body {
                        term
                    } else if is_forall {
                        self.ctx
                            .terms
                            .mk_forall_with_triggers(vars, combined, triggers)
                    } else {
                        self.ctx
                            .terms
                            .mk_exists_with_triggers(vars, combined, triggers)
                    }
                } else if kept.is_empty() {
                    combined
                } else if is_forall {
                    self.ctx.terms.mk_forall(kept, combined)
                } else {
                    self.ctx.terms.mk_exists(kept, combined)
                }
            }
            // Let and future variants: left unchanged.
            _ => term,
        };
        rebuilt
    }

    /// Substitute the reconstructed interpretations for every application of a
    /// mapped function in `term`, bottom-up: `f(t⃗)` becomes the first-match
    /// `ite` chain over the rows with the `else` value at the end — the exact
    /// beta-reduction of the printed `define-fun` body at `t⃗`. Returns the
    /// rewritten term and whether EVERY arity>0 declared-function application
    /// was substituted (`false` keeps the check from ever refuting/confirming
    /// on a partially-interpreted formula unless the UNSAT direction makes it
    /// sound regardless).
    fn apply_quantified_gate_uf_interps(
        &mut self,
        term: TermId,
        interps: &DetHashMap<String, QuantifiedGateUfInterp>,
        elems: &mut QuantifiedGateElements,
    ) -> (TermId, bool) {
        let _ = elems;
        let mut memo: DetHashMap<TermId, (TermId, bool)> = DetHashMap::default();
        let declared_fns: HashSet<String> = self
            .ctx
            .symbol_iter()
            .filter(|(_, info)| !info.arg_sorts.is_empty())
            .map(|(name, info)| self.ctx.symbol_identity_name(name, info).to_string())
            .collect();
        let complete = Cell::new(true);
        let result = self.rewrite_uf_apps(term, interps, &declared_fns, &mut memo, &complete, 0);
        (result, complete.get())
    }

    /// Recursive worker for [`Self::apply_quantified_gate_uf_interps`].
    fn rewrite_uf_apps(
        &mut self,
        term: TermId,
        interps: &DetHashMap<String, QuantifiedGateUfInterp>,
        declared_fns: &HashSet<String>,
        memo: &mut DetHashMap<TermId, (TermId, bool)>,
        complete: &Cell<bool>,
        depth: u32,
    ) -> TermId {
        if let Some(&(rewritten, was_complete)) = memo.get(&term) {
            if !was_complete {
                complete.set(false);
            }
            return rewritten;
        }
        if depth > 512 {
            complete.set(false);
            return term;
        }
        let before_complete = complete.get();
        complete.set(true);
        let rewritten = match self.ctx.terms.get(term).clone() {
            TermData::Const(_) | TermData::Var(..) => term,
            TermData::App(sym, args) => {
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&a| {
                        self.rewrite_uf_apps(a, interps, declared_fns, memo, complete, depth + 1)
                    })
                    .collect();
                let arity_matches = |interp: &QuantifiedGateUfInterp| {
                    interp
                        .rows
                        .iter()
                        .all(|(row_args, _)| row_args.len() == new_args.len())
                };
                if let Some(interp) = interps.get(sym.name()).filter(|i| arity_matches(i)) {
                    let mut acc = interp.else_value;
                    for (row_args, row_result) in interp.rows.iter().rev() {
                        let mut conds = Vec::with_capacity(new_args.len());
                        for (&actual, &expected) in new_args.iter().zip(row_args.iter()) {
                            conds.push(self.ctx.terms.mk_eq(actual, expected));
                        }
                        let cond = if conds.len() == 1 {
                            conds[0]
                        } else {
                            self.ctx.terms.mk_and(conds)
                        };
                        acc = self.ctx.terms.mk_ite(cond, *row_result, acc);
                    }
                    acc
                } else {
                    if !args.is_empty() && declared_fns.contains(sym.name()) {
                        // An application of a function whose printed
                        // interpretation could not be reconstructed: it stays
                        // FREE in the nested solve.
                        complete.set(false);
                    }
                    if new_args == args {
                        term
                    } else {
                        crate::ematching::mk_app_simplified(
                            &mut self.ctx.terms,
                            &sym,
                            new_args,
                            term,
                        )
                    }
                }
            }
            TermData::Not(inner) => {
                let ni =
                    self.rewrite_uf_apps(inner, interps, declared_fns, memo, complete, depth + 1);
                if ni == inner {
                    term
                } else {
                    self.ctx.terms.mk_not(ni)
                }
            }
            TermData::Ite(c, t, e) => {
                let nc = self.rewrite_uf_apps(c, interps, declared_fns, memo, complete, depth + 1);
                let nt = self.rewrite_uf_apps(t, interps, declared_fns, memo, complete, depth + 1);
                let ne = self.rewrite_uf_apps(e, interps, declared_fns, memo, complete, depth + 1);
                if nc == c && nt == t && ne == e {
                    term
                } else {
                    self.ctx.terms.mk_ite(nc, nt, ne)
                }
            }
            TermData::Forall(vars, body, triggers) => {
                let nb =
                    self.rewrite_uf_apps(body, interps, declared_fns, memo, complete, depth + 1);
                if nb == body {
                    term
                } else {
                    self.ctx.terms.mk_forall_with_triggers(vars, nb, triggers)
                }
            }
            TermData::Exists(vars, body, triggers) => {
                let nb =
                    self.rewrite_uf_apps(body, interps, declared_fns, memo, complete, depth + 1);
                if nb == body {
                    term
                } else {
                    self.ctx.terms.mk_exists_with_triggers(vars, nb, triggers)
                }
            }
            // Anything else (Let and future variants): unchanged, and the
            // rewrite is no longer known-complete.
            _ => {
                complete.set(false);
                term
            }
        };
        let was_complete = complete.get();
        memo.insert(term, (rewritten, was_complete));
        complete.set(before_complete && was_complete);
        rewritten
    }

    /// Isolated nested solve of a QUANTIFIER-FREE assertion list, with the
    /// FULL nested-solve state discipline: every piece of verdict/model/
    /// validation state the solve can perturb is saved and restored
    /// (`ctx.assertions`, `incr_theory_state`, `incr_bv_state`, `last_model`,
    /// `last_model_validated`, `last_validation_stats`, `last_unknown_reason`,
    /// `defer_model_validation`, `last_result`, `skip_model_eval`;
    /// `last_statistics` is snapshotted by the gate driver). The outer `Sat`
    /// therefore keeps its own witness on the CONFIRM leg — the nested solve
    /// can never ship a nulled/foreign model. Runs `solve_for_category`
    /// directly (below the emit funnel), so no gate/certificate/proof machinery
    /// re-enters; anything unclassifiable or undecided returns `Unknown`.
    fn quantified_gate_isolated_solve(&mut self, mut assertions: Vec<TermId>) -> SolveResult {
        if assertions
            .iter()
            .any(|&t| contains_quantifier(&self.ctx.terms, t))
        {
            return SolveResult::Unknown;
        }
        // Slice the gate budget per nested solve: one undecidable nested
        // problem must not starve the remaining conjuncts' checks.
        let saved_deadline = self.solve_deadline.get();
        let slice = Instant::now() + Duration::from_millis(500);
        self.set_deadline(match saved_deadline {
            Some(d) if d < slice => Some(d),
            _ => Some(slice),
        });
        // The model-table expansion used by the quantified gate naturally
        // produces obligations of the form
        //
        //   not (= p (and p q_1 ... q_n)).
        //
        // Sending that spelling directly through Tseitin + LIA makes the
        // solver enumerate hundreds of mutually exclusive disequalities.  In
        // the mid-range Bool-UF certificate this occasionally consumed the
        // entire 500 ms fail-closed slice under host load even though the
        // obligation has the exact Boolean normal form `p /\ !(and q_i)`.
        // Normalize only this top-level, equivalence-preserving absorption
        // identity before theory dispatch.  It exposes `p` as a unit; the
        // ordinary LIA VariableSubstitution pass then folds the residue to
        // false deterministically.  The slice itself stays unchanged, and
        // every unrecognized shape still follows the existing Unknown path.
        // DT certificate search consumes similarly shaped Int-returning
        // tables, but relies on their original Boolean skeleton to complete a
        // model.  Keep this UFLIA completeness aid out of every context with
        // datatype declarations; the target Bool-UF/Int lane has none.
        let has_datatype_declarations = self.ctx.datatype_iter().next().is_some();
        if !has_datatype_declarations {
            for assertion in &mut assertions {
                *assertion = quantified_gate_simplify_negated_absorbed_bool_eq(
                    &mut self.ctx.terms,
                    *assertion,
                );
            }
        }
        // Same Nelson-Oppen purification the top-level pipeline applies —
        // skolem UF applications inside arithmetic stay related to it.
        crate::executor::purify_int_uf_arith::purify_int_uf_arith(
            &mut self.ctx.terms,
            &mut assertions,
        );
        let (category, _) = self.detect_logic_category(&assertions);
        if matches!(category, LogicCategory::Other) {
            // The slice is nested-solve-local.  Even an unsupported category
            // must not leak the shortened deadline into the outer solve.
            self.set_deadline(saved_deadline);
            return SolveResult::Unknown;
        }

        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, assertions);
        let saved_theory_state = self.incr_theory_state.take();
        let saved_bv_state = self.incr_bv_state.take();
        let saved_model = self.last_model.take();
        let saved_model_validated = self.last_model_validated;
        let saved_validation_stats = self.last_validation_stats.take();
        let saved_unknown_reason = self.last_unknown_reason;
        let saved_defer = self.defer_model_validation;
        let saved_last_result = self.last_result.take();
        let saved_skip_model_eval = self.skip_model_eval;
        // A nested UNSAT builds a proof of the NESTED formula; without this
        // save/restore the outer (kept-`Sat`) solve would carry a foreign
        // `last_proof` that a later Alethe export could surface.
        let saved_proof = self.last_proof.take();
        let saved_proof_overrides = self.last_proof_term_overrides.take();
        let saved_proof_quality = self.last_proof_quality.take();
        let saved_qfax_refinement = self.qfax_refinement_clause.take();
        let saved_rejected_array = self.last_rejected_array_assertion.take();
        self.defer_model_validation = false;

        let result = self.solve_for_category(category);

        self.ctx.assertions = saved_assertions;
        self.incr_theory_state = saved_theory_state;
        self.incr_bv_state = saved_bv_state;
        self.last_model = saved_model;
        self.last_model_validated = saved_model_validated;
        self.last_validation_stats = saved_validation_stats;
        self.last_unknown_reason = saved_unknown_reason;
        self.defer_model_validation = saved_defer;
        self.last_result = saved_last_result;
        self.skip_model_eval = saved_skip_model_eval;
        self.last_proof = saved_proof;
        self.last_proof_term_overrides = saved_proof_overrides;
        self.last_proof_quality = saved_proof_quality;
        self.qfax_refinement_clause = saved_qfax_refinement;
        self.last_rejected_array_assertion = saved_rejected_array;
        self.set_deadline(saved_deadline);

        result.unwrap_or(SolveResult::Unknown)
    }

    /// Build the MODEL PINS for `conjunct`: one `(= leaf <value-term>)` per
    /// free constant leaf whose independent-gate model value is representable
    /// as a closed term. `total` iff EVERY free symbol of the conjunct was
    /// pinned exactly — no arity>0 uninterpreted function, no unrepresentable
    /// value (datatype, sequence, FP, algebraic real), nothing the evaluator
    /// left unevaluable. Uninterpreted-sort element values pin to the shared
    /// per-token element constants in `elems`. Fill-only: never fabricates a
    /// value (an unpinnable leaf is left FREE, which can only weaken a
    /// confirm into a fail-close, never invent one).
    /// `exclude` lists gate-created constants (skolems, universe elements)
    /// that must stay FREE: they are not model symbols, and the evaluator
    /// would otherwise default-value them into spurious pins (a pinned skolem
    /// turns `∃i.¬M[i]` into `¬M[0]` — a bogus confirm).
    fn quantified_gate_model_pins(
        &mut self,
        conjunct: TermId,
        elems: &mut QuantifiedGateElements,
        exclude: &HashSet<TermId>,
    ) -> QuantifiedGatePins {
        // Names of declared arity>0 functions (applications of these are UF
        // applications the pin set cannot express).
        let declared_fns: HashSet<String> = self
            .ctx
            .symbol_iter()
            .filter(|(_, info)| !info.arg_sorts.is_empty())
            .map(|(name, info)| self.ctx.symbol_identity_name(name, info).to_string())
            .collect();

        let mut leaves: Vec<TermId> = Vec::new();
        let mut total = true;
        let mut scope: Vec<String> = Vec::new();
        let mut visits = 0usize;
        self.collect_quantified_gate_leaves(
            conjunct,
            &declared_fns,
            &mut scope,
            &mut leaves,
            &mut total,
            &mut visits,
        );
        // Gate-created constants stay FREE — they are not model symbols.
        leaves.retain(|leaf| !exclude.contains(leaf));

        // Evaluate each leaf under the SAME independent view the printers'
        // reconstruction path uses, then convert to pin terms.
        let mut leaf_values: Vec<(TermId, ModelValue, Sort)> = Vec::new();
        {
            let Some(model) = self.last_model.as_ref() else {
                return QuantifiedGatePins {
                    equalities: Vec::new(),
                    total: false,
                };
            };
            let view = IndependentModelView::new(self, model);
            view.ensure_def_index();
            for &leaf in &leaves {
                match ay_model_check::evaluate_term(&self.ctx.terms, &view, leaf) {
                    EvalOutcome::Value(mv) => {
                        leaf_values.push((leaf, mv, self.ctx.terms.sort(leaf).clone()));
                    }
                    EvalOutcome::Unevaluable(_) => total = false,
                    #[allow(unreachable_patterns)]
                    _ => total = false,
                }
            }
        }
        let mut equalities = Vec::new();
        for (leaf, mv, sort) in leaf_values {
            match model_value_to_pin_term(&mut self.ctx.terms, &mv, &sort, elems) {
                Some(value_term) => {
                    equalities.push(self.ctx.terms.mk_eq(leaf, value_term));
                }
                None => total = false,
            }
        }
        QuantifiedGatePins { equalities, total }
    }

    /// Scope-tracked free-leaf walk for the pin builder. Pushes every free
    /// constant leaf (a `Var`, or a nullary application) into `leaves`; clears
    /// `total` on any construct the pin set cannot express exactly (arity>0
    /// declared UF application, non-empty `let`, or a walk-budget overrun).
    #[allow(clippy::too_many_arguments)]
    fn collect_quantified_gate_leaves(
        &self,
        term: TermId,
        declared_fns: &HashSet<String>,
        scope: &mut Vec<String>,
        leaves: &mut Vec<TermId>,
        total: &mut bool,
        visits: &mut usize,
    ) {
        *visits += 1;
        if *visits > 20_000 {
            *total = false;
            return;
        }
        match self.ctx.terms.get(term).clone() {
            TermData::Const(_) => {}
            TermData::Var(name, _) => {
                if !scope.iter().any(|s| s == &name) && !leaves.contains(&term) {
                    leaves.push(term);
                }
            }
            TermData::App(sym, args) => {
                if args.is_empty() {
                    if !leaves.contains(&term) {
                        leaves.push(term);
                    }
                    return;
                }
                if declared_fns.contains(sym.name()) {
                    // An arity>0 UF application: its interpretation cannot be
                    // expressed as an equality pin.
                    *total = false;
                }
                for &arg in &args {
                    self.collect_quantified_gate_leaves(
                        arg,
                        declared_fns,
                        scope,
                        leaves,
                        total,
                        visits,
                    );
                }
            }
            TermData::Not(inner) => {
                self.collect_quantified_gate_leaves(
                    inner,
                    declared_fns,
                    scope,
                    leaves,
                    total,
                    visits,
                );
            }
            TermData::Ite(c, t, e) => {
                for child in [c, t, e] {
                    self.collect_quantified_gate_leaves(
                        child,
                        declared_fns,
                        scope,
                        leaves,
                        total,
                        visits,
                    );
                }
            }
            TermData::Let(bindings, body) => {
                if !bindings.is_empty() {
                    // An unexpanded let binds names the walk cannot faithfully
                    // resolve; keep collecting best-effort but never claim a
                    // total substitution.
                    *total = false;
                }
                for (_, value) in &bindings {
                    self.collect_quantified_gate_leaves(
                        *value,
                        declared_fns,
                        scope,
                        leaves,
                        total,
                        visits,
                    );
                }
                let depth = scope.len();
                scope.extend(bindings.iter().map(|(n, _)| n.clone()));
                self.collect_quantified_gate_leaves(
                    body,
                    declared_fns,
                    scope,
                    leaves,
                    total,
                    visits,
                );
                scope.truncate(depth);
            }
            TermData::Forall(vars, body, _) | TermData::Exists(vars, body, _) => {
                let depth = scope.len();
                scope.extend(vars.iter().map(|(n, _)| n.clone()));
                self.collect_quantified_gate_leaves(
                    body,
                    declared_fns,
                    scope,
                    leaves,
                    total,
                    visits,
                );
                scope.truncate(depth);
            }
            _ => {
                *total = false;
            }
        }
    }

    /// Whether any quantifier binder inside `term` ranges over a sort with an
    /// uninterpreted component (uninterpreted sort or datatype, directly or
    /// inside an array/sequence sort). Such a binder's domain in the EMITTED
    /// model is the model's finite universe, which a nested solve is free to
    /// enlarge — so a nested SAT over it can neither confirm an existential
    /// nor refute a universal (see `check_quantified_conjunct_against_model`)
    /// unless the binder was expanded over that universe first.
    fn term_has_uninterpreted_sort_binder(&self, term: TermId) -> bool {
        let mut stack = vec![term];
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            if let TermData::Forall(vars, _, _) | TermData::Exists(vars, _, _) =
                self.ctx.terms.get(t)
            {
                if vars.iter().any(|(_, s)| sort_mentions_uninterpreted(s)) {
                    return true;
                }
            }
            stack.extend(self.ctx.terms.children(t));
        }
        false
    }
}

/// Return the integer variable selected by a point equality such as `x = 7`.
fn quantified_gate_int_point_variable(terms: &TermStore, term: TermId) -> Option<TermId> {
    let TermData::App(equality, args) = terms.get(term) else {
        return None;
    };
    if equality.name() != "=" || args.len() != 2 {
        return None;
    }
    for (variable, point) in [(args[0], args[1]), (args[1], args[0])] {
        if matches!(terms.get(variable), TermData::Var(..))
            && terms.sort(variable) == &Sort::Int
            && matches!(terms.get(point), TermData::Const(ay_core::Constant::Int(_)))
        {
            return Some(variable);
        }
    }
    None
}

/// Normalize the specific large integer-point Boolean-table residue emitted by
/// a printer-table quantified-model check:
///
/// ```text
/// !((x = k) = ((x = k) /\ (x != k_1) /\ ...))
///     <=> (x = k) /\ !((x != k_1) /\ ...)
/// ```
///
/// Outer and point equality are symmetric.  This is deliberately a top-level
/// gate-obligation rewrite rather than a general distributive simplifier: it
/// is linear in the already-materialized table, cannot expand the term DAG,
/// and leaves every other shape byte-for-byte unchanged.  Requiring the exact
/// integer point-table grammar prevents an equivalent rewrite from perturbing
/// unrelated certificate search lanes.
fn quantified_gate_simplify_negated_absorbed_bool_eq(
    terms: &mut TermStore,
    assertion: TermId,
) -> TermId {
    // Small absorption residues are cheap for the existing gate solver and,
    // more importantly, retain useful search structure for the DT model
    // certificate fallback.  The timeout this rewrite addresses is specific
    // to printer tables with hundreds of leaves, so keep the intervention
    // explicitly in that high-fanout lane.
    const MIN_TABLE_FANOUT: usize = 256;

    let TermData::Not(inner) = terms.get(assertion).clone() else {
        return assertion;
    };
    let TermData::App(eq, eq_args) = terms.get(inner).clone() else {
        return assertion;
    };
    if eq.name() != "=" || eq_args.len() != 2 || terms.sort(eq_args[0]) != &Sort::Bool {
        return assertion;
    }

    for (pivot, compound) in [(eq_args[0], eq_args[1]), (eq_args[1], eq_args[0])] {
        let TermData::App(connective, args) = terms.get(compound).clone() else {
            continue;
        };
        if connective.name() != "and" {
            continue;
        }
        if args.len() < MIN_TABLE_FANOUT {
            continue;
        }
        let Some(pivot_index) = args.iter().position(|&arg| arg == pivot) else {
            continue;
        };
        let Some(table_variable) = quantified_gate_int_point_variable(terms, pivot) else {
            continue;
        };
        let mut rest = args;
        let _ = rest.remove(pivot_index);
        if !rest.iter().all(|&entry| {
            let TermData::Not(point) = terms.get(entry) else {
                return false;
            };
            quantified_gate_int_point_variable(terms, *point) == Some(table_variable)
        }) {
            continue;
        }
        let residue = terms.mk_and(rest);
        let not_residue = terms.mk_not(residue);
        return terms.mk_and(vec![pivot, not_residue]);
    }

    assertion
}

/// Outcome of validating one quantified assertion conjunct against the
/// emitted model (#quantified-model-gate).
enum QuantifiedModelCheck {
    /// Proved TRUE under the emitted model.
    Confirmed,
    /// Proved FALSE under the emitted model. `clean` marks a
    /// total-substitution, no-uninterpreted-sort-binder refutation — a
    /// concrete counterexample instance worth the loud soundness alarm.
    Refuted { clean: bool },
    /// Neither provable nor refutable within the gate's means/budget —
    /// fail closed.
    Indeterminate(&'static str),
    /// Indeterminate, but the emitted witness cannot falsify the conjunct at
    /// all — every uninterpreted-function head lacks a printed
    /// interpretation, or the (substituted) conjunct is CLOSED (no model
    /// symbols left) — so the verdict defers to the machinery that minted it
    /// (exactly HEAD's trust level; refutation outcomes are never converted
    /// to this).
    Deferred,
}

/// The model pins for one quantified conjunct: equality terms forcing each
/// representable free leaf to its exact emitted-model value, plus whether the
/// pin set is TOTAL over the conjunct's free symbols.
struct QuantifiedGatePins {
    equalities: Vec<TermId>,
    total: bool,
}

/// Cap on EUF table rows per reconstructed function interpretation
/// (#quantified-model-gate) — a larger table drops the function from the
/// substitution map (fail-close direction only). Generous: the reconstruction
/// is one linear `ite` chain per application, and a fail-close here downgrades
/// a genuine `sat`.
const QUANTIFIED_GATE_MAX_UF_ROWS: usize = 512;

/// Cap on total instances produced by expanding uninterpreted-sort binders
/// over the model's finite universes (#quantified-model-gate).
const QUANTIFIED_GATE_MAX_USORT_INSTANCES: usize = 64;

/// One reconstructed printer-visible function interpretation
/// (#quantified-model-gate): the resolved table rows IN ORDER minus the last
/// (whose result is `else_value`), exactly `format_function_table`'s
/// first-match `ite` chain.
struct QuantifiedGateUfInterp {
    rows: Vec<(Vec<TermId>, TermId)>,
    else_value: TermId,
}

/// One resolved raw EUF-table entry (#quantified-model-gate), phase-A form —
/// exactly what `resolve_table_value` would print, before term conversion.
enum QmgRowVal {
    /// An `@?N` placeholder resolved through the independent view (arrays).
    Model(ModelValue),
    /// An `@?N` placeholder resolved through the printer's own evaluator.
    Eval(EvalValue),
    /// An `@Sort!n` uninterpreted-sort element token, verbatim.
    Token(String),
    /// An already-concrete literal string from EUF extraction.
    Literal(String),
}

/// Convert a resolved raw table entry into a closed term of `sort`. `None`
/// for anything the term language cannot express exactly — the caller then
/// drops the whole function from the substitution map (fail-close direction
/// only, #no-fabricated-model-values).
fn qmg_row_val_to_term(
    terms: &mut TermStore,
    val: &QmgRowVal,
    sort: &Sort,
    elems: &mut QuantifiedGateElements,
) -> Option<TermId> {
    match val {
        QmgRowVal::Model(mv) => model_value_to_pin_term(terms, mv, sort, elems),
        QmgRowVal::Eval(ev) => match (ev, sort) {
            (EvalValue::Bool(b), Sort::Bool) => Some(terms.mk_bool(*b)),
            (EvalValue::Rational(r), Sort::Int) if r.is_integer() => {
                Some(terms.mk_int(r.to_integer()))
            }
            (EvalValue::Rational(r), Sort::Real) => Some(terms.mk_rational(r.clone())),
            (EvalValue::BitVec { value, width }, Sort::BitVec(_)) => {
                Some(terms.mk_bitvec(value.clone(), *width))
            }
            (EvalValue::String(s), Sort::String) => Some(terms.mk_string(s.clone())),
            (EvalValue::Element(token), Sort::Uninterpreted(_)) => {
                Some(elems.term_for(terms, token, sort.clone()))
            }
            _ => None,
        },
        QmgRowVal::Token(token) => match sort {
            Sort::Uninterpreted(_) => Some(elems.term_for(terms, token, sort.clone())),
            _ => None,
        },
        QmgRowVal::Literal(raw) => match sort {
            Sort::Bool => match raw.as_str() {
                "true" => Some(terms.mk_bool(true)),
                "false" => Some(terms.mk_bool(false)),
                _ => None,
            },
            Sort::Int => {
                let stripped = raw
                    .strip_prefix("(- ")
                    .and_then(|s| s.strip_suffix(')'))
                    .map(|s| format!("-{s}"));
                let text = stripped.as_deref().unwrap_or(raw.as_str());
                text.parse::<num_bigint::BigInt>()
                    .ok()
                    .map(|i| terms.mk_int(i))
            }
            Sort::BitVec(w) => {
                if let Some(bits) = raw.strip_prefix("#b") {
                    num_bigint::BigInt::parse_bytes(bits.as_bytes(), 2)
                        .map(|v| terms.mk_bitvec(v, w.width))
                } else if let Some(hex) = raw.strip_prefix("#x") {
                    num_bigint::BigInt::parse_bytes(hex.as_bytes(), 16)
                        .map(|v| terms.mk_bitvec(v, w.width))
                } else {
                    None
                }
            }
            _ => None,
        },
    }
}

/// Shared uninterpreted-sort element context for one conjunct check
/// (#quantified-model-gate): each model universe token maps to ONE fresh
/// constant, reused across interpretation rows, binder expansion, and pins, so
/// token identity is preserved; `distinct_assertions` then pins the tokens
/// pairwise-distinct exactly as the emitted model holds them (never letting a
/// nested solve merge two universe elements into a spurious refutation).
#[derive(Default)]
struct QuantifiedGateElements {
    by_token: DetHashMap<String, TermId>,
    by_sort: DetHashMap<String, Vec<TermId>>,
}

impl QuantifiedGateElements {
    /// The shared constant for `token` of uninterpreted sort `sort`
    /// (created fresh on first use).
    fn term_for(&mut self, terms: &mut TermStore, token: &str, sort: Sort) -> TermId {
        if let Some(&t) = self.by_token.get(token) {
            return t;
        }
        let sort_name = match &sort {
            Sort::Uninterpreted(name) => name.clone(),
            _ => String::new(),
        };
        let fresh = terms.mk_fresh_var(&format!("qmg!elem!{token}"), sort);
        self.by_token.insert(token.to_string(), fresh);
        self.by_sort.entry(sort_name).or_default().push(fresh);
        fresh
    }

    /// Every element constant created so far.
    fn all_terms(&self) -> HashSet<TermId> {
        self.by_token.values().copied().collect()
    }

    /// One `distinct` assertion per sort with two or more used elements.
    fn distinct_assertions(&self, terms: &mut TermStore) -> Vec<TermId> {
        let mut out = Vec::new();
        let mut sorts: Vec<&String> = self.by_sort.keys().collect();
        sorts.sort();
        for sort_name in sorts {
            let elems = &self.by_sort[sort_name];
            if elems.len() >= 2 {
                out.push(terms.mk_distinct(elems.clone()));
            }
        }
        out
    }
}

/// Effective finite domain of a wide BitVec binder whose matrix is VACUOUS
/// outside a literal unsigned range (#quantified-model-gate). Returns
/// `Some(k)` — domain `[0, k)` — exactly when:
///
/// - `is_forall` and the body is (an `or` containing) a disjunct
///   `(not (bvult x C))` / `(not (bvule x C))` for the binder `x` and a
///   same-width bitvector literal `C`: every out-of-range instance of the
///   body is literally TRUE through that disjunct, so
///   `∀x. body ⟺ ⋀_{v<k} body[x:=v]` (k = C, resp. C+1); or
/// - `!is_forall` and the body is (an `and` containing) a conjunct
///   `(bvult x C)` / `(bvule x C)`: every out-of-range instance is literally
///   FALSE, so `∃x. body ⟺ ⋁_{v<k} body[x:=v]`.
///
/// Both directions are pure logical equivalences of the quantified formula —
/// valid under any surrounding polarity — so expanding on them can never
/// change the conjunct's truth, only make it decidable. The guard shape is
/// what verifier encoders emit for fixed-length collections
/// (`∀i. i <u len ⇒ a[i] = f(i)` with `len` a literal after ground folding).
/// Anything else — symbolic bound, width mismatch, guard on a different
/// variable — returns `None` and the binder is kept (fail-closed as before).
fn quantified_gate_guard_bounded_bv_domain(
    terms: &TermStore,
    body: TermId,
    name: &str,
    sort: &Sort,
    is_forall: bool,
) -> Option<u64> {
    use ay_core::term::{Constant, Symbol};
    let Sort::BitVec(w) = sort else {
        return None;
    };
    let width = w.width;
    // `x OP C` with `x` the binder and `C` a same-width literal; returns the
    // exclusive domain bound (bvult → C, bvule → C+1).
    let bound_of = |t: TermId| -> Option<u64> {
        let TermData::App(Symbol::Named(op), args) = terms.get(t) else {
            return None;
        };
        if args.len() != 2 || !matches!(op.as_str(), "bvult" | "bvule") {
            return None;
        }
        let TermData::Var(vn, _) = terms.get(args[0]) else {
            return None;
        };
        if vn != name {
            return None;
        }
        let TermData::Const(Constant::BitVec { value, width: cw }) = terms.get(args[1]) else {
            return None;
        };
        if *cw != width {
            return None;
        }
        let c = u64::try_from(value.clone()).ok()?;
        match op.as_str() {
            "bvult" => Some(c),
            _ => c.checked_add(1),
        }
    };
    if is_forall {
        let disjuncts: Vec<TermId> = match terms.get(body) {
            TermData::App(Symbol::Named(op), args) if op == "or" => args.clone(),
            _ => vec![body],
        };
        disjuncts.into_iter().find_map(|d| match terms.get(d) {
            TermData::Not(inner) => bound_of(*inner),
            _ => None,
        })
    } else {
        let conjuncts: Vec<TermId> = match terms.get(body) {
            TermData::App(Symbol::Named(op), args) if op == "and" => args.clone(),
            _ => vec![body],
        };
        conjuncts.into_iter().find_map(bound_of)
    }
}

/// STRICT model-independence for the quantified gate's CLOSED-sentence
/// deferral (#quantified-model-gate): `true` only when the ORIGINAL conjunct
/// is a genuinely closed sentence over fixed-interpretation domains —
/// * every `Var` occurrence is bound by an enclosing quantifier of the
///   conjunct itself (declared 0-arity constants are interned as `Var`, so
///   any free `Var` is a model symbol);
/// * every application head is a TOTAL builtin connective / arithmetic
///   operator from the whitelist below (no uninterpreted functions, no
///   arrays, no theory ops, and no `div`/`mod`/`/`, whose by-zero value is
///   per-model — same reasoning as the quantifier-loop precheck's
///   `is_builtin_operator`);
/// * every binder sort is `Bool`/`Int`/`Real`/`BitVec` (an
///   uninterpreted-sort binder makes the sentence's truth depend on the
///   model's carrier cardinality — `∀ x y : U. x = y` is true exactly in
///   singleton carriers).
///
/// This predicate MUST be evaluated on the conjunct BEFORE any
/// UF-interpretation substitution and BEFORE ground-value folding:
/// substitution pours the printed witness's content into the term, so "no
/// model symbol occurs AFTER substitution" is exactly backwards — the
/// substituted sentence became closed BECAUSE the witness was injected, and
/// its falsity IS the witness's falsity (the auflia-model escape class:
/// `∀x∃y. f(y) = x` with a printed `f` folds to a symbol-free sentence whose
/// truth is precisely the claim under test). Deferring on such a sentence
/// ships an unvalidated model.
///
/// Conservative in every direction: an unknown operator, an `Indexed`
/// symbol, a `Let`, an over-budget walk, or any future term kind returns
/// `false` — the caller then fails closed to Indeterminate (never a wrong
/// verdict, only a possible sat→unknown downgrade).
fn quantified_gate_model_independent(terms: &TermStore, conjunct: TermId) -> bool {
    use ay_core::term::Symbol;
    /// Total, model-independent operators only.
    fn allowed_head(name: &str) -> bool {
        matches!(
            name,
            "and"
                | "or"
                | "not"
                | "=>"
                | "xor"
                | "="
                | "distinct"
                | "ite"
                | "+"
                | "-"
                | "*"
                | "abs"
                | "<"
                | "<="
                | ">"
                | ">="
                | "true"
                | "false"
        )
    }
    fn fixed_sort(sort: &Sort) -> bool {
        matches!(sort, Sort::Bool | Sort::Int | Sort::Real | Sort::BitVec(_))
    }
    enum Frame {
        Enter(TermId),
        Exit(Vec<String>),
    }
    // Scoped multiset of active binder names. No visited-set: boundness of a
    // shared subterm depends on the scope it is reached through, so each
    // path must be walked (bounded by the budget below).
    let mut bound: HashMap<String, usize> = HashMap::new();
    let mut stack = vec![Frame::Enter(conjunct)];
    let mut budget = 100_000usize;
    while let Some(frame) = stack.pop() {
        match frame {
            Frame::Exit(names) => {
                for name in names {
                    match bound.get_mut(&name) {
                        Some(n) if *n > 1 => *n -= 1,
                        _ => {
                            bound.remove(&name);
                        }
                    }
                }
            }
            Frame::Enter(t) => {
                if budget == 0 {
                    return false;
                }
                budget -= 1;
                match terms.get(t) {
                    TermData::Const(_) => {}
                    TermData::Var(name, _) => {
                        if !bound.contains_key(name) {
                            return false;
                        }
                    }
                    TermData::App(sym, args) => {
                        if !matches!(sym, Symbol::Named(_)) {
                            return false;
                        }
                        // `div`/`mod`/`rem` are fixed theory functions ONLY
                        // with a nonzero literal divisor: SMT-LIB leaves
                        // division-by-zero uninterpreted, so a symbolic or
                        // zero divisor makes the sentence's truth depend on
                        // a structure choice — conservatively model-DEPENDENT.
                        let divlike = matches!(sym.name(), "div" | "mod" | "rem");
                        if divlike {
                            use ay_core::term::Constant;
                            use num_traits::Zero;
                            let nonzero_lit_divisor = args.len() == 2
                                && matches!(
                                    terms.get(args[1]),
                                    TermData::Const(Constant::Int(v)) if !v.is_zero()
                                );
                            if !nonzero_lit_divisor {
                                return false;
                            }
                        } else if !allowed_head(sym.name()) {
                            return false;
                        }
                        stack.extend(args.iter().map(|&a| Frame::Enter(a)));
                    }
                    TermData::Not(inner) => stack.push(Frame::Enter(*inner)),
                    TermData::Ite(c, a, b) => {
                        stack.push(Frame::Enter(*c));
                        stack.push(Frame::Enter(*a));
                        stack.push(Frame::Enter(*b));
                    }
                    TermData::Forall(vars, body, _) | TermData::Exists(vars, body, _) => {
                        if !vars.iter().all(|(_, s)| fixed_sort(s)) {
                            return false;
                        }
                        let names: Vec<String> = vars.iter().map(|(n, _)| n.clone()).collect();
                        for name in &names {
                            *bound.entry(name.clone()).or_insert(0) += 1;
                        }
                        // LIFO: the body subtree drains fully before the
                        // Exit frame closes the scope.
                        stack.push(Frame::Exit(names));
                        stack.push(Frame::Enter(*body));
                    }
                    // `Let` should not survive elaboration; any other or
                    // future term kind is unclassified — conservatively
                    // model-DEPENDENT.
                    _ => return false,
                }
            }
        }
    }
    true
}

/// Whether `sort` mentions an uninterpreted component (uninterpreted sort or
/// datatype, directly or inside an array/sequence sort).
fn sort_mentions_uninterpreted(sort: &Sort) -> bool {
    match sort {
        Sort::Uninterpreted(_) | Sort::Datatype(_) => true,
        Sort::Array(arr) => {
            sort_mentions_uninterpreted(&arr.index_sort)
                || sort_mentions_uninterpreted(&arr.element_sort)
        }
        Sort::Seq(elem) => sort_mentions_uninterpreted(elem),
        _ => false,
    }
}

/// The sort-default value term the printer renders for an EMPTY resolved
/// function table (`format_default_value` semantics), or `None` for sorts
/// whose default the gate does not reconstruct (fail-close direction only).
fn quantified_gate_default_value_term(
    terms: &mut TermStore,
    sort: &Sort,
    elems: &mut QuantifiedGateElements,
) -> Option<TermId> {
    match sort {
        Sort::Bool => Some(terms.mk_bool(false)),
        Sort::Int => Some(terms.mk_int(num_bigint::BigInt::from(0))),
        Sort::Real => {
            Some(terms.mk_rational(num_rational::BigRational::from(num_bigint::BigInt::from(0))))
        }
        Sort::String => Some(terms.mk_string(String::new())),
        Sort::BitVec(w) => Some(terms.mk_bitvec(num_bigint::BigInt::from(0), w.width)),
        Sort::Array(arr) => {
            let default = quantified_gate_default_value_term(terms, &arr.element_sort, elems)?;
            Some(terms.mk_const_array(arr.index_sort.clone(), default))
        }
        Sort::Uninterpreted(name) => {
            let token = format!("@{name}!0");
            Some(elems.term_for(terms, &token, sort.clone()))
        }
        _ => None,
    }
}

/// Convert an independent-gate [`ModelValue`] into a closed term of `sort`,
/// for use in a model-pin equality or a reconstructed interpretation row.
/// Uninterpreted-sort elements map to the shared per-token constants in
/// `elems`. `None` for values the term language cannot express exactly
/// (datatypes, sequences, FP) — the caller then leaves the leaf FREE and
/// clears `total`, which can only weaken a confirm into a fail-close
/// (#no-fabricated-model-values).
fn model_value_to_pin_term(
    terms: &mut TermStore,
    mv: &ModelValue,
    sort: &Sort,
    elems: &mut QuantifiedGateElements,
) -> Option<TermId> {
    match (mv, sort) {
        (ModelValue::Bool(b), _) => Some(terms.mk_bool(*b)),
        (ModelValue::Int(i), Sort::Real) => {
            Some(terms.mk_rational(num_rational::BigRational::from(i.clone())))
        }
        (ModelValue::Int(i), _) => Some(terms.mk_int(i.clone())),
        (ModelValue::Real(r), Sort::Int) if r.is_integer() => Some(terms.mk_int(r.to_integer())),
        (ModelValue::Real(r), _) => Some(terms.mk_rational(r.clone())),
        (ModelValue::BitVec { width, value }, _) => Some(terms.mk_bitvec(value.clone(), *width)),
        (ModelValue::Str(s), Sort::String) => Some(terms.mk_string(s.clone())),
        (ModelValue::Uninterpreted(token), Sort::Uninterpreted(_)) => {
            Some(elems.term_for(terms, token, sort.clone()))
        }
        (ModelValue::Array(av), Sort::Array(arr)) => {
            let default = model_value_to_pin_term(terms, &av.default, &arr.element_sort, elems)?;
            let mut acc = terms.mk_const_array(arr.index_sort.clone(), default);
            // Oldest-first entries; applying stores in order preserves the
            // newest-wins select semantics.
            for (idx, val) in &av.store {
                let index_term = model_value_to_pin_term(terms, idx, &arr.index_sort, elems)?;
                let value_term = model_value_to_pin_term(terms, val, &arr.element_sort, elems)?;
                acc = terms.mk_store(acc, index_term, value_term);
            }
            Some(acc)
        }
        _ => None,
    }
}

/// Sort classification for the authoritative-ground fragment walk.
#[derive(Clone, Copy, PartialEq, Eq)]
enum SortClass {
    /// A scalar the evaluator commits to a concrete value (Bool/Int/Real/BV/
    /// uninterpreted element/char/finite-domain).
    Scalar,
    /// An array or datatype container (only allowed as a `select`'s array
    /// operand).
    Container,
    /// FP / strings / sequences / regex — ground evaluation is incomplete.
    NonAuthoritative,
}

#[cfg(test)]
mod tests {
    use ay_core::kani_compat::DetHashMap;
    use ay_frontend::parse;
    use ay_lia::LiaModel;
    use num_bigint::BigInt;

    use super::*;

    /// Solve `input` through the full executor pipeline (gate included).
    fn solved(input: &str) -> (Executor, Vec<String>) {
        let commands = parse(input).expect("valid SMT-LIB input");
        let mut exec = Executor::new();
        let outputs = exec.execute_all(&commands).expect("execute succeeds");
        (exec, outputs)
    }

    /// A model over ONLY the given LIA assignments (every other sub-model
    /// empty), used to synthetically replace the solver's real witness.
    fn synthetic_lia_model(values: &[(TermId, i64)]) -> Model {
        let mut lia = DetHashMap::default();
        for &(t, v) in values {
            lia.insert(t, BigInt::from(v));
        }
        Model {
            sat_model: vec![],
            term_to_var: DetHashMap::default(),
            bool_overrides: DetHashMap::default(),
            euf_model: None,
            array_model: None,
            lra_model: None,
            lia_model: Some(LiaModel { values: lia }),
            bv_model: None,
            fp_model: None,
            string_model: None,
            seq_model: None,
            completed_values: DetHashMap::default(),
            dt_ground: DetHashMap::default(),
            dt_pins: DetHashMap::default(),
        }
    }

    /// The post-UF-substitution obligation produced by the mid-range Bool-UF
    /// discharge: `P(v)`'s printed table says true only at 300, while its
    /// pointwise definition says exactly `v = 300`.
    fn midrange_bool_uf_gate_obligation(exec: &mut Executor) -> TermId {
        let q = exec.ctx.terms.mk_fresh_var("qmg!stress", Sort::Int);
        let three_hundred = exec.ctx.terms.mk_int(BigInt::from(300));
        let pivot = exec.ctx.terms.mk_eq(three_hundred, q);
        let mut table = Vec::with_capacity(301);
        table.push(pivot);
        for value in 0..300 {
            let value = exec.ctx.terms.mk_int(BigInt::from(value));
            let equality = exec.ctx.terms.mk_eq(value, q);
            table.push(exec.ctx.terms.mk_not(equality));
        }
        let table = exec.ctx.terms.mk_and(table);
        let definition_matches_table = exec.ctx.terms.mk_eq(pivot, table);
        exec.ctx.terms.mk_not(definition_matches_table)
    }

    /// Regression for the E4/E5 discharge timeout: the same valid table
    /// obligation must prove UNSAT repeatedly inside the unchanged 500 ms
    /// nested-solve slice.  Fresh executors prevent incremental solver state
    /// from making later iterations artificially easier.
    #[test]
    fn quantified_gate_bool_uf_discharge_is_repeatable() {
        for iteration in 0..16 {
            let mut exec = Executor::new();
            let obligation = midrange_bool_uf_gate_obligation(&mut exec);
            assert!(
                matches!(
                    exec.quantified_gate_isolated_solve(vec![obligation]),
                    SolveResult::Unsat(_)
                ),
                "iteration {iteration}: valid Bool-UF table equivalence was not proved"
            );
        }
    }

    /// Small absorption-shaped obligations stay byte-for-byte on the legacy
    /// path.  Rewriting those can perturb the DT-certificate fallback's search
    /// order even though the replacement is propositionally equivalent.
    #[test]
    fn quantified_gate_small_absorption_is_not_rewritten() {
        let mut exec = Executor::new();
        let pivot = exec.ctx.terms.mk_var("qmg!small-p", Sort::Bool);
        let residue = exec.ctx.terms.mk_var("qmg!small-q", Sort::Bool);
        let compound = exec.ctx.terms.mk_and(vec![pivot, residue]);
        let equality = exec.ctx.terms.mk_eq(pivot, compound);
        let assertion = exec.ctx.terms.mk_not(equality);

        assert_eq!(
            quantified_gate_simplify_negated_absorbed_bool_eq(&mut exec.ctx.terms, assertion),
            assertion
        );
    }

    /// Fanout alone is insufficient: unrelated Boolean/DT table obligations
    /// must retain their original search structure.
    #[test]
    fn quantified_gate_large_non_integer_table_is_not_rewritten() {
        let mut exec = Executor::new();
        let pivot = exec.ctx.terms.mk_var("qmg!large-p", Sort::Bool);
        let mut table = Vec::with_capacity(256);
        table.push(pivot);
        for _ in 1..256 {
            table.push(exec.ctx.terms.mk_fresh_var("qmg!large-q", Sort::Bool));
        }
        let compound = exec.ctx.terms.mk_and(table);
        let equality = exec.ctx.terms.mk_eq(pivot, compound);
        let assertion = exec.ctx.terms.mk_not(equality);

        assert_eq!(
            quantified_gate_simplify_negated_absorbed_bool_eq(&mut exec.ctx.terms, assertion),
            assertion
        );
    }

    /// The normalization is a completeness aid, not a verdict escape hatch.
    /// Mixed nonlinear Int/Real arithmetic is intentionally unsupported by
    /// the nested dispatcher and must remain fail-closed Unknown.  The local
    /// 500 ms slice must also restore the caller's longer deadline.
    #[test]
    fn quantified_gate_out_of_fragment_stays_unknown_and_restores_deadline() {
        let mut exec = Executor::new();
        let x = exec.ctx.terms.mk_var("qmg!real", Sort::Real);
        let y = exec.ctx.terms.mk_var("qmg!int", Sort::Int);
        let x_squared = exec.ctx.terms.mk_mul(vec![x, x]);
        let two = exec
            .ctx
            .terms
            .mk_rational(num_rational::BigRational::from_integer(BigInt::from(2)));
        let nonlinear_real = exec.ctx.terms.mk_eq(x_squared, two);
        let zero = exec.ctx.terms.mk_int(BigInt::from(0));
        let integer_bound = exec.ctx.terms.mk_ge(y, zero);
        let assertions = vec![nonlinear_real, integer_bound];
        let (category, _) = exec.detect_logic_category(&assertions);
        assert_eq!(category, LogicCategory::QfNira);

        let outer_deadline = Instant::now() + Duration::from_secs(10);
        exec.set_deadline(Some(outer_deadline));
        assert_eq!(
            exec.quantified_gate_isolated_solve(assertions),
            SolveResult::Unknown
        );
        assert_eq!(exec.solve_deadline.get(), Some(outer_deadline));
    }

    #[test]
    fn array_model_newest_first_duplicate_index_is_preserved_by_gate() {
        let (mut exec, outputs) = solved(
            "(set-logic QF_AX)\
             (declare-const a (Array Int Int))\
             (assert (= (select a 7) 2))\
             (check-sat)",
        );
        assert_eq!(outputs[0], "sat", "baseline formula must be sat");

        let a = exec
            .ctx
            .terms
            .mk_var("a", Sort::array(Sort::Int, Sort::Int));
        let mut array_model = ay_arrays::ArrayModel::default();
        array_model.array_values.insert(
            a,
            ay_arrays::ArrayInterpretation {
                default: Some("0".to_string()),
                // The outer/newest store is authoritative and must make the
                // asserted read 2; the older duplicate value 1 is shadowed.
                stores: vec![
                    ("7".to_string(), "2".to_string()),
                    ("7".to_string(), "1".to_string()),
                ],
                index_sort: Some(Sort::Int),
                element_sort: Some(Sort::Int),
            },
        );
        exec.last_model
            .as_mut()
            .expect("baseline solve produced a model")
            .array_model = Some(array_model);

        assert!(matches!(
            exec.confirm_sat_with_independent_gate(),
            GateVerdict::ConfirmedSat
        ));
    }

    #[test]
    fn extensionality_merge_ignores_shadowed_duplicate_index() {
        let (mut exec, outputs) = solved(
            "(set-logic QF_AX)\
             (declare-const a (Array Int Int))\
             (declare-const b (Array Int Int))\
             (assert (= a b))\
             (assert (= (select a 7) 2))\
             (check-sat)",
        );
        assert_eq!(outputs[0], "sat", "baseline formula must be sat");

        let array_sort = Sort::array(Sort::Int, Sort::Int);
        let a = exec.ctx.terms.mk_var("a", array_sort.clone());
        let b = exec.ctx.terms.mk_var("b", array_sort);
        let mut array_model = ay_arrays::ArrayModel::default();
        array_model.array_values.insert(
            a,
            ay_arrays::ArrayInterpretation {
                // Partial entries force the equality-class merge path.
                default: None,
                stores: vec![
                    ("7".to_string(), "2".to_string()),
                    ("7".to_string(), "1".to_string()),
                ],
                index_sort: Some(Sort::Int),
                element_sort: Some(Sort::Int),
            },
        );
        array_model.array_values.insert(
            b,
            ay_arrays::ArrayInterpretation {
                default: None,
                stores: Vec::new(),
                index_sort: Some(Sort::Int),
                element_sort: Some(Sort::Int),
            },
        );
        exec.last_model
            .as_mut()
            .expect("baseline solve produced a model")
            .array_model = Some(array_model);

        assert!(matches!(
            exec.confirm_sat_with_independent_gate(),
            GateVerdict::ConfirmedSat
        ));
    }

    const XEQ5: &str = "(set-logic QF_LIA)(declare-fun x () Int)(assert (= x 5))(check-sat)";

    /// SOUNDNESS REGRESSION — a `Sat` whose emitted witness is GROUND-REFUTED
    /// by the independent gate must ship as `unknown`, NEVER as `sat`, with no
    /// environment variable required (the pre-2026-07 monitor-by-default
    /// posture kept the `sat` unless `AY_MODEL_CHECK_STRICT` was set — that
    /// was the stopgap this pins as removed). The invalid-witness scenario is
    /// constructed synthetically (the real witness is replaced with `x = 4`
    /// against `(assert (= x 5))`) so the test stays valid after the
    /// underlying model-construction bug classes (BV/NRA/strings) are fixed.
    #[test]
    fn ground_refuted_model_downgrades_sat_to_unknown_unconditionally() {
        let (mut exec, outputs) = solved(XEQ5);
        assert_eq!(outputs[0], "sat", "baseline formula must be sat");
        assert!(
            !exec.ctx.assertions.is_empty(),
            "gate must have original assertions to re-check"
        );

        // Corrupt the witness: x = 4 ground-falsifies (= x 5).
        let x = exec.ctx.terms.mk_var("x", Sort::Int);
        exec.last_model = Some(synthetic_lia_model(&[(x, 4)]));

        let gated = exec.apply_independent_model_gate(SolveResult::Sat);
        assert_eq!(
            gated,
            SolveResult::Unknown,
            "a ground-refuted witness must downgrade Sat to Unknown unconditionally"
        );
        assert!(
            exec.last_model.is_none(),
            "the refuted witness must not remain observable via get-model"
        );
        assert_eq!(
            exec.last_statistics.get_string("model_check_gate.result"),
            Some("model-violates"),
            "the downgrade must be attributed to the ModelViolates arm"
        );
    }

    /// The soundness-gate alarm's debug payload (printed to stderr by
    /// [`Executor::report_caught_invalid_model`]) must name the violated
    /// assertion's leaves and their falsifying model values. Pins the
    /// `format_falsifying_assignment` output so the "loud warning with debugging
    /// information" cannot silently regress to a bare notice.
    #[test]
    fn gate_alarm_falsifying_assignment_names_leaf_and_value() {
        let (mut exec, outputs) = solved(XEQ5);
        assert_eq!(outputs[0], "sat");
        let x = exec.ctx.terms.mk_var("x", Sort::Int);
        exec.last_model = Some(synthetic_lia_model(&[(x, 4)]));
        let assertion = exec.ctx.assertions[0];
        let assignment = exec.format_falsifying_assignment(assertion);
        assert!(
            assignment.contains("x = 4"),
            "the gate alarm must report the falsifying leaf value `x = 4`, got: {assignment}"
        );
    }

    /// Each `EvalValue` variant renders to a compact debug string for the alarm.
    #[test]
    fn gate_alarm_eval_value_display_renders_variants() {
        use num_rational::BigRational;
        assert_eq!(eval_value_display(&EvalValue::Bool(false)), "false");
        assert_eq!(
            eval_value_display(&EvalValue::Rational(BigRational::from_integer(
                BigInt::from(7)
            ))),
            "7"
        );
        assert_eq!(
            eval_value_display(&EvalValue::String("ab".into())),
            "\"ab\""
        );
        assert_eq!(eval_value_display(&EvalValue::Unknown), "?");
    }

    /// The gate must not over-degrade: a VALID witness passes through the full
    /// pipeline (gate enforced) as `sat`.
    #[test]
    fn valid_model_stays_sat_under_enforced_gate() {
        let (exec, outputs) = solved(XEQ5);
        assert_eq!(outputs[0], "sat");
        assert_eq!(
            exec.last_statistics.get_string("model_check_gate.result"),
            Some("confirmed-sat"),
            "the gate must independently confirm the valid witness"
        );
    }

    /// The `CannotConfirm` arm is EVALUATOR INCOMPLETENESS (a leaf the gate
    /// cannot pin), not a refutation: the verdict is kept and the gap is
    /// recorded. This pins the deliberate ModelViolates/CannotConfirm
    /// asymmetry: enforcement fires on concrete refutations only.
    #[test]
    fn coverage_gap_keeps_sat_and_is_recorded() {
        let (mut exec, outputs) = solved(XEQ5);
        assert_eq!(outputs[0], "sat");

        // A LIA model with NO value for x: the leaf is unpinned (Unknown),
        // nothing is refuted, so the gate cannot confirm — a coverage gap.
        exec.last_model = Some(synthetic_lia_model(&[]));

        let gated = exec.apply_independent_model_gate(SolveResult::Sat);
        assert_eq!(
            gated,
            SolveResult::Sat,
            "evaluator incompleteness must not masquerade as a refutation"
        );
        assert_eq!(
            exec.last_statistics.get_string("model_check_gate.result"),
            Some("cannot-confirm"),
            "the coverage gap must be recorded in the gate telemetry"
        );
    }

    /// READ-CONGRUENCE GATE REGRESSION (QF_ALIA seed-1212 cases 202/262): a
    /// witness with EQUAL index values (`z = x = 0`) and an UNPINNED free
    /// array leaf falsifies `(distinct -3 (select arr1 z) (select arr1 x))`
    /// in EVERY completion — the two reads share the congruence key, so the
    /// distinct can never hold. The plain ground walk fails open here (the
    /// select results are unpinned, so the assertion looks non-ground); the
    /// congruent-read evaluator must fail it CLOSED to `unknown`. Constructed
    /// synthetically so the test stays valid now that the model-CONSTRUCTION
    /// side (read-congruence index splits in arrays final_check) is fixed.
    #[test]
    fn read_congruence_violation_with_unpinned_array_downgrades_to_unknown() {
        let (mut exec, outputs) = solved(
            "(set-logic QF_ALIA)\
             (declare-const x Int)\
             (declare-const z Int)\
             (declare-const arr1 (Array Int Int))\
             (assert (distinct (- 3) (select arr1 z) (select arr1 x)))\
             (check-sat)",
        );
        assert_eq!(outputs[0], "sat", "baseline formula must be sat");

        // Corrupt the witness: z = x = 0 with arr1 left unpinned. Read
        // congruence makes the distinct false in every completion.
        let x = exec.ctx.terms.mk_var("x", Sort::Int);
        let z = exec.ctx.terms.mk_var("z", Sort::Int);
        exec.last_model = Some(synthetic_lia_model(&[(x, 0), (z, 0)]));

        let gated = exec.apply_independent_model_gate(SolveResult::Sat);
        // The independent gate records the coverage gap (arr1 unpinned); the
        // authoritative fail-closed pass must then catch the for-all-
        // completions refutation via congruent-read evaluation.
        let gated = exec.apply_authoritative_failclosed_gate(gated);
        assert_eq!(
            gated,
            SolveResult::Unknown,
            "a read-congruence-refuted witness must not ship as sat"
        );
        assert!(
            exec.last_model.is_none(),
            "the refuted witness must not remain observable via get-model"
        );
    }

    /// The congruent-read evaluator must stay CONSERVATIVE: reads over
    /// DISTINCT index values (or distinct array leaves) are indeterminate,
    /// never a refutation — a valid witness with unpinned reads keeps `sat`.
    #[test]
    fn read_congruence_distinct_index_values_keep_sat() {
        let (mut exec, outputs) = solved(
            "(set-logic QF_ALIA)\
             (declare-const x Int)\
             (declare-const z Int)\
             (declare-const arr1 (Array Int Int))\
             (assert (distinct (- 3) (select arr1 z) (select arr1 x)))\
             (check-sat)",
        );
        assert_eq!(outputs[0], "sat");

        // z != x: some completion of arr1 satisfies the distinct, so the
        // congruent-read pass must not refute.
        let x = exec.ctx.terms.mk_var("x", Sort::Int);
        let z = exec.ctx.terms.mk_var("z", Sort::Int);
        exec.last_model = Some(synthetic_lia_model(&[(x, 1), (z, 0)]));

        let gated = exec.apply_independent_model_gate(SolveResult::Sat);
        let gated = exec.apply_authoritative_failclosed_gate(gated);
        assert_eq!(
            gated,
            SolveResult::Sat,
            "an indeterminate congruent-read verdict must keep the sat"
        );
    }

    /// EXTENSIONALITY-CLASS COMPLETENESS REGRESSION (#ext-class-adopt-emitted,
    /// #ext-class-read-cover) — the TLA+ func-BMC `UNCHANGED` shape: per-step
    /// array variables asserted equal (`(= f1 f0)`, NO store terms) with a
    /// ground select pin on one member (`(= 42 (select f0 1))`). The array
    /// theory emits an `array_model` entry for only ONE member of the class;
    /// branch 3 of the gate's array resolution used to FABRICATE the class
    /// value from the canonical sort default (Int → 0), ground-"refute" the
    /// pin against its own fabrication (`select → 0 ≠ 42`), and downgrade a
    /// genuine Sat to Unknown/Incomplete. The fix adopts the emitted entry /
    /// merged committed reads instead, so this must solve `sat` AND the gate
    /// must CONFIRM it (not merely keep it as an unenforced coverage gap).
    /// The refutation arm is untouched — see
    /// `ground_refuted_model_downgrades_sat_to_unknown_unconditionally`.
    #[test]
    fn extensionality_class_with_ground_read_pin_confirms_sat() {
        let (exec, outputs) = solved(
            "(set-logic QF_AUFLIA)\
             (declare-fun f0 () (Array Int Int))\
             (declare-fun f1 () (Array Int Int))\
             (assert (= 42 (select f0 1)))\
             (assert (= f1 f0))\
             (check-sat)",
        );
        assert_eq!(
            outputs[0], "sat",
            "an asserted-equal array class with a satisfiable ground read pin \
             must solve sat, not be downgraded by the gate's own fabricated \
             class default"
        );
        assert_eq!(
            exec.last_statistics.get_string("model_check_gate.result"),
            Some("confirmed-sat"),
            "the gate must confirm the witness from the emitted/committed \
             model values (adopted entry or merged committed reads)"
        );
    }

    /// The dual guard of `extensionality_class_with_ground_read_pin_confirms_sat`:
    /// the same UNCHANGED shape made UNSATISFIABLE (two contradictory pins on
    /// the two class members) must still answer `unsat` — the completeness fix
    /// must not let the class adoption/merge speak louder than the solver on
    /// genuinely conflicting reads.
    #[test]
    fn extensionality_class_with_contradictory_read_pins_stays_unsat() {
        let (_exec, outputs) = solved(
            "(set-logic QF_AUFLIA)\
             (declare-fun f0 () (Array Int Int))\
             (declare-fun f1 () (Array Int Int))\
             (assert (= 42 (select f0 1)))\
             (assert (= 43 (select f1 1)))\
             (assert (= f1 f0))\
             (check-sat)",
        );
        assert_eq!(
            outputs[0], "unsat",
            "contradictory reads through an asserted-equal array class must \
             stay unsat"
        );
    }

    /// COMPLETION-ORDERING REGRESSION (#array-completion-order, seed 21453).
    ///
    /// A witness that VALIDATES under the gate's evaluator but is EMITTED with a
    /// different value is an invalid witness. The concrete class: a combined
    /// AUFLIA solve commits an Int variable's value to the arithmetic (LIA)
    /// model, while a STALE value survives in the merged EUF `term_values` map.
    /// `evaluate_var` — the value the gate checks — resolves LIA-FIRST (so the
    /// gate validated `i = 0`), but `(get-model)` used to read the merged EUF
    /// map FIRST for EVERY sort, so it printed the stale EUF value `-2`. The
    /// emitted model then FALSIFIED the formula (`(= 0 i)` became `(= 0 -2)`)
    /// even though the gate had confirmed the LIA witness. `(get-model)` now
    /// skips the EUF map for Int/Real, so an arithmetic variable prints the same
    /// LIA/LRA value the gate validated — emit stays faithful to validation.
    #[test]
    fn get_model_int_prefers_lia_over_stale_euf_term_value() {
        let (mut exec, outputs) =
            solved("(set-logic QF_UFLIA)(declare-fun i () Int)(assert (<= i i))(check-sat)");
        assert_eq!(outputs[0], "sat");
        let i = exec.ctx.terms.mk_var("i", Sort::Int);

        // The validated model commits `i = 0` in LIA; a STALE EUF entry says -2.
        let mut lia = DetHashMap::default();
        lia.insert(i, BigInt::from(0));
        let mut euf = ay_euf::EufModel::default();
        euf.term_values.insert(i, "-2".to_string());
        exec.last_model = Some(Model {
            sat_model: vec![],
            term_to_var: DetHashMap::default(),
            bool_overrides: DetHashMap::default(),
            euf_model: Some(euf),
            array_model: None,
            lra_model: None,
            lia_model: Some(LiaModel { values: lia }),
            bv_model: None,
            fp_model: None,
            string_model: None,
            seq_model: None,
            completed_values: DetHashMap::default(),
            dt_ground: DetHashMap::default(),
            dt_pins: DetHashMap::default(),
        });
        exec.last_result = Some(SolveResult::Sat);

        let model_str = exec.model();
        assert!(
            model_str.contains("i () Int 0"),
            "get-model must emit the gate-validated LIA value 0 (LIA-first, like \
             evaluate_var), not the stale merged-EUF value; got: {model_str}"
        );
        assert!(
            !model_str.contains("(- 2)"),
            "get-model must NOT emit the stale merged-EUF value -2; got: {model_str}"
        );
    }
}
