// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bridge between the solver and the INDEPENDENT, fail-closed model-check gate
//! ([`ay_model_check`]).
//!
//! After `check-sat` produces `Sat` with a model, the gate re-evaluates every
//! assertion under that model with a *separate*, solver-independent evaluator.
//! Both non-confirming verdicts fail closed unconditionally (no environment
//! variable or caller mode can weaken this):
//!
//! * [`GateVerdict::ModelViolates`] — the gate ground-evaluated an assertion
//!   under the emitted model to `false`. That is a CONCRETE REFUTATION of the
//!   witness, so the `Sat` is ALWAYS downgraded to `Unknown` (fail closed).
//!   The (untrusted) search engine can therefore never ship a refuted model
//!   as `sat`.
//! * [`GateVerdict::CannotConfirm`] — the gate could not ground-evaluate some
//!   fragment (FP, quantifiers, infinite-domain UF, ...). That is evaluator
//!   INCOMPLETENESS rather than a refutation, but it is not evidence for a
//!   public SAT claim, so `Sat` is downgraded to `Unknown` and result artifacts
//!   are revoked.
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
use ay_core::term::{Symbol, TermData, TermEntryStamp, TermStoreSnapshotStamp};
use ay_core::time::Instant;
use ay_core::{Sort, TermId, TermStore};
use ay_fp::FpModelValue;
use ay_frontend::{DeclarationKind, SourceContextStamp};
use ay_model_check::{
    ArrayValue, EvalOutcome, Evaluator, GateVerdict, ModelValue, ModelView, ProjectionLookupError,
    ProvenUnconstrainedKind,
};

use super::{EvalValue, Model, QuantifiedConfirmationModelEpoch};
use crate::ematching::contains_quantifier;
use crate::executor::quantifier_loop::result_mapping::CheckedGroundDecision;
use crate::executor::{Executor, QueryAuthorityEpoch};
use crate::executor_types::{SolveResult, UnknownReason};
use crate::logic_detection::LogicCategory;

/// Exact roots of the public query being certified: the provenance-captured
/// pre-solve assertion snapshot when available, otherwise the current base
/// stack, plus every temporary `check-sat-assuming` literal. Solver-injected
/// axioms in a mutated context must not replace captured source roots, and
/// assumptions are semantically part of the query rather than optional model
/// hints.
impl Executor {
    /// Return the canonical ordered roots of the public query currently being
    /// certified. Quantified theorem producers and every public model gate must
    /// use this same constructor so temporary assumptions cannot fall outside a
    /// certificate's authenticated root window.
    pub(in crate::executor) fn independent_gate_query_roots(&self) -> Vec<TermId> {
        let mut roots = self
            .independent_gate_authored_assertions
            .as_ref()
            .map_or_else(|| self.ctx.assertions.clone(), Clone::clone);
        if let Some(assumptions) = self.last_assumptions.as_ref() {
            for &assumption in assumptions {
                if !roots.contains(&assumption) {
                    roots.push(assumption);
                }
            }
        }
        roots
    }
}

fn independent_gate_query_roots(exec: &Executor) -> Vec<TermId> {
    exec.independent_gate_query_roots()
}

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
            // A symbolic sequence may have no concrete `SeqModel` payload even
            // though EUF assigned the term an exact equivalence-class element.
            // Preserve that MODEL-PROVIDED identity as an opaque, sort-tagged
            // gate value.  This is sufficient for equality-only / declared-UF
            // uses, while every `seq.*` consumer still requires a concrete
            // `ModelValue::Seq` and therefore remains fail-closed.
            Sort::Seq(_) => {
                let ev = self.exec.evaluate_var(self.model, t, &sort);
                eval_value_to_model_value(&ev, &sort).or_else(|| {
                    self.model
                        .euf_model
                        .as_ref()
                        .and_then(|euf| euf.term_values.get(&t))
                        .map(|class| sequence_euf_class_value(&sort, class))
                })
            }
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
                // #dt-element-canon: the theory leaf lookup hands back an
                // OPAQUE element token for a datatype-sorted leaf; re-encode a
                // nullary-constructor token into the canonical `Datatype`
                // value so it is comparable with the identical value arriving
                // through `nullary_constructor_leaf` above.
                let ev = self.exec.evaluate_var(self.model, t, &sort);
                self.model_value_for(&ev, &sort)
            }
            // Every scalar / seq / uninterpreted leaf is resolved by the model's
            // existing leaf lookup, then converted into a gate value.
            // A Real leaf whose value is IRRATIONAL. `ModelValue::Real` holds a
            // `BigRational` and cannot express `sqrt(2)`, so such a leaf reached
            // the gate UNPINNED ("model does not pin this leaf") and a correct
            // `sat` failed closed. Publish the root object instead.
            //
            // The checker RE-DERIVES rather than trusts: `Algebraic::root_of`
            // re-counts the roots in the claimed interval with its OWN Sturm
            // chain and rejects an interval that does not isolate exactly one.
            // A wrong isolation claim from the solver is caught here, not
            // adopted — which is the whole point of an independent gate.
            Sort::Real => self.algebraic_leaf(t).or_else(|| {
                let ev = self.exec.evaluate_var(self.model, t, &sort);
                eval_value_to_model_value(&ev, &sort)
            }),
            _ => {
                let ev = self.exec.evaluate_var(self.model, t, &sort);
                eval_value_to_model_value(&ev, &sort)
            }
        }
    }

    /// Return only the exact checked projection index. The independent
    /// evaluator owns beta reduction so its graph, memo, depth, and bindings
    /// survive across the projection boundary.
    fn projection_argument(&self, t: TermId) -> Result<Option<usize>, ProjectionLookupError> {
        let result_sort = self.exec.ctx.terms.sort(t);
        let TermData::App(symbol, arguments) = self.exec.ctx.terms.get(t) else {
            return Ok(None);
        };
        self.model
            .projection_ufs
            .projected_argument_for_application(
                symbol,
                &self.exec.ctx.terms,
                arguments,
                result_sort,
            )
            .map_err(|error| ProjectionLookupError::inconsistent_model(error.to_string()))
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
            // A datatype-returning UF application can be pinned only by an
            // authored ground equality (for example `(= (bridge x) (tail
            // x))`) while the extracted EUF payload remains an opaque
            // `Element`.  Resolve that application through the same
            // unconditional definitional-equality index used for datatype
            // leaves before converting the opaque payload.  This is model
            // completion, not an assertion skip: UF applications are still
            // keyed by independently evaluated argument values below, and the
            // gate still checks every authored ground sibling, so conflicting
            // definitions or non-functional rows are rejected.
            if let Some(v) = self.datatype_leaf(t) {
                return Some(v);
            }
            // #dt-app-element-encoding — the SAME enum value must not reach the
            // gate in two encodings. A datatype-sorted application with no
            // e-graph value and no defining equality falls through to
            // `evaluate_term`, which yields `EvalValue::Element("v1")`, and
            // `eval_value_to_model_value` maps every `Element` to
            // `ModelValue::Uninterpreted` regardless of sort — while the same
            // value reached as a LEAF is normalized to `ModelValue::Datatype`
            // by `nullary_constructor_leaf`. Comparing the two then observes
            // "incomparable" and the gate cannot confirm a correct model.
            //
            // Normalize here through the leaf path's OWN parser, which returns
            // `Datatype { ctor, args: [] }` only for a real nullary constructor
            // name and `None` for anything else (abstract `@Unit!0` tokens,
            // wrong arity). Fail-closed: a non-constructor token leaves the
            // application exactly as unpinned as before, no value is
            // fabricated, and congruence is still enforced by `uf_graph`.
            if let EvalValue::Element(token) = self.exec.evaluate_term(self.model, t) {
                if let Some(v) = self.exec.parse_rendered_dt_value(&token, &sort) {
                    return Some(v);
                }
            }
            // A selector-bearing datatype application can still be represented
            // by an abstract EUF class token even though the model printer has
            // already committed that class to one concrete constructor tree.
            // Read the printer's existing reconstruction here, just as
            // `leaf_value` does for datatype constants, so the same published
            // value cannot enter the congruence graph once as `Datatype` and
            // once as `Uninterpreted`. This is deliberately restricted to the
            // exact datatype sort and to a successfully parsed renderer result:
            // an unresolved class remains unpinned and therefore fails closed.
            if self.exec.selector_bearing_datatype(&sort) {
                if let Sort::Uninterpreted(sort_name) = &sort {
                    if let Some(rendered) = self.exec.resolve_dt_value(sort_name, t, self.model) {
                        if let Some(value) = self.exec.parse_rendered_dt_value(&rendered, &sort) {
                            return Some(value);
                        }
                    }
                }
            }
            // For an all-nullary datatype, the exact EUF class may be the only
            // model evidence tying this application to a constructor. Read the
            // unique constructor from that class without falling back to a
            // fabricated datatype default.
            //
            // #dt-app-euf-class — the SAME producer gap one level deeper, and
            // the one that costs the FINITE-ENUM sats.
            //
            // For an all-nullary (enum) datatype the model commits `(f a)`'s
            // value ONLY as an equivalence-class membership: the executor's
            // `add_finite_enum_domain_coverage` asserts `(or (= t c0) … )`, the
            // SAT layer picks a disjunct, and EUF merges `(f a)` into that
            // constructor's class. But the class is NAMED by a minted
            // `@Enum!n` representative (`ay-euf` model_extraction mints
            // `@{sort}!{n}` for every `Sort::Uninterpreted` class, and an enum
            // datatype is lowered to exactly that), so the branch above sees a
            // token that is not a constructor NAME and declines, and the value
            // reaches the gate as `Uninterpreted("@Enum!0")` — while the same
            // value reached as a LEAF is `Datatype { ctor: "c0" }` via
            // `nullary_constructor_leaf`. `value_eq` then reports
            // "equality between incomparable model values (Datatype vs
            // Uninterpreted)" and the gate CannotConfirm a correct witness:
            //
            //   (declare-datatypes ((Enum 0)) (((c0) (c1) (c2))))
            //   (declare-fun f (Enum) Enum) (declare-const a Enum)
            //   (assert (not (= a (f a))))     ; z3: sat — AY published unknown
            //
            // ONE VALUE IN TWO ENCODINGS, fixed at the PRODUCER exactly as
            // `#dt-element-canon` prescribes: `value_eq` is untouched, and the
            // class match is the SAME one `(get-value ((f a)))` already prints
            // (`resolve_dt_value` strategy 2 — verified: it prints `c1`, not
            // the canonical default `c0`, when the class holds `c1`).
            //
            // NOT `resolve_dt_value` itself: that function ends in
            // `datatype_canonical_value`, a FABRICATED default for a value
            // nothing determines. Adopting it here would be the gate inventing
            // a value — the one thing it must never do. `dt_euf_class_constructor`
            // is the model-reading half alone, and declines (leaving the
            // application exactly as unpinned as today) when no unique nullary
            // constructor shares the class.
            if let Some(ctor) = self.exec.dt_euf_class_constructor(self.model, t) {
                if let Some(v) = self.exec.parse_rendered_dt_value(&ctor, &sort) {
                    return Some(v);
                }
            }
        }
        // An ARRAY-sorted UF application is the mirror of the datatype case
        // just above, and needs the same treatment (#seq-array-uf-def):
        // verification-consumer's Seq encoding carries a sequence's backing array through a
        // plain `seq_array : Seq -> (Array Int Int)`, and the array solver
        // materializes no entry for an application no `select` constrains — so
        // `evaluate_term` below yields nothing and the gate could not confirm
        // `(= (const-array 0) (seq_array v))` even as a `check-sat-assuming`
        // premise. `array_leaf` resolves it through its asserted definitional
        // equality exactly as it already does for a bare array VARIABLE,
        // carrying the same cycle guard and the same "evaluate the defining
        // expression with the gate's own evaluator" discipline.
        //
        // Congruence is still enforced, not bypassed: `uf_app_value` results
        // are keyed by evaluated ARGUMENT VALUES in the gate's `uf_graph`, so
        // two congruent applications resolving to different arrays are
        // surfaced as a violation rather than honoured (#uflia-uf-collapse).
        if let Sort::Array(arr) = &sort {
            if let Some(value) = self.array_leaf(t, &arr.index_sort, &arr.element_sort) {
                return Some(value);
            }
        }
        let ev = self.exec.evaluate_term(self.model, t);
        let structural = if matches!((&sort, &ev), (Sort::Seq(_), EvalValue::Element(_))) {
            // An `Element` is not, by itself, a sequence value.  Accept opaque
            // sequence identities only through the exact EUF `term_values`
            // lookup below, which supplies their model provenance.
            None
        } else {
            // #dt-element-canon: the enum-SAT lane's `decode_enum_model`
            // publishes a datatype-sorted UF application (`(u p1)`) as the
            // constructor NAME, which arrives here as `EvalValue::Element`.
            // Re-encode it canonically so it is comparable with the same value
            // reaching the gate as a `Datatype` through a nullary-constructor
            // leaf — see `canonical_dt_element` for the 66538b006f account.
            self.model_value_for(&ev, &sort)
        };
        structural
            .or_else(|| {
                matches!(sort, Sort::Seq(_))
                    .then(|| {
                        self.model
                            .euf_model
                            .as_ref()
                            .and_then(|euf| euf.term_values.get(&t))
                            .map(|class| sequence_euf_class_value(&sort, class))
                    })
                    .flatten()
            })
            // LAST RESORT (#gate-scalar-uf-def): nothing in the model pins this
            // genuine declared-UF application, but an asserted equality may
            // DEFINE it — `(= v (f i))`. Theory applications are excluded by
            // the exact declaration-kind guard; evaluator-proven unconstrained
            // theory inputs use the separately typed method above. Placed after
            // every model read, so a committed value always wins.
            .or_else(|| self.uf_app_definition_value(t))
    }

    /// Resolve only an evaluator-PROVEN unconstrained theory application from
    /// an asserted definition.
    ///
    /// This is deliberately separate from [`Self::uf_app_value`]. A missing
    /// committed value for an ordinary theory application is never permission
    /// to believe the assertion that mentions it: only `ay-model-check` can mint
    /// the typed reason after independently evaluating the arguments and proving
    /// that SMT-LIB leaves this exact input unconstrained. We then defensively
    /// recheck the exact canonical head and signature before consulting the same
    /// unconditional definition index used for genuine UFs.
    fn proven_unconstrained_app_value(
        &self,
        t: TermId,
        kind: ProvenUnconstrainedKind,
    ) -> Option<ModelValue> {
        // Legal declarations colliding with a builtin receive a private core
        // identity. Seeing a live declaration own one of the canonical
        // identities means that invariant was bypassed; neither the theory head
        // nor the definition-index control operators are then trustworthy.
        if !self.canonical_theory_bindings_are_coherent() {
            return None;
        }

        let TermData::App(Symbol::Named(name), args) = self.exec.ctx.terms.get(t) else {
            return None;
        };
        let result_sort = self.exec.ctx.terms.sort(t);
        let exact_shape = match (kind, name.as_str(), args.as_slice(), result_sort) {
            (ProvenUnconstrainedKind::FpToRealNonFinite, "fp.to_real", [arg], Sort::Real) => {
                matches!(self.exec.ctx.terms.sort(*arg), Sort::FloatingPoint(_, _))
            }
            (ProvenUnconstrainedKind::RealDivByZero, "/", [left, right], Sort::Real) => {
                self.exec.ctx.terms.sort(*left) == &Sort::Real
                    && self.exec.ctx.terms.sort(*right) == &Sort::Real
            }
            (ProvenUnconstrainedKind::IntDivByZero, "div", [left, right], Sort::Int)
            | (ProvenUnconstrainedKind::IntModByZero, "mod", [left, right], Sort::Int) => {
                self.exec.ctx.terms.sort(*left) == &Sort::Int
                    && self.exec.ctx.terms.sort(*right) == &Sort::Int
            }
            _ => false,
        };
        exact_shape
            .then(|| self.asserted_app_definition_value(t))
            .flatten()
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
        // #dt-element-canon: an array over a datatype element sort reads back an
        // opaque element token for the same reason a UF application does.
        self.model_value_for(&ev, &sort)
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
    /// Whether every live declaration at a canonical theory-operator identity
    /// is positively owned by the theory layer.
    ///
    /// Source declarations that collide with builtin spellings receive private
    /// core identities and therefore remain ordinary UFs. Declaration-activated
    /// operators retain their canonical identities with an effective
    /// [`DeclarationKind::Theory`]. Any other live owner at a canonical identity
    /// means low-level registration bypassed those invariants. In that state the
    /// definition index cannot safely interpret even its control heads (`and`,
    /// `or`, `ite`, ...), so every assertion-derived application value must fail
    /// closed rather than borrow authority from a forged operator.
    fn canonical_theory_bindings_are_coherent(&self) -> bool {
        !self.exec.ctx.symbol_iter().any(|(surface, info)| {
            let identity = self.exec.ctx.symbol_identity_name(surface, info);
            ay_frontend::is_canonical_theory_operator_identity(identity)
                && self
                    .exec
                    .ctx
                    .effective_declaration_kind(info.declaration_id())
                    != Some(DeclarationKind::Theory)
        })
    }

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
    /// The root object for a Real leaf the NRA lane assigned an algebraic
    /// value, re-validated by the independent checker.
    ///
    /// Only the algebraic POINT is published. A non-identity residue is a
    /// derived expression rather than a variable's assignment, and the gate
    /// computes derived values itself from the term — so declining here keeps
    /// the checker's arithmetic independent of the solver's.
    fn algebraic_leaf(&self, t: TermId) -> Option<ModelValue> {
        let value = self.exec.nra_algebraic_model.get(&t)?;
        if !value.is_identity() {
            return None;
        }
        let alpha = value.alpha();
        let coefficients = alpha
            .poly_coeffs()
            .into_iter()
            .map(num_rational::BigRational::from)
            .collect();
        let (lo, hi) = alpha.interval();
        ay_model_check::algebraic::Algebraic::root_of(coefficients, lo.clone(), hi.clone())
            .ok()
            .map(|a| ModelValue::Algebraic(Box::new(a)))
    }

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

        // 1b. A preprocessing-recorded variable substitution is also an exact
        // definition, even though the defining equality has been consumed and
        // therefore cannot appear in `array_definitions`. Resolve only the
        // recorded forward edge, require the replacement to have the identical
        // array sort, and evaluate it compositionally through this independent
        // view. This is stronger evidence than the poisoned theory model below:
        // the preprocessor may replace `a24 -> a9`, while `a9` itself resolves
        // through an authored equality to a concrete store chain.
        //
        // The outer `array_leaf` cycle guard is already active for `t`, so a
        // malformed/cyclic substitution chain (`a -> b -> a`) fails closed.
        if let Some(&replacement) = self.exec.recorded_var_substitutions.get(&t) {
            if self.exec.ctx.terms.sort(replacement) == self.exec.ctx.terms.sort(t) {
                let ev = Evaluator::new(&self.exec.ctx.terms, self);
                if let EvalOutcome::Value(v @ ModelValue::Array(_)) = ev.evaluate(replacement) {
                    return Some(v);
                }
            }
        }

        // A read-conflicted theory interpretation is not evidence for the
        // array value, but an independently evaluated authored definition
        // above is.  Keep the conflict fail-closed for every fallback below;
        // this ordering permits only the stronger, assertion-derived value.
        if self
            .model
            .array_model
            .as_ref()
            .is_some_and(|arrays| arrays.read_conflicted.contains(&t))
        {
            return None;
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
        // This is the shared consumer boundary for array and datatype
        // definitions. A prebuilt/shared index must not remain authoritative if
        // a malformed live declaration owns an identity that `index_walk`
        // interprets as a theory control head.
        if !self.canonical_theory_bindings_are_coherent() {
            return Vec::new();
        }
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
        // `index_walk` assigns semantics to `=`, `and`, `or`, `ite`, and `if`
        // from their canonical identities. If low-level registration let an
        // ordinary declaration forge any canonical theory identity, none of
        // those interpretations is authoritative. Memoize an empty index so
        // every array/datatype/application definition fails closed, including
        // callers that eagerly build the index before asking for a definition.
        if !self.canonical_theory_bindings_are_coherent() {
            self.building_index.set(false);
            *self.def_index.borrow_mut() = Some(HashMap::new());
            self.resolved.borrow_mut().clear();
            self.resolved_none.borrow_mut().clear();
            return;
        }
        if self.def_index.borrow().is_some() || self.building_index.get() {
            return;
        }
        self.building_index.set(true);
        let mut map: HashMap<TermId, Vec<TermId>> = HashMap::new();
        for assertion in independent_gate_query_roots(self.exec) {
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
        // Record a `(= l r)` where the operands are array/datatype sorted, or
        // where either side is an APPLICATION of any other sort.
        //
        // #gate-scalar-uf-def: the second case is what lets a SCALAR-sorted
        // uninterpreted application be resolved from its asserted definition.
        // `(assert (= v (f i)))` pins `f` at `i` exactly as `(assert (= a
        // (store b i x)))` pins the array `a`, but only the array/datatype
        // sorts were indexed — so `(f i)` reached `uf_app_value` with nothing
        // behind it, the model committed no per-application value, and the gate
        // could not confirm a witness the solver had correctly found ("model
        // commits no value for this application of `f`"). The same gap hid an
        // FP result SMT-LIB deliberately leaves unconstrained: `(assert (=
        // (fp.to_real x) 5.0))` with `x` NaN is satisfiable precisely BECAUSE
        // that assertion is what fixes the value, and it was the one thing the
        // gate would not read.
        //
        // Restricted to equalities with an APPLICATION side: a leaf-to-leaf
        // scalar alias is already served by `leaf_value`, and only
        // `uf_app_value` consults this new class of entry, so the index grows
        // only where it is used.
        //
        // SOUND — the same argument as the array/datatype entries, reused
        // wholesale: `index_walk` records a partner ONLY along an
        // unconditionally-asserted path, so `l = r` holds in every model of the
        // assertions; the value is produced by the gate's OWN evaluator under
        // the fixed model, never taken on trust; single-valuedness is still
        // enforced by `uf_graph`, which keys applications by evaluated ARGUMENT
        // values, so two definitions that disagree at coincident arguments
        // collapse to one value and surface the conflict; and every assertion —
        // including each definition not chosen — is still re-checked, so a
        // wrong resolution can only produce `ModelViolates`, never a
        // confirmation.
        if let TermData::App(sym, args) = self.exec.ctx.terms.get(cand) {
            if sym.name() == "=" && args.len() == 2 {
                let (l, r) = (args[0], args[1]);
                if l != r {
                    let ls = self.exec.ctx.terms.sort(l).clone();
                    let structural =
                        matches!(ls, Sort::Array(_)) || self.exec.datatype_sort_name(&ls).is_some();
                    let app_sided = matches!(self.exec.ctx.terms.get(l), TermData::App(_, _))
                        || matches!(self.exec.ctx.terms.get(r), TermData::App(_, _));
                    if structural || app_sided {
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

    /// Resolve an uninterpreted APPLICATION `t` through an asserted definitional
    /// equality `(= t <expr>)` — the scalar analogue of [`Self::array_leaf`]
    /// branch 1 and [`Self::datatype_leaf`] (#gate-scalar-uf-def).
    ///
    /// Consulted only after the solver's own evaluator has declined to pin the
    /// application, so a model that DOES commit a value keeps it, and a
    /// definition contradicting that value still surfaces as `ModelViolates` on
    /// the defining assertion. See [`Self::index_walk`] for why every partner
    /// read here is unconditionally entailed by the assertions.
    ///
    /// Partners are filtered to `t`'s own sort (an `=` is homogeneous, so this
    /// only screens out a malformed index entry) and evaluated with the gate's
    /// OWN evaluator; the first that yields a concrete value wins — they are all
    /// asserted equal, and each losing definition is itself a top-level
    /// assertion the gate ground-checks, so a disagreement is reported there
    /// rather than hidden here. Cycles (`(= (f i) (g (f i)))`) are cut by the
    /// shared `resolving` stack, which fails the resolution closed.
    ///
    /// A CONFLICT CHECK over the partners (evaluate them all; adopt nothing if
    /// two disagree) was written here and deliberately dropped. It is not the
    /// stricter option, it is the blunter one: partners are recorded only from
    /// [`independent_gate_query_roots`] — exactly the assertions this gate
    /// re-checks — so two partners that evaluate to different values under the
    /// fixed model mean the model itself falsifies one of those two asserted
    /// equalities, and adopting the first makes the gate report that as
    /// `ModelViolates` (an exact refutation). Refusing here instead erases the
    /// refutation and downgrades it to a `CannotConfirm` coverage gap. It also
    /// costs the early exit, turning each nested resolution's branching factor
    /// from 1 into the partner count.
    fn uf_app_definition_value(&self, t: TermId) -> Option<ModelValue> {
        // DECLARED UNINTERPRETED FUNCTIONS ONLY — never a theory operator.
        //
        // This is the guard that keeps the fallback from papering over a bug in
        // the gate's OWN theory evaluators. For a genuinely uninterpreted `f`,
        // "the model pins nothing" means the value is free, and an asserted
        // equality is the only thing that can fix it — reading it is exactly
        // right. For a THEORY operation the gate is itself responsible for
        // computing the value, and it cannot distinguish "SMT-LIB leaves this
        // free" (`fp.to_real` at NaN/±Inf) from "my evaluator failed to compute
        // a value that IS determined". Adopting the assertion's own claim in
        // the second case would turn an evaluator bug into a confirmed wrong
        // `sat` — the precise hazard
        // `independent_gate_rejects_unspecified_fp_to_real_witness` pins. So
        // theory heads stay fail-closed here; widening `fp.to_real` at its
        // unspecified points belongs in the FP evaluator, which can tell the
        // two cases apart.
        let TermData::App(sym, args) = self.exec.ctx.terms.get(t) else {
            return None;
        };
        // A canonical theory identity is never an ordinary UF, even when a
        // low-level native alias incorrectly installs an Uninterpreted
        // declaration at that exact identity. Builtin-colliding source
        // declarations receive private core identities and remain eligible.
        // Indexed applications are theory syntax or malformed at this generic
        // boundary; source-declared UFs always carry a non-indexed identity.
        if matches!(sym, Symbol::Indexed(..))
            || ay_frontend::is_canonical_theory_operator_identity(sym.name())
        {
            return None;
        }
        // Positive authority only: the exact core head must resolve to a live,
        // non-nullary declaration whose full signature matches this application
        // and whose CURRENT semantic kind is an ordinary uninterpreted function.
        // Never fall back from a missing core identity to a surface-name lookup:
        // builtin-colliding declarations deliberately carry a private core
        // identity, and accepting the builtin spelling via their surface binding
        // would conflate two different functions. The effective-kind lookup is
        // also load-bearing for declared functions
        // adopted as definitional macros; their original declaration remains
        // `Uninterpreted`, but the live interpretation is no longer free.
        let declared = self
            .exec
            .ctx
            .symbol_info_by_identity(sym.name())
            .is_some_and(|info| {
                !info.arg_sorts.is_empty()
                    && info.arg_sorts.len() == args.len()
                    && info
                        .arg_sorts
                        .iter()
                        .zip(args)
                        .all(|(expected, &arg)| expected == self.exec.ctx.terms.sort(arg))
                    && &info.sort == self.exec.ctx.terms.sort(t)
                    && self
                        .exec
                        .ctx
                        .effective_declaration_kind(info.declaration_id())
                        == Some(DeclarationKind::Uninterpreted)
            });
        if !declared {
            return None;
        }
        self.asserted_app_definition_value(t)
    }

    /// Read one application through an unconditionally asserted equality.
    ///
    /// Eligibility is intentionally owned by the caller: ordinary UF lookup
    /// first proves an exact live `DeclarationKind::Uninterpreted` binding;
    /// typed theory lookup proves an exact allowlisted unconstrained input. This
    /// shared core only performs the entailed-definition resolution, including
    /// exact result-sort filtering and cycle-safe independent evaluation.
    fn asserted_app_definition_value(&self, t: TermId) -> Option<ModelValue> {
        // `ensure_def_index` recognizes interpreted control heads by their exact
        // canonical identities. If an ordinary declaration has forged any such
        // identity, even a different, legitimate UF target could otherwise
        // inherit a conditionally asserted equality as though it were entailed.
        if !self.canonical_theory_bindings_are_coherent() {
            return None;
        }
        let sort = self.exec.ctx.terms.sort(t).clone();
        self.ensure_def_index();
        let partners: Vec<TermId> = {
            let idx = self.def_index.borrow();
            idx.as_ref()?
                .get(&t)?
                .iter()
                .copied()
                .filter(|&p| *self.exec.ctx.terms.sort(p) == sort)
                .collect()
        };
        if partners.is_empty() {
            return None;
        }
        if !self.resolving.borrow_mut().insert(t) {
            self.cycle_hits.set(self.cycle_hits.get() + 1);
            return None; // cycle ⇒ fail closed
        }
        let mut result = None;
        for def in partners {
            let ev = Evaluator::new(&self.exec.ctx.terms, self);
            if let EvalOutcome::Value(v) = ev.evaluate(def) {
                result = Some(v);
                break;
            }
        }
        self.resolving.borrow_mut().remove(&t);
        result
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

    /// Re-encode a model-published OPAQUE element token into the gate's
    /// CANONICAL encoding for a datatype-sorted term (#dt-element-canon).
    ///
    /// WHY THIS EXISTS. [`EvalValue`] cannot carry datatype structure: the model
    /// side renders a `ModelValue::Datatype` back DOWN to
    /// `EvalValue::Element(<canonical string>)` (`dt_construct.rs`), and the
    /// enum-SAT lane's producer `decode_enum_model` (`enum_sat.rs`) builds its
    /// `EufModel` with the constructor NAMES as the sort's elements. So the SAME
    /// value reaches this gate in TWO encodings: a bare nullary-constructor leaf
    /// via [`Self::nullary_constructor_leaf`] as `Datatype { ctor: "u0", args: [] }`,
    /// and the UF application `(u p1)` as `Uninterpreted("u0")` (through
    /// `eval_value_to_model_value`). `value_eq` then refuses the comparison —
    ///
    /// ```text
    /// c probe value_eq incomparable: a=Datatype { ctor: "u0", args: [] } b=Uninterpreted("u0")
    /// ```
    ///
    /// — 891 times on `QF_UFDT/20210312-Bouvier/vlsat3_k13.smt2`, so the gate
    /// reports `CannotConfirm`. Before `66538b006f` that gap was recorded and the
    /// verdict kept; `66538b006f` made it downgrade `Sat` to `Unknown`, which is
    /// what cost the whole `QF_UFDT/Bouvier` sat stratum (100/100) of the banked
    /// SQ QF_Datatypes score.
    ///
    /// THE FIX IS IN THE PRODUCER, exactly as `ay-model-check/src/lib.rs:254-260`
    /// prescribes ("the fix for that is to normalize the PRODUCER; teaching
    /// `value_eq` to equate encodings would loosen the comparison this gate
    /// depends on"). `value_eq` is untouched and the gate is not opened: an
    /// element token that is NOT a nullary constructor of the term's own datatype
    /// still fails closed exactly as today.
    ///
    /// WHY `Datatype { ctor, args: [] }` IS THE CANONICAL ENCODING, not
    /// `Uninterpreted(name)`:
    ///  * it is what the model PRINTER publishes. `(get-model)` on `vlsat3_k13`
    ///    emits `(define-fun u ((x0 Place)) Unit (ite (= x0 p1) u0 ...))` — the
    ///    bare constructor symbol — and `Datatype { ctor: "u0", args: [] }` is
    ///    that same value, while `Uninterpreted("u0")` is a token of a sort the
    ///    problem does not declare. Reading the canonical form keeps the gate
    ///    checking the witness it actually ships (#mv-gate-reads-printed-dt).
    ///  * it is strictly MORE checkable: over a `Datatype` value the evaluator
    ///    decides testers and projects selectors; over an `Uninterpreted` token
    ///    it can only compare identity. Equal tokens still compare equal, so no
    ///    comparison that succeeds today changes its answer.
    ///
    /// FAITHFULNESS. The token is adopted only when it is, verbatim, a NULLARY
    /// constructor of the datatype named by `sort` — resolved through the SAME
    /// two lookups [`Self::nullary_constructor_leaf`] uses, so the two sides of
    /// an equality agree by construction. Anything else (an EUF class
    /// representative such as `@Unit!0`, a non-nullary constructor, a
    /// non-datatype sort) returns `None` and the existing conversion runs
    /// unchanged.
    ///
    /// `AY_DT_ELEMENT_CANON=0` opts out (A/B measurement only); opting out can
    /// only restore today's fail-closed `CannotConfirm`, never widen a verdict.
    fn canonical_dt_element(&self, ev: &EvalValue, sort: &Sort) -> Option<ModelValue> {
        let EvalValue::Element(token) = ev else {
            return None;
        };
        // Read the opt-out ONCE: this runs on every datatype-sorted leaf and UF
        // application (~9k atoms x 2 on `vlsat3_k13`), and this division is
        // already time-sensitive.
        static CANON_ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        if !*CANON_ON.get_or_init(|| std::env::var("AY_DT_ELEMENT_CANON").as_deref() != Ok("0")) {
            return None;
        }
        let dt_name = self.exec.datatype_sort_name(sort)?;
        let (_, ctor_names) = self
            .exec
            .ctx
            .datatype_iter()
            .find(|(dt, _)| *dt == dt_name)?;
        if !ctor_names.iter().any(|c| c == token) {
            return None;
        }
        // A constructor NAME of this datatype; require it to be NULLARY — a
        // token for a constructor with fields carries no field values, and
        // fabricating them here would be exactly the model invention the gate
        // exists to prevent.
        if !self.exec.ctx.constructor_selector_info(token)?.is_empty() {
            return None;
        }
        Some(ModelValue::Datatype {
            ctor: token.clone(),
            args: Vec::new(),
        })
    }

    /// [`eval_value_to_model_value`] in the gate's canonical encoding: a
    /// datatype-sorted opaque element token is re-encoded by
    /// [`Self::canonical_dt_element`] first (#dt-element-canon); everything else
    /// converts exactly as before.
    fn model_value_for(&self, ev: &EvalValue, sort: &Sort) -> Option<ModelValue> {
        if let Some(v) = self.canonical_dt_element(ev, sort) {
            return Some(v);
        }
        eval_value_to_model_value(ev, sort)
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
        self.parse_leaf_at_depth(s, sort, 0)
    }

    /// [`Self::parse_leaf`] carrying the nesting budget the array-text reader
    /// needs to recurse through an array-of-array cell.
    ///
    /// #gate-nested-array-encoding — an ARRAY-sorted CELL (the default or a
    /// store value of a NESTED array) reaches the gate as the printer's SMT-LIB
    /// text, and [`Executor::parse_model_value_string`] hands every
    /// array-sorted string straight back as an opaque `EvalValue::Element`.
    /// The same array value then exists in the gate in TWO encodings: a
    /// structured `ModelValue::Array` when it arrives as a plain array LEAF,
    /// and this unparsed text when it arrives as a nested cell. Comparing them
    /// lands in `value_eq`'s incomparable arm ("Array vs Uninterpreted") and
    /// the gate cannot confirm a witness that is in fact correct — the
    /// deductive-checks ground-seed shape `(= seed (select m #x0..0))`, where `seed`
    /// resolves to `Array{default: #x0..0}` while `m`'s cell is the string
    /// `"((as const (Array (_ BitVec 64) (_ BitVec 64))) #x0000000000000000)"`.
    ///
    /// The fix is the one `value_eq`'s incomparable arm prescribes: normalize
    /// the PRODUCER, never teach `value_eq` to equate encodings. Parsing the
    /// printed array back into the SAME structured value the leaf path builds
    /// makes the two encodings one.
    ///
    /// FAIL-SOFT, not fail-closed: an array text this reader cannot parse falls
    /// through to exactly today's opaque-token behaviour, so no leaf that
    /// resolves today stops resolving. FAITHFUL: the text IS the emitted
    /// witness, and the gate still re-checks every assertion against the parsed
    /// value — a misparse can only surface as `ModelViolates`, never confirm a
    /// wider model.
    fn parse_leaf_at_depth(&self, s: &str, sort: &Sort, depth: u32) -> Option<ModelValue> {
        if depth > 32 {
            return None;
        }
        if let Sort::Array(arr) = sort {
            if let Some(v) = self.parse_array_text(s, &arr.index_sort, &arr.element_sort, depth + 1)
            {
                return Some(v);
            }
        }
        // #dt-element-canon, at the array-cell boundary. A DATATYPE-sorted array
        // cell reaches the gate as the printer's SMT-LIB text — a constructor
        // APPLICATION such as `(PbTerm_PbTerm #x00..00)`. The scalar layer below
        // hands any such text back as an opaque `Element`, which
        // `model_value_for` can only normalize when it names a NULLARY
        // constructor; a constructor with fields therefore arrives as
        // `ModelValue::Uninterpreted("(PbTerm_PbTerm #x00..00)")` while the SAME
        // value reaching the gate as a datatype LEAF is the structured
        // `Datatype { ctor, args }`. `value_eq` then reports "equality between
        // incomparable model values (Datatype vs Uninterpreted)" and a ground
        // seed `(= seed (select arr #x0..0))` — the shape deductive-checks emits for
        // every array-argument function — cannot be confirmed even when the
        // model is right.
        //
        // Fixed where the two encodings are produced, never in `value_eq`: parse
        // the text with the SAME reader the datatype leaf/application paths use,
        // so one value has one encoding. FAIL-SOFT: text this reader declines
        // falls through to exactly today's opaque behaviour, and the gate still
        // re-checks every assertion against whatever it parsed.
        if self.exec.datatype_sort_name(sort).is_some() {
            if let Some(v) = self.exec.parse_rendered_dt_value(s, sort) {
                return Some(v);
            }
        }
        let ev = self.exec.parse_model_value_string(s, &Some(sort.clone()));
        // Array interpretations store values as strings.  A nullary datatype
        // constructor therefore parses through the scalar layer as an
        // `Element`, just like a datatype-sorted UF result.  Normalize it at
        // this producer boundary so an array key `red` and the authored
        // constructor term `red` reach the independent evaluator in the same
        // canonical Datatype encoding.
        self.model_value_for(&ev, sort)
    }

    /// Read the printer's SMT-LIB rendering of an ARRAY value back into a
    /// structured [`ModelValue::Array`]. Handles the two forms the model
    /// printer emits — the const-array base `((as const <sort>) <default>)` and
    /// a `(store <array> <index> <value>)` chain over it — and returns `None`
    /// for anything else (a `lambda`, an abstract `@`-atom, a partial
    /// rendering), which keeps the caller on its existing path.
    ///
    /// STORE ORDER: SMT-LIB nests oldest-innermost and the OUTERMOST `store`
    /// wins at a repeated index; [`ArrayValue`] is oldest-first and
    /// `array_select` scans it in REVERSE. Recursing into the base BEFORE
    /// pushing this level's entry therefore reproduces the emitted witness's
    /// winner exactly.
    fn parse_array_text(
        &self,
        s: &str,
        index_sort: &Sort,
        element_sort: &Sort,
        depth: u32,
    ) -> Option<ModelValue> {
        if depth > 32 {
            return None;
        }
        let items = sexpr_items(s)?;
        match items.first()?.as_str() {
            // `(store <array> <index> <value>)`
            "store" if items.len() == 4 => {
                let base = self.parse_array_text(&items[1], index_sort, element_sort, depth + 1)?;
                let ModelValue::Array(mut arr) = base else {
                    return None;
                };
                let key = self.parse_leaf_at_depth(&items[2], index_sort, depth + 1)?;
                let val = self.parse_leaf_at_depth(&items[3], element_sort, depth + 1)?;
                arr.store.push((key, val));
                Some(ModelValue::Array(arr))
            }
            // `((as const <sort>) <default>)` — the head is itself the
            // parenthesised `(as const <sort>)` qualifier.
            head if items.len() == 2 && head.starts_with('(') => {
                let qual = sexpr_items(head)?;
                if qual.len() != 3 || qual[0] != "as" || qual[1] != "const" {
                    return None;
                }
                let default = self.parse_leaf_at_depth(&items[1], element_sort, depth + 1)?;
                Some(ModelValue::Array(Box::new(ArrayValue {
                    default,
                    store: Vec::new(),
                })))
            }
            _ => None,
        }
    }
}

/// Split the BODY of a parenthesised s-expression into its top-level items,
/// respecting nesting, `"…"` string literals (with the SMT-LIB `""` escape) and
/// `|…|` quoted symbols. `None` when `s` is not ONE balanced parenthesised form
/// — so a bare atom, a truncated rendering, or `(a)(b)` all decline rather than
/// parse into something the caller would mistake for a value.
fn sexpr_items(s: &str) -> Option<Vec<String>> {
    let body = s.trim().strip_prefix('(')?.strip_suffix(')')?;
    let mut items: Vec<String> = Vec::new();
    let mut cur = String::new();
    let mut depth: i32 = 0;
    let mut in_str = false;
    let mut in_sym = false;
    let mut chars = body.chars().peekable();
    while let Some(c) = chars.next() {
        if in_str {
            cur.push(c);
            if c == '"' {
                // `""` is an escaped quote inside an SMT-LIB string literal.
                if chars.peek() == Some(&'"') {
                    cur.push(chars.next()?);
                } else {
                    in_str = false;
                }
            }
            continue;
        }
        if in_sym {
            cur.push(c);
            if c == '|' {
                in_sym = false;
            }
            continue;
        }
        match c {
            '"' => {
                in_str = true;
                cur.push(c);
            }
            '|' => {
                in_sym = true;
                cur.push(c);
            }
            '(' => {
                depth += 1;
                cur.push(c);
            }
            ')' => {
                depth -= 1;
                if depth < 0 {
                    return None; // the leading `(` did not match the trailing one
                }
                cur.push(c);
            }
            c if c.is_whitespace() && depth == 0 => {
                if !cur.is_empty() {
                    items.push(std::mem::take(&mut cur));
                }
            }
            _ => cur.push(c),
        }
    }
    if depth != 0 || in_str || in_sym {
        return None;
    }
    if !cur.is_empty() {
        items.push(cur);
    }
    Some(items)
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
        (
            V::FloatingPoint {
                sign: sign1,
                exponent: exponent1,
                significand: significand1,
                exponent_bits: exponent_bits1,
                significand_bits: significand_bits1,
            },
            V::FloatingPoint {
                sign: sign2,
                exponent: exponent2,
                significand: significand2,
                exponent_bits: exponent_bits2,
                significand_bits: significand_bits2,
            },
        ) => {
            sign1 == sign2
                && exponent1 == exponent2
                && significand1 == significand2
                && exponent_bits1 == exponent_bits2
                && significand_bits1 == significand_bits2
        }
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
/// represent (unknown, an FP format wider than AY's exact u64 carrier, or a
/// non-integer in an Int context) becomes `None`, which makes the leaf unpinned
/// and the gate fail closed.
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
        EvalValue::Fp(fp) => fp_value_to_independent_model(fp, sort),
        EvalValue::Unknown => None,
    }
}

/// Copy AY's concrete FP witness into the independent gate's raw IEEE carrier.
///
/// The copy is deliberately field-level instead of calling the solver's
/// `to_rational`: the independent evaluator must reconstruct `fp.to_real`
/// itself.  Special values receive their canonical AY encodings; that retains
/// structural SMT equality while `fp.to_real` rejects their all-ones exponent.
fn fp_value_to_independent_model(fp: &FpModelValue, sort: &Sort) -> Option<ModelValue> {
    let Sort::FloatingPoint(sort_eb, sort_sb) = sort else {
        return None;
    };
    let eb = fp.eb();
    let sb = fp.sb();
    if eb != *sort_eb || sb != *sort_sb || !(2..64).contains(&eb) || !(2..=64).contains(&sb) {
        return None;
    }
    let max_exponent = (1u64 << eb) - 1;
    let significand_limit = 1u64 << (sb - 1);
    let (sign, exponent, significand) = match fp {
        FpModelValue::PosZero { .. } => (false, 0, 0),
        FpModelValue::NegZero { .. } => (true, 0, 0),
        FpModelValue::PosInf { .. } => (false, max_exponent, 0),
        FpModelValue::NegInf { .. } => (true, max_exponent, 0),
        FpModelValue::NaN { .. } => (false, max_exponent, 1u64 << (sb - 2)),
        FpModelValue::Fp {
            sign,
            exponent,
            significand,
            ..
        } => {
            if *exponent > max_exponent || *significand >= significand_limit {
                return None;
            }
            (*sign, *exponent, *significand)
        }
    };
    Some(ModelValue::FloatingPoint {
        sign,
        exponent,
        significand,
        exponent_bits: eb,
        significand_bits: sb,
    })
}

/// Reify one EUF-provided class identity for a sequence-sorted term.
///
/// The sort tag is part of the token: EUF is permitted to reuse a printable
/// class name such as `e0` in two different carriers, but those elements are
/// not interchangeable.  The raw class identity is never inferred from term
/// syntax or a `TermId`; absence of the model entry therefore remains `None`.
fn sequence_euf_class_value(sort: &Sort, class: &str) -> ModelValue {
    ModelValue::Uninterpreted(format!(
        "@ay-seq-euf-class:{sort:?}:{}:{class}",
        class.len()
    ))
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
/// the generic proof model supplies `enforce = false`. Every live unconfirmed
/// publication call site supplies `enforce = true`; `CannotConfirm` bypasses
/// this helper only to downgrade directly (see
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

    /// Revoke the one-shot direct quantified-model handoff on both the
    /// executor and the installed model it named.
    pub(in crate::executor) fn revoke_quantified_model_confirmation_authority(&mut self) {
        self.quantified_model_confirmation = None;
        if let Some(model) = self.last_model.as_mut() {
            model.revoke_quantified_confirmation();
        }
    }

    /// Run the independent gate over the current `Sat` model and assertions.
    pub(in crate::executor) fn confirm_sat_with_independent_gate(&self) -> GateVerdict {
        // Ordinary internal confirmations have no authority to skip quantified
        // leaves. The one-shot direct handoff is available only through the
        // designated SAT-funnel consumer below.
        self.confirm_sat_with_independent_gate_confirmation(None)
    }

    fn confirm_sat_with_independent_gate_confirmation(
        &self,
        confirmation: Option<&QuantifiedModelConfirmation>,
    ) -> GateVerdict {
        // Select the public obligation window exactly once. Detection,
        // certificate scope checks, quantified-leaf filtering, and the final
        // evaluator must all refer to this same ordered root snapshot.
        let query_roots = independent_gate_query_roots(self);
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
        // A specialized quantified certificate is allowed to discharge only
        // the quantified LEAF conjuncts it checked. The compositional evaluator
        // still checks every ground sibling. This is an evidence composition,
        // not a skip: the quantified gate runs first and sets one of these
        // markers only after its own fail-closed validation succeeds.
        let finite_table_certified = self.finite_table_cert_grant_active
            && self
                .finite_table_cert_witness_state
                .as_ref()
                .is_some_and(|state| state.is_installed_current_for(self, &query_roots, model));
        let dt_certified = self.dt_cert_grant_active
            && self
                .dt_cert_query_grant
                .as_ref()
                .is_some_and(|grant| grant.is_current_for(self, &query_roots));
        let bv_full_domain_certified = self.bv_quantifier_full_domain_proof
            && self
                .bv_quantifier_full_domain_query_grant
                .as_ref()
                .is_some_and(|grant| grant.is_current_for(self, &query_roots));
        let const_interp_certified = self.const_interp_cert_grant_active
            && self
                .const_interp_cert_witness_state
                .as_ref()
                .is_some_and(|state| state.is_installed_current_for(self, &query_roots, model));
        let mbqi_certified = self.mbqi_sat_cert_grant_active
            && self
                .mbqi_sat_cert_query_grant
                .as_ref()
                .is_some_and(|grant| grant.is_current_for(self, &query_roots));
        let direct_confirmation = confirmation
            .and_then(|confirmation| confirmation.bind_current(self, &query_roots, model));
        let directly_confirmed = direct_confirmation.is_some();
        let quantified_certified = dt_certified
            || finite_table_certified
            || bv_full_domain_certified
            || const_interp_certified
            || mbqi_certified
            || self
                .cegqi_uf_recompletion_grant
                .as_ref()
                .is_some_and(|grant| grant.is_current_for(self, &query_roots))
            // The immediately preceding quantified gate checked this exact
            // root snapshot against this exact installed model. Statistics are
            // diagnostic only: even the string `confirmed` cannot discharge a
            // quantified leaf without this typed, current capability.
            || directly_confirmed;
        let mut independently_checkable = Vec::new();
        if quantified_certified {
            for &assertion in &query_roots {
                let mut conjuncts = Vec::new();
                crate::executor::quantifier_loop::collect_and_conjuncts(
                    &self.ctx.terms,
                    assertion,
                    &mut conjuncts,
                );
                if conjuncts.is_empty() {
                    conjuncts.push(assertion);
                }
                independently_checkable.extend(
                    conjuncts
                        .into_iter()
                        .filter(|term| !contains_quantifier(&self.ctx.terms, *term)),
                );
            }
        }
        let assertions = if quantified_certified {
            independently_checkable.as_slice()
        } else {
            query_roots.as_slice()
        };
        let verdict = ay_model_check::confirm_model(&self.ctx.terms, &view, assertions);
        // Keep the borrow-bound model authority alive through the complete
        // compositional evaluation. No model mutation can interleave with this
        // pure consumer.
        let _confirmation_still_borrowed = direct_confirmation.as_ref();
        verdict
    }

    /// Authority-grade independent confirmation for a strict-gate coverage
    /// exception.
    ///
    /// Unlike [`Self::confirm_sat_with_independent_gate`], this deliberately
    /// admits neither model-independent tautology recovery nor a residual
    /// satisfiability extension.  Every exact authored assertion must evaluate
    /// compositionally to `Bool(true)` under one fresh independent evaluator;
    /// an unsupported atom, unpinned leaf, non-Boolean result, or explicit
    /// `false` fails closed.  This stronger predicate is used only for the
    /// `arrays-read-conflict-uneval` completeness lane, where AY's primary
    /// array witness is poisoned but the separate model view can sometimes
    /// reconstruct and check the complete witness from authored definitions.
    pub(in crate::executor) fn confirm_sat_with_fully_evaluated_independent_gate(
        &self,
    ) -> GateVerdict {
        let Some(model) = self.last_model.as_ref() else {
            return GateVerdict::CannotConfirm {
                reason: "no model was produced".to_string(),
            };
        };
        let assertions = independent_gate_query_roots(self);
        if assertions.is_empty() {
            return GateVerdict::CannotConfirm {
                reason: "no authored assertions were available".to_string(),
            };
        }

        let view = IndependentModelView::new(self, model);
        view.ensure_def_index();
        let evaluator = Evaluator::new(&self.ctx.terms, &view);
        for assertion in assertions {
            let outcome = evaluator.evaluate(assertion);
            match outcome {
                EvalOutcome::Value(ModelValue::Bool(true)) => {}
                EvalOutcome::Value(ModelValue::Bool(false)) => {
                    return GateVerdict::ModelViolates { assertion };
                }
                EvalOutcome::Value(_) => {
                    return GateVerdict::CannotConfirm {
                        reason: "authored assertion did not evaluate to a boolean".to_string(),
                    };
                }
                EvalOutcome::Unevaluable(reason) => {
                    return GateVerdict::CannotConfirm { reason };
                }
            }
        }
        GateVerdict::ConfirmedSat
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
                && !self.is_exact_dt_internal_symbol(self.ctx.symbol_identity_name(name, info))
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
            if self.is_exact_dt_internal_symbol(self.ctx.symbol_identity_name(name, info)) {
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
    /// ENFORCEMENT IS UNCONDITIONAL for both a refutation and a coverage gap;
    /// no environment variable or API call can weaken this posture:
    ///
    /// * [`GateVerdict::ModelViolates`] — the emitted model ground-falsifies an
    ///   assertion: a concrete, independently-derived refutation of the witness.
    ///   Downgrading `Sat` to `Unknown` on a concrete refutation is ALWAYS sound
    ///   (`unknown` is never a wrong answer), so the downgrade is enforced
    ///   unconditionally. This is the permanent guarantee that no wrong-model
    ///   class — present or future — ships as `sat`.
    /// * [`GateVerdict::CannotConfirm`] — the independent evaluator could not
    ///   establish that every authored assertion and query-local assumption is
    ///   true in the published witness. The solver may be right, but the public
    ///   SAT claim is not independently certified, so it degrades to `Unknown`.
    ///
    /// The gate never alters a verdict toward unsoundness — at most
    /// `Sat` → `Unknown`.
    pub(in crate::executor) fn apply_independent_model_gate(
        &mut self,
        result: SolveResult,
    ) -> SolveResult {
        if result != SolveResult::Sat {
            self.revoke_quantified_model_confirmation_authority();
            return result;
        }
        let confirmation = self.quantified_model_confirmation.take();
        let verdict = self.confirm_sat_with_independent_gate_confirmation(confirmation.as_ref());
        // The direct quantified confirmation is a one-gate handoff, not
        // durable SAT authority. Consume it regardless of the independent
        // verdict so no later internal check can reuse it.
        self.revoke_quantified_model_confirmation_authority();
        match verdict {
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
                // `CannotConfirm` is distinct from `ModelViolates`: it is a
                // coverage gap, not evidence that the candidate is false. It is
                // nevertheless insufficient evidence for an authoritative SAT
                // publication. Correctness wins over completeness at this
                // boundary, so every unconfirmed witness fails closed.
                self.downgrade_sat_after_gate(&format!(
                    "independent model checker could not confirm the model: {reason}"
                ));
                SolveResult::Unknown
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
    pub(in crate::executor) fn downgrade_sat_after_gate(&mut self, detail: &str) {
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

    /// AUTHORITATIVE-GROUND FAIL-CLOSED gate (defense in depth, #sat-chokepoint).
    ///
    /// The independent gate rejects every [`GateVerdict::CannotConfirm`]
    /// before this pass can observe a public `Sat`. This narrower historical
    /// classifier remains in the funnel and in direct regression tests as a
    /// second fail-closed boundary: if ordering changes, an authoritatively
    /// ground assertion that the evaluator under-computed still cannot escape.
    ///
    /// This gate re-asks per-assertion: if any assertion the independent
    /// evaluator left unevaluated is authoritatively GROUND
    /// ([`assertion_is_authoritatively_ground`](Self::assertion_is_authoritatively_ground)),
    /// the `Sat` fails CLOSED — downgraded to `Unknown` through the same
    /// contract-carrying [`gate_keeps_sat`] core as the `ModelViolates` arm.
    /// Non-authoritative coverage gaps are handled by the universal independent
    /// gate, not accepted here.
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
        // This branch is reachable only in direct regression use or if a future
        // funnel reordering presents the recorded CannotConfirm state as Sat.
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
    /// coverage gap is outside this narrower defense-in-depth classifier.
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
                // coverage-gap signature recorded by the independent evaluator.
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
            // `ConfirmedSat` upstream and never reaches this fallback arm. The
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
    /// The independent gate reports these as a `CannotConfirm` coverage gap
    /// (sequence ground evaluation is deliberately incomplete — see
    /// [`authoritative_sort_class`](Self::authoritative_sort_class)) and now
    /// rejects them universally. This pass remains a theory-specific second
    /// boundary and preserves its regression diagnostics.
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
    /// never reaches this fallback arm, so it stays `sat`.
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
        // Defense in depth for a recorded CannotConfirm state. In the public
        // funnel the universal independent gate already downgraded that state.
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
        // unconfirmable leaf is ordinary quantifier/UF evaluator incompleteness
        // (E-matching / MBQI /
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
    /// incomplete; the universal independent gate handles that as `unknown`).
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
    /// (`ay_model_check` reports `CannotConfirm` on `Forall`/`Exists`). This
    /// earlier quantified-model checker fails closed on those obligations while
    /// retaining SAT completeness when it independently proves the emitted
    /// model's quantified assertions. Historically no gate checked a
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
    /// funnel before the compositional independent evaluator, over the funnel's
    /// scoped combined assertion set (so `check-sat-assuming` roots are covered).
    /// A successful certificate lets that evaluator skip only the quantified
    /// leaf conjuncts while it still checks every ground sibling. Zero cost on
    /// quantifier-free problems (keyed on `contains_quantifier`).
    pub(in crate::executor) fn apply_quantified_model_failclosed_gate(
        &mut self,
        result: SolveResult,
    ) -> SolveResult {
        // A confirmation is valid for exactly one direct handoff. Revoke any
        // predecessor before inspecting this result, including on non-SAT and
        // recursive paths.
        self.revoke_quantified_model_confirmation_authority();
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
        // Capture one exact public obligation window and use it for every
        // decision below, including all typed grant currentness checks and the
        // quantified leaves sent to nested confirmation.
        let query_roots = independent_gate_query_roots(self);
        let query_epoch = self.query_authority_epoch.clone();
        let source_context_stamp = self.ctx.source_context_stamp();
        let has_quantified_assertion = query_roots
            .iter()
            .copied()
            .any(|assertion| contains_quantifier(&self.ctx.terms, assertion));
        if !has_quantified_assertion {
            return result;
        }
        // The all-or-nothing DT certificate already checked every snapshot
        // universal against its completed model M'.  The retained emission
        // candidate M intentionally contains only the ground core, which the
        // preceding strict and independent gates still checked.  Record the
        // certificate handoff explicitly and do not let the independent gate's
        // ground-core `ConfirmedSat` marker short-circuit this provenance.
        if self.dt_cert_grant_active
            && self
                .dt_cert_query_grant
                .as_ref()
                .is_some_and(|grant| grant.is_current_for(self, &query_roots))
        {
            self.last_statistics
                .set_string("model_check_gate.quantified", "deferred-certified-dt");
            return result;
        }
        // Exact parallel of the DT handoff above, for the finite-table SAT
        // certificate on the CEGQI-classified-`Sat` route. That certificate has
        // likewise already checked EVERY snapshot universal, under an explicitly
        // constructed interpretation; the retained emission candidate carries
        // only the ground core, which the strict gate has checked and the
        // independent gate still checks. Without this handoff a `forall` over an
        // infinite domain is unevaluable against the ground-core model, this gate
        // fails closed, and a certified `Sat` is published as `unknown`.
        if self.finite_table_cert_grant_active
            && self
                .finite_table_cert_witness_state
                .as_ref()
                .is_some_and(|state| {
                    self.last_model.as_ref().is_some_and(|model| {
                        state.is_installed_current_for(self, &query_roots, model)
                    })
                })
        {
            self.last_statistics.set_string(
                "model_check_gate.quantified",
                "deferred-certified-finite-table",
            );
            return result;
        }
        // A BV quantifier full-domain proof is equally authoritative: every
        // binder value was covered either by exact finite-domain expansion,
        // exhaustive BV-MBQI enumeration, or a symbolic entailment refutation.
        // The independent evaluator still checks every ground sibling; only
        // the already-proved quantified leaves are discharged here.
        if self.bv_quantifier_full_domain_proof
            && self
                .bv_quantifier_full_domain_query_grant
                .as_ref()
                .is_some_and(|grant| grant.is_current_for(self, &query_roots))
        {
            self.last_statistics.set_string(
                "model_check_gate.quantified",
                "deferred-certified-bv-full-domain",
            );
            return result;
        }
        // Exact parallel again, for the CONSTANT-INTERPRETATION certificate.
        // Its evidence is the strongest of the three: every snapshot `forall`
        // was discharged by an independent ground-solver `Unsat` on the
        // negated body, substituted under the certified interpretation and
        // Skolemized with fresh constants. Same reason for the handoff — the
        // emission candidate cannot ground-evaluate those universals.
        //
        // Placed AFTER the two siblings, so a solve carrying more than one
        // marker records the older certificate's provenance and this one's
        // string is dropped. That ordering is deliberate and matches the
        // existing dt-before-finite-table precedence.
        if self.const_interp_cert_grant_active
            && self
                .const_interp_cert_witness_state
                .as_ref()
                .is_some_and(|state| {
                    self.last_model.as_ref().is_some_and(|model| {
                        state.is_installed_current_for(self, &query_roots, model)
                    })
                })
        {
            self.last_statistics.set_string(
                "model_check_gate.quantified",
                "deferred-certified-const-interp",
            );
            return result;
        }
        // MBQI SAT certification likewise discharges every restored universal
        // through a complete finite-domain check or an explicitly constructed
        // total interpretation. Preserve that authority through the public
        // funnel while leaving every ground sibling to the independent gate.
        if self.mbqi_sat_cert_grant_active
            && self
                .mbqi_sat_cert_query_grant
                .as_ref()
                .is_some_and(|grant| grant.is_current_for(self, &query_roots))
        {
            self.last_statistics
                .set_string("model_check_gate.quantified", "deferred-certified-mbqi-sat");
            return result;
        }
        // The sealed CEGQI theorem carries the exact completed UF model used
        // to refute every counterexample group. Its grant additionally binds
        // that model to this query epoch, restored root vector, live source
        // declarations, and frontend scope. Only quantified leaves are
        // discharged; the independent gate still checks every ground sibling.
        if self
            .cegqi_uf_recompletion_grant
            .as_ref()
            .is_some_and(|grant| grant.is_current_for(self, &query_roots))
        {
            self.last_statistics.set_string(
                "model_check_gate.quantified",
                "deferred-certified-cegqi-uf-recompletion",
            );
            return result;
        }
        // A quantified `Sat` without an emitted model has no witness that any
        // model gate can validate. In particular, CEGQI may classify an empty
        // ground remainder as `Sat` after stripping a quantifier nested under
        // a Boolean connective. That classification is not a certificate for
        // the original formula, so fail closed unless one of the authenticated
        // whole-snapshot certificate handoffs above is active.
        if self.last_model.is_none() {
            self.last_statistics
                .set_string("model_check_gate.quantified", "missing-model-failclosed");
            self.downgrade_sat_after_gate(
                "a quantified satisfiable result had no emitted model to validate",
            );
            return SolveResult::Unknown;
        }
        // Collect the quantified LEAF conjuncts of the scoped assertion set
        // (each `(and …)` assertion is true iff all its leaf conjuncts are).
        let mut candidates: Vec<TermId> = Vec::new();
        for &assertion in &query_roots {
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

        // Seal the exact candidate model BEFORE any nested confirmation solve.
        // Those solves save and restore this model, but a foreign replacement,
        // clone, query rotation, source mutation, or root-window mutation must
        // make the eventual handoff impossible.
        let Some(check_scope) = QuantifiedModelCheckScope::capture(
            self,
            query_epoch,
            source_context_stamp,
            &query_roots,
        ) else {
            self.last_statistics
                .set_string("model_check_gate.quantified", "stale-scope-failclosed");
            self.downgrade_sat_after_gate(
                "the quantified-model check scope was stale before validation",
            );
            return SolveResult::Unknown;
        };

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
                if deferred_any {
                    // A DEFERRED quantified conjunct is not model evidence. The
                    // public SAT boundary is universally fail-closed, independent
                    // of --self-check, so solver confidence alone cannot replace a
                    // complete certificate.
                    self.last_statistics
                        .set_string("model_check_gate.quantified", "deferred-failclosed");
                    self.downgrade_sat_after_gate(
                        "a quantified assertion could not be confirmed \
                         against the emitted model (deferred: the witness pins no \
                         interpretation for its functions) — failing closed rather \
                         than trusting the solver's unchecked `sat`",
                    );
                    SolveResult::Unknown
                } else {
                    let Some(confirmation) = check_scope.finish(self) else {
                        self.last_statistics
                            .set_string("model_check_gate.quantified", "stale-scope-failclosed");
                        self.downgrade_sat_after_gate(
                            "the quantified-model confirmation became stale during validation",
                        );
                        return SolveResult::Unknown;
                    };
                    self.quantified_model_confirmation = Some(confirmation);
                    self.last_statistics
                        .set_string("model_check_gate.quantified", "confirmed");
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

    /// Positively certify every quantified leaf in the CURRENT assertion set
    /// against the retained model, using the same checker as the mandatory
    /// publication gate.
    ///
    /// Quantifier-result restoration invokes this only after ordinary model
    /// validation has checked the ground siblings but skipped a quantifier.
    /// The bridge is deliberately limited to the regression class that needs
    /// it: at least one leaf must contain a provably vacuous binder that the
    /// mandatory checker removes. It must not turn that checker into a general
    /// post-hoc SAT authority for live quantifiers (in particular, enumerating
    /// only the datatype values present in a model does not cover a recursive
    /// datatype's full carrier). Every retained leaf must then return
    /// [`QuantifiedModelCheck::Confirmed`]. A refutation, deferral,
    /// indeterminate result, missing model, recursion, or exhausted deadline
    /// returns `false` and preserves the existing fail-closed `Unknown` path.
    pub(in crate::executor) fn quantified_model_gate_confirms_current_assertions(
        &mut self,
    ) -> bool {
        if self.last_model.is_none() || self.in_quantified_model_gate {
            return false;
        }

        let assertions = self.ctx.assertions.clone();
        let mut candidates = Vec::new();
        for assertion in assertions {
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
            for conjunct in conjuncts {
                let is_and_node = matches!(
                    self.ctx.terms.get(conjunct),
                    TermData::App(sym, _) if sym.name() == "and"
                );
                if !is_and_node
                    && contains_quantifier(&self.ctx.terms, conjunct)
                    && self.quantified_gate_drop_vacuous_binders(conjunct) != conjunct
                    && !candidates.contains(&conjunct)
                {
                    candidates.push(conjunct);
                }
            }
        }
        if candidates.is_empty() {
            return false;
        }

        let saved_deadline = self.solve_deadline.get();
        let budget = Instant::now() + Duration::from_secs(2);
        self.set_deadline(match saved_deadline {
            Some(deadline) if deadline < budget => Some(deadline),
            _ => Some(budget),
        });
        let saved_statistics = self.last_statistics.clone();
        self.in_quantified_model_gate = true;
        let confirmed = candidates.into_iter().all(|conjunct| {
            !self.solve_deadline.expired()
                && matches!(
                    self.check_quantified_conjunct_against_model(conjunct),
                    QuantifiedModelCheck::Confirmed
                )
        });
        self.in_quantified_model_gate = false;
        self.set_deadline(saved_deadline);
        self.last_statistics = saved_statistics;
        confirmed
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
    ///    * anything else (alternations, quantifiers under connectives) — the
    ///      QE prepass may produce a quantifier-free candidate, but its bounded
    ///      differential checks are not a proof of universal equivalence. The
    ///      candidate therefore never confirms or refutes the source; the gate
    ///      fails closed and leaves confirmation to the constructive witness
    ///      route or the exact global-validity fallback.
    fn check_quantified_conjunct_against_model(
        &mut self,
        conjunct: TermId,
    ) -> QuantifiedModelCheck {
        let source_conjunct = conjunct;
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

        // Exact vacuity normalization at the model-check boundary. The main
        // quantifier pipeline may certify a solve-time snapshot after dropping
        // an unused binder, but public SAT emission deliberately restores the
        // authored assertion before reaching this independent gate. Re-derive
        // only that unconditional equivalence here instead of trusting a
        // solve-time marker:
        //
        //   Q x. P  ==  P, when x is not free in P
        //
        // for either quantifier over SMT's non-empty sorts. This is intentionally
        // narrower than the preprocessing pass: no arithmetic feasibility,
        // hoisting, QE, or model-dependent fold is part of the rewrite.
        let conjunct = self.quantified_gate_drop_unused_binders(conjunct);

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

        // (1c2) Drop VACUOUS binders (#satgate-vacuous-binder). Over the
        // non-empty sorts SMT-LIB mandates, `∀v.φ ≡ φ ≡ ∃v.φ` whenever `v` does
        // not occur free in `φ` — an unconditional equivalence, so this cannot
        // change the conjunct's truth value in ANY structure, the emitted model
        // included. It is purely enabling: the routes below can only decide a
        // conjunct whose quantifier prefix they recognise, and a vacuous binder
        // buried in the matrix defeats both of them (the prefix route requires
        // `!contains_quantifier(matrix)`; the general route's `deep_qe` refuses
        // a vacuous binder outright — `find_bound_var → None` does not PROVE
        // non-occurrence there, see `qe_prepass`'s module header — and then
        // fails closed on the residual quantifier at
        // `quantified_gate_general_check`).
        //
        // WHY THIS EXISTS (bisected): `66538b006f` made gate (2)'s deferral
        // fail closed for every solve, not just under `--self-check`
        // (`if deferred_any && self.self_check` -> `if deferred_any`). That
        // turned "the gate could not decide this conjunct" into a published
        // `unknown`, which is how `benchmarks/smt/regression/
        // false_unsat_cegqi_entailed_inner_forall_witness.smt2` (measured `sat`
        // before that commit, `unknown` 5/5 after) regressed. The conjunct
        // reaching the gate there is
        //   (forall ((x Int)) (or (forall ((y Int)) (not (= 1 x))) (not (= 0 x))))
        // — `y` is vacuous (the `(select ((as const …) 1) y)` folded to `1`),
        // and dropping it leaves a plain universal prefix over a
        // quantifier-free matrix whose negation the gate's own nested solve
        // refutes. So the fix MINTS the certificate that was missing rather
        // than relaxing the funnel: the answer becomes `Confirmed`, not
        // `Deferred`. The fail-closed gate itself is untouched — every
        // conjunct the gate still cannot decide still degrades to `unknown`
        // (verified: `crates/ay-dpll/tests/fixtures/
        // ufbv_uf_completion_strict_leg_wrong_sat.smt2`, a declared-`unsat`
        // instance that a blanket disable of the site turns into a WRONG `sat`,
        // stays `unknown`).
        //
        // The non-occurrence test is a POSITIVE proof that fails safe on any
        // unrecognised node kind (`TermData` is `#[non_exhaustive]`), so a
        // binder is only ever dropped when its variable provably cannot appear
        // — never the dangling-binder UNSAT→SAT hazard.
        let devacuoused = self.quantified_gate_drop_vacuous_binders(conjunct);
        if devacuoused != conjunct && std::env::var("AY_DEBUG_QMG").is_ok() {
            // Observability, and the build MARKER this change is verified by
            // (`strings -a target/release/ay | grep 'QMG dropped vacuous
            // binders'`). A `last_statistics` key would be pointless here: the
            // gate snapshots and restores the statistics around the whole
            // conjunct loop, so anything written inside it is discarded.
            safe_eprintln!(
                "QMG dropped vacuous binders: {}",
                self.format_term(devacuoused)
            );
        }
        let conjunct = devacuoused;

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
                    let r = self.quantified_gate_checked_ground_solve(nested);
                    if std::env::var("AY_DEBUG_QMG").is_ok() {
                        safe_eprintln!("QMG universal nested result: {r:?}");
                    }
                    match r {
                        Some(QuantifiedGateCheckedGroundDecision {
                            decision: CheckedGroundDecision::Unsat(proof),
                            roots,
                        }) => {
                            if proof.consume(self, &roots) {
                                QuantifiedModelCheck::Confirmed
                            } else {
                                QuantifiedModelCheck::Indeterminate(
                                    "checked universal refutation became stale",
                                )
                            }
                        }
                        Some(QuantifiedGateCheckedGroundDecision {
                            decision: CheckedGroundDecision::Sat(model),
                            roots,
                        }) => {
                            if !model.consume(self, &roots) {
                                QuantifiedModelCheck::Indeterminate(
                                    "checked universal witness became stale",
                                )
                            } else if clean {
                                QuantifiedModelCheck::Refuted { clean: true }
                            } else {
                                QuantifiedModelCheck::Indeterminate(
                                    "universal negation satisfiable under partial pins",
                                )
                            }
                        }
                        None if closed => QuantifiedModelCheck::Deferred,
                        None => QuantifiedModelCheck::Indeterminate("nested solve undecided"),
                    }
                } else {
                    nested.push(instance);
                    match self.quantified_gate_checked_ground_solve(nested) {
                        // UNSAT over every structure: the model has no witness
                        // either — a sound refutation even under partial pins.
                        Some(QuantifiedGateCheckedGroundDecision {
                            decision: CheckedGroundDecision::Unsat(proof),
                            roots,
                        }) => {
                            if proof.consume(self, &roots) {
                                QuantifiedModelCheck::Refuted { clean }
                            } else {
                                QuantifiedModelCheck::Indeterminate(
                                    "checked existential refutation became stale",
                                )
                            }
                        }
                        Some(QuantifiedGateCheckedGroundDecision {
                            decision: CheckedGroundDecision::Sat(model),
                            roots,
                        }) => {
                            if !model.consume(self, &roots) {
                                QuantifiedModelCheck::Indeterminate(
                                    "checked existential witness became stale",
                                )
                            } else if clean {
                                QuantifiedModelCheck::Confirmed
                            } else {
                                QuantifiedModelCheck::Indeterminate(
                                    "existential witness under partial pins",
                                )
                            }
                        }
                        None if closed => QuantifiedModelCheck::Deferred,
                        None => QuantifiedModelCheck::Indeterminate("nested solve undecided"),
                    }
                }
            }
            // FORALL-EXISTS alternation: a universal prefix over a matrix
            // that is itself existential. The general route may run `deep_qe`
            // as a candidate screen, but never treats that sampled rewrite as
            // theorem authority. Its fail-closed result enables the
            // constructive witness route to try an exact witness obligation.
            // Confirm-only, so a failed synthesis leaves the general route's
            // own fail-closed outcome exactly as it was.
            Some(true) => {
                let general = self.quantified_gate_general_check(
                    conjunct,
                    &interps,
                    &mut elems,
                    model_independent,
                );
                if matches!(
                    &general,
                    QuantifiedModelCheck::Deferred | QuantifiedModelCheck::Indeterminate(_)
                ) {
                    match self.quantified_gate_forall_exists_witness_check(
                        &binders, matrix, &interps, &mut elems,
                    ) {
                        Some(confirmed) => confirmed,
                        None => general,
                    }
                } else {
                    general
                }
            }
            _ => self.quantified_gate_general_check(
                conjunct,
                &interps,
                &mut elems,
                model_independent,
            ),
        };
        // Prefer the model-specific check, including the constructive
        // FORALL-EXISTS witness route above. In particular, a concrete
        // refutation of the emitted witness must never be overridden by a
        // stronger global-validity query. The latter is only a completeness
        // fallback after every model-specific route could not decide the
        // conjunct. `Deferred` is likewise undecided: it means a
        // model-independent closed residue survived QE, not that theorem
        // authority has already confirmed the source.
        let outcome = match outcome {
            undecided @ (QuantifiedModelCheck::Indeterminate(_)
            | QuantifiedModelCheck::Deferred) => {
                match self.certify_globally_valid_quantified_conjunct(source_conjunct) {
                    Some(checked) => checked.confirm(self, source_conjunct),
                    None => undecided,
                }
            }
            decided => decided,
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

    /// Drop only semantically unused quantifier binders for the quantified
    /// model gate.
    ///
    /// Binder occurrence is checked with lexical shadowing: a same-named inner
    /// quantifier/`let` binding does not keep an outer binder alive, while a
    /// `let` value is still inspected because simultaneous SMT-LIB bindings do
    /// not scope over their own right-hand sides. Trigger groups mentioning a
    /// removed binder are discarded; triggers guide matching but do not change
    /// quantifier semantics.
    fn quantified_gate_drop_unused_binders(&mut self, root: TermId) -> TermId {
        let mut memo: DetHashMap<TermId, TermId> = DetHashMap::default();
        self.quantified_gate_drop_unused_binders_rec(root, &mut memo)
    }

    fn quantified_gate_drop_unused_binders_rec(
        &mut self,
        term: TermId,
        memo: &mut DetHashMap<TermId, TermId>,
    ) -> TermId {
        if let Some(&normalized) = memo.get(&term) {
            return normalized;
        }
        let normalized = match self.ctx.terms.get(term).clone() {
            TermData::Const(_) | TermData::Var(..) => term,
            TermData::App(symbol, arguments) => {
                let normalized_arguments: Vec<TermId> = arguments
                    .iter()
                    .map(|&argument| self.quantified_gate_drop_unused_binders_rec(argument, memo))
                    .collect();
                if normalized_arguments == arguments {
                    term
                } else {
                    let sort = self.ctx.terms.sort(term).clone();
                    self.ctx.terms.mk_app(symbol, normalized_arguments, sort)
                }
            }
            TermData::Not(inner) => {
                let normalized_inner = self.quantified_gate_drop_unused_binders_rec(inner, memo);
                if normalized_inner == inner {
                    term
                } else {
                    self.ctx.terms.mk_not(normalized_inner)
                }
            }
            TermData::Ite(condition, then_term, else_term) => {
                let normalized_condition =
                    self.quantified_gate_drop_unused_binders_rec(condition, memo);
                let normalized_then = self.quantified_gate_drop_unused_binders_rec(then_term, memo);
                let normalized_else = self.quantified_gate_drop_unused_binders_rec(else_term, memo);
                if normalized_condition == condition
                    && normalized_then == then_term
                    && normalized_else == else_term
                {
                    term
                } else {
                    self.ctx
                        .terms
                        .mk_ite(normalized_condition, normalized_then, normalized_else)
                }
            }
            TermData::Let(bindings, body) => {
                let normalized_bindings: Vec<(String, TermId)> = bindings
                    .iter()
                    .map(|(name, value)| {
                        (
                            name.clone(),
                            self.quantified_gate_drop_unused_binders_rec(*value, memo),
                        )
                    })
                    .collect();
                let normalized_body = self.quantified_gate_drop_unused_binders_rec(body, memo);
                if normalized_bindings == bindings && normalized_body == body {
                    term
                } else {
                    self.ctx.terms.mk_let(normalized_bindings, normalized_body)
                }
            }
            TermData::Forall(vars, body, triggers) => {
                let normalized_body = self.quantified_gate_drop_unused_binders_rec(body, memo);
                let kept: Vec<(String, Sort)> = vars
                    .iter()
                    .filter(|(name, _)| {
                        self.quantified_gate_name_occurs_free(normalized_body, name)
                    })
                    .cloned()
                    .collect();
                if kept.is_empty() {
                    normalized_body
                } else if kept.len() == vars.len() && normalized_body == body {
                    term
                } else {
                    let triggers = self.quantified_gate_retain_triggers(&triggers, &vars, &kept);
                    self.ctx
                        .terms
                        .mk_forall_with_triggers(kept, normalized_body, triggers)
                }
            }
            TermData::Exists(vars, body, triggers) => {
                let normalized_body = self.quantified_gate_drop_unused_binders_rec(body, memo);
                let kept: Vec<(String, Sort)> = vars
                    .iter()
                    .filter(|(name, _)| {
                        self.quantified_gate_name_occurs_free(normalized_body, name)
                    })
                    .cloned()
                    .collect();
                if kept.is_empty() {
                    normalized_body
                } else if kept.len() == vars.len() && normalized_body == body {
                    term
                } else {
                    let triggers = self.quantified_gate_retain_triggers(&triggers, &vars, &kept);
                    self.ctx
                        .terms
                        .mk_exists_with_triggers(kept, normalized_body, triggers)
                }
            }
            // `TermData` is non-exhaustive. A future term form is retained
            // byte-for-byte until its binding semantics are audited here.
            _ => term,
        };
        memo.insert(term, normalized);
        normalized
    }

    /// Whether `target` occurs free with respect to a quantifier that binds it
    /// outside `term`.
    fn quantified_gate_name_occurs_free(&self, term: TermId, target: &str) -> bool {
        match self.ctx.terms.get(term) {
            TermData::Var(name, _) => name == target,
            TermData::App(_, arguments) => arguments
                .iter()
                .any(|&argument| self.quantified_gate_name_occurs_free(argument, target)),
            TermData::Not(inner) => self.quantified_gate_name_occurs_free(*inner, target),
            TermData::Ite(condition, then_term, else_term) => {
                self.quantified_gate_name_occurs_free(*condition, target)
                    || self.quantified_gate_name_occurs_free(*then_term, target)
                    || self.quantified_gate_name_occurs_free(*else_term, target)
            }
            TermData::Let(bindings, body) => {
                bindings
                    .iter()
                    .any(|(_, value)| self.quantified_gate_name_occurs_free(*value, target))
                    || (!bindings.iter().any(|(name, _)| name == target)
                        && self.quantified_gate_name_occurs_free(*body, target))
            }
            TermData::Forall(vars, body, _) | TermData::Exists(vars, body, _) => {
                !vars.iter().any(|(name, _)| name == target)
                    && self.quantified_gate_name_occurs_free(*body, target)
            }
            TermData::Const(_) => false,
            _ => false,
        }
    }

    fn quantified_gate_retain_triggers(
        &self,
        triggers: &[Vec<TermId>],
        all_vars: &[(String, Sort)],
        kept: &[(String, Sort)],
    ) -> Vec<Vec<TermId>> {
        let dropped: Vec<&str> = all_vars
            .iter()
            .filter(|(name, _)| !kept.iter().any(|(kept_name, _)| kept_name == name))
            .map(|(name, _)| name.as_str())
            .collect();
        triggers
            .iter()
            .filter(|group| {
                group.iter().all(|&trigger| {
                    dropped
                        .iter()
                        .all(|name| !self.quantified_gate_name_occurs_free(trigger, name))
                })
            })
            .cloned()
            .collect()
    }

    /// Prove a quantified conjunct independently of the retained model.
    ///
    /// Negative-polarity deep Skolemization produces an equisatisfiable NNF
    /// representation of `not source`. Only a quantifier-free residue may enter
    /// the isolated solver. A definitive UNSAT therefore proves `source` valid
    /// in every interpretation; any alternation residue, stop, source-context
    /// change, or non-UNSAT result declines without minting authority.
    fn certify_globally_valid_quantified_conjunct(
        &mut self,
        source: TermId,
    ) -> Option<GloballyValidQuantifiedConjunct> {
        if self.should_abort_theory_loop() {
            return None;
        }

        // The source-to-ground implication is intentionally tiny and exact:
        // only a trigger-free top-level, single-binder forall with a
        // quantifier-free body. Triggers are semantically annotations, but
        // excluding them keeps this proof kernel's source reconstruction
        // byte-exact instead of silently discarding authored metadata.
        // Deep/nested and multi-binder Skolemization remain useful candidate
        // transforms elsewhere, but their richer dependency/capture rules are
        // not theorem authority for this fallback.
        let (binder_name, binder_sort, body) = match self.ctx.terms.get(source).clone() {
            TermData::Forall(binders, body, triggers)
                if binders.len() == 1 && triggers.is_empty() =>
            {
                let (name, sort) = binders.into_iter().next()?;
                if contains_quantifier(&self.ctx.terms, body) {
                    return None;
                }
                (name, sort, body)
            }
            _ => return None,
        };

        let source_context_stamp = self.ctx.source_context_stamp();
        let term_count_before = self.ctx.terms.len();
        let (negated, provenance) =
            crate::skolemize::skolemize_deep_with_provenance(&mut self.ctx.terms, source, false);
        let negated = negated?;
        let [provenance] = provenance.as_slice() else {
            return None;
        };
        if provenance.quantified != source
            || contains_quantifier(&self.ctx.terms, negated)
            || self.should_abort_theory_loop()
        {
            return None;
        }

        // Authenticate the actual witness minted by Skolemization. Registry
        // membership is creation-site provenance rather than a name-prefix
        // heuristic; the term-index bounds additionally prove this live Var
        // was appended by this exact transformation, not borrowed from the
        // pre-existing source universe.
        let TermData::Var(witness_name, _) = self.ctx.terms.get(provenance.witness) else {
            return None;
        };
        if (provenance.witness.0 as usize) < term_count_before
            || (provenance.witness.0 as usize) >= self.ctx.terms.len()
            || self.ctx.terms.sort(provenance.witness) != &binder_sort
            || !self.ctx.terms.is_skolem_symbol(witness_name)
        {
            return None;
        }

        // Recompute the exact source-body substitution independently of the
        // provenance record, then require the returned root to be the literal
        // negation of that same instance. Any folding or different rewrite
        // shape declines; it can cost completeness but cannot launder a nearby
        // formula's ground proof into authority for `source`.
        let mut substitution: DetHashMap<String, TermId> = DetHashMap::default();
        substitution.insert(binder_name, provenance.witness);
        let recomputed =
            crate::ematching::subst_vars_exact_qf(&mut self.ctx.terms, body, &substitution)?;
        if recomputed != provenance.instance
            || !matches!(
                self.ctx.terms.get(negated),
                TermData::Not(instance) if *instance == recomputed
            )
        {
            return None;
        }

        // Do not run this theorem query on the outer Executor. In particular,
        // `active_support_axioms` contains ground instances that are valid only
        // under the OUTER asserted foralls. Letting one of those instances into
        // a refutation of `not source` would be circular: a consequence of
        // `source` is not an admissible premise for proving `source` globally
        // valid. The disposable helper clones only the frontend Context into a
        // fresh Executor, so support axioms, semantic-verification memos, proof
        // state, models, and every other solve-derived artifact all start empty
        // and die with the probe.
        let roots = vec![negated];
        let checked = self.checked_ground_solve(roots.clone(), LogicCategory::Other, 500)?;
        let verified_unsat = match checked {
            CheckedGroundDecision::Unsat(proof) => proof.consume(self, &roots),
            CheckedGroundDecision::Sat(_) => false,
        };
        if !verified_unsat
            || self.should_abort_theory_loop()
            || source_context_stamp != self.ctx.source_context_stamp()
        {
            return None;
        }
        Some(GloballyValidQuantifiedConjunct {
            source,
            query_epoch: self.query_authority_epoch.clone(),
            source_context_stamp,
            roots: independent_gate_query_roots(self).into(),
            term_snapshot: self.ctx.terms.snapshot_stamp(),
        })
    }

    /// FORALL-EXISTS route (#quantified-model-gate alternation): confirm
    /// `∀x⃗. ∃y⃗. body` in the emitted model by SYNTHESISING a witness TERM for
    /// the existential block and discharging the resulting purely UNIVERSAL
    /// obligation with the gate's own quantifier-FREE nested solver.
    ///
    /// The caller has already normalized the conjunct's polarity to
    /// `∀ uni_binders. matrix`; this route requires `matrix` itself to
    /// normalize to `∃ ex_binders. body` with `body` quantifier-free.
    ///
    /// ## Why the existing routes cannot
    ///
    /// The prefix route only fires when the matrix under the FIRST quantifier
    /// block is quantifier-free — an alternation breaks its parse loop on the
    /// polarity switch. The general route hands `pins ∧ conjunct` to
    /// `deep_qe`, which is a Presburger/LRA elimination: it leaves an
    /// NIA alternation exactly as it found it, and
    /// [`Self::quantified_gate_general_check`] then refuses the residual
    /// quantifier. `quantified_gate_checked_ground_solve` likewise refuses any
    /// quantified assertion outright. So a ∀∃ conjunct has NO ground instance
    /// for the gate to evaluate and every lane ends in `Deferred` /
    /// `Indeterminate`, i.e. a published `unknown`.
    ///
    /// ## The certificate
    ///
    /// For a term tuple `t⃗` over the universal variables,
    ///
    /// ```text
    ///   pins ∧ distinct ∧ ¬body[y⃗ := t⃗][x⃗ := sk⃗]   UNSAT      (ground solve)
    ///     ⟹ pins ∧ distinct ⊨ ∀x⃗. body[y⃗ := t⃗]              (sk⃗ fresh)
    ///     ⟹ M ⊨ ∀x⃗. body[y⃗ := t⃗]              (M ⊨ pins ∧ distinct, by construction)
    ///     ⟹ M ⊨ ∀x⃗ ∃y⃗. body                    (t⃗ IS a witness function)
    /// ```
    ///
    /// so the accepting evidence is a GROUND `Unsat` — exactly the evidence
    /// class the universal prefix route already accepts — never a nested
    /// QUANTIFIED verdict. `¬body` is built after the same
    /// [`Self::apply_quantified_gate_uf_interps`] substitution and under the
    /// same [`Self::quantified_gate_model_pins`] the other routes use, so the
    /// emitted model's own values are what the ground solve reasons about: a
    /// model that falsifies the alternation makes the negation SATISFIABLE and
    /// this route declines (the NON-VACUITY bar — see
    /// `forall_exists_witness_route_confirm_is_model_sensitive`, which holds
    /// the formula fixed and flips only the emitted value of a constant).
    ///
    /// ## Fail-closed perimeter
    ///
    /// CONFIRM-ONLY, and grant-only. Substituting a term for an existential
    /// binder is an UNDER-approximation (`∀x⃗. φ[y:=t] ⟹ ∀x⃗∃y. φ`, never the
    /// converse), so a candidate that fails to discharge proves nothing about
    /// the model and returns `None`; the caller then runs the unchanged
    /// general route and its unchanged fail-closed outcomes. This route never
    /// returns `Refuted` and never converts an `Indeterminate` into a
    /// `Deferred`. Partial pins only make the ground obligation HARDER (an
    /// unpinned leaf is universally quantified over by the `Unsat`), so the
    /// implication above survives `pins.total == false`; the same holds for an
    /// unsubstituted uninterpreted function, which stays free.
    fn quantified_gate_forall_exists_witness_check(
        &mut self,
        uni_binders: &[(String, Sort)],
        matrix: TermId,
        interps: &DetHashMap<String, QuantifiedGateUfInterp>,
        elems: &mut QuantifiedGateElements,
    ) -> Option<QuantifiedModelCheck> {
        let debug = std::env::var("AY_DEBUG_QMG").is_ok();
        if uni_binders.is_empty() || uni_binders.len() > QUANTIFIED_GATE_MAX_WITNESS_BINDERS {
            return None;
        }
        // Fixed-interpretation binder sorts only. An uninterpreted-sort
        // universal's truth depends on the model's carrier, which the prefix
        // route handles by expanding over the printed universe; this route
        // deliberately does not duplicate that machinery.
        if !uni_binders
            .iter()
            .all(|(_, sort)| quantified_gate_witness_sort(sort))
        {
            return None;
        }

        // Second polarity-normalized block: `matrix ≡ ∃ ex_binders. body`.
        let mut ex_binders: Vec<(String, Sort)> = Vec::new();
        let mut universal: Option<bool> = None;
        let mut cur = matrix;
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
                    ex_binders.extend(vars);
                    cur = body;
                }
                TermData::Exists(vars, body, _) => {
                    if *universal.get_or_insert(!positive) == positive {
                        break;
                    }
                    ex_binders.extend(vars);
                    cur = body;
                }
                _ => break,
            }
        }
        if universal != Some(false) {
            return None;
        }
        let body = if positive {
            cur
        } else {
            self.ctx.terms.mk_not(cur)
        };
        if contains_quantifier(&self.ctx.terms, body) {
            return None;
        }
        if ex_binders.is_empty() || ex_binders.len() > QUANTIFIED_GATE_MAX_WITNESS_BINDERS {
            return None;
        }
        if !ex_binders
            .iter()
            .all(|(_, sort)| quantified_gate_witness_sort(sort))
        {
            return None;
        }
        // A name shared between the two blocks (or repeated inside one) makes
        // "substitute the universal variable for the existential binder" an
        // ill-defined capture question. Refuse rather than reason about it.
        let mut names: Vec<&String> = uni_binders
            .iter()
            .chain(ex_binders.iter())
            .map(|(n, _)| n)
            .collect();
        let before = names.len();
        names.sort();
        names.dedup();
        if names.len() != before {
            return None;
        }

        // Candidate witness terms per existential binder, strongest first.
        let mut per_binder: Vec<Vec<TermId>> = Vec::with_capacity(ex_binders.len());
        for ex in &ex_binders {
            let candidates = self.quantified_gate_witness_candidates(body, ex, uni_binders);
            if candidates.is_empty() {
                return None;
            }
            per_binder.push(candidates);
        }

        for tuple in quantified_gate_witness_tuples(&per_binder) {
            if self.solve_deadline.expired() {
                break;
            }
            let mut subst: DetHashMap<String, TermId> = DetHashMap::default();
            for ((name, _), &witness) in ex_binders.iter().zip(tuple.iter()) {
                subst.insert(name.clone(), witness);
            }
            let instantiated = crate::ematching::subst_vars(&mut self.ctx.terms, body, &subst);

            // Skolemize the universal prefix with fresh constants.
            let mut universals: DetHashMap<String, TermId> = DetHashMap::default();
            let mut skolems: HashSet<TermId> = HashSet::default();
            for (name, sort) in uni_binders {
                let fresh = self
                    .ctx
                    .terms
                    .mk_fresh_var(&format!("qmg!fe!{name}"), sort.clone());
                skolems.insert(fresh);
                universals.insert(name.clone(), fresh);
            }
            let instance =
                crate::ematching::subst_vars(&mut self.ctx.terms, instantiated, &universals);
            let (instance, _) = self.apply_quantified_gate_uf_interps(instance, interps, elems);
            let mut exclude = skolems;
            exclude.extend(elems.all_terms());
            let pins = self.quantified_gate_model_pins(instance, elems, &exclude);
            let mut nested = pins.equalities.clone();
            nested.extend(elems.distinct_assertions(&mut self.ctx.terms));
            let target = self.ctx.terms.mk_not(instance);
            nested.push(target);
            let result = self.quantified_gate_checked_ground_solve(nested);
            if debug {
                safe_eprintln!(
                    "QMG forall-exists witness obligation: not {} -> {result:?}",
                    self.format_term(instance)
                );
            }
            if let Some(QuantifiedGateCheckedGroundDecision {
                decision: CheckedGroundDecision::Unsat(proof),
                roots,
            }) = result
            {
                if proof.consume(self, &roots) {
                    return Some(QuantifiedModelCheck::Confirmed);
                }
            }
        }
        None
    }

    /// Witness-term candidates for ONE existential binder of
    /// [`Self::quantified_gate_forall_exists_witness_check`], strongest first:
    ///
    /// 1. EQUALITY-DETERMINED — a top-level conjunct `(= y e)` / `(= e y)` of
    ///    the matrix whose other side names no existential binder. Such an
    ///    equality is a NECESSARY condition of the matrix, so if a witness
    ///    exists at all it is this term.
    /// 2. IDENTITY on each universal binder of the same sort (`y := x`), the
    ///    witness for the monotone shapes (`∀x∃y. y·y ≥ x`).
    /// 3. The sort's zero/false constant.
    ///
    /// Purely heuristic: every candidate is CHECKED by a ground `Unsat`
    /// obligation before it can confirm anything, so a bad candidate costs a
    /// nested solve and nothing else.
    fn quantified_gate_witness_candidates(
        &mut self,
        body: TermId,
        ex: &(String, Sort),
        uni_binders: &[(String, Sort)],
    ) -> Vec<TermId> {
        let (ex_name, ex_sort) = ex;
        let mut out: Vec<TermId> = Vec::new();

        let mut conjuncts = Vec::new();
        crate::executor::quantifier_loop::collect_and_conjuncts(
            &self.ctx.terms,
            body,
            &mut conjuncts,
        );
        if conjuncts.is_empty() {
            conjuncts.push(body);
        }
        for conjunct in conjuncts {
            let TermData::App(sym, args) = self.ctx.terms.get(conjunct).clone() else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            for (side, other) in [(args[0], args[1]), (args[1], args[0])] {
                let is_binder = matches!(
                    self.ctx.terms.get(side),
                    TermData::Var(name, _) if name == ex_name
                );
                if !is_binder || self.ctx.terms.sort(other) != ex_sort {
                    continue;
                }
                // The other side must be a term over the UNIVERSAL variables
                // and model symbols only: a witness may not mention the
                // existential binders it is supposed to eliminate.
                if quantified_gate_mentions_var(&self.ctx.terms, other, ex_name) {
                    continue;
                }
                if !out.contains(&other) {
                    out.push(other);
                }
            }
        }

        for (name, sort) in uni_binders {
            if sort != ex_sort {
                continue;
            }
            let var = self.ctx.terms.mk_var(name.clone(), sort.clone());
            if !out.contains(&var) {
                out.push(var);
            }
        }

        let zero = match ex_sort {
            Sort::Int => Some(self.ctx.terms.mk_int(num_bigint::BigInt::from(0))),
            Sort::Real => Some(self.ctx.terms.mk_rational(
                num_rational::BigRational::from_integer(num_bigint::BigInt::from(0)),
            )),
            Sort::Bool => Some(self.ctx.terms.mk_bool(false)),
            Sort::BitVec(bv) => {
                let width = bv.width;
                Some(self.ctx.terms.mk_bitvec(num_bigint::BigInt::from(0), width))
            }
            _ => None,
        };
        if let Some(zero) = zero {
            if !out.contains(&zero) {
                out.push(zero);
            }
        }

        out.truncate(QUANTIFIED_GATE_MAX_WITNESS_CANDIDATES);
        out
    }

    /// General/alternation candidate screen.
    ///
    /// `deep_qe` is guarded by bounded differential testing, which is useful
    /// for finding candidate residues but is not a universal equivalence proof.
    /// Consequently neither a SAT nor an UNSAT solve of its quantifier-free
    /// residue is authority about the authored quantified conjunct. This route
    /// always fails closed; exact confirmation remains available through the
    /// constructive forall-exists witness route and the isolated
    /// global-validity proof fallback.
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
        let has_residual_quantifier = nested
            .iter()
            .any(|&t| contains_quantifier(&self.ctx.terms, t));
        if std::env::var("AY_DEBUG_QMG").is_ok() {
            safe_eprintln!(
                "QMG general clean={clean} closed={closed} total={} ufs_complete={ufs_complete} residual_quantifier={has_residual_quantifier}",
                pins.total
            );
            for &term in &nested {
                safe_eprintln!("QMG general assertion: {}", self.format_term(term));
            }
        }
        if has_residual_quantifier {
            if closed {
                return QuantifiedModelCheck::Deferred;
            }
            return QuantifiedModelCheck::Indeterminate("residual quantifier after QE");
        }
        // Do not solve the candidate and map its result back to the source.
        // Without a proof that `deep_qe` preserved this exact formula in both
        // directions, either mapping would be circular authority: SAT could
        // confirm a false source, and UNSAT could spuriously refute a valid
        // emitted model. The exact routes following this function own both
        // decisions.
        QuantifiedModelCheck::Indeterminate(
            "quantifier-free QE candidate lacks exact equivalence authority",
        )
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
                // Certificate-built total tables have an exact typed source.
                // Consume it directly instead of reparsing the separately
                // rendered EUF table (`-1`/`(- 1)`, Real decimal spellings,
                // and placeholder resolution must not change the model the
                // SAT certificate proved).
                if let Some(total) = model.certified_total_ufs.by_symbol.get(name) {
                    let (arg_sorts, result_sort) = declared[name].clone();
                    if total.arg_sorts != arg_sorts
                        || total.result_sort != result_sort
                        || total.rows.len() >= QUANTIFIED_GATE_MAX_UF_ROWS
                    {
                        if qmg_debug {
                            safe_eprintln!(
                                "QMG interp {name}: dropped (typed total-table signature/size mismatch)"
                            );
                        }
                        deferable_heads += 1;
                        continue;
                    }
                    let mut rows: Vec<(Vec<QmgRowVal>, QmgRowVal)> = total
                        .rows
                        .iter()
                        .map(|(args, value)| {
                            (
                                args.iter().cloned().map(QmgRowVal::Eval).collect(),
                                QmgRowVal::Eval(value.clone()),
                            )
                        })
                        .collect();
                    // Phase B treats the final row's result as the else branch;
                    // its argument tuple is converted but never used.
                    let carrier = arg_sorts
                        .iter()
                        .map(|_| {
                            QmgRowVal::Eval(EvalValue::Rational(
                                num_rational::BigRational::from_integer(num_bigint::BigInt::from(
                                    0,
                                )),
                            ))
                        })
                        .collect();
                    rows.push((carrier, QmgRowVal::Eval(total.default.clone())));
                    collected.push(RowValues {
                        name: name.clone(),
                        arg_sorts,
                        result_sort,
                        rows,
                    });
                    continue;
                }
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

    /// Drop VACUOUS binders from `term` (#satgate-vacuous-binder), innermost
    /// first, collapsing a fully-vacuous quantifier to its body.
    ///
    /// Every SMT-LIB sort is non-empty, so `∀v:S.φ ≡ φ` and `∃v:S.φ ≡ φ`
    /// whenever `v` does not occur free in `φ`. The rewrite is therefore an
    /// unconditional EQUIVALENCE at any polarity and any binder depth: it
    /// cannot change the conjunct's truth value in the emitted model, so it can
    /// neither manufacture a `Confirmed` nor suppress a `Refuted`. It only
    /// removes prefix noise that stops the routes in
    /// [`check_quantified_conjunct_against_model`] from DECIDING a conjunct
    /// they are otherwise perfectly able to decide (see the call site for the
    /// bisected `66538b006f` regression this recovers).
    ///
    /// SOUNDNESS: a binder is dropped only on a POSITIVE non-occurrence proof
    /// from [`Self::quantified_gate_binder_may_occur`], which answers "may
    /// occur" for every node kind it does not recognise. Dropping a binder
    /// whose variable still occurs would free it — the dangling-binder
    /// UNSAT→SAT hazard `qe_prepass`/`qe_light` document — so the conservative
    /// direction here is to KEEP, which merely leaves the gate where it is
    /// today (a fail-closed `unknown`). `Let` bodies are not rewritten
    /// (a let-bound name could shadow a binder), only traversed by the
    /// occurrence test.
    fn quantified_gate_drop_vacuous_binders(&mut self, term: TermId) -> TermId {
        let mut cache: DetHashMap<TermId, TermId> = DetHashMap::default();
        self.quantified_gate_drop_vacuous_binders_memo(term, &mut cache)
    }

    /// Memoized worker for [`Self::quantified_gate_drop_vacuous_binders`]. The
    /// cache is sound over the hash-consed DAG because a node's rewrite depends
    /// only on that node's own subtree (each drop is an equivalence for ALL
    /// valuations of the term's free variables, outer-bound ones included), and
    /// it keeps a shared subterm from being rewritten once per path.
    fn quantified_gate_drop_vacuous_binders_memo(
        &mut self,
        term: TermId,
        cache: &mut DetHashMap<TermId, TermId>,
    ) -> TermId {
        if let Some(&hit) = cache.get(&term) {
            return hit;
        }
        let rewritten = match self.ctx.terms.get(term).clone() {
            TermData::Const(_) | TermData::Var(..) => term,
            TermData::App(sym, args) => {
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&a| self.quantified_gate_drop_vacuous_binders_memo(a, cache))
                    .collect();
                if new_args == args {
                    term
                } else {
                    let sort = self.ctx.terms.sort(term).clone();
                    self.ctx.terms.mk_app(sym, new_args, sort)
                }
            }
            TermData::Not(inner) => {
                let ni = self.quantified_gate_drop_vacuous_binders_memo(inner, cache);
                if ni == inner {
                    term
                } else {
                    self.ctx.terms.mk_not(ni)
                }
            }
            TermData::Ite(c, t, e) => {
                let nc = self.quantified_gate_drop_vacuous_binders_memo(c, cache);
                let nt = self.quantified_gate_drop_vacuous_binders_memo(t, cache);
                let ne = self.quantified_gate_drop_vacuous_binders_memo(e, cache);
                if nc == c && nt == t && ne == e {
                    term
                } else {
                    self.ctx.terms.mk_ite(nc, nt, ne)
                }
            }
            TermData::Forall(vars, body, triggers) => {
                let nb = self.quantified_gate_drop_vacuous_binders_memo(body, cache);
                let kept: Vec<(String, Sort)> = vars
                    .iter()
                    .filter(|(n, _)| self.quantified_gate_binder_may_occur(nb, n))
                    .cloned()
                    .collect();
                if kept.is_empty() {
                    nb
                } else if kept.len() == vars.len() && nb == body {
                    term
                } else {
                    // A trigger group mentioning a dropped binder is invalid;
                    // drop the group (triggers are E-matching hints, never
                    // semantics).
                    let new_triggers =
                        quantified_gate_retain_triggers(&self.ctx.terms, &triggers, &vars, &kept);
                    self.ctx
                        .terms
                        .mk_forall_with_triggers(kept, nb, new_triggers)
                }
            }
            TermData::Exists(vars, body, triggers) => {
                let nb = self.quantified_gate_drop_vacuous_binders_memo(body, cache);
                let kept: Vec<(String, Sort)> = vars
                    .iter()
                    .filter(|(n, _)| self.quantified_gate_binder_may_occur(nb, n))
                    .cloned()
                    .collect();
                if kept.is_empty() {
                    nb
                } else if kept.len() == vars.len() && nb == body {
                    term
                } else {
                    let new_triggers =
                        quantified_gate_retain_triggers(&self.ctx.terms, &triggers, &vars, &kept);
                    self.ctx
                        .terms
                        .mk_exists_with_triggers(kept, nb, new_triggers)
                }
            }
            // `Let` (a let-bound name may shadow the binder) and any node kind
            // this gate does not model are left verbatim.
            _ => term,
        };
        cache.insert(term, rewritten);
        rewritten
    }

    /// Whether a binder named `name` MAY occur anywhere in `term`.
    ///
    /// `false` is a PROOF of non-occurrence: every node kind that can hold a
    /// subterm is traversed, and any unrecognised kind (`TermData` is
    /// `#[non_exhaustive]`) answers `true`. Shadowing inner binders are not
    /// stopped at, which can only over-report occurrence — and over-reporting
    /// merely CONSERVES a binder, never drops a live one. This is the
    /// difference from `result_mapping`'s `term_mentions_name`, whose
    /// unrecognised-node fallback is `false`; the SAT-publication gate must not
    /// mint a certificate on an unverified assumption.
    fn quantified_gate_binder_may_occur(&self, term: TermId, name: &str) -> bool {
        let mut stack = vec![term];
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::Const(_) => {}
                TermData::Var(n, _) => {
                    if n == name {
                        return true;
                    }
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                TermData::Forall(_, b, triggers) | TermData::Exists(_, b, triggers) => {
                    stack.push(*b);
                    for grp in triggers {
                        stack.extend(grp.iter().copied());
                    }
                }
                TermData::Let(bindings, b) => {
                    stack.extend(bindings.iter().map(|(_, v)| *v));
                    stack.push(*b);
                }
                // Unrecognised node kind: NOT traversed, so non-occurrence is
                // unproven — answer "may occur" and keep the binder.
                _ => return true,
            }
        }
        false
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

    /// Check one quantifier-free gate obligation through the public verdict
    /// funnels on a disposable executor, then consume the resulting affine
    /// decision only while its exact ordered roots and every outer authority
    /// binding remain current. Raw `solve_for_category` results never cross
    /// this boundary: SAT requires an independently validated model and UNSAT
    /// requires a strictly verified proof.
    fn quantified_gate_checked_ground_solve(
        &mut self,
        assertions: Vec<TermId>,
    ) -> Option<QuantifiedGateCheckedGroundDecision> {
        if assertions
            .iter()
            .any(|&t| contains_quantifier(&self.ctx.terms, t))
        {
            return None;
        }
        let roots = assertions;
        let decision = self.checked_ground_solve(roots.clone(), LogicCategory::Other, 500)?;
        Some(QuantifiedGateCheckedGroundDecision {
            decision,
            roots: roots.into(),
        })
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

/// Sealed handoff proving that the direct quantified-model gate confirmed
/// every quantified leaf of one exact public obligation window against one
/// exact installed model.
///
/// The constructor and fields stay in this module.  A diagnostic statistic, a
/// solver routing Boolean, or another certificate therefore cannot mint this
/// authority.  The compositional independent gate accepts it only while every
/// query/source/root/model binding remains current, then the SAT funnel
/// consumes it.
#[must_use = "quantified model confirmation must reach the independent gate"]
#[derive(Debug)]
pub(in crate::executor) struct QuantifiedModelConfirmation {
    query_epoch: QueryAuthorityEpoch,
    source_context_stamp: SourceContextStamp,
    roots: Box<[TermId]>,
    root_entries: Box<[TermEntryStamp]>,
    model_epoch: QuantifiedConfirmationModelEpoch,
}

impl QuantifiedModelConfirmation {
    fn bind_current<'a>(
        &self,
        executor: &'a Executor,
        roots: &[TermId],
        model: &'a Model,
    ) -> Option<CurrentQuantifiedModelConfirmation<'a>> {
        let installed = executor.last_model.as_ref()?;
        if !std::ptr::eq(installed, model)
            || !self
                .query_epoch
                .is_same_epoch(&executor.query_authority_epoch)
            || self.source_context_stamp != executor.ctx.source_context_stamp()
            || self.roots.as_ref() != roots
            || !self.root_entries.iter().copied().map(Some).eq(self
                .roots
                .iter()
                .map(|&root| executor.ctx.terms.entry_stamp(root)))
            || !model.carries_quantified_confirmation(&self.model_epoch)
        {
            return None;
        }
        Some(CurrentQuantifiedModelConfirmation { _model: model })
    }
}

/// Borrow-bound view of a current direct confirmation.
///
/// Holding this value keeps the exact installed model immutably borrowed for
/// the entire independent evaluation that consumes the quantified authority.
struct CurrentQuantifiedModelConfirmation<'a> {
    _model: &'a Model,
}

/// Pre-check identity of the exact query and model whose quantified leaves are
/// about to be validated.
///
/// Nested isolated solves necessarily mutate executor result state. Capturing
/// only after they return would authenticate whatever model happened to be
/// installed at the end rather than the model actually inspected. This scope
/// seals the incoming model first and can finish only if every binding is still
/// exact after all checks.
struct QuantifiedModelCheckScope {
    query_epoch: QueryAuthorityEpoch,
    source_context_stamp: SourceContextStamp,
    roots: Box<[TermId]>,
    root_entries: Box<[TermEntryStamp]>,
    model_epoch: QuantifiedConfirmationModelEpoch,
}

impl QuantifiedModelCheckScope {
    fn capture(
        executor: &mut Executor,
        query_epoch: QueryAuthorityEpoch,
        source_context_stamp: SourceContextStamp,
        roots: &[TermId],
    ) -> Option<Self> {
        if !query_epoch.is_same_epoch(&executor.query_authority_epoch)
            || source_context_stamp != executor.ctx.source_context_stamp()
            || independent_gate_query_roots(executor) != roots
        {
            return None;
        }
        let root_entries = roots
            .iter()
            .map(|&root| executor.ctx.terms.entry_stamp(root))
            .collect::<Option<Vec<_>>>()?;
        let model_epoch = executor.last_model.as_mut()?.seal_quantified_confirmation();
        Some(Self {
            query_epoch,
            source_context_stamp,
            roots: roots.into(),
            root_entries: root_entries.into_boxed_slice(),
            model_epoch,
        })
    }

    fn finish(self, executor: &Executor) -> Option<QuantifiedModelConfirmation> {
        if !self
            .query_epoch
            .is_same_epoch(&executor.query_authority_epoch)
            || self.source_context_stamp != executor.ctx.source_context_stamp()
            || independent_gate_query_roots(executor).as_slice() != self.roots.as_ref()
            || !self.root_entries.iter().copied().map(Some).eq(self
                .roots
                .iter()
                .map(|&root| executor.ctx.terms.entry_stamp(root)))
            || !executor
                .last_model
                .as_ref()
                .is_some_and(|model| model.carries_quantified_confirmation(&self.model_epoch))
        {
            return None;
        }
        Some(QuantifiedModelConfirmation {
            query_epoch: self.query_epoch,
            source_context_stamp: self.source_context_stamp,
            roots: self.roots,
            root_entries: self.root_entries,
            model_epoch: self.model_epoch,
        })
    }
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

/// One checked disposable-ground result kept together with the exact ordered
/// roots its private SAT/UNSAT payload must consume against. Neither the
/// decision nor its evidence is cloneable, and callers destructure this value
/// only at the semantic acceptance site.
#[derive(Debug)]
struct QuantifiedGateCheckedGroundDecision {
    decision: CheckedGroundDecision,
    roots: Box<[TermId]>,
}

/// Sealed, non-cloneable theorem authority for one exact quantified conjunct.
///
/// Construction is private to the independent gate and requires a definitive
/// isolated refutation of the conjunct's quantifier-free negation.
#[must_use = "global quantified validity authority must be consumed"]
struct GloballyValidQuantifiedConjunct {
    source: TermId,
    query_epoch: QueryAuthorityEpoch,
    source_context_stamp: SourceContextStamp,
    roots: Box<[TermId]>,
    term_snapshot: TermStoreSnapshotStamp,
}

impl GloballyValidQuantifiedConjunct {
    fn confirm(self, executor: &mut Executor, source: TermId) -> QuantifiedModelCheck {
        if self.source == source
            && self
                .query_epoch
                .is_same_epoch(&executor.query_authority_epoch)
            && self.source_context_stamp == executor.ctx.source_context_stamp()
            && self.roots.as_ref() == independent_gate_query_roots(executor).as_slice()
            && self.term_snapshot == executor.ctx.terms.snapshot_stamp()
            && !executor.should_abort_theory_loop()
        {
            QuantifiedModelCheck::Confirmed
        } else {
            QuantifiedModelCheck::Indeterminate("globally-valid quantified authority became stale")
        }
    }
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

/// Cap on binders per quantifier block in the ∀∃ witness route
/// (#quantified-model-gate alternation). Confirm-only, so a cap can only cost
/// a confirm, never soundness.
const QUANTIFIED_GATE_MAX_WITNESS_BINDERS: usize = 3;

/// Cap on candidate witness terms per existential binder.
const QUANTIFIED_GATE_MAX_WITNESS_CANDIDATES: usize = 4;

/// Cap on candidate TUPLES actually discharged. Each costs one nested ground
/// solve out of the gate's shared per-check-sat budget.
const QUANTIFIED_GATE_MAX_WITNESS_TUPLES: usize = 6;

/// Binder sorts the ∀∃ witness route accepts: fixed-interpretation domains
/// only, so a witness TERM means the same thing in every structure satisfying
/// the pins. `Sort::Uninterpreted` is excluded on purpose — its carrier is
/// model-dependent and the prefix route's universe expansion owns it.
fn quantified_gate_witness_sort(sort: &Sort) -> bool {
    matches!(sort, Sort::Bool | Sort::Int | Sort::Real | Sort::BitVec(_))
}

/// Does `term` contain a `Var` named `name`? Used to reject a witness
/// candidate that mentions the existential binder it must eliminate.
/// Conservative: an over-budget walk answers `true` (candidate rejected).
fn quantified_gate_mentions_var(terms: &TermStore, term: TermId, name: &str) -> bool {
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut stack = vec![term];
    let mut budget = 20_000usize;
    while let Some(t) = stack.pop() {
        if budget == 0 {
            return true;
        }
        budget -= 1;
        if !seen.insert(t) {
            continue;
        }
        if let TermData::Var(var, _) = terms.get(t) {
            if var == name {
                return true;
            }
        }
        stack.extend(terms.children(t));
    }
    false
}

/// Candidate witness TUPLES in "strongest first" order: the cartesian product
/// of the per-binder candidate lists, ordered so the first candidate of every
/// binder is tried first, capped at [`QUANTIFIED_GATE_MAX_WITNESS_TUPLES`].
fn quantified_gate_witness_tuples(per_binder: &[Vec<TermId>]) -> Vec<Vec<TermId>> {
    let mut tuples: Vec<Vec<TermId>> = vec![Vec::new()];
    for candidates in per_binder {
        let mut next = Vec::new();
        for prefix in &tuples {
            for &candidate in candidates {
                let mut extended = prefix.clone();
                extended.push(candidate);
                next.push(extended);
            }
        }
        tuples = next;
    }
    tuples.truncate(QUANTIFIED_GATE_MAX_WITNESS_TUPLES);
    tuples
}

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
            Sort::Real => match Executor::parse_real_string(raw) {
                EvalValue::Rational(r) => Some(terms.mk_rational(r)),
                _ => None,
            },
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

/// Keep only the trigger groups that mention NO dropped binder name
/// (#satgate-vacuous-binder): a trigger referencing an eliminated binder is
/// ill-formed. Sound in either direction — triggers are E-matching hints, never
/// semantics — so the cheap syntactic name test is enough here.
fn quantified_gate_retain_triggers(
    terms: &TermStore,
    triggers: &[Vec<TermId>],
    all_vars: &[(String, Sort)],
    kept: &[(String, Sort)],
) -> Vec<Vec<TermId>> {
    let dropped: Vec<&str> = all_vars
        .iter()
        .filter(|(n, _)| !kept.iter().any(|(k, _)| k == n))
        .map(|(n, _)| n.as_str())
        .collect();
    if dropped.is_empty() {
        return triggers.to_vec();
    }
    triggers
        .iter()
        .filter(|grp| {
            grp.iter().all(|&t| {
                !dropped
                    .iter()
                    .any(|d| term_mentions_binder_name(terms, t, d))
            })
        })
        .cloned()
        .collect()
}

/// Syntactic "does a `Var` named `name` occur in `term`" for trigger hygiene
/// only. Over-reporting is harmless (the group is merely dropped).
fn term_mentions_binder_name(terms: &TermStore, term: TermId, name: &str) -> bool {
    let mut stack = vec![term];
    let mut seen: HashSet<TermId> = HashSet::default();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::Var(n, _) => {
                if n == name {
                    return true;
                }
            }
            TermData::Const(_) => {}
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => stack.push(*b),
            TermData::Let(bindings, b) => {
                stack.extend(bindings.iter().map(|(_, v)| *v));
                stack.push(*b);
            }
            _ => return true,
        }
    }
    false
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
    use ay_core::term::Symbol;
    use ay_frontend::parse;
    use ay_lia::LiaModel;
    use num_bigint::BigInt;
    use num_rational::BigRational;

    use super::*;

    /// Solve `input` through the full executor pipeline (gate included).
    fn solved(input: &str) -> (Executor, Vec<String>) {
        let commands = parse(input).expect("valid SMT-LIB input");
        let mut exec = Executor::new();
        let outputs = exec.execute_all(&commands).expect("execute succeeds");
        (exec, outputs)
    }

    fn loaded(input: &str) -> Executor {
        let commands = parse(input).expect("valid SMT-LIB input");
        let mut exec = Executor::new();
        for command in &commands {
            assert!(
                exec.execute(command).expect("execute succeeds").is_none(),
                "fixture must not contain a query command"
            );
        }
        exec
    }

    /// Forge the impossible state the defensive coherence gate is meant to
    /// reject without weakening the production native-alias registrar.
    ///
    /// Any live non-theory declaration at a canonical theory identity poisons
    /// interpretation of that identity, independently of its signature.  The
    /// ordinary low-level symbol registrar is sufficient to construct that
    /// corrupt internal state for a unit test; production native aliases must
    /// continue rejecting an absent canonical target.
    fn forge_non_theory_canonical_owner(exec: &mut Executor, identity: &str, sort: Sort) {
        assert!(ay_frontend::is_canonical_theory_operator_identity(identity));
        let term = exec.ctx.terms.mk_fresh_named_var(identity, sort.clone());
        exec.ctx.register_symbol(identity.to_string(), term, sort);
        let declaration = exec
            .ctx
            .symbol_info_by_identity(identity)
            .expect("forged canonical owner must be live");
        assert_eq!(
            exec.ctx
                .effective_declaration_kind(declaration.declaration_id()),
            Some(DeclarationKind::Uninterpreted),
            "fixture must install a non-theory owner at `{identity}`"
        );
    }

    fn only_quantified_assertion(exec: &Executor) -> TermId {
        exec.ctx
            .assertions
            .iter()
            .copied()
            .find(|&term| contains_quantifier(&exec.ctx.terms, term))
            .expect("fixture has a quantified assertion")
    }

    fn quantified_gate_checked_unsat(exec: &mut Executor, roots: Vec<TermId>) -> bool {
        let Some(QuantifiedGateCheckedGroundDecision { decision, roots }) =
            exec.quantified_gate_checked_ground_solve(roots)
        else {
            return false;
        };
        match decision {
            CheckedGroundDecision::Unsat(proof) => proof.consume(exec, &roots),
            CheckedGroundDecision::Sat(_) => false,
        }
    }

    #[test]
    fn default_quantified_gate_reads_exact_dedicated_authored_roots() {
        let mut exec = loaded(
            r#"
                (set-logic UFLIA)
                (declare-fun f (Int) Int)
                (declare-const a Int)
                (assert (forall ((x Int)) (>= (f x) 0)))
                (assert (> a 0))
            "#,
        );
        let authored = exec.ctx.assertions.clone();
        assert!(authored
            .iter()
            .any(|&root| contains_quantifier(&exec.ctx.terms, root)));
        assert!(!exec.self_check(), "the regression exercises default mode");
        assert!(exec.self_check_authored_assertions.is_none());

        // Model a preprocessing pass that replaced the working assertion
        // window. The independent gate must still select the ordered authored
        // roots, without borrowing the self-check/model-completion slot.
        let rewritten = exec.ctx.terms.true_term();
        exec.ctx.assertions = vec![rewritten];
        exec.independent_gate_authored_assertions = Some(authored.clone());

        assert_eq!(independent_gate_query_roots(&exec), authored);
        assert!(exec.self_check_authored_assertions.is_none());
    }

    #[test]
    fn checked_quantified_gate_probe_preserves_outer_proof_suppression() {
        let mut exec = Executor::new();
        exec.last_unsat_proof_reconstruction_suppressed = true;
        let contradiction = exec.ctx.terms.false_term();

        assert!(
            quantified_gate_checked_unsat(&mut exec, vec![contradiction]),
            "the disposable fixture must carry a strictly checked refutation"
        );
        assert!(
            exec.last_unsat_proof_reconstruction_suppressed,
            "a disposable checked solve must not alter the outer proof-authority marker"
        );
    }

    #[test]
    fn quantified_gate_checked_evidence_rejects_every_stale_binding() {
        fn checked_false() -> (Executor, QuantifiedGateCheckedGroundDecision) {
            let mut exec = Executor::new();
            let contradiction = exec.ctx.terms.false_term();
            let checked = exec
                .quantified_gate_checked_ground_solve(vec![contradiction])
                .expect("false must produce checked UNSAT evidence");
            (exec, checked)
        }

        let (mut wrong_roots, checked) = checked_false();
        let QuantifiedGateCheckedGroundDecision { decision, .. } = checked;
        let CheckedGroundDecision::Unsat(proof) = decision else {
            panic!("false must be UNSAT");
        };
        let different_roots = [wrong_roots.ctx.terms.true_term()];
        assert!(
            !proof.consume(&mut wrong_roots, &different_roots),
            "a checked proof cannot be retargeted to nearby roots"
        );

        let (mut epoch_stale, checked) = checked_false();
        epoch_stale.advance_query_authority_epoch();
        let QuantifiedGateCheckedGroundDecision { decision, roots } = checked;
        let CheckedGroundDecision::Unsat(proof) = decision else {
            panic!("false must be UNSAT");
        };
        assert!(
            !proof.consume(&mut epoch_stale, &roots),
            "a later public query cannot reuse checked ground evidence"
        );

        let (mut terms_stale, checked) = checked_false();
        let _ = terms_stale
            .ctx
            .terms
            .mk_fresh_var("post-ground-check", Sort::Bool);
        let QuantifiedGateCheckedGroundDecision { decision, roots } = checked;
        let CheckedGroundDecision::Unsat(proof) = decision else {
            panic!("false must be UNSAT");
        };
        assert!(
            !proof.consume(&mut terms_stale, &roots),
            "a changed term universe cannot reuse checked ground evidence"
        );
    }

    #[test]
    fn exact_single_forall_mints_typed_global_validity() {
        let mut exec = loaded(
            r#"
                (set-logic LIA)
                (assert (forall ((x Int)) (< x (+ x 1))))
            "#,
        );
        let source = only_quantified_assertion(&exec);

        let checked = exec
            .certify_globally_valid_quantified_conjunct(source)
            .expect("the exact Skolem instance has a strictly checked UNSAT proof");

        assert!(matches!(
            checked.confirm(&mut exec, source),
            QuantifiedModelCheck::Confirmed
        ));
    }

    #[test]
    fn false_single_forall_cannot_mint_global_validity() {
        let mut exec = loaded(
            r#"
                (set-logic LIA)
                (assert (forall ((x Int)) (= x 0)))
            "#,
        );
        let source = only_quantified_assertion(&exec);

        assert!(
            exec.certify_globally_valid_quantified_conjunct(source)
                .is_none(),
            "a checked SAT negation cannot mint global-validity authority"
        );
    }

    #[test]
    fn multi_binder_forall_cannot_enter_single_binder_proof_kernel() {
        let mut exec = loaded(
            r#"
                (set-logic LIA)
                (assert (forall ((x Int) (y Int)) (< x (+ x 1))))
            "#,
        );
        let source = only_quantified_assertion(&exec);

        assert!(
            exec.certify_globally_valid_quantified_conjunct(source)
                .is_none(),
            "multi-binder provenance is outside the exact fallback contract"
        );
    }

    #[test]
    fn patterned_forall_cannot_enter_trigger_free_proof_kernel() {
        let mut exec = loaded(
            r#"
                (set-logic LIA)
                (assert (forall ((x Int))
                    (! (< x (+ x 1)) :pattern ((+ x 1)))))
            "#,
        );
        let source = only_quantified_assertion(&exec);

        assert!(
            exec.certify_globally_valid_quantified_conjunct(source)
                .is_none(),
            "trigger-bearing source provenance is outside the exact fallback contract"
        );
    }

    #[test]
    fn nested_forall_cannot_enter_quantifier_free_body_proof_kernel() {
        let mut exec = loaded(
            r#"
                (set-logic LIA)
                (assert (forall ((x Int))
                    (forall ((y Int)) (< y (+ y 1)))))
            "#,
        );
        let source = only_quantified_assertion(&exec);

        assert!(
            exec.certify_globally_valid_quantified_conjunct(source)
                .is_none(),
            "nested Skolem provenance is outside the exact fallback contract"
        );
    }

    #[test]
    fn folded_negated_instance_cannot_mint_global_validity() {
        let mut exec = loaded(
            r#"
                (set-logic UF)
                (declare-sort U 0)
                (declare-fun f (U) U)
                (assert (forall ((x U)) (= (f x) (f x))))
            "#,
        );
        let source = only_quantified_assertion(&exec);

        assert!(
            exec.certify_globally_valid_quantified_conjunct(source)
                .is_none(),
            "even a valid formula must decline when Skolemization folds away the exact negated root"
        );
    }

    #[test]
    fn outer_forall_support_cannot_circularly_mint_global_validity() {
        let mut exec = loaded(
            r#"
                (set-logic LIA)
                (assert (forall ((x Int)) (= x 0)))
                (assert false)
            "#,
        );
        let source = only_quantified_assertion(&exec);

        // Model the state of a wrong-SAT outer quantifier solve that derived a
        // contradictory ground instance from the very forall this gate is now
        // checking. The explicit `false` assertion keeps the support writer's
        // production invariant (the support root is in the outer assertion
        // set). Such an instance is sound support for the OUTER asserted
        // problem, but using it while refuting `not source` would beg the
        // question and "prove" the false source from one of its consequences.
        let contradictory_instance = exec.ctx.terms.false_term();
        exec.active_support_axioms
            .push(ay_core::TheoryLit::new(contradictory_instance, true));
        let support_before = exec.active_support_axioms.clone();

        assert!(
            exec.certify_globally_valid_quantified_conjunct(source)
                .is_none(),
            "a satisfiable negation must stay SAT even when the outer solve carries circular support"
        );
        assert_eq!(
            exec.active_support_axioms, support_before,
            "the disposable theorem probe must neither consume nor rewrite outer support"
        );
    }

    #[test]
    fn forall_exists_residue_cannot_mint_global_validity() {
        let mut exec = loaded(
            r#"
                (set-logic LIA)
                (assert (forall ((x Int)) (exists ((y Int)) (> y x))))
            "#,
        );
        let source = only_quantified_assertion(&exec);

        assert!(
            exec.certify_globally_valid_quantified_conjunct(source)
                .is_none(),
            "a residual universal in the negation must fail closed"
        );
    }

    #[test]
    fn global_validity_authority_stales_on_query_roots_and_term_universe() {
        fn fixture() -> (Executor, TermId, GloballyValidQuantifiedConjunct) {
            let mut exec = loaded(
                r#"
                    (set-logic LIA)
                    (declare-const c Int)
                    (assert (forall ((x Int)) (< x (+ x 1))))
                    (assert (>= c 0))
                "#,
            );
            let source = only_quantified_assertion(&exec);
            let authority = exec
                .certify_globally_valid_quantified_conjunct(source)
                .expect("fixture must mint exact checked authority");
            (exec, source, authority)
        }

        let (mut epoch_stale, source, authority) = fixture();
        epoch_stale.advance_query_authority_epoch();
        assert!(matches!(
            authority.confirm(&mut epoch_stale, source),
            QuantifiedModelCheck::Indeterminate(_)
        ));

        let (mut roots_stale, source, authority) = fixture();
        roots_stale.ctx.assertions.reverse();
        assert!(matches!(
            authority.confirm(&mut roots_stale, source),
            QuantifiedModelCheck::Indeterminate(_)
        ));

        let (mut terms_stale, source, authority) = fixture();
        let _ = terms_stale
            .ctx
            .terms
            .mk_fresh_var("post-cert-mutation", Sort::Bool);
        assert!(matches!(
            authority.confirm(&mut terms_stale, source),
            QuantifiedModelCheck::Indeterminate(_)
        ));
    }

    /// A model over ONLY the given LIA assignments (every other sub-model
    /// empty), used to synthetically replace the solver's real witness.
    fn synthetic_lia_model(values: &[(TermId, i64)]) -> Model {
        let mut lia = DetHashMap::default();
        for &(t, v) in values {
            lia.insert(t, BigInt::from(v));
        }
        Model {
            quantified_confirmation_seal: Default::default(),
            quantified_grant_model_seal: Default::default(),
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
            projection_ufs: Default::default(),
            certified_total_ufs: Default::default(),
            certified_const_interps: Default::default(),
            formula_neutral_function_defaults: Default::default(),
            completed_values: DetHashMap::default(),
            dt_ground: DetHashMap::default(),
            dt_pins: DetHashMap::default(),
        }
    }

    /// `deep_qe` can reduce this true Presburger alternation to a ground
    /// candidate, but its finite differential guard is not an equivalence
    /// proof. The general route must therefore decline rather than mint the
    /// `Confirmed` authority that lets a public SAT verdict survive.
    #[test]
    fn quantifier_free_deep_qe_candidate_cannot_confirm_source() {
        let mut exec = loaded(
            r#"
                (set-logic LIA)
                (assert (forall ((x Int)) (exists ((y Int)) (> y x))))
            "#,
        );
        let source = only_quantified_assertion(&exec);
        exec.last_model = Some(synthetic_lia_model(&[]));

        // Lock the fixture to the authority boundary under test: this must be
        // a case where the candidate pass actually removes every quantifier.
        let mut candidate = vec![source];
        crate::executor::qe_prepass::deep_qe(
            &mut exec.ctx.terms,
            &mut candidate,
            exec.solve_interrupt.as_deref(),
        );
        assert!(
            !contains_quantifier(&exec.ctx.terms, candidate[0]),
            "fixture must reach a quantifier-free deep-QE candidate"
        );

        let mut elems = QuantifiedGateElements::default();
        let outcome =
            exec.quantified_gate_general_check(source, &DetHashMap::default(), &mut elems, true);
        assert!(matches!(
            outcome,
            QuantifiedModelCheck::Indeterminate(
                "quantifier-free QE candidate lacks exact equivalence authority"
            )
        ));
    }

    /// A model carrying only exact EUF equivalence-class identities.
    fn synthetic_euf_model(values: &[(TermId, &str)]) -> Model {
        let mut model = synthetic_lia_model(&[]);
        model.lia_model = None;
        let mut euf = ay_euf::EufModel::default();
        for &(term, class) in values {
            euf.term_values.insert(term, class.to_string());
        }
        model.euf_model = Some(euf);
        model
    }

    /// A model carrying one exact floating-point leaf assignment.
    fn synthetic_fp_model(term: TermId, value: FpModelValue) -> Model {
        let mut model = synthetic_lia_model(&[]);
        model.lia_model = None;
        let mut values = DetHashMap::default();
        values.insert(term, value);
        model.fp_model = Some(ay_fp::FpModel { values });
        model
    }

    #[test]
    fn scalar_uf_definition_requires_exact_private_declaration_identity() {
        let mut exec = loaded(
            r#"
                (declare-fun rem (Int Int) Int)
                (assert (= (rem 1 2) 7))
            "#,
        );
        let assertion = exec.ctx.assertions[0];
        let TermData::App(_, equality_args) = exec.ctx.terms.get(assertion).clone() else {
            panic!("fixture assertion must be an equality application");
        };
        let declared_app = equality_args
            .iter()
            .copied()
            .find(|&term| matches!(exec.ctx.terms.get(term), TermData::App(_, _)))
            .expect("fixture equality must contain the declared application");
        let TermData::App(declared_symbol, _) = exec.ctx.terms.get(declared_app) else {
            unreachable!("application selected above");
        };
        let declared_symbol = declared_symbol.clone();
        assert_ne!(
            declared_symbol.name(),
            "rem",
            "a builtin-colliding declaration must retain its private core identity"
        );

        let model = synthetic_lia_model(&[]);
        let view = IndependentModelView::new(&exec, &model);
        assert!(
            matches!(
                view.uf_app_definition_value(declared_app),
                Some(ModelValue::Int(value)) if value == BigInt::from(7)
            ),
            "the exact private identity of a live ordinary UF remains eligible"
        );
        drop(view);

        // Owning the exact symbol identity is not enough if a malformed core
        // application borrows it at a different signature.
        let true_term = exec.ctx.terms.true_term();
        let two = exec.ctx.terms.mk_int(BigInt::from(2));
        let forged_signature =
            exec.ctx
                .terms
                .mk_app(declared_symbol, vec![true_term, two], Sort::Int);
        let zero = exec.ctx.terms.mk_int(BigInt::from(0));
        let forged_definition = exec.ctx.terms.mk_eq(forged_signature, zero);
        exec.independent_gate_authored_assertions = Some(vec![forged_definition]);
        let view = IndependentModelView::new(&exec, &model);
        assert!(
            view.uf_app_definition_value(forged_signature).is_none(),
            "an exact declaration identity at a forged signature must fail closed"
        );
        drop(view);

        // A raw builtin `rem` head is NOT the declaration above.  A fallback
        // from exact identity to the surface-name table used to borrow the
        // private declaration's authority and resolve this forged application.
        let one = exec.ctx.terms.mk_int(BigInt::from(1));
        let two = exec.ctx.terms.mk_int(BigInt::from(2));
        let forged_builtin = exec
            .ctx
            .terms
            .mk_app(Symbol::named("rem"), vec![one, two], Sort::Int);
        let forged_definition = exec.ctx.terms.mk_eq(forged_builtin, zero);
        exec.independent_gate_authored_assertions = Some(vec![forged_definition]);

        let view = IndependentModelView::new(&exec, &model);
        assert!(
            view.uf_app_definition_value(forged_builtin).is_none(),
            "a surface spelling must not inherit a distinct private declaration identity"
        );
    }

    #[test]
    fn scalar_uf_definition_rejects_nonfree_declaration_kinds() {
        // A problem-level definition has fixed semantics even if a raw core
        // application of its registered name reaches this defensive fallback.
        let mut defined = loaded("(define-fun f ((x Int)) Int (+ x 1))");
        let info = defined.ctx.symbol_info("f").expect("defined symbol info");
        assert_eq!(
            defined
                .ctx
                .effective_declaration_kind(info.declaration_id()),
            Some(DeclarationKind::Defined)
        );
        let arg = defined.ctx.terms.mk_int(BigInt::from(4));
        let app = defined
            .ctx
            .terms
            .mk_app(Symbol::named("f"), vec![arg], Sort::Int);
        let value = defined.ctx.terms.mk_int(BigInt::from(5));
        let equality = defined.ctx.terms.mk_eq(app, value);
        defined.independent_gate_authored_assertions = Some(vec![equality]);
        let model = synthetic_lia_model(&[]);
        assert!(
            IndependentModelView::new(&defined, &model)
                .uf_app_definition_value(app)
                .is_none(),
            "defined functions must not be treated as free UF interpretations"
        );

        // Declaration-activated collection operators live in the symbol table,
        // but their positive kind is Theory rather than Uninterpreted.
        let mut theory =
            loaded("(declare-fun set.subset ((Array Int Bool) (Array Int Bool)) Bool)");
        let info = theory
            .ctx
            .symbol_info("set.subset")
            .expect("theory symbol info");
        assert_eq!(
            theory.ctx.effective_declaration_kind(info.declaration_id()),
            Some(DeclarationKind::Theory)
        );
        let false_term = theory.ctx.terms.false_term();
        let array = theory.ctx.terms.mk_const_array(Sort::Int, false_term);
        let app =
            theory
                .ctx
                .terms
                .mk_app(Symbol::named("set.subset"), vec![array, array], Sort::Bool);
        let true_term = theory.ctx.terms.true_term();
        let equality = theory.ctx.terms.mk_eq(app, true_term);
        theory.independent_gate_authored_assertions = Some(vec![equality]);
        assert!(
            IndependentModelView::new(&theory, &model)
                .uf_app_definition_value(app)
                .is_none(),
            "theory declarations must not be treated as free UF interpretations"
        );

        // Macro adoption overlays the stable declaration identity with an
        // effective non-free kind while its defining forall remains live.
        let mut adopted = loaded(
            r#"
                (declare-fun g (Int) Int)
                (assert (forall ((x Int)) (= (g x) (+ x 1))))
            "#,
        );
        let info = adopted.ctx.symbol_info("g").expect("adopted symbol info");
        assert_eq!(
            adopted
                .ctx
                .effective_declaration_kind(info.declaration_id()),
            Some(DeclarationKind::AdoptedDefinition)
        );
        let arg = adopted.ctx.terms.mk_int(BigInt::from(8));
        let app = adopted
            .ctx
            .terms
            .mk_app(Symbol::named("g"), vec![arg], Sort::Int);
        let value = adopted.ctx.terms.mk_int(BigInt::from(9));
        let equality = adopted.ctx.terms.mk_eq(app, value);
        adopted.independent_gate_authored_assertions = Some(vec![equality]);
        assert!(
            IndependentModelView::new(&adopted, &model)
                .uf_app_definition_value(app)
                .is_none(),
            "adopted definitions must not reuse their original free-UF kind"
        );
    }

    #[test]
    fn scalar_uf_definition_rejects_native_alias_at_fp_min_identity() {
        let mut exec = Executor::new();
        let fp16 = Sort::FloatingPoint(5, 11);
        forge_non_theory_canonical_owner(&mut exec, "fp.min", fp16.clone());

        let positive_zero = exec.ctx.terms.mk_var("fp-min-positive-zero", fp16.clone());
        let negative_zero = exec.ctx.terms.mk_var("fp-min-negative-zero", fp16.clone());
        let minimum = exec.ctx.terms.mk_app(
            Symbol::named("fp.min"),
            vec![positive_zero, negative_zero],
            fp16,
        );
        let definition = exec.ctx.terms.mk_eq(minimum, positive_zero);
        exec.independent_gate_authored_assertions = Some(vec![definition]);

        let mut model = synthetic_fp_model(positive_zero, FpModelValue::PosZero { eb: 5, sb: 11 });
        model
            .fp_model
            .as_mut()
            .expect("synthetic FP model")
            .values
            .insert(negative_zero, FpModelValue::NegZero { eb: 5, sb: 11 });
        let view = IndependentModelView::new(&exec, &model);

        assert!(
            view.uf_app_definition_value(minimum).is_none(),
            "an evaluator-owned fp.min application must never borrow generic UF authority"
        );
    }

    #[test]
    fn independent_gate_confirms_exact_finite_fp_to_real_witness() {
        let mut exec = Executor::new();
        let fp16 = Sort::FloatingPoint(5, 11);
        let x = exec.ctx.terms.mk_var("fp-to-real-x", fp16);
        let r = exec.ctx.terms.mk_var("fp-to-real-r", Sort::Real);
        let to_real = exec
            .ctx
            .terms
            .mk_app(Symbol::named("fp.to_real"), vec![x], Sort::Real);
        let definition = exec.ctx.terms.mk_eq(r, to_real);
        let one = exec
            .ctx
            .terms
            .mk_rational(BigRational::from_integer(BigInt::from(1)));
        let greater_than_one = exec
            .ctx
            .terms
            .mk_app(Symbol::named(">"), vec![r, one], Sort::Bool);
        exec.independent_gate_authored_assertions = Some(vec![definition, greater_than_one]);
        let mut model = synthetic_fp_model(
            x,
            FpModelValue::Fp {
                sign: false,
                exponent: 16,
                significand: 256,
                eb: 5,
                sb: 11,
            },
        );
        let mut real_values = DetHashMap::default();
        real_values.insert(r, BigRational::new(BigInt::from(5), BigInt::from(2)));
        model.lra_model = Some(ay_lra::LraModel {
            values: real_values,
        });
        exec.last_model = Some(model);

        assert!(matches!(
            exec.confirm_sat_with_fully_evaluated_independent_gate(),
            GateVerdict::ConfirmedSat
        ));
    }

    #[test]
    fn independent_gate_confirms_proven_unconstrained_fp_to_real_witness() {
        let mut exec = Executor::new();
        let fp16 = Sort::FloatingPoint(5, 11);
        let x = exec.ctx.terms.mk_var("fp-to-real-inf", fp16);
        let to_real = exec
            .ctx
            .terms
            .mk_app(Symbol::named("fp.to_real"), vec![x], Sort::Real);
        let zero = exec
            .ctx
            .terms
            .mk_rational(BigRational::from_integer(BigInt::from(0)));
        let assertion = exec.ctx.terms.mk_eq(to_real, zero);
        exec.independent_gate_authored_assertions = Some(vec![assertion]);
        exec.last_model = Some(synthetic_fp_model(
            x,
            FpModelValue::PosInf { eb: 5, sb: 11 },
        ));

        assert!(matches!(
            exec.confirm_sat_with_fully_evaluated_independent_gate(),
            GateVerdict::ConfirmedSat
        ));
    }

    #[test]
    fn independent_gate_rejects_finite_fp_to_real_assertion_fallback() {
        let mut exec = Executor::new();
        let fp16 = Sort::FloatingPoint(5, 11);
        let x = exec.ctx.terms.mk_var("fp-to-real-finite", fp16);
        let to_real = exec
            .ctx
            .terms
            .mk_app(Symbol::named("fp.to_real"), vec![x], Sort::Real);
        let five = exec
            .ctx
            .terms
            .mk_rational(BigRational::from_integer(BigInt::from(5)));
        let assertion = exec.ctx.terms.mk_eq(to_real, five);
        exec.independent_gate_authored_assertions = Some(vec![assertion]);
        exec.last_model = Some(synthetic_fp_model(
            x,
            // Float16 +1.0: exponent=bias=15, zero stored fraction.
            FpModelValue::Fp {
                sign: false,
                exponent: 15,
                significand: 0,
                eb: 5,
                sb: 11,
            },
        ));

        assert!(matches!(
            exec.confirm_sat_with_fully_evaluated_independent_gate(),
            GateVerdict::ModelViolates { assertion: rejected } if rejected == assertion
        ));
    }

    #[test]
    fn independent_gate_confirms_exact_zero_divisor_definition_fallbacks() {
        let mut exec = Executor::new();
        let int_one = exec.ctx.terms.mk_int(BigInt::from(1));
        let int_zero = exec.ctx.terms.mk_int(BigInt::from(0));
        let int_five = exec.ctx.terms.mk_int(BigInt::from(5));
        let int_six = exec.ctx.terms.mk_int(BigInt::from(6));
        let int_div =
            exec.ctx
                .terms
                .mk_app(Symbol::named("div"), vec![int_one, int_zero], Sort::Int);
        let int_mod =
            exec.ctx
                .terms
                .mk_app(Symbol::named("mod"), vec![int_one, int_zero], Sort::Int);
        let div_definition = exec.ctx.terms.mk_eq(int_div, int_five);
        let mod_definition = exec.ctx.terms.mk_eq(int_mod, int_six);

        let real_one = exec
            .ctx
            .terms
            .mk_rational(BigRational::from_integer(BigInt::from(1)));
        let real_zero = exec
            .ctx
            .terms
            .mk_rational(BigRational::from_integer(BigInt::from(0)));
        let real_seven = exec
            .ctx
            .terms
            .mk_rational(BigRational::from_integer(BigInt::from(7)));
        let real_div =
            exec.ctx
                .terms
                .mk_app(Symbol::named("/"), vec![real_one, real_zero], Sort::Real);
        let real_definition = exec.ctx.terms.mk_eq(real_div, real_seven);

        exec.independent_gate_authored_assertions =
            Some(vec![div_definition, mod_definition, real_definition]);
        exec.last_model = Some(Model::empty());

        assert!(matches!(
            exec.confirm_sat_with_fully_evaluated_independent_gate(),
            GateVerdict::ConfirmedSat
        ));
    }

    #[test]
    fn typed_unconstrained_bridge_rejects_exact_identity_collisions() {
        let fp16 = Sort::FloatingPoint(5, 11);
        let collisions = [
            ("fp.to_real", fp16),
            ("/", Sort::Real),
            ("div", Sort::Int),
            ("mod", Sort::Int),
            ("=", Sort::Bool),
            ("and", Sort::Bool),
            ("or", Sort::Bool),
            ("not", Sort::Bool),
            ("=>", Sort::Bool),
            ("ite", Sort::Int),
            ("if", Sort::Int),
        ];

        for (identity, range) in collisions {
            let mut exec = Executor::new();
            forge_non_theory_canonical_owner(&mut exec, identity, range);

            let declaration = exec
                .ctx
                .symbol_info_by_identity(identity)
                .expect("collision must own the exact core identity");
            assert_eq!(
                exec.ctx
                    .effective_declaration_kind(declaration.declaration_id()),
                Some(DeclarationKind::Uninterpreted),
                "fixture must exercise a live ordinary declaration at `{identity}`"
            );

            let one = exec.ctx.terms.mk_int(BigInt::from(1));
            let zero = exec.ctx.terms.mk_int(BigInt::from(0));
            let seven = exec.ctx.terms.mk_int(BigInt::from(7));
            let div = exec
                .ctx
                .terms
                .mk_app(Symbol::named("div"), vec![one, zero], Sort::Int);
            let definition = exec.ctx.terms.mk_eq(div, seven);
            exec.independent_gate_authored_assertions = Some(vec![definition]);
            let model = Model::empty();
            let view = IndependentModelView::new(&exec, &model);

            assert!(
                view.uf_app_definition_value(div).is_none(),
                "canonical theory head must not borrow generic UF authority under `{identity}` collision"
            );
            assert!(
                view.uf_app_value(div).is_none(),
                "generic model lookup must not bypass typed authority under `{identity}` collision"
            );
            assert!(
                view.proven_unconstrained_app_value(div, ProvenUnconstrainedKind::IntDivByZero,)
                    .is_none(),
                "typed lookup must fail closed under `{identity}` collision"
            );
        }
    }

    #[test]
    fn asserted_uf_definition_rejects_forged_control_identity_collisions() {
        let collisions = [
            ("or", Sort::Bool),
            ("not", Sort::Bool),
            ("=>", Sort::Bool),
            ("ite", Sort::Int),
        ];

        for (identity, range) in collisions {
            let mut exec = loaded("(declare-fun f (Int) Int)");
            let one = exec.ctx.terms.mk_int(BigInt::from(1));
            let seven = exec.ctx.terms.mk_int(BigInt::from(7));
            let app = exec
                .ctx
                .terms
                .mk_app(Symbol::named("f"), vec![one], Sort::Int);
            let definition = exec.ctx.terms.mk_eq(app, seven);
            exec.independent_gate_authored_assertions = Some(vec![definition]);
            let model = synthetic_lia_model(&[]);

            let coherent_view = IndependentModelView::new(&exec, &model);
            assert!(
                matches!(
                    coherent_view.uf_app_definition_value(app),
                    Some(ModelValue::Int(value)) if value == BigInt::from(7)
                ),
                "the ordinary f fixture must resolve before the adversarial registration"
            );
            drop(coherent_view);

            forge_non_theory_canonical_owner(&mut exec, identity, range);
            let declaration = exec
                .ctx
                .symbol_info_by_identity(identity)
                .expect("collision must own the exact core identity");
            assert_eq!(
                exec.ctx
                    .effective_declaration_kind(declaration.declaration_id()),
                Some(DeclarationKind::Uninterpreted),
                "fixture must install a non-theory owner at `{identity}`"
            );

            let view = IndependentModelView::new(&exec, &model);
            assert!(
                !view.canonical_theory_bindings_are_coherent(),
                "the forged `{identity}` owner must poison assertion-derived authority"
            );
            assert!(
                view.asserted_app_definition_value(app).is_none(),
                "the shared definition boundary must reject ordinary f under forged `{identity}`"
            );
            assert!(
                view.uf_app_definition_value(app).is_none(),
                "ordinary f must not borrow asserted-definition authority under forged `{identity}`"
            );
        }
    }

    #[test]
    fn array_and_datatype_definition_index_rejects_forged_control_identities() {
        let collisions = ["=", "and", "or", "ite", "if"];

        for identity in collisions {
            let mut exec = loaded(
                r#"
                    (declare-datatype D ((mkD) (otherD)))
                    (declare-const d D)
                    (assert (= d mkD))
                "#,
            );
            let datatype_definition = exec.ctx.assertions[0];
            let datatype_leaf = exec
                .ctx
                .symbol_info("d")
                .and_then(|info| info.term)
                .expect("declared datatype leaf");
            let TermData::App(datatype_eq, datatype_args) = exec.ctx.terms.get(datatype_definition)
            else {
                panic!(
                    "datatype fixture must retain its asserted equality, got {:?}",
                    exec.ctx.terms.get(datatype_definition)
                );
            };
            assert_eq!(datatype_eq.name(), "=");
            let datatype_partner = datatype_args
                .iter()
                .copied()
                .find(|&term| term != datatype_leaf)
                .expect("datatype equality partner");

            let zero = exec.ctx.terms.mk_int(BigInt::from(0));
            let constant = exec.ctx.terms.mk_const_array(Sort::Int, zero);
            let array_leaf = exec
                .ctx
                .terms
                .mk_var("indexed-array", Sort::array(Sort::Int, Sort::Int));
            let array_definition = exec.ctx.terms.mk_eq(array_leaf, constant);
            let both_definitions = exec.ctx.terms.mk_app(
                Symbol::named("and"),
                vec![array_definition, datatype_definition],
                Sort::Bool,
            );
            let false_term = exec.ctx.terms.false_term();
            let true_term = exec.ctx.terms.true_term();
            let root = match identity {
                "=" => None,
                "and" => Some(both_definitions),
                "or" => Some(exec.ctx.terms.mk_app(
                    Symbol::named("or"),
                    vec![false_term, both_definitions],
                    Sort::Bool,
                )),
                "ite" | "if" => Some(exec.ctx.terms.mk_app(
                    Symbol::named(identity),
                    vec![true_term, both_definitions, false_term],
                    Sort::Bool,
                )),
                _ => unreachable!("collision table contains only index controls"),
            };
            exec.independent_gate_authored_assertions = Some(root.map_or_else(
                || vec![array_definition, datatype_definition],
                |term| vec![term],
            ));

            let model = Model::empty();
            let coherent = IndependentModelView::new(&exec, &model);
            assert!(
                coherent
                    .definitions_for(array_leaf, DefKind::Array)
                    .contains(&constant),
                "baseline `{identity}` walk must index the array definition"
            );
            assert!(
                coherent
                    .definitions_for(datatype_leaf, DefKind::Datatype)
                    .contains(&datatype_partner),
                "baseline `{identity}` walk must index the datatype definition"
            );
            drop(coherent);

            forge_non_theory_canonical_owner(&mut exec, identity, Sort::Bool);
            let poisoned = IndependentModelView::new(&exec, &model);
            assert!(!poisoned.canonical_theory_bindings_are_coherent());

            poisoned.ensure_def_index();
            assert!(
                poisoned
                    .def_index
                    .borrow()
                    .as_ref()
                    .is_some_and(HashMap::is_empty),
                "eager index construction must memoize no authority under forged `{identity}`"
            );
            assert!(
                poisoned
                    .definitions_for(array_leaf, DefKind::Array)
                    .is_empty(),
                "array definitions must fail closed under forged `{identity}`"
            );
            assert!(
                poisoned
                    .definitions_for(datatype_leaf, DefKind::Datatype)
                    .is_empty(),
                "datatype definitions must fail closed under forged `{identity}`"
            );
        }
    }

    #[test]
    fn asserted_uf_definition_allows_declaration_activated_theory_bindings() {
        let mut exec = loaded(
            r#"
                (declare-fun set.subset ((Array Int Bool) (Array Int Bool)) Bool)
                (declare-fun f (Int) Int)
            "#,
        );
        let theory = exec
            .ctx
            .symbol_info("set.subset")
            .expect("declaration-activated theory binding");
        assert_eq!(
            exec.ctx.effective_declaration_kind(theory.declaration_id()),
            Some(DeclarationKind::Theory)
        );

        let one = exec.ctx.terms.mk_int(BigInt::from(1));
        let seven = exec.ctx.terms.mk_int(BigInt::from(7));
        let app = exec
            .ctx
            .terms
            .mk_app(Symbol::named("f"), vec![one], Sort::Int);
        let definition = exec.ctx.terms.mk_eq(app, seven);
        exec.independent_gate_authored_assertions = Some(vec![definition]);
        let model = synthetic_lia_model(&[]);
        let view = IndependentModelView::new(&exec, &model);

        assert!(view.canonical_theory_bindings_are_coherent());
        assert!(matches!(
            view.uf_app_definition_value(app),
            Some(ModelValue::Int(value)) if value == BigInt::from(7)
        ));
    }

    #[test]
    fn map_target_definitions_do_not_poison_independent_definition_recovery() {
        let cases = [
            (
                "define-fun",
                r#"
                    (define-fun div ((x Int) (y Int)) Int x)
                    (declare-fun f (Int) Int)
                "#,
                vec!["div"],
            ),
            (
                "define-fun-rec",
                r#"
                    (define-fun-rec mod ((x Int)) Int
                        (ite (= x 0) 5 (mod 0)))
                    (declare-fun f (Int) Int)
                "#,
                vec!["mod"],
            ),
            (
                "define-funs-rec",
                r#"
                    (define-funs-rec
                        ((abs ((x Int)) Int) (min ((x Int)) Int))
                        ((ite (= x 0) 11 (min 0))
                         (ite (= x 0) 11 (abs 0))))
                    (declare-fun f (Int) Int)
                "#,
                vec!["abs", "min"],
            ),
        ];

        for (label, script, defined_names) in cases {
            let mut exec = loaded(script);
            for name in defined_names {
                let info = exec.ctx.symbol_info(name).expect("defined symbol metadata");
                assert_eq!(
                    exec.ctx.effective_declaration_kind(info.declaration_id()),
                    Some(DeclarationKind::Defined),
                    "{label}: definition kind"
                );
                assert!(
                    info.internal_name.as_deref().is_some_and(|id| id != name),
                    "{label}: `{name}` must not own its canonical theory identity"
                );
            }

            let one = exec.ctx.terms.mk_int(BigInt::from(1));
            let seven = exec.ctx.terms.mk_int(BigInt::from(7));
            let app = exec
                .ctx
                .terms
                .mk_app(Symbol::named("f"), vec![one], Sort::Int);
            let definition = exec.ctx.terms.mk_eq(app, seven);
            exec.independent_gate_authored_assertions = Some(vec![definition]);
            let model = synthetic_lia_model(&[]);
            let view = IndependentModelView::new(&exec, &model);

            assert!(
                view.canonical_theory_bindings_are_coherent(),
                "{label}: legal map-target definitions must not poison canonical theory ownership"
            );
            assert!(matches!(
                view.uf_app_definition_value(app),
                Some(ModelValue::Int(value)) if value == BigInt::from(7)
            ));
        }
    }

    #[test]
    fn native_map_target_constant_does_not_poison_independent_definition_recovery() {
        let mut exec = loaded("(declare-fun f (Int) Int)");
        let native = exec.register_native_global_constant("div".to_string(), Sort::Int);
        let core_name = match exec.ctx.terms.get(native) {
            TermData::Var(name, _) => name.clone(),
            other => panic!("native constant must be a Var, got {other:?}"),
        };
        let native_info = exec
            .ctx
            .symbol_info("div")
            .expect("native constant metadata");
        assert_ne!(core_name, "div");
        assert_eq!(
            native_info.internal_name.as_deref(),
            Some(core_name.as_str())
        );
        assert_eq!(
            exec.ctx
                .effective_declaration_kind(native_info.declaration_id()),
            Some(DeclarationKind::Uninterpreted)
        );
        assert!(exec.ctx.symbol_info_by_identity("div").is_none());

        let one = exec.ctx.terms.mk_int(BigInt::from(1));
        let seven = exec.ctx.terms.mk_int(BigInt::from(7));
        let app = exec
            .ctx
            .terms
            .mk_app(Symbol::named("f"), vec![one], Sort::Int);
        let definition = exec.ctx.terms.mk_eq(app, seven);
        exec.independent_gate_authored_assertions = Some(vec![definition]);
        let model = synthetic_lia_model(&[]);
        let view = IndependentModelView::new(&exec, &model);

        assert!(view.canonical_theory_bindings_are_coherent());
        assert!(matches!(
            view.uf_app_definition_value(app),
            Some(ModelValue::Int(value)) if value == BigInt::from(7)
        ));
    }

    #[test]
    fn typed_unconstrained_bridge_rejects_mismatched_shapes() {
        let mut exec = Executor::new();
        let int_one = exec.ctx.terms.mk_int(BigInt::from(1));
        let int_zero = exec.ctx.terms.mk_int(BigInt::from(0));
        let int_seven = exec.ctx.terms.mk_int(BigInt::from(7));
        let real_one = exec
            .ctx
            .terms
            .mk_rational(BigRational::from_integer(BigInt::from(1)));
        let real_seven = exec
            .ctx
            .terms
            .mk_rational(BigRational::from_integer(BigInt::from(7)));

        let wrong_head =
            exec.ctx
                .terms
                .mk_app(Symbol::named("mod"), vec![int_one, int_zero], Sort::Int);
        let indexed_head = exec.ctx.terms.mk_app(
            Symbol::indexed("div", vec![0]),
            vec![int_one, int_zero],
            Sort::Int,
        );
        let wrong_arity = exec.ctx.terms.mk_app(
            Symbol::named("div"),
            vec![int_one, int_zero, int_one],
            Sort::Int,
        );
        let wrong_argument_sort =
            exec.ctx
                .terms
                .mk_app(Symbol::named("div"), vec![real_one, int_zero], Sort::Int);
        let wrong_result_sort =
            exec.ctx
                .terms
                .mk_app(Symbol::named("div"), vec![int_one, int_zero], Sort::Real);

        exec.independent_gate_authored_assertions = Some(vec![
            exec.ctx.terms.mk_eq(wrong_head, int_seven),
            exec.ctx.terms.mk_eq(indexed_head, int_seven),
            exec.ctx.terms.mk_eq(wrong_arity, int_seven),
            exec.ctx.terms.mk_eq(wrong_argument_sort, int_seven),
            exec.ctx.terms.mk_eq(wrong_result_sort, real_seven),
        ]);
        let model = Model::empty();
        let view = IndependentModelView::new(&exec, &model);

        for (label, term) in [
            ("reason/head mismatch", wrong_head),
            ("indexed head", indexed_head),
            ("wrong arity", wrong_arity),
            ("wrong argument sort", wrong_argument_sort),
            ("wrong result sort", wrong_result_sort),
        ] {
            assert!(
                view.proven_unconstrained_app_value(term, ProvenUnconstrainedKind::IntDivByZero,)
                    .is_none(),
                "typed fallback accepted {label}"
            );
            assert!(
                view.uf_app_definition_value(term).is_none(),
                "generic fallback accepted {label}"
            );
        }
    }

    #[test]
    fn fully_evaluated_gate_checks_false_temporary_assumption() {
        let mut exec = Executor::new();
        let x = exec.ctx.terms.mk_var("assuming-x", Sort::Int);
        let five = exec.ctx.terms.mk_int(BigInt::from(5));
        let four = exec.ctx.terms.mk_int(BigInt::from(4));
        let base = exec.ctx.terms.mk_eq(x, five);
        let assumption = exec.ctx.terms.mk_eq(x, four);
        exec.independent_gate_authored_assertions = Some(vec![base]);
        exec.last_assumptions = Some(vec![assumption]);
        exec.last_model = Some(synthetic_lia_model(&[(x, 5)]));

        assert!(matches!(
            exec.confirm_sat_with_fully_evaluated_independent_gate(),
            GateVerdict::ModelViolates { assertion } if assertion == assumption
        ));
    }

    #[test]
    fn fully_evaluated_gate_accepts_true_temporary_assumption() {
        let mut exec = Executor::new();
        let x = exec.ctx.terms.mk_var("assuming-positive-x", Sort::Int);
        let five = exec.ctx.terms.mk_int(BigInt::from(5));
        let base = exec.ctx.terms.mk_eq(x, five);
        exec.independent_gate_authored_assertions = Some(vec![base]);
        exec.last_assumptions = Some(vec![base]);
        exec.last_model = Some(synthetic_lia_model(&[(x, 5)]));

        assert!(matches!(
            exec.confirm_sat_with_fully_evaluated_independent_gate(),
            GateVerdict::ConfirmedSat
        ));
    }

    #[test]
    fn fully_evaluated_gate_fails_closed_on_unevaluable_assumption() {
        let mut exec = Executor::new();
        let true_term = exec.ctx.terms.true_term();
        let unpinned = exec.ctx.terms.mk_var("assuming-unpinned", Sort::Bool);
        exec.independent_gate_authored_assertions = Some(vec![true_term]);
        exec.last_assumptions = Some(vec![unpinned]);
        exec.last_model = Some(synthetic_lia_model(&[]));

        assert!(matches!(
            exec.confirm_sat_with_fully_evaluated_independent_gate(),
            GateVerdict::CannotConfirm { .. }
        ));
    }

    #[test]
    fn assumption_definition_is_visible_to_read_conflicted_array_gate() {
        let mut exec = Executor::new();
        let zero = exec.ctx.terms.mk_int(BigInt::from(0));
        let constant = exec.ctx.terms.mk_const_array(Sort::Int, zero);
        let target = exec
            .ctx
            .terms
            .mk_var("assuming-array-target", Sort::array(Sort::Int, Sort::Int));
        let definition = exec.ctx.terms.mk_eq(target, constant);
        let read = exec.ctx.terms.mk_select(target, zero);
        let read_is_zero = exec.ctx.terms.mk_eq(read, zero);
        let true_term = exec.ctx.terms.true_term();
        exec.independent_gate_authored_assertions = Some(vec![true_term]);
        exec.last_assumptions = Some(vec![definition, read_is_zero]);

        let mut model = synthetic_lia_model(&[]);
        let mut arrays = ay_arrays::ArrayModel::default();
        arrays.read_conflicted.insert(target);
        model.array_model = Some(arrays);
        exec.last_model = Some(model);

        assert!(matches!(
            exec.confirm_sat_with_fully_evaluated_independent_gate(),
            GateVerdict::ConfirmedSat
        ));

        // Without the exact defining assumption, the poisoned leaf must not
        // be reconstructed from unrelated/transient state.
        exec.last_assumptions = Some(vec![read_is_zero]);
        assert!(matches!(
            exec.confirm_sat_with_fully_evaluated_independent_gate(),
            GateVerdict::CannotConfirm { .. }
        ));
    }

    #[test]
    fn sequence_euf_same_and_distinct_classes_are_exact() {
        let mut exec = Executor::new();
        let seq_int = Sort::Seq(Box::new(Sort::Int));
        let x = exec.ctx.terms.mk_var("seq-euf-x", seq_int.clone());
        let y = exec.ctx.terms.mk_var("seq-euf-y", seq_int.clone());
        let z = exec.ctx.terms.mk_var("seq-euf-z", seq_int);
        let equal = exec.ctx.terms.mk_eq(x, y);
        let distinct = exec.ctx.terms.mk_distinct(vec![x, z]);
        let model = synthetic_euf_model(&[(x, "e0"), (y, "e0"), (z, "e1")]);
        let view = IndependentModelView::new(&exec, &model);

        assert!(matches!(
            ay_model_check::evaluate_term(&exec.ctx.terms, &view, equal),
            EvalOutcome::Value(ModelValue::Bool(true))
        ));
        assert!(matches!(
            ay_model_check::evaluate_term(&exec.ctx.terms, &view, distinct),
            EvalOutcome::Value(ModelValue::Bool(true))
        ));
    }

    #[test]
    fn sequence_euf_declared_function_still_enforces_congruence() {
        let mut exec = Executor::new();
        let seq_int = Sort::Seq(Box::new(Sort::Int));
        let x = exec.ctx.terms.mk_var("seq-euf-arg-x", seq_int.clone());
        let y = exec.ctx.terms.mk_var("seq-euf-arg-y", seq_int.clone());
        let f = Symbol::Named("seq_euf_f".to_string());
        let fx = exec.ctx.terms.mk_app(f.clone(), vec![x], seq_int.clone());
        let fy = exec.ctx.terms.mk_app(f, vec![y], seq_int);
        let outputs_differ = exec.ctx.terms.mk_distinct(vec![fx, fy]);
        let model =
            synthetic_euf_model(&[(x, "arg"), (y, "arg"), (fx, "out-left"), (fy, "out-right")]);
        let view = IndependentModelView::new(&exec, &model);

        assert!(matches!(
            ay_model_check::evaluate_term(&exec.ctx.terms, &view, outputs_differ),
            EvalOutcome::Value(ModelValue::Bool(false))
        ));
    }

    #[test]
    fn sequence_euf_identity_is_sort_tagged_and_model_backed_only() {
        let mut exec = Executor::new();
        let seq_int = Sort::Seq(Box::new(Sort::Int));
        let seq_bool = Sort::Seq(Box::new(Sort::Bool));
        let int_seq = exec.ctx.terms.mk_var("seq-euf-int", seq_int.clone());
        let bool_seq = exec.ctx.terms.mk_var("seq-euf-bool", seq_bool);
        let unpinned = exec.ctx.terms.mk_var("seq-euf-unpinned", seq_int.clone());
        let syntactic_equality = exec.ctx.terms.mk_eq(int_seq, unpinned);
        exec.ctx.assertions.push(syntactic_equality);
        let model = synthetic_euf_model(&[(int_seq, "e0"), (bool_seq, "e0")]);
        let view = IndependentModelView::new(&exec, &model);

        let int_value = view.leaf_value(int_seq).expect("Seq Int class value");
        let bool_value = view.leaf_value(bool_seq).expect("Seq Bool class value");
        assert!(
            !values_equal(&int_value, &bool_value),
            "the same printable EUF class in different sequence carriers must not alias"
        );
        assert!(view.leaf_value(unpinned).is_none());
        assert!(matches!(
            ay_model_check::evaluate_term(&exec.ctx.terms, &view, syntactic_equality),
            EvalOutcome::Unevaluable(_)
        ));
    }

    #[test]
    fn sequence_euf_opaque_value_cannot_feed_sequence_builtins() {
        let mut exec = Executor::new();
        let seq_int = Sort::Seq(Box::new(Sort::Int));
        let x = exec.ctx.terms.mk_var("seq-euf-built-in", seq_int);
        let len = exec
            .ctx
            .terms
            .mk_app(Symbol::Named("seq.len".to_string()), vec![x], Sort::Int);
        let model = synthetic_euf_model(&[(x, "e0")]);
        let view = IndependentModelView::new(&exec, &model);

        assert!(matches!(
            ay_model_check::evaluate_term(&exec.ctx.terms, &view, len),
            EvalOutcome::Unevaluable(_)
        ));
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
                quantified_gate_checked_unsat(&mut exec, vec![obligation]),
                "iteration {iteration}: valid Bool-UF table equivalence was not proved"
            );
        }
    }

    /// Mixed nonlinear Int/Real arithmetic is intentionally unsupported by
    /// the checked probe and must remain fail-closed. The disposable 500 ms
    /// budget must also leave the caller's longer deadline untouched.
    #[test]
    fn quantified_gate_out_of_fragment_stays_unknown_and_restores_deadline() {
        let mut exec = Executor::new();
        let x = exec.ctx.terms.mk_var("qmg!real", Sort::Real);
        let y = exec.ctx.terms.mk_var("qmg!int", Sort::Int);
        let x_squared = exec.ctx.terms.mk_mul(vec![x, x]);
        let two = exec
            .ctx
            .terms
            .mk_rational(BigRational::from_integer(BigInt::from(2)));
        let nonlinear_real = exec.ctx.terms.mk_eq(x_squared, two);
        let zero = exec.ctx.terms.mk_int(BigInt::from(0));
        let integer_bound = exec.ctx.terms.mk_ge(y, zero);
        let assertions = vec![nonlinear_real, integer_bound];
        let (category, _) = exec.detect_logic_category(&assertions);
        assert_eq!(category, LogicCategory::QfNira);

        let outer_deadline = Instant::now() + Duration::from_secs(10);
        exec.set_deadline(Some(outer_deadline));
        assert!(
            exec.quantified_gate_checked_ground_solve(assertions)
                .is_none(),
            "an unsupported checked probe must not return a decision token"
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

    #[test]
    fn read_conflicted_array_resolves_through_recorded_substitution_chain() {
        let mut exec = Executor::new();
        let array_sort = Sort::array(Sort::Int, Sort::Int);
        let zero = exec.ctx.terms.mk_int(BigInt::from(0));
        let thirty = exec.ctx.terms.mk_int(BigInt::from(30));
        let base = exec.ctx.terms.mk_const_array(Sort::Int, zero);
        let stored = exec.ctx.terms.mk_store(base, zero, thirty);
        let source = exec
            .ctx
            .terms
            .mk_var("seq_array_proxy_source", array_sort.clone());
        let target = exec.ctx.terms.mk_var("seq_array_proxy_target", array_sort);
        let source_definition = exec.ctx.terms.mk_eq(source, stored);
        exec.ctx.assertions.push(source_definition);
        exec.recorded_var_substitutions.insert(target, source);

        let mut model = Model::empty();
        let mut arrays = ay_arrays::ArrayModel::default();
        arrays.read_conflicted.extend([target, source]);
        model.array_model = Some(arrays);
        let view = IndependentModelView::new(&exec, &model);

        let Some(ModelValue::Array(value)) = view.leaf_value(target) else {
            panic!("recorded substitution chain must reconstruct the array");
        };
        assert!(values_equal(
            &value.default,
            &ModelValue::Int(BigInt::from(0))
        ));
        assert_eq!(value.store.len(), 1);
        assert!(values_equal(
            &value.store[0].0,
            &ModelValue::Int(BigInt::from(0))
        ));
        assert!(values_equal(
            &value.store[0].1,
            &ModelValue::Int(BigInt::from(30))
        ));
    }

    #[test]
    fn cyclic_recorded_array_substitutions_fail_closed() {
        let mut exec = Executor::new();
        let array_sort = Sort::array(Sort::Int, Sort::Int);
        let a = exec.ctx.terms.mk_var("array-cycle-a", array_sort.clone());
        let b = exec.ctx.terms.mk_var("array-cycle-b", array_sort);
        exec.recorded_var_substitutions.insert(a, b);
        exec.recorded_var_substitutions.insert(b, a);

        let mut model = Model::empty();
        let mut arrays = ay_arrays::ArrayModel::default();
        arrays.read_conflicted.extend([a, b]);
        model.array_model = Some(arrays);
        let view = IndependentModelView::new(&exec, &model);

        assert!(view.leaf_value(a).is_none());
        assert!(view.leaf_value(b).is_none());
    }

    #[test]
    fn read_conflicted_array_needs_an_exact_same_sort_recorded_edge() {
        let mut exec = Executor::new();
        let array_sort = Sort::array(Sort::Int, Sort::Int);
        let target = exec
            .ctx
            .terms
            .mk_var("array-nonrecorded-target", array_sort.clone());
        let unrelated = exec
            .ctx
            .terms
            .mk_var("array-nonrecorded-source", array_sort);
        let zero = exec.ctx.terms.mk_int(BigInt::from(0));
        let base = exec.ctx.terms.mk_const_array(Sort::Int, zero);
        let unrelated_definition = exec.ctx.terms.mk_eq(unrelated, base);
        exec.ctx.assertions.push(unrelated_definition);

        let mut model = Model::empty();
        let mut arrays = ay_arrays::ArrayModel::default();
        arrays.read_conflicted.insert(target);
        model.array_model = Some(arrays);
        let view = IndependentModelView::new(&exec, &model);
        assert!(
            view.leaf_value(target).is_none(),
            "an unrelated definition must not authorize the poisoned target"
        );

        drop(view);
        exec.recorded_var_substitutions.insert(target, zero);
        let view = IndependentModelView::new(&exec, &model);
        assert!(
            view.leaf_value(target).is_none(),
            "an ill-sorted recorded edge must not authorize array reconstruction"
        );
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

    #[test]
    fn nontrivial_model_less_sat_fails_closed_even_with_validation_marker() {
        let mut exec = Executor::new();
        let assertion = exec.ctx.terms.true_term();
        exec.ctx.assertions.push(assertion);
        exec.last_result = Some(SolveResult::Sat);
        exec.last_model_validated = true;
        assert!(exec.last_model.is_none(), "the setup must have no witness");

        let gated = exec.apply_independent_model_gate(SolveResult::Sat);

        assert_eq!(gated, SolveResult::Unknown);
        assert_eq!(
            exec.last_statistics.get_string("model_check_gate.result"),
            Some("cannot-confirm")
        );
        assert_eq!(
            exec.last_statistics
                .get_string("model_check_gate.cannot_confirm_reason"),
            Some("no model was produced")
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

    #[test]
    fn quantified_sat_without_model_fails_closed() {
        let commands = parse(
            "(set-logic AUFLIA)\
             (assert (forall ((x Int)) (= x x)))",
        )
        .expect("valid SMT-LIB input");
        let mut exec = Executor::new();
        let outputs = exec.execute_all(&commands).expect("execute succeeds");
        assert!(outputs.is_empty(), "the setup must not solve the formula");
        assert!(exec.last_model.is_none(), "the setup must have no witness");

        let gated = exec.apply_quantified_model_failclosed_gate(SolveResult::Sat);
        assert_eq!(
            gated,
            SolveResult::Unknown,
            "a quantified SAT classification without a model is not a certificate"
        );
        assert_eq!(
            exec.last_statistics
                .get_string("model_check_gate.quantified"),
            Some("missing-model-failclosed")
        );
    }

    fn typed_quantified_confirmation_fixture() -> Executor {
        let mut exec = loaded(
            "(set-logic LIA)\
             (assert (forall ((x Int)) (= x x)))",
        );
        exec.last_model = Some(Model::empty());
        let roots = independent_gate_query_roots(&exec);
        let query_epoch = exec.query_authority_epoch.clone();
        let source_context_stamp = exec.ctx.source_context_stamp();
        let scope = QuantifiedModelCheckScope::capture(
            &mut exec,
            query_epoch,
            source_context_stamp,
            &roots,
        )
        .expect("fixture captures the checked model");
        let confirmation = scope.finish(&exec).expect("fixture remains current");
        exec.quantified_model_confirmation = Some(confirmation);
        exec
    }

    fn confirm_with_designated_quantified_handoff(exec: &Executor) -> GateVerdict {
        exec.confirm_sat_with_independent_gate_confirmation(
            exec.quantified_model_confirmation.as_ref(),
        )
    }

    #[test]
    fn forged_confirmed_telemetry_cannot_skip_quantified_leaves() {
        let mut exec = loaded(
            "(set-logic LIA)\
             (assert (forall ((x Int)) (= x x)))",
        );
        exec.last_model = Some(Model::empty());
        exec.last_statistics
            .set_string("model_check_gate.quantified", "confirmed");

        assert!(
            matches!(
                exec.confirm_sat_with_independent_gate(),
                GateVerdict::CannotConfirm { .. }
            ),
            "diagnostic text must never discharge a quantified leaf"
        );
    }

    #[test]
    fn quantified_check_scope_rejects_postcheck_model_replacement() {
        let mut exec = loaded(
            "(set-logic LIA)\
             (assert (forall ((x Int)) (= x x)))",
        );
        exec.last_model = Some(Model::empty());
        let roots = independent_gate_query_roots(&exec);
        let query_epoch = exec.query_authority_epoch.clone();
        let source_context_stamp = exec.ctx.source_context_stamp();
        let scope = QuantifiedModelCheckScope::capture(
            &mut exec,
            query_epoch,
            source_context_stamp,
            &roots,
        )
        .expect("pre-check scope captures the incoming model");

        let mut foreign = exec.last_model.as_ref().expect("fixture model").clone();
        let true_term = exec.ctx.terms.true_term();
        foreign
            .completed_values
            .insert(true_term, EvalValue::Bool(false));
        exec.last_model = Some(foreign);

        assert!(
            scope.finish(&exec).is_none(),
            "a clone installed after checking must not inherit the incoming model seal"
        );
    }

    #[test]
    fn quantified_check_scope_rejects_reused_root_slot() {
        let mut exec = Executor::new();
        exec.last_model = Some(Model::empty());
        let checkpoint = exec.ctx.terms.rollback_checkpoint();
        let body = exec.ctx.terms.true_term();
        let root = exec
            .ctx
            .terms
            .mk_forall(vec![("x".to_string(), Sort::Int)], body);
        let original_entry = exec
            .ctx
            .terms
            .entry_stamp(root)
            .expect("captured root is live");
        exec.ctx.assertions.push(root);
        let query_epoch = exec.query_authority_epoch.clone();
        let source_context_stamp = exec.ctx.source_context_stamp();
        let scope = QuantifiedModelCheckScope::capture(
            &mut exec,
            query_epoch,
            source_context_stamp,
            &[root],
        )
        .expect("scope captures the live quantified root");

        exec.ctx.assertions.clear();
        exec.ctx.terms.rollback_to(checkpoint);
        let replacement_body = exec.ctx.terms.false_term();
        let replacement = exec.ctx.terms.mk_forall(
            vec![("replacement".to_string(), Sort::Int)],
            replacement_body,
        );
        assert_eq!(replacement, root, "rollback should reuse the numeric slot");
        assert_ne!(
            exec.ctx.terms.entry_stamp(replacement),
            Some(original_entry),
            "the reused slot must have a different birth identity"
        );
        exec.ctx.assertions.push(replacement);

        assert!(
            scope.finish(&exec).is_none(),
            "numeric root equality cannot authenticate a rolled-back term"
        );
    }

    #[test]
    fn quantified_confirmation_rejects_reused_root_slot() {
        let mut exec = Executor::new();
        exec.last_model = Some(Model::empty());
        let checkpoint = exec.ctx.terms.rollback_checkpoint();
        let body = exec.ctx.terms.true_term();
        let root = exec
            .ctx
            .terms
            .mk_forall(vec![("x".to_string(), Sort::Int)], body);
        exec.ctx.assertions.push(root);
        let query_epoch = exec.query_authority_epoch.clone();
        let source_context_stamp = exec.ctx.source_context_stamp();
        let confirmation = QuantifiedModelCheckScope::capture(
            &mut exec,
            query_epoch,
            source_context_stamp,
            &[root],
        )
        .and_then(|scope| scope.finish(&exec))
        .expect("confirmation captures the live quantified root");

        exec.ctx.assertions.clear();
        exec.ctx.terms.rollback_to(checkpoint);
        let replacement_body = exec.ctx.terms.false_term();
        let replacement = exec.ctx.terms.mk_forall(
            vec![("replacement".to_string(), Sort::Int)],
            replacement_body,
        );
        assert_eq!(replacement, root, "rollback should reuse the numeric slot");
        exec.ctx.assertions.push(replacement);
        let model = exec
            .last_model
            .as_ref()
            .expect("sealed model remains installed");

        assert!(
            confirmation
                .bind_current(&exec, &[replacement], model)
                .is_none(),
            "a confirmation cannot be retargeted onto a reused root slot"
        );
    }

    #[test]
    fn quantified_confirmation_accepts_append_only_term_growth() {
        let mut exec = typed_quantified_confirmation_fixture();
        let roots = independent_gate_query_roots(&exec);
        let _suffix = exec
            .ctx
            .terms
            .mk_fresh_var("post-confirmation-suffix", Sort::Bool);
        let confirmation = exec
            .quantified_model_confirmation
            .as_ref()
            .expect("fixture installs a confirmation");
        let model = exec.last_model.as_ref().expect("fixture installs a model");

        assert!(
            confirmation.bind_current(&exec, &roots, model).is_some(),
            "unreferenced append-only suffix terms preserve every root entry"
        );
    }

    #[test]
    fn typed_quantified_confirmation_is_exact_and_stales_on_every_binding() {
        let mut exec = typed_quantified_confirmation_fixture();
        assert!(
            matches!(
                exec.confirm_sat_with_independent_gate(),
                GateVerdict::CannotConfirm { .. }
            ),
            "ordinary internal checks must not borrow the designated handoff"
        );
        exec.last_statistics
            .set_string("model_check_gate.quantified", "confirmed");
        assert_eq!(
            exec.apply_independent_model_gate(SolveResult::Sat),
            SolveResult::Sat,
            "the designated consumer may use the exact sealed handoff"
        );
        assert!(exec.quantified_model_confirmation.is_none());
        assert_eq!(
            exec.last_statistics
                .get_string("model_check_gate.quantified"),
            Some("confirmed"),
            "consumption does not rewrite diagnostic telemetry"
        );
        assert!(
            matches!(
                exec.confirm_sat_with_independent_gate(),
                GateVerdict::CannotConfirm { .. }
            ),
            "stale confirmed telemetry cannot resurrect a consumed handoff"
        );

        let mut epoch_stale = typed_quantified_confirmation_fixture();
        epoch_stale.advance_query_authority_epoch();
        assert!(matches!(
            confirm_with_designated_quantified_handoff(&epoch_stale),
            GateVerdict::CannotConfirm { .. }
        ));

        let mut source_stale = typed_quantified_confirmation_fixture();
        let push = parse("(push 1)").expect("valid push");
        source_stale
            .ctx
            .process_command(&push[0])
            .expect("push changes the source/scope stamp");
        assert!(matches!(
            confirm_with_designated_quantified_handoff(&source_stale),
            GateVerdict::CannotConfirm { .. }
        ));

        let mut roots_stale = typed_quantified_confirmation_fixture();
        let true_term = roots_stale.ctx.terms.true_term();
        roots_stale.ctx.assertions.push(true_term);
        assert!(matches!(
            confirm_with_designated_quantified_handoff(&roots_stale),
            GateVerdict::CannotConfirm { .. }
        ));

        let mut model_stale = typed_quantified_confirmation_fixture();
        model_stale.last_model = Some(Model::empty());
        assert!(matches!(
            confirm_with_designated_quantified_handoff(&model_stale),
            GateVerdict::CannotConfirm { .. }
        ));

        let mut cloned_model_stale = typed_quantified_confirmation_fixture();
        let mut cloned = cloned_model_stale
            .last_model
            .as_ref()
            .expect("fixture model")
            .clone();
        let true_term = cloned_model_stale.ctx.terms.true_term();
        cloned
            .completed_values
            .insert(true_term, EvalValue::Bool(false));
        cloned_model_stale.last_model = Some(cloned);
        assert!(matches!(
            confirm_with_designated_quantified_handoff(&cloned_model_stale),
            GateVerdict::CannotConfirm { .. }
        ));

        let mut revoked = typed_quantified_confirmation_fixture();
        revoked
            .last_model
            .as_mut()
            .expect("fixture model")
            .revoke_quantified_confirmation();
        assert!(matches!(
            confirm_with_designated_quantified_handoff(&revoked),
            GateVerdict::CannotConfirm { .. }
        ));
    }

    #[test]
    fn canonical_quantified_authority_clear_consumes_direct_confirmation() {
        let mut exec = typed_quantified_confirmation_fixture();
        assert!(matches!(
            confirm_with_designated_quantified_handoff(&exec),
            GateVerdict::ConfirmedSat
        ));

        exec.clear_quantified_sat_authority();

        assert!(exec.quantified_model_confirmation.is_none());
        assert!(matches!(
            confirm_with_designated_quantified_handoff(&exec),
            GateVerdict::CannotConfirm { .. }
        ));
    }

    #[test]
    fn quantified_gate_independently_confirms_vacuous_inner_forall() {
        let mut exec = loaded(
            r#"
                (set-logic AUFLIA)
                (define-fun a ((x Int)) Bool (= x 0))
                (define-fun A () (Array Int Int) ((as const (Array Int Int)) 1))
                (assert (forall ((x Int))
                    (=> (a x)
                        (forall ((y Int)) (not (= (select A y) x))))))
            "#,
        );
        // Force the proofless global-validity fallback to decline. The model
        // gate must independently confirm the exact vacuity equivalence and
        // the remaining quantifier-free matrix instead.
        exec.set_produce_proofs(true);
        exec.last_model = Some(Model::empty());

        assert_eq!(
            exec.apply_quantified_model_failclosed_gate(SolveResult::Sat),
            SolveResult::Sat
        );
        assert_eq!(
            exec.last_statistics
                .get_string("model_check_gate.quantified"),
            Some("confirmed")
        );
    }

    #[test]
    fn quantified_gate_keeps_used_inner_binder_and_fails_closed() {
        let mut exec = loaded(
            r#"
                (set-logic UFLIA)
                (declare-fun f (Int) Int)
                (assert (forall ((x Int))
                    (or (forall ((y Int)) (= (f x) y)) (= x 0))))
            "#,
        );
        exec.set_produce_proofs(true);
        exec.last_model = Some(Model::empty());

        assert_eq!(
            exec.apply_quantified_model_failclosed_gate(SolveResult::Sat),
            SolveResult::Unknown,
            "a genuinely used residual binder must not be erased or certified"
        );
        assert_eq!(
            exec.last_unknown_reason,
            Some(UnknownReason::Incomplete),
            "the gate records the reason before the public funnel commits last_result"
        );
        assert!(
            exec.last_model.is_none(),
            "a fail-closed quantified witness must not remain observable"
        );
    }

    /// Evaluator incompleteness is not a refutation, but it is also not an
    /// independent SAT certificate. The public boundary must fail closed.
    #[test]
    fn coverage_gap_fails_closed_and_is_recorded() {
        let (mut exec, outputs) = solved(XEQ5);
        assert_eq!(outputs[0], "sat");

        // A LIA model with NO value for x: the leaf is unpinned (Unknown),
        // nothing is refuted, so the gate cannot confirm — a coverage gap.
        exec.last_model = Some(synthetic_lia_model(&[]));

        let gated = exec.apply_independent_model_gate(SolveResult::Sat);
        assert_eq!(
            gated,
            SolveResult::Unknown,
            "an independently unconfirmed witness must not retain SAT authority"
        );
        assert!(exec.last_model.is_none());
        // The GATE's own field, not the `unknown_reason()` accessor. That
        // accessor returns `None` unless `last_result == Some(Unknown)`, and
        // setting `last_result` is the CALLER's job (`emit_sat_verdict`), not
        // the gate's -- so driving the gate in isolation and then querying the
        // whole-path accessor was asserting something this unit can never
        // establish. The production path is unaffected and does report it:
        // a gate-declined query prints `(:reason-unknown incomplete)`.
        assert_eq!(
            exec.last_unknown_reason,
            Some(UnknownReason::Incomplete),
            "the gate must record WHY it could not confirm"
        );
        assert_eq!(
            exec.last_statistics.get_string("model_check_gate.result"),
            Some("cannot-confirm"),
            "the coverage gap must be recorded in the gate telemetry"
        );
    }

    /// `--self-check` observes the same mandatory public policy.
    #[test]
    fn self_check_coverage_gap_fails_closed_to_unknown() {
        let (mut exec, outputs) = solved(XEQ5);
        assert_eq!(outputs[0], "sat");
        exec.last_model = Some(synthetic_lia_model(&[]));
        exec.set_self_check(true);

        let gated = exec.apply_independent_model_gate(SolveResult::Sat);
        assert_eq!(gated, SolveResult::Unknown);
        assert!(exec.last_model.is_none());
        // The GATE's own field, not the `unknown_reason()` accessor. That
        // accessor returns `None` unless `last_result == Some(Unknown)`, and
        // setting `last_result` is the CALLER's job (`emit_sat_verdict`), not
        // the gate's -- so driving the gate in isolation and then querying the
        // whole-path accessor was asserting something this unit can never
        // establish. The production path is unaffected and does report it:
        // a gate-declined query prints `(:reason-unknown incomplete)`.
        assert_eq!(
            exec.last_unknown_reason,
            Some(UnknownReason::Incomplete),
            "the gate must record WHY it could not confirm"
        );
        assert_eq!(
            exec.last_statistics.get_string("model_check_gate.result"),
            Some("cannot-confirm")
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
    fn read_congruence_distinct_index_values_are_indeterminate_not_refuted() {
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

        // The property is CONSERVATISM: the congruent-read pass must not treat
        // reads at distinct indices as a REFUTATION. It is not that the gate
        // returns `Sat` -- this witness deliberately pins only `x` and `z`, so
        // `arr1` is an unpinned leaf and the gate cannot confirm it. Refusing
        // to confirm a partial model is correct, and it lands on `Unknown` by
        // the same route a refutation does, so the verdict alone cannot tell
        // the two apart. The telemetry can, and that is what is asserted.
        assert_eq!(
            exec.last_statistics.get_string("model_check_gate.result"),
            Some("cannot-confirm"),
            "distinct-index reads are INDETERMINATE, never a refutation"
        );
        assert_ne!(
            exec.last_statistics.get_string("model_check_gate.result"),
            Some("model-violates"),
            "the congruent-read pass must not refute a valid witness"
        );
        assert_eq!(gated, SolveResult::Unknown);
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
            quantified_confirmation_seal: Default::default(),
            quantified_grant_model_seal: Default::default(),
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
            projection_ufs: Default::default(),
            certified_total_ufs: Default::default(),
            certified_const_interps: Default::default(),
            formula_neutral_function_defaults: Default::default(),
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

    /// A ∀∃ alternation whose truth depends on the EMITTED VALUE of a model
    /// constant. `∀x:Int. ∃y:Int. (y = 1 ∧ x·y ≥ x + c)` forces `y := 1`, so
    /// the alternation says exactly `c ≤ 0` (z3 5.0.0 differential, measured:
    /// `sat` with `(= c 0)`, `unsat` with `(= c 5)`).
    ///
    /// It is deliberately NONLINEAR (`x·y`) so `deep_qe` cannot eliminate the
    /// alternation and the general route stays non-decisive — the ∀∃ witness
    /// route is the only lane that can decide it.
    const FORALL_EXISTS_MODEL_SENSITIVE: &str = "(set-logic NIA)\
         (declare-fun c () Int)\
         (assert (forall ((x Int)) (exists ((y Int)) (and (= y 1) (>= (* x y) (+ x c))))))";

    /// Load [`FORALL_EXISTS_MODEL_SENSITIVE`] and publish `c := value` as the
    /// emitted witness, with NO `check-sat` — the gate is exercised on a model
    /// this test chose, so the two legs below differ in the MODEL alone.
    fn forall_exists_gate_with_c(value: i64) -> Executor {
        let commands = parse(FORALL_EXISTS_MODEL_SENSITIVE).expect("valid SMT-LIB input");
        let mut exec = Executor::new();
        exec.execute_all(&commands).expect("execute succeeds");
        let c = exec.ctx.terms.mk_var("c", Sort::Int);
        exec.last_model = Some(synthetic_lia_model(&[(c, value)]));
        exec
    }

    /// THE NON-VACUITY BAR for the ∀∃ witness route.
    ///
    /// A confirm that did not actually evaluate the quantified body under the
    /// emitted model would pass the first leg and the second one too. This
    /// test holds the FORMULA and the CODE PATH fixed and varies only the
    /// model:
    ///
    /// * `c = 0` — the synthesised witness `y := 1` reduces the conjunct to
    ///   the ground obligation `¬(sk·1 ≥ sk + 0)`, which is UNSAT, so the gate
    ///   CONFIRMS and the `Sat` survives with the quantified-gate marker;
    /// * `c = 5` — the same witness yields `¬(sk·1 ≥ sk + 5)`, which is
    ///   SATISFIABLE, no other candidate discharges, and the gate fails closed
    ///   to `Unknown`.
    ///
    /// The second leg is a MUTANT MODEL the gate must reject, and does.
    #[test]
    fn forall_exists_witness_route_confirm_is_model_sensitive() {
        let mut honest = forall_exists_gate_with_c(0);
        assert_eq!(
            honest.apply_quantified_model_failclosed_gate(SolveResult::Sat),
            SolveResult::Sat,
            "the ∀∃ witness route must confirm the alternation under c = 0"
        );
        assert_eq!(
            honest
                .last_statistics
                .get_string("model_check_gate.quantified"),
            Some("confirmed"),
            "the Sat must survive because the QUANTIFIED gate confirmed the \
             alternation — not because some lane bypassed it"
        );

        let mut mutant = forall_exists_gate_with_c(5);
        assert_eq!(
            mutant.apply_quantified_model_failclosed_gate(SolveResult::Sat),
            SolveResult::Unknown,
            "a model that FALSIFIES the alternation must never be confirmed"
        );
        assert_ne!(
            mutant
                .last_statistics
                .get_string("model_check_gate.quantified"),
            Some("confirmed"),
            "the mutant model must not be recorded as a quantified-gate confirm"
        );
    }

    /// The witness route is CONFIRM-ONLY over a genuinely quantifier-free
    /// obligation: it must decline when no candidate term witnesses the
    /// existential. `∀x:Int. ∃y:Int. (y ≤ x ∧ y ≥ x+1)` is FALSE for every
    /// `x`, so every candidate leaves the negated obligation satisfiable and
    /// the gate must fail closed even though the sentence is closed and
    /// alternating — the same shape the route confirms above.
    #[test]
    fn forall_exists_witness_route_declines_when_no_witness_exists() {
        let commands = parse(
            "(set-logic NIA)\
             (assert (forall ((x Int)) (exists ((y Int)) \
                (and (<= y x) (>= y (+ x 1)) (>= (* x x) 0)))))",
        )
        .expect("valid SMT-LIB input");
        let mut exec = Executor::new();
        exec.execute_all(&commands).expect("execute succeeds");
        exec.last_model = Some(synthetic_lia_model(&[]));
        assert_eq!(
            exec.apply_quantified_model_failclosed_gate(SolveResult::Sat),
            SolveResult::Unknown,
            "an unwitnessable ∀∃ must never be confirmed by the witness route"
        );
    }
}

#[cfg(test)]
mod sexpr_items_tests {
    use super::sexpr_items;

    #[test]
    fn splits_top_level_items_and_keeps_nested_forms_whole() {
        assert_eq!(
            sexpr_items("((as const (Array (_ BitVec 64) (_ BitVec 64))) #x0000000000000000)"),
            Some(vec![
                "(as const (Array (_ BitVec 64) (_ BitVec 64)))".to_string(),
                "#x0000000000000000".to_string(),
            ]),
            "the `as const` head is ONE item, not four"
        );
        // The head splits in turn into exactly the three tokens
        // `parse_array_text` matches on before it will read a const-array.
        assert_eq!(
            sexpr_items("(as const (Array Int Int))"),
            Some(vec![
                "as".to_string(),
                "const".to_string(),
                "(Array Int Int)".to_string(),
            ])
        );
        assert_eq!(
            sexpr_items("(store a #x01 #x02)"),
            Some(vec![
                "store".to_string(),
                "a".to_string(),
                "#x01".to_string(),
                "#x02".to_string()
            ])
        );
        // Nested stores stay whole at the top level, so the store chain is
        // consumed one level per recursion (outermost store wins).
        assert_eq!(
            sexpr_items("(store (store a 0 1) 2 3)").unwrap()[1],
            "(store a 0 1)"
        );
        // A nested array cell comes back whole, for the caller to parse in turn.
        assert_eq!(
            sexpr_items("((as const (Array Int (Array Int Int))) ((as const (Array Int Int)) 0))")
                .unwrap()[1],
            "((as const (Array Int Int)) 0)"
        );
        // Leading/trailing whitespace and runs of spaces.
        assert_eq!(
            sexpr_items("  (  store   a  0 1 )  "),
            Some(vec![
                "store".to_string(),
                "a".to_string(),
                "0".to_string(),
                "1".to_string()
            ])
        );
    }

    /// Parens inside a STRING literal are not structure, and `""` is the
    /// SMT-LIB escape for one quote INSIDE a literal rather than its end.
    #[test]
    fn string_literals_are_opaque() {
        assert_eq!(
            sexpr_items(r#"(store a "a (b" "c)d")"#),
            Some(vec![
                "store".to_string(),
                "a".to_string(),
                r#""a (b""#.to_string(),
                r#""c)d""#.to_string(),
            ])
        );
        assert_eq!(
            sexpr_items(r#"(store a "he said ""hi"" )" 0)"#),
            Some(vec![
                "store".to_string(),
                "a".to_string(),
                r#""he said ""hi"" )""#.to_string(),
                "0".to_string(),
            ]),
            "an escaped quote does not end the literal, so the `)` stays inside it"
        );
    }

    /// A `|…|` quoted symbol is one atom, whatever it contains.
    #[test]
    fn quoted_symbols_are_opaque() {
        assert_eq!(
            sexpr_items("(store a |weird (name)| 0)"),
            Some(vec![
                "store".to_string(),
                "a".to_string(),
                "|weird (name)|".to_string(),
                "0".to_string(),
            ])
        );
        assert_eq!(sexpr_items("(store a |unterminated 0)"), None);
    }

    /// Anything not a single balanced parenthesized form is refused, so an
    /// unrecognized rendering stays opaque rather than becoming a wrong value.
    /// A wrong array here would be confirmed as readily as a right one, whereas
    /// `None` only costs a refusal.
    #[test]
    fn malformed_input_is_refused() {
        assert_eq!(sexpr_items("not-parenthesized"), None);
        assert_eq!(sexpr_items("(unbalanced"), None);
        assert_eq!(sexpr_items("unbalanced)"), None);
        assert_eq!(sexpr_items("(a))("), None, "balanced count, wrong nesting");
        assert_eq!(sexpr_items(r#"("unterminated)"#), None);
        assert_eq!(sexpr_items("(a (b)"), None);
        assert_eq!(sexpr_items("((as const (Array Int Int)) 0"), None);
        assert_eq!(
            sexpr_items("@Array!0"),
            None,
            "an abstract atom is not a form"
        );
        assert_eq!(sexpr_items(""), None);
        // An empty form parses, with NO items — `parse_array_text`'s
        // `items.first()?` is what refuses it, so it never reads as an array.
        assert_eq!(sexpr_items("()"), Some(Vec::new()));
    }
}
