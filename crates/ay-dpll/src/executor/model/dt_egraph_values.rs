// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Single-source datatype value assignment from the solver's final e-graph
//! (#mv-dt-single-source).
//!
//! At `Sat`, the datatype lanes leave an e-graph behind: the pure-DT pipeline
//! exports the interactive `DtSolver` state directly ([`ay_dt::DtModel`] via
//! `extract_models`), and the eager combined lanes (`solve_dt_ax` — the route
//! the QF_DT `has_uf` widening actually takes for the barrett-jsat family)
//! leave the same information in the EUF model's equivalence classes plus the
//! SAT assignment of the tester/equality atoms, from which an equivalent
//! [`ay_dt::DtModel`] is synthesized here. This module derives from either
//! export ONE rendered SMT-LIB value per datatype-sorted class, and every
//! print-time consumer — `(get-model)` constants, `(get-value)` resolution
//! (`resolve_dt_value`), and the total selector definitions' committed cases —
//! reads THAT assignment.
//!
//! Why: the legacy path re-derived each printed value per term through
//! independent syntactic strategies with canonical-default fallbacks, so two
//! terms the e-graph had MERGED could print different trees, and two terms
//! asserted DISEQUAL could both fall to the same fabricated default — the
//! Dolmen `E:bad-model` (ModelUnsat) class root-caused by the M3 probe and
//! sharpened by M4 F1 (v1l40058: printed totalization committed
//! `cdr(null) = null`, collapsing an asserted disequality the internal model
//! satisfied).
//!
//! Construction (bottom-up, fail-closed):
//! - a class with a committed constructor APPLICATION renders that constructor
//!   over the values of its argument terms' classes;
//! - a class committed only by a TESTER renders the tester's constructor, with
//!   each field read from the class of the matching selector application when
//!   one exists, and completed with a canonical default otherwise (genuinely
//!   free slack);
//! - an UNCOMMITTED class takes a generated value: distinct-by-construction
//!   candidates (nullary constructors, then a pumped recursive constructor)
//!   filtered by negative-tester commitments, preferring values unused by any
//!   other same-sort class;
//! - selector CONGRUENCE over rendered values is reconciled: two selector
//!   applications whose arguments render to the SAME value must render to the
//!   same value themselves — free application classes are PINNED to the
//!   committed value, a selector application on a right-constructor argument
//!   is pinned to the argument's rendered field, equal-rendered argument
//!   classes are separated through recursive slack, and TESTER-only
//!   commitments (which may be don't-care SAT noise — the eager encoding only
//!   axiomatizes covered terms) are DEMOTED to free when they block a repair;
//! - asserted-DISEQUAL classes with colliding values are separated over
//!   bounded rounds by re-choosing slack; an unseparable collision is left in
//!   place (the false equality atom may itself be don't-care noise);
//! - finally, a structural SELF-CHECK re-evaluates every assertion with all
//!   datatype boundary subterms pinned to the assignment's validator-visible
//!   values. Only a fully-true re-evaluation lets the total selector
//!   definitions ship; on failure they are withheld (partial model, at worst
//!   0 points, never a wrong one) and still-violated disequality classes are
//!   poisoned out of the constant emission. This check is what makes the
//!   noise-demotion sound: a load-bearing atom the repairs flipped always
//!   surfaces here, fail-closed.
//!
//! The assignment is deterministic (TermId-ordered iteration everywhere) and
//! memoized per accepted model, so `(get-model)` and any number of
//! `(get-value)` queries observe identical values.

use std::sync::Arc;

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{Sort, TermId};

use super::{EvalValue, Executor, Model};

/// Hard cap on value-construction recursion depth (fail-closed poison past it).
const DT_VALUE_DEPTH: u32 = 4096;

/// Candidate budget when choosing a value for an uncommitted class.
const DT_FRESH_CANDIDATES: u64 = 64;

/// Maximum repair/reconciliation rebuild rounds before poisoning violators.
const DT_REPAIR_ROUNDS: u32 = 8;

/// Separation attempts per class PAIR before leaving its collision in place
/// (#dt-egraph-sticky-free). Two classes can CHASE each other — each repair
/// re-choice re-colliding at the next generated value when their slack feeds
/// shared structure — and every attempt pumps another avoid entry, churning
/// values across the whole assignment. A pair that did not separate in a few
/// attempts is left colliding for the structural self-check to arbitrate
/// (don't-care noise passes; a load-bearing collision fails closed).
const DT_PAIR_SEPARATION_ATTEMPTS: u32 = 3;

/// The per-class rendered value assignment (see module docs).
pub(in crate::executor) struct DtEgraphAssignment {
    /// The e-graph export the assignment was derived from (theory export or
    /// EUF synthesis); carries the term -> class-representative map.
    pub(in crate::executor) dtm: ay_dt::DtModel,
    /// Class representative -> rendered SMT-LIB constructor value.
    pub(in crate::executor) class_value: HashMap<TermId, String>,
    /// Class representative -> rendered field values, parallel to the
    /// rendered constructor's declared selector order (empty for nullary;
    /// absent for classes whose value was pinned opaquely).
    pub(in crate::executor) class_fields: HashMap<TermId, Vec<String>>,
    /// Class representative -> the constructor its value renders with.
    pub(in crate::executor) class_ctor: HashMap<TermId, String>,
    /// Classes that could not be coherently valued (fail-closed; callers must
    /// fall back or omit, never default).
    pub(in crate::executor) poisoned: HashSet<TermId>,
    /// Classes the failed structural self-check PROVED incoherent: their
    /// values (or shared class) still violate an asserted disequality after
    /// every repair round. Stage-4 review F2: these must never be delegated
    /// to a legacy emitter — it re-derives the same proven collision
    /// (`c8-tester-distinct` → E:bad-model, voiding); their constant
    /// definitions are OMITTED outright. A subset of `poisoned` (the other
    /// poisons keep the pre-existing legacy fallback, which the M1/M3
    /// samples validated end-to-end).
    pub(in crate::executor) diseq_incoherent: HashSet<TermId>,
    /// Whether the final assignment PASSED the structural self-check: every
    /// assertion re-evaluates to true with all datatype boundary subterms
    /// pinned to the assignment's rendered values (the same way the model
    /// validator will evaluate the printed model). When false, the total
    /// selector definitions are withheld entirely — a partial model is at
    /// worst 0 points to a validator, never a wrong one.
    pub(in crate::executor) self_check_ok: bool,
}

/// Verdict of the single-source UF-function-table rewrite
/// ([`Executor::dt_egraph_rewrite_uf_table`], stage-4 review F3).
pub(in crate::executor) enum DtUfTableRewrite {
    /// No selector-bearing datatype argument/result position: the legacy
    /// emission is unaffected (enum-only tables keep their validated path).
    NotApplicable,
    /// Every datatype-sorted branch key/value was rendered through the
    /// single-source assignment (and the rendered keys are collision-free):
    /// emit THIS table.
    Rewritten(Vec<(Vec<String>, String)>),
    /// Fail-closed: the definition must be OMITTED entirely (a partial model
    /// is at worst 0 points to a validator, never a wrong one) — never
    /// delegated to the legacy abstract-element emission, whose branch keys
    /// the validator cannot match against the printed constants.
    Drop,
}

/// How a class's constructor is committed by the e-graph export.
#[derive(Clone)]
enum CtorCommit {
    /// A registered constructor application lives in the class.
    App(String, Vec<TermId>),
    /// Only a tester constrains the class (positively, or negatively down to
    /// a single remaining constructor).
    Tester(String),
    /// Unconstrained (modulo the ruled-out constructors and pins).
    Free,
}

impl Executor {
    /// Drop the DT e-graph export and its derived assignment (called on every
    /// stored verdict and at each `check_sat` entry, #mv-dt-single-source).
    pub(in crate::executor) fn clear_dt_theory_model(&mut self) {
        self.dt_theory_model = None;
        self.dt_validation_wants_egraph = false;
        self.dt_egraph_assignment.replace(None);
    }

    /// Whether a single-source assignment is derivable for the current model
    /// (cheap check; the assignment itself is built lazily). True when the DT
    /// lane exported its e-graph, or an EUF model over declared datatypes can
    /// be synthesized (array-free problems only — datatype-carrying-array VCs
    /// keep the gate-reconstruction emission path).
    pub(in crate::executor) fn dt_egraph_available(&self, model: &Model) -> bool {
        if self.dt_theory_model.is_some() {
            return true;
        }
        self.dt_egraph_synth_applicable(model)
    }

    /// The single-source rendered value of a datatype-sorted `term` under the
    /// current e-graph assignment, or `None` when there is no assignment, the
    /// term's class is poisoned, or the term cannot be resolved structurally —
    /// callers fall back to the legacy strategies (fail-closed, never a
    /// fabricated default from HERE).
    pub(in crate::executor) fn dt_egraph_value(
        &self,
        model: &Model,
        term: TermId,
    ) -> Option<String> {
        if self.dt_egraph_building.get() {
            // Reentrancy latch: evaluation nested inside the builder must not
            // consult the (incomplete) assignment.
            return None;
        }
        let sort = self.ctx.terms.sort(term).clone();
        self.datatype_sort_name(&sort)?;
        let asg = self.dt_egraph_assignment_cached(model)?;
        // Single-engine coherence (merge of #mv-dt-single-source with
        // #dt-total-model): an assignment that FAILED its structural
        // self-check must not serve ANY value — mixing its surviving class
        // values with the total-construction/legacy fallbacks that the
        // remaining (withheld) positions take can split one model across two
        // disagreeing free-slack engines (observed: `(distinct a b c d)`
        // over a finite parametric sort refuted at emit because two engines
        // picked colliding completions). Withholding wholesale falls back to
        // the validated `dt_ground` construction and the legacy strategies —
        // at worst a partial model, never a mixed one. The UF-table rewrite
        // and the totalization scan already fail closed on the same flag.
        if !asg.self_check_ok {
            return None;
        }
        let rep = asg.dtm.rep(term);
        if let Some(v) = asg.class_value.get(&rep) {
            return Some(v.clone());
        }
        if asg.poisoned.contains(&rep) {
            return None;
        }
        // Terms created after the assignment was built (fresh `(get-value)`
        // composites): resolve structurally against the assignment so answers
        // stay coherent with the printed model.
        self.dt_egraph_structural_value(model, &asg, term, 64)
    }

    /// Whether `term`'s class was PROVEN INCOHERENT by the failed structural
    /// self-check's disequality sweep: its printed value (or shared class)
    /// violates an asserted disequality after every repair round. The
    /// constant emission must OMIT such a definition entirely (fail-closed) —
    /// never delegate to a legacy emitter, which re-derives the same proven
    /// collision (stage-4 review F2: `c8-tester-distinct` printed a known
    /// `distinct`-violating collision through the legacy constant path after
    /// the self-check had already proved it wrong — E:bad-model,
    /// division-voiding; omission is at worst a 0-point partial model).
    /// Build-time poisons (cycle / pin-conflict / generation failure) are NOT
    /// flagged here: for those the check proved nothing about the legacy
    /// value, and the pre-existing fallback is sample-validated (e.g.
    /// `c3b-demote-sat` prints a correct tower through it, Dolmen exit 0).
    pub(in crate::executor) fn dt_egraph_class_poisoned(
        &self,
        model: &Model,
        term: TermId,
    ) -> bool {
        if self.dt_egraph_building.get() {
            return false;
        }
        if self.datatype_sort_name(self.ctx.terms.sort(term)).is_none() {
            return false;
        }
        let Some(asg) = self.dt_egraph_assignment_cached(model) else {
            return false;
        };
        asg.diseq_incoherent.contains(&asg.dtm.rep(term))
    }

    /// Whether the assignment passed its structural self-check (assertions
    /// re-evaluate true against the validator-visible values). False (or no
    /// assignment) means the total selector definitions must be WITHHELD:
    /// a partial model is at worst 0 points, a wrong one voids.
    pub(in crate::executor) fn dt_egraph_self_check_ok(&self, model: &Model) -> bool {
        if self.dt_egraph_building.get() {
            return false;
        }
        self.dt_egraph_assignment_cached(model)
            .is_some_and(|asg| asg.self_check_ok)
    }

    /// The committed constructor of `term`'s class under the assignment, if
    /// one was rendered (used by the totalization scan to detect
    /// owning-constructor arguments without string parsing).
    pub(in crate::executor) fn dt_egraph_class_ctor(
        &self,
        model: &Model,
        term: TermId,
    ) -> Option<String> {
        if self.dt_egraph_building.get() {
            return None;
        }
        let asg = self.dt_egraph_assignment_cached(model)?;
        let rep = asg.dtm.rep(term);
        asg.class_ctor.get(&rep).cloned()
    }

    /// Whether `sort` is a SELECTOR-BEARING datatype (at least one
    /// constructor has a field). Enum-only (all-nullary) datatypes are
    /// excluded: they have no selector totalizations, their eager enum-SAT
    /// emission is validated end-to-end, and the single-source assignment is
    /// deliberately not derived for them.
    pub(in crate::executor) fn selector_bearing_datatype(&self, sort: &Sort) -> bool {
        let Some(dt_name) = self.datatype_sort_name(sort) else {
            return false;
        };
        self.ctx
            .datatype_iter()
            .find(|(n, _)| *n == dt_name)
            .is_some_and(|(_, ctors)| {
                ctors.iter().any(|c| {
                    self.ctx
                        .constructor_selector_info(c)
                        .is_some_and(|fs| !fs.is_empty())
                })
            })
    }

    /// Single-source rewrite of a UF function table over selector-bearing
    /// datatype sorts (stage-4 review F3, #mv-dt-single-source).
    ///
    /// The legacy emission keys UF-table branches on ABSTRACT e-graph elements
    /// (`(as @N!k N)`) while the constants print concrete constructor trees
    /// from the single-source assignment; a validator evaluating the printed
    /// model can then never match a branch key, every application falls to the
    /// default arm, and a satisfied disequality `(not (= (f a) (f b)))`
    /// evaluates false — E:bad-model, division-voiding (`c1-ufdt-f`).
    ///
    /// Rewrites every datatype-sorted branch key/value through the SAME
    /// per-class assignment the constants print, so the validator's table
    /// lookup reproduces exactly the values the structural self-check pinned
    /// for the corresponding applications. Fail-closed at every gap:
    /// no assignment, failed self-check, an unmapped/poisoned element, or two
    /// distinct element keys whose RENDERED values collide with diverging
    /// results (the rendered table would no longer be a function graph) all
    /// yield [`DtUfTableRewrite::Drop`] — the caller omits the definition
    /// (partial, non-voiding) rather than print an unfaithful one.
    pub(in crate::executor) fn dt_egraph_rewrite_uf_table(
        &self,
        model: &Model,
        arg_sorts: &[Sort],
        result_sort: &Sort,
        table: &[(Vec<String>, String)],
    ) -> DtUfTableRewrite {
        // Applicability: any SELECTOR-BEARING datatype position. Rewriting
        // then covers EVERY datatype-sorted position (enum sorts included —
        // once the table must read the assignment, mixed sorts must read one
        // coherent source).
        if !arg_sorts
            .iter()
            .chain(std::iter::once(result_sort))
            .any(|s| self.selector_bearing_datatype(s))
        {
            return DtUfTableRewrite::NotApplicable;
        }
        let arg_dt: Vec<bool> = arg_sorts
            .iter()
            .map(|s| self.datatype_sort_name(s).is_some())
            .collect();
        let res_dt = self.datatype_sort_name(result_sort).is_some();
        if self.dt_egraph_building.get() {
            return DtUfTableRewrite::Drop;
        }
        let (Some(asg), Some(euf)) = (
            self.dt_egraph_assignment_cached(model),
            model.euf_model.as_ref(),
        ) else {
            return DtUfTableRewrite::Drop;
        };
        if !asg.self_check_ok {
            // The assignment could not certify the assertions; a table read
            // through it is as unfaithful as the abstract one. Fail closed.
            return DtUfTableRewrite::Drop;
        }

        // Abstract element -> single-source rendered value, over all
        // datatype-sorted terms (TermId-ascending scan = deterministic). An
        // element observed with two diverging class values, or valued by a
        // poisoned/unvalued class, is CONFLICTED and unmappable.
        let mut elem_value: HashMap<&str, &str> = HashMap::default();
        let mut conflicted: HashSet<&str> = HashSet::default();
        for raw in 0..self.ctx.terms.len() {
            let tid = TermId(raw as u32);
            if self.datatype_sort_name(self.ctx.terms.sort(tid)).is_none() {
                continue;
            }
            let Some(elem) = euf.term_values.get(&tid) else {
                continue;
            };
            match asg.class_value.get(&asg.dtm.rep(tid)) {
                None => {
                    conflicted.insert(elem.as_str());
                }
                Some(v) => match elem_value.get(elem.as_str()) {
                    None => {
                        elem_value.insert(elem.as_str(), v.as_str());
                    }
                    Some(prev) if *prev == v.as_str() => {}
                    Some(_) => {
                        conflicted.insert(elem.as_str());
                    }
                },
            }
        }
        let map_dt = |raw: &str| -> Option<String> {
            if conflicted.contains(raw) {
                return None;
            }
            if let Some(v) = elem_value.get(raw) {
                return Some((*v).to_string());
            }
            // Not an e-graph element: accept only a bare NULLARY-constructor
            // token, which is its own single-source rendering; anything else
            // is unmappable (fail-closed).
            if !raw.starts_with('@')
                && !raw.contains(['(', ' '])
                && self.ctx.is_constructor(raw).is_some()
            {
                return Some(self.dt_surface(raw).to_string());
            }
            None
        };

        let mut out: Vec<(Vec<String>, String)> = Vec::with_capacity(table.len());
        let mut seen: HashMap<Vec<String>, String> = HashMap::default();
        for (args, result) in table {
            let mut new_args = Vec::with_capacity(args.len());
            for (i, a) in args.iter().enumerate() {
                if arg_dt.get(i).copied().unwrap_or(false) {
                    let Some(v) = map_dt(a) else {
                        return DtUfTableRewrite::Drop;
                    };
                    new_args.push(v);
                } else {
                    new_args.push(a.clone());
                }
            }
            let new_result = if res_dt {
                let Some(v) = map_dt(result) else {
                    return DtUfTableRewrite::Drop;
                };
                v
            } else {
                result.clone()
            };
            match seen.get(&new_args) {
                None => {
                    seen.insert(new_args.clone(), new_result.clone());
                    out.push((new_args, new_result));
                }
                // Two element-level points that render to the SAME key: a
                // duplicate with an agreeing result is dropped; a diverging
                // result means the rendered table is not a function graph.
                Some(prev) if *prev == new_result => {}
                Some(_) => return DtUfTableRewrite::Drop,
            }
        }
        DtUfTableRewrite::Rewritten(out)
    }

    /// Memoized assignment for the current model (`None` when underivable).
    fn dt_egraph_assignment_cached(&self, model: &Model) -> Option<Arc<DtEgraphAssignment>> {
        if let Some(asg) = self.dt_egraph_assignment.borrow().as_ref() {
            return Some(asg.clone());
        }
        let dtm = match self.dt_theory_model.as_ref() {
            Some(dtm) => dtm.clone(),
            None => self.synthesize_dt_model_from_euf(model)?,
        };
        // Build with the reentrancy latch set so nested evaluation cannot
        // re-enter the builder.
        self.dt_egraph_building.set(true);
        let built = Arc::new(self.build_dt_egraph_assignment(model, dtm));
        self.dt_egraph_building.set(false);
        *self.dt_egraph_assignment.borrow_mut() = Some(built.clone());
        Some(built)
    }

    /// Whether the EUF-model synthesis applies: datatypes declared, an EUF
    /// model present, and NO array sort anywhere in the term store — the
    /// datatype-carrying-array emission is owned by the independent gate's
    /// entailed reconstruction (`gate_emit_reconstructions`), which this
    /// single-source path must not displace.
    fn dt_egraph_synth_applicable(&self, model: &Model) -> bool {
        if model.euf_model.is_none() || self.ctx.datatype_iter().next().is_none() {
            return false;
        }
        // Selector-free (all-nullary enum) problems have nothing for the
        // single-source assignment to fix — no selector totalizations exist —
        // and the eager enum-SAT lane that usually solves them produces a
        // model whose SAT-atom bookkeeping this synthesis must not
        // reinterpret (observed: Bouvier vlsat3 constant collisions). The
        // legacy enum emission is already validated end-to-end; keep it.
        let has_selectors = self
            .ctx
            .ctor_selectors_iter()
            .any(|(_c, sels)| !sels.is_empty());
        if !has_selectors {
            return false;
        }
        for raw in 0..self.ctx.terms.len() {
            if matches!(self.ctx.terms.sort(TermId(raw as u32)), Sort::Array(_)) {
                return false;
            }
        }
        true
    }

    /// Synthesize a [`ay_dt::DtModel`] from the EUF model's equivalence
    /// classes plus the SAT assignment of the tester/equality atoms — the
    /// eager combined lanes (e.g. `solve_dt_ax`) prove datatype facts through
    /// the instantiated axioms over EUF, so this carries the same committed
    /// structure the interactive `DtSolver` would have exported.
    fn synthesize_dt_model_from_euf(&self, model: &Model) -> Option<ay_dt::DtModel> {
        if !self.dt_egraph_synth_applicable(model) {
            return None;
        }
        let euf = model.euf_model.as_ref()?;
        let mut dtm = ay_dt::DtModel::default();

        // Class representatives: smallest TermId per EUF element, over
        // datatype-sorted terms (TermId-ascending scan = deterministic).
        let mut elem_rep: HashMap<&str, TermId> = HashMap::default();
        let asserted: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();
        for raw in 0..self.ctx.terms.len() {
            let tid = TermId(raw as u32);
            if self.datatype_sort_name(self.ctx.terms.sort(tid)).is_none() {
                continue;
            }
            if let Some(elem) = euf.term_values.get(&tid) {
                let rep = *elem_rep.entry(elem.as_str()).or_insert(tid);
                dtm.rep_of.insert(tid, rep);
            }
        }

        for raw in 0..self.ctx.terms.len() {
            let tid = TermId(raw as u32);
            match self.ctx.terms.get(tid) {
                // Constructor applications (incl. nullary constructor Vars).
                TermData::App(sym, args) => {
                    if let Some((_dt, ctor)) = self.ctx.is_constructor(sym.name()) {
                        dtm.ctor_app_of
                            .entry(dtm.rep(tid))
                            .or_insert_with(|| (ctor, args.clone()));
                        continue;
                    }
                    // Tester atoms `(is-C x)`: truth from assertion / SAT model.
                    if args.len() == 1 {
                        if let Some(ctor) = sym.name().strip_prefix("is-") {
                            if self.ctx.is_constructor(ctor).is_some() {
                                let value = if asserted.contains(&tid) {
                                    Some(true)
                                } else {
                                    self.term_value(&model.sat_model, &model.term_to_var, tid)
                                };
                                let rep = dtm.rep(args[0]);
                                match value {
                                    Some(true) => {
                                        dtm.pos_tester_of
                                            .entry(rep)
                                            .or_insert_with(|| ctor.to_string());
                                    }
                                    Some(false) => {
                                        let ruled = dtm.neg_testers_of.entry(rep).or_default();
                                        if !ruled.iter().any(|c| c == ctor) {
                                            ruled.push(ctor.to_string());
                                        }
                                    }
                                    None => {}
                                }
                            }
                            continue;
                        }
                    }
                    // Disequalities: `(= a b)` atoms ENCODED THIS SOLVE and
                    // assigned false, plus `(distinct ...)` atoms assigned
                    // true, over datatype-sorted operands. The
                    // `term_to_var` filter keeps stale popped-scope atoms out.
                    let is_eq = sym.name() == "=" && args.len() == 2;
                    let is_distinct = sym.name() == "distinct" && args.len() >= 2;
                    if (is_eq || is_distinct)
                        && self
                            .datatype_sort_name(self.ctx.terms.sort(args[0]))
                            .is_some()
                        && model.term_to_var.contains_key(&tid)
                    {
                        match self.term_value(&model.sat_model, &model.term_to_var, tid) {
                            Some(false) if is_eq => dtm.diseqs.push((args[0], args[1])),
                            Some(true) if is_distinct => {
                                for i in 0..args.len() {
                                    for j in (i + 1)..args.len() {
                                        dtm.diseqs.push((args[i], args[j]));
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }
                TermData::Var(name, _) => {
                    if let Some((_dt, ctor)) = self.ctx.is_constructor(name) {
                        dtm.ctor_app_of
                            .entry(dtm.rep(tid))
                            .or_insert_with(|| (ctor, Vec::new()));
                    }
                }
                _ => {}
            }
        }
        Some(dtm)
    }

    /// Structural resolution for terms outside the built assignment (fresh
    /// `(get-value)` composites): constructor literals render over resolved
    /// arguments; a selector application on a class whose rendered constructor
    /// OWNS the selector projects the rendered field. Anything else is `None`
    /// (legacy fallback) — never a fabricated default here.
    fn dt_egraph_structural_value(
        &self,
        model: &Model,
        asg: &DtEgraphAssignment,
        term: TermId,
        depth: u32,
    ) -> Option<String> {
        if depth == 0 {
            return None;
        }
        match self.ctx.terms.get(term) {
            TermData::Var(name, _) => {
                // A nullary constructor constant is its own value.
                self.ctx
                    .is_constructor(name)
                    .map(|(_dt, ctor)| self.dt_surface(&ctor).to_string())
            }
            TermData::App(sym, args) => {
                if let Some((_dt, ctor)) = self.ctx.is_constructor(sym.name()) {
                    let mut parts = Vec::with_capacity(args.len());
                    for &arg in args {
                        let sort = self.ctx.terms.sort(arg).clone();
                        let part = if self.datatype_sort_name(&sort).is_some() {
                            let rep = asg.dtm.rep(arg);
                            if let Some(v) = asg.class_value.get(&rep) {
                                Some(v.clone())
                            } else if asg.poisoned.contains(&rep) {
                                None
                            } else {
                                self.dt_egraph_structural_value(model, asg, arg, depth - 1)
                            }
                        } else {
                            self.dt_egraph_scalar_part(model, arg, &sort)
                        };
                        parts.push(part?);
                    }
                    return Some(render_ctor(self.dt_surface(&ctor), &parts));
                }
                // Selector application on a right-constructor class: project.
                if args.len() == 1 {
                    let sel = sym.name();
                    let arg_rep = asg.dtm.rep(args[0]);
                    let cls_ctor = asg.class_ctor.get(&arg_rep)?;
                    let idx = self
                        .ctx
                        .constructor_selectors(cls_ctor)?
                        .iter()
                        .position(|s| s == sel)?;
                    return asg.class_fields.get(&arg_rep)?.get(idx).cloned();
                }
                None
            }
            _ => None,
        }
    }

    /// Rendered value of a NON-datatype field term: committed theory-model
    /// value first, then assertion-derived bounds, then the canonical default
    /// (a completion of genuinely free scalar slack — same policy as the
    /// legacy field materialization).
    fn dt_egraph_scalar_part(&self, model: &Model, term: TermId, sort: &Sort) -> Option<String> {
        // Pins-free read: the single-source assignment must not inherit the
        // total-construction engine's fabricated free-slack defaults
        // (#mv-dt-single-source; see `lookup_term_value_no_dt_pins`).
        let mut val = self.lookup_term_value_no_dt_pins(model, term);
        if matches!(val, EvalValue::Unknown) {
            match sort {
                Sort::Int => {
                    if let Some(v) = self.extract_int_from_assertion_bounds(term) {
                        val = EvalValue::Rational(num_rational::BigRational::from(v));
                    }
                }
                Sort::Real => {
                    if let Some(v) = self.extract_real_from_assertion_bounds(term) {
                        val = EvalValue::Rational(v);
                    }
                }
                _ => {}
            }
        }
        if matches!(val, EvalValue::Unknown) {
            return Some(self.canonical_default_value(sort));
        }
        Some(self.format_eval_value(&val, term))
    }

    /// Build the per-class assignment (see module docs for the algorithm).
    fn build_dt_egraph_assignment(&self, model: &Model, dtm: ay_dt::DtModel) -> DtEgraphAssignment {
        // ---- static indices (shared by every repair round) ----

        // All selector names, for the selector-application index.
        let mut sel_names: HashSet<&str> = HashSet::default();
        for (_ctor, sels) in self.ctx.ctor_selectors_iter() {
            for s in sels {
                sel_names.insert(s.as_str());
            }
        }

        // Datatype-sorted classes (rep -> datatype name), the selector
        // application index ((rep, sel) -> smallest application term), and the
        // deterministic build order.
        let mut class_sort: HashMap<TermId, String> = HashMap::default();
        let mut sel_apps: HashMap<(TermId, String), TermId> = HashMap::default();
        let mut reps_ordered: Vec<TermId> = Vec::new();
        for raw in 0..self.ctx.terms.len() {
            let tid = TermId(raw as u32);
            let sort = self.ctx.terms.sort(tid);
            if let Some(dt_name) = self.datatype_sort_name(sort) {
                let rep = dtm.rep(tid);
                if !class_sort.contains_key(&rep) {
                    class_sort.insert(rep, dt_name);
                    reps_ordered.push(rep);
                }
            }
            if let TermData::App(sym, args) = self.ctx.terms.get(tid) {
                if args.len() == 1 && sel_names.contains(sym.name()) {
                    sel_apps
                        .entry((dtm.rep(args[0]), sym.name().to_string()))
                        .or_insert(tid);
                }
            }
        }
        // Deterministic congruence-scan order: by (selector, application id).
        let mut sel_apps_ordered: Vec<((TermId, String), TermId)> = sel_apps
            .iter()
            .map(|((rep, sel), &app)| ((*rep, sel.clone()), app))
            .collect();
        sel_apps_ordered.sort_by(|a, b| (&a.0 .1, a.1 .0).cmp(&(&b.0 .1, b.1 .0)));

        // Per-class constructor commitment.
        let mut commits: HashMap<TermId, CtorCommit> = HashMap::default();
        let mut ruled_out: HashMap<TermId, Vec<String>> = HashMap::default();
        let mut poisoned: HashSet<TermId> = HashSet::default();
        for &rep in &reps_ordered {
            let commit = if let Some((ctor, args)) = dtm.ctor_app_of.get(&rep) {
                // Defensive: a positive tester disagreeing with the committed
                // application would mean an inconsistent accepted assignment —
                // never value such a class.
                if dtm.pos_tester_of.get(&rep).is_some_and(|t| t != ctor) {
                    poisoned.insert(rep);
                    continue;
                }
                CtorCommit::App(ctor.clone(), args.clone())
            } else if let Some(ctor) = dtm.pos_tester_of.get(&rep) {
                CtorCommit::Tester(ctor.clone())
            } else if let Some(ruled) = dtm.neg_testers_of.get(&rep) {
                ruled_out.insert(rep, ruled.clone());
                let dt_name = &class_sort[&rep];
                let remaining: Vec<&String> = self
                    .ctx
                    .datatype_iter()
                    .find(|(n, _)| n == dt_name)
                    .map(|(_, cs)| cs.iter().filter(|c| !ruled.contains(c)).collect())
                    .unwrap_or_default();
                if remaining.len() == 1 {
                    CtorCommit::Tester(remaining[0].clone())
                } else {
                    CtorCommit::Free
                }
            } else {
                CtorCommit::Free
            };
            commits.insert(rep, commit);
        }

        // ---- iterative build + congruence/disequality reconciliation ----

        let (memo, fields_memo, ctor_memo, poisoned) = {
            let mut builder = AsgBuilder {
                exec: self,
                model,
                dtm: &dtm,
                class_sort: &class_sort,
                commits: &commits,
                ruled_out: &ruled_out,
                sel_apps: &sel_apps,
                memo: HashMap::default(),
                fields_memo: HashMap::default(),
                ctor_memo: HashMap::default(),
                in_progress: HashSet::default(),
                used_by_sort: HashMap::default(),
                avoid: HashMap::default(),
                pins: HashMap::default(),
                pin_source: HashMap::default(),
                sticky: HashMap::default(),
                separation_attempts: HashMap::default(),
                demoted: HashSet::default(),
                poisoned,
            };

            let mut round = 0u32;
            loop {
                builder.reset_round();
                for &rep in &reps_ordered {
                    let _ = builder.class_value(rep, DT_VALUE_DEPTH);
                }
                let final_round = round >= DT_REPAIR_ROUNDS;
                let mut changed = false;
                changed |= builder.reconcile_congruence(&sel_apps_ordered, final_round);
                changed |= builder.reconcile_diseqs(final_round);
                if !changed {
                    break;
                }
                if final_round {
                    // Poisons were applied; one last rebuild propagates them.
                    builder.reset_round();
                    for &rep in &reps_ordered {
                        let _ = builder.class_value(rep, DT_VALUE_DEPTH);
                    }
                    break;
                }
                round += 1;
            }

            if !builder.poisoned.is_empty() {
                tracing::warn!(
                    poisoned = builder.poisoned.len(),
                    "dt-egraph assignment: some classes could not be coherently \
                 valued; their consumers fail closed (#mv-dt-single-source)"
                );
                if std::env::var_os("AY_PHASE_TRACE").is_some() {
                    let mut reps: Vec<u32> = builder.poisoned.iter().map(|t| t.0).collect();
                    reps.sort_unstable();
                    eprintln!("c phase-trace dt-egraph-poisoned reps={reps:?}");
                }
            }

            (
                builder.memo,
                builder.fields_memo,
                builder.ctor_memo,
                builder.poisoned,
            )
        };

        let mut class_value = HashMap::default();
        for (rep, v) in &memo {
            if let Some(v) = v {
                class_value.insert(*rep, v.clone());
            }
        }
        let mut assignment = DtEgraphAssignment {
            dtm,
            class_value,
            class_fields: fields_memo,
            class_ctor: ctor_memo,
            poisoned,
            diseq_incoherent: HashSet::default(),
            self_check_ok: false,
        };
        assignment.self_check_ok = self.dt_egraph_self_check(model, &assignment);
        if !assignment.self_check_ok {
            tracing::warn!(
                "dt-egraph assignment failed the structural self-check; total \
                 selector definitions withheld (#mv-dt-single-source)"
            );
            if std::env::var_os("AY_PHASE_TRACE").is_some() {
                eprintln!("c phase-trace dt-egraph-self-check failed");
            }
            // The totalizations are withheld (see the totalization scan), but
            // CONSTANTS still print from this assignment. Close the remaining
            // constant-vs-constant channel: any class pair still violating an
            // asserted disequality is poisoned so those constants fall back
            // to the legacy emission instead of printing a known collision.
            let diseqs = assignment.dtm.diseqs.clone();
            for (lhs, rhs) in diseqs {
                if self.datatype_sort_name(self.ctx.terms.sort(lhs)).is_none() {
                    continue;
                }
                let (rl, rr) = (assignment.dtm.rep(lhs), assignment.dtm.rep(rhs));
                let collided = rl == rr
                    || match (
                        assignment.class_value.get(&rl),
                        assignment.class_value.get(&rr),
                    ) {
                        (Some(a), Some(b)) => a == b,
                        _ => false,
                    };
                if collided {
                    assignment.class_value.remove(&rl);
                    assignment.class_value.remove(&rr);
                    assignment.poisoned.insert(rl);
                    assignment.poisoned.insert(rr);
                    // The check PROVED these classes' printed values violate
                    // an asserted disequality: mark them so the constant
                    // emission omits them outright instead of delegating to
                    // the legacy emitter, which re-derives the same collision
                    // (stage-4 review F2).
                    assignment.diseq_incoherent.insert(rl);
                    assignment.diseq_incoherent.insert(rr);
                }
            }
        }
        assignment
    }

    /// Re-evaluate every assertion against the finished assignment, with all
    /// datatype boundary subterms pinned to the assignment's rendered values —
    /// i.e. evaluate the assertions the way the model VALIDATOR will evaluate
    /// the printed model (structural constructor semantics, class values for
    /// selector applications and datatype leaves). True only when every
    /// assertion is definitively true.
    ///
    /// This is what makes the tester DEMOTIONS in the builder safe: a
    /// demotion can only flip a DON'T-CARE tester atom. If the atom was
    /// load-bearing, some assertion now evaluates false (or unresolvable)
    /// here, and the caller withholds the totalizations (fail-closed partial,
    /// never a wrong printed model).
    fn dt_egraph_self_check(&self, model: &Model, asg: &DtEgraphAssignment) -> bool {
        let mut overrides: HashMap<TermId, EvalValue> = HashMap::default();
        let mut memo: HashMap<TermId, Option<String>> = HashMap::default();
        let assertions = self.ctx.assertions.clone();
        for &assertion in &assertions {
            if !self.collect_asg_overrides(model, asg, assertion, 4096, &mut overrides, &mut memo) {
                return false;
            }
        }
        let _guard = super::dt_model::OverrideGuard::install(overrides);
        for &assertion in &assertions {
            if !matches!(self.evaluate_term(model, assertion), EvalValue::Bool(true)) {
                if std::env::var_os("AY_PHASE_TRACE").is_some() {
                    eprintln!(
                        "c phase-trace dt-egraph-self-check-fail assertion={}",
                        assertion.0
                    );
                }
                return false;
            }
        }
        true
    }

    /// The value the model VALIDATOR will compute for a datatype-sorted term
    /// under the printed model: constructor applications render structurally
    /// over their arguments' values; everything else (constants, selector
    /// applications, UF applications) reads the printed/committed class value.
    fn asg_structural_value(
        &self,
        model: &Model,
        asg: &DtEgraphAssignment,
        term: TermId,
        depth: u32,
        memo: &mut HashMap<TermId, Option<String>>,
    ) -> Option<String> {
        if let Some(v) = memo.get(&term) {
            return v.clone();
        }
        if depth == 0 {
            return None;
        }
        let out = (|| {
            if let TermData::App(sym, args) = self.ctx.terms.get(term) {
                if let Some((_dt, ctor)) = self.ctx.is_constructor(sym.name()) {
                    let mut parts = Vec::with_capacity(args.len());
                    for &arg in args {
                        let sort = self.ctx.terms.sort(arg).clone();
                        let part = if self.datatype_sort_name(&sort).is_some() {
                            self.asg_structural_value(model, asg, arg, depth - 1, memo)
                        } else {
                            self.dt_egraph_scalar_part(model, arg, &sort)
                        };
                        parts.push(part?);
                    }
                    return Some(render_ctor(self.dt_surface(&ctor), &parts));
                }
                // Right-constructor selector application: the validator
                // computes it STRUCTURALLY — the matching field of the
                // argument's printed value — so the printed class value of
                // the application must AGREE with that field, and the
                // self-check must re-verify the agreement rather than assume
                // it (#dt-egraph-owner-recheck). Pre-provenance, the
                // assumption was enforced by the final round poisoning every
                // still-moving pin; with same-source pin updates accepted on
                // the final round, a last-reconcile update could in theory
                // leave a sibling owner point on the same application class
                // (or a downstream owner field) stale after the closing
                // rebuild — invisible to a class_value read (both sides
                // share it) but visible to the validator. A disagreement
                // fails closed here (self-check false, totalizations
                // withheld); it is never repaired at check time.
                if args.len() == 1
                    && self
                        .datatype_sort_name(self.ctx.terms.sort(args[0]))
                        .is_some()
                {
                    let arg_rep = asg.dtm.rep(args[0]);
                    if let (Some(ctor), Some(fields)) =
                        (asg.class_ctor.get(&arg_rep), asg.class_fields.get(&arg_rep))
                    {
                        if let Some(idx) = self
                            .ctx
                            .constructor_selectors(ctor)
                            .and_then(|sels| sels.iter().position(|s| s.as_str() == sym.name()))
                        {
                            // Malformed parallel arrays fail closed via `?`.
                            let expected = fields.get(idx)?.clone();
                            let rep = asg.dtm.rep(term);
                            let got = asg.class_value.get(&rep)?;
                            if *got != expected {
                                if std::env::var_os("AY_PHASE_TRACE").is_some() {
                                    eprintln!(
                                        "c phase-trace dt-egraph-owner-stale app={} sel={} \
                                         arg_rep={} expected={expected} got={got}",
                                        term.0,
                                        sym.name(),
                                        arg_rep.0,
                                    );
                                }
                                return None;
                            }
                            return Some(expected);
                        }
                    }
                }
            }
            if let TermData::Var(name, _) = self.ctx.terms.get(term) {
                if let Some((_dt, ctor)) = self.ctx.is_constructor(name) {
                    return Some(self.dt_surface(&ctor).to_string());
                }
            }
            let rep = asg.dtm.rep(term);
            asg.class_value.get(&rep).cloned()
        })();
        memo.insert(term, out.clone());
        out
    }

    /// Walk an assertion, pinning every datatype boundary subterm (datatype
    /// leaves and applications, recognizers, datatype (dis)equalities) to the
    /// assignment's validator-visible value. Returns false when any needed
    /// value is unavailable (the self-check then fails closed).
    fn collect_asg_overrides(
        &self,
        model: &Model,
        asg: &DtEgraphAssignment,
        term: TermId,
        depth: u32,
        overrides: &mut HashMap<TermId, EvalValue>,
        memo: &mut HashMap<TermId, Option<String>>,
    ) -> bool {
        if depth == 0 {
            return false;
        }
        if overrides.contains_key(&term) {
            return true;
        }
        // Any datatype-sorted subterm pins to its validator-visible value.
        if self.datatype_sort_name(self.ctx.terms.sort(term)).is_some() {
            return match self.asg_structural_value(model, asg, term, depth, memo) {
                Some(v) => {
                    overrides.insert(term, EvalValue::Element(v));
                    true
                }
                None => false,
            };
        }
        match self.ctx.terms.get(term) {
            TermData::App(sym, args) => {
                // Recognizer `(is-C x)` over a datatype term.
                if args.len() == 1 {
                    if let Some(ctor) = sym.name().strip_prefix("is-") {
                        if self.ctx.is_constructor(ctor).is_some() {
                            let Some(v) =
                                self.asg_structural_value(model, asg, args[0], depth - 1, memo)
                            else {
                                return false;
                            };
                            let is_c = value_head(&v) == self.dt_surface(ctor);
                            overrides.insert(term, EvalValue::Bool(is_c));
                            return true;
                        }
                    }
                }
                // Datatype (dis)equality atoms.
                let dt_operands = !args.is_empty()
                    && self
                        .datatype_sort_name(self.ctx.terms.sort(args[0]))
                        .is_some();
                if dt_operands && matches!(sym.name(), "=" | "distinct") && args.len() >= 2 {
                    let mut vals = Vec::with_capacity(args.len());
                    for &arg in args {
                        let Some(v) = self.asg_structural_value(model, asg, arg, depth - 1, memo)
                        else {
                            return false;
                        };
                        vals.push(v);
                    }
                    let truth = if sym.name() == "=" {
                        vals.windows(2).all(|w| w[0] == w[1])
                    } else {
                        (0..vals.len()).all(|i| (i + 1..vals.len()).all(|j| vals[i] != vals[j]))
                    };
                    overrides.insert(term, EvalValue::Bool(truth));
                    return true;
                }
                args.iter()
                    .all(|&a| self.collect_asg_overrides(model, asg, a, depth - 1, overrides, memo))
            }
            TermData::Not(inner) => {
                self.collect_asg_overrides(model, asg, *inner, depth - 1, overrides, memo)
            }
            TermData::Ite(c, t, e) => {
                self.collect_asg_overrides(model, asg, *c, depth - 1, overrides, memo)
                    && self.collect_asg_overrides(model, asg, *t, depth - 1, overrides, memo)
                    && self.collect_asg_overrides(model, asg, *e, depth - 1, overrides, memo)
            }
            TermData::Let(bindings, body) => {
                bindings.iter().all(|(_, v)| {
                    self.collect_asg_overrides(model, asg, *v, depth - 1, overrides, memo)
                }) && self.collect_asg_overrides(model, asg, *body, depth - 1, overrides, memo)
            }
            _ => true,
        }
    }
}

/// Render a constructor value: nullary as the bare (surface) name, otherwise
/// `(name part…)` — matching the legacy printer's rendering so downstream
/// head-matching and Dolmen round-trips are unchanged.
fn render_ctor(surface: &str, parts: &[String]) -> String {
    if parts.is_empty() {
        surface.to_string()
    } else {
        format!("({} {})", surface, parts.join(" "))
    }
}

/// One build round's state over the static commitment indices.
struct AsgBuilder<'a> {
    exec: &'a Executor,
    model: &'a Model,
    dtm: &'a ay_dt::DtModel,
    class_sort: &'a HashMap<TermId, String>,
    commits: &'a HashMap<TermId, CtorCommit>,
    ruled_out: &'a HashMap<TermId, Vec<String>>,
    sel_apps: &'a HashMap<(TermId, String), TermId>,
    /// rep -> rendered value (`None` = poisoned this round).
    memo: HashMap<TermId, Option<String>>,
    fields_memo: HashMap<TermId, Vec<String>>,
    ctor_memo: HashMap<TermId, String>,
    in_progress: HashSet<TermId>,
    used_by_sort: HashMap<String, HashSet<String>>,
    /// Persistent across rounds: values each class must NOT take (repair).
    avoid: HashMap<TermId, HashSet<String>>,
    /// Persistent across rounds: exact values FREE classes must take
    /// (congruence pins). `bool` = pinned by a forced source (a committed
    /// class), which may not be overwritten.
    pins: HashMap<TermId, (String, bool)>,
    /// Persistent across rounds: the selector POINT each congruence pin came
    /// from — pinned class -> (argument class, selector name)
    /// (#dt-egraph-pin-provenance). Two uses: a re-pin arriving from the SAME
    /// point carries a rippled upstream value and UPDATES the pin (only pins
    /// from two DIFFERENT points genuinely conflict), and the disequality
    /// repair descends through an owner pin into the committed application's
    /// field class — the pinned value IS that class's rendered value, so
    /// separating the pinned side means re-choosing the field's slack.
    pin_source: HashMap<TermId, (TermId, String)>,
    /// Persistent across rounds: the (ctor, parts, value) a FREE unpinned
    /// class chose in an earlier round (#dt-egraph-sticky-free). Free choices
    /// must be STABLE: without this, every round re-runs the generator under
    /// a drifted `used_by_sort`/pin landscape, values shift, every owner pin
    /// downstream re-updates, the loop never reaches a fixpoint inside the
    /// round budget, and the final round poisons whatever was still moving
    /// (observed on typed_v3l30084: seven final-round pin poisons on
    /// assertion-boundary classes → self-check override collection fails →
    /// Sat withdrawn). A sticky value is dropped only when a repair
    /// explicitly rules it out (avoid entry) — re-choosing is the repair
    /// loop's job, not the renderer's.
    sticky: HashMap<TermId, (String, Vec<String>, String)>,
    /// Persistent across rounds: how many separation attempts each class
    /// pair has consumed (see [`DT_PAIR_SEPARATION_ATTEMPTS`]).
    separation_attempts: HashMap<(TermId, TermId), u32>,
    /// Persistent across rounds: tester-committed classes DEMOTED to free.
    /// A tester commitment reflects a SAT-model atom value that may be
    /// don't-care noise (the eager encoding only instantiates the shape
    /// axioms for covered terms), so on an unrepairable congruence conflict
    /// with a REAL structural commitment the tester side yields. The final
    /// structural self-check re-validates every assertion against the
    /// resulting assignment, so a genuinely load-bearing tester can never be
    /// silently falsified — the check fails closed instead.
    demoted: HashSet<TermId>,
    /// Persistent across rounds: classes that fail closed.
    poisoned: HashSet<TermId>,
}

impl AsgBuilder<'_> {
    fn reset_round(&mut self) {
        self.memo.clear();
        self.fields_memo.clear();
        self.ctor_memo.clear();
        self.in_progress.clear();
        self.used_by_sort.clear();
    }

    fn is_free(&self, rep: TermId) -> bool {
        self.demoted.contains(&rep)
            || matches!(self.commits.get(&rep), Some(CtorCommit::Free) | None)
    }

    /// The class's effective commitment (demotions apply).
    fn commit_of(&self, rep: TermId) -> CtorCommit {
        if self.demoted.contains(&rep) {
            return CtorCommit::Free;
        }
        self.commits.get(&rep).cloned().unwrap_or(CtorCommit::Free)
    }

    /// Memoized per-class value (None = poisoned).
    fn class_value(&mut self, rep: TermId, depth: u32) -> Option<String> {
        if self.poisoned.contains(&rep) {
            return None;
        }
        if let Some(v) = self.memo.get(&rep) {
            return v.clone();
        }
        if depth == 0 || !self.in_progress.insert(rep) {
            // Depth exhaustion or a structural cycle through the e-graph:
            // no finite value exists — fail closed.
            if std::env::var_os("AY_PHASE_TRACE").is_some() {
                eprintln!("c phase-trace dt-egraph-poison site=cycle rep={}", rep.0);
            }
            self.poisoned.insert(rep);
            self.memo.insert(rep, None);
            return None;
        }
        let out = stacker::maybe_grow(super::EVAL_STACK_RED_ZONE, super::EVAL_STACK_SIZE, || {
            self.class_value_inner(rep, depth)
        });
        self.in_progress.remove(&rep);
        if out.is_none() {
            self.poisoned.insert(rep);
        } else if let (Some(v), Some(sort)) = (&out, self.class_sort.get(&rep)) {
            self.used_by_sort
                .entry(sort.clone())
                .or_default()
                .insert(v.clone());
        }
        self.memo.insert(rep, out.clone());
        out
    }

    fn avoid_hit(&self, rep: TermId, v: &String) -> bool {
        self.avoid.get(&rep).is_some_and(|s| s.contains(v))
    }

    fn class_value_inner(&mut self, rep: TermId, depth: u32) -> Option<String> {
        match self.commit_of(rep) {
            CtorCommit::App(ctor, args) => {
                let mut parts = Vec::with_capacity(args.len());
                for &arg in &args {
                    parts.push(self.field_part(arg, depth - 1)?);
                }
                let v = render_ctor(self.exec.dt_surface(&ctor), &parts);
                if self.avoid_hit(rep, &v) {
                    // Fully committed value under an avoid constraint: the
                    // repair should have picked the other side; fail closed.
                    return None;
                }
                self.fields_memo.insert(rep, parts);
                self.ctor_memo.insert(rep, ctor);
                Some(v)
            }
            CtorCommit::Tester(ctor) => {
                let fields: Vec<(String, Sort)> = self
                    .exec
                    .ctx
                    .constructor_selector_info(&ctor)
                    .map(|fs| fs.to_vec())
                    .unwrap_or_default();
                let mut parts = Vec::with_capacity(fields.len());
                let mut free_dt_field: Option<(usize, String)> = None;
                for (idx, (sel, fsort)) in fields.iter().enumerate() {
                    if let Some(&app) = self.sel_apps.get(&(rep, sel.clone())) {
                        parts.push(self.field_part(app, depth - 1)?);
                    } else {
                        // Genuinely free field: canonical default; remember the
                        // first free datatype field as repair slack.
                        if free_dt_field.is_none() {
                            if let Some(fdt) = self.exec.datatype_sort_name(fsort) {
                                free_dt_field = Some((idx, fdt));
                            }
                        }
                        parts.push(self.exec.canonical_default_value(fsort));
                    }
                }
                let mut v = render_ctor(self.exec.dt_surface(&ctor), &parts);
                if self.avoid_hit(rep, &v) {
                    // Bump the free datatype field through generated values
                    // until the composed value clears the avoid set.
                    let (idx, fdt) = free_dt_field?;
                    let mut ok = false;
                    for k in 0..DT_FRESH_CANDIDATES {
                        let Some((_, _, cand)) = self.gen_value(&fdt, k, &[], depth - 1) else {
                            break;
                        };
                        parts[idx] = cand;
                        v = render_ctor(self.exec.dt_surface(&ctor), &parts);
                        if !self.avoid_hit(rep, &v) {
                            ok = true;
                            break;
                        }
                    }
                    if !ok {
                        return None;
                    }
                }
                self.fields_memo.insert(rep, parts);
                self.ctor_memo.insert(rep, ctor);
                Some(v)
            }
            CtorCommit::Free => {
                // A congruence pin fixes the value exactly (it is another
                // class's committed value for the same selector point).
                if let Some((pinned, _)) = self.pins.get(&rep).cloned() {
                    if self.avoid_hit(rep, &pinned) {
                        return None;
                    }
                    if let Some(ruled) = self.ruled_out.get(&rep) {
                        let head = value_head(&pinned);
                        if ruled.iter().any(|c| self.exec.dt_surface(c) == head) {
                            return None;
                        }
                    }
                    if let Some(ctor) = self.ctor_from_head(&pinned) {
                        // Field view of the pinned value
                        // (#dt-egraph-pinned-fields): the validator computes a
                        // selector on this class STRUCTURALLY (the matching
                        // field of the rendered value), so the owner rule and
                        // the self-check's owner recheck must see the pinned
                        // value's fields exactly like a rendered one's —
                        // without this, a selector application on a pinned
                        // constructor-headed class fell to the wrong-ctor
                        // canonicalization table (validator-unfaithful) and
                        // the owner recheck was blind to the projection.
                        if let Some(parts) = split_value_parts(&pinned) {
                            if self
                                .exec
                                .ctx
                                .constructor_selectors(&ctor)
                                .is_some_and(|sels| sels.len() == parts.len())
                            {
                                self.fields_memo.insert(rep, parts);
                            }
                        }
                        self.ctor_memo.insert(rep, ctor);
                    }
                    return Some(pinned);
                }
                // Sticky re-render (#dt-egraph-sticky-free): keep the value
                // chosen in an earlier round unless a repair has since ruled
                // it out — free choices must be stable for the repair loop to
                // reach a fixpoint (see the field docs).
                if let Some((ctor, parts, v)) = self.sticky.get(&rep).cloned() {
                    if !self.avoid_hit(rep, &v) {
                        self.fields_memo.insert(rep, parts);
                        self.ctor_memo.insert(rep, ctor);
                        return Some(v);
                    }
                    self.sticky.remove(&rep);
                }
                let sort = self.class_sort.get(&rep)?.clone();
                let ruled: Vec<String> = self.ruled_out.get(&rep).cloned().unwrap_or_default();
                // Tier 1 prefers values no other same-sort class uses (so
                // asserted-disequal free classes separate without repair);
                // tier 2 only honors this class's explicit avoid set (finite
                // sorts may have to share).
                for tier in 0..2 {
                    for k in 0..DT_FRESH_CANDIDATES {
                        let Some((ctor, parts, v)) = self.gen_value(&sort, k, &ruled, depth) else {
                            break;
                        };
                        if self.avoid_hit(rep, &v) {
                            continue;
                        }
                        if tier == 0
                            && self
                                .used_by_sort
                                .get(&sort)
                                .is_some_and(|used| used.contains(&v))
                        {
                            continue;
                        }
                        self.sticky
                            .insert(rep, (ctor.clone(), parts.clone(), v.clone()));
                        self.fields_memo.insert(rep, parts);
                        self.ctor_memo.insert(rep, ctor);
                        return Some(v);
                    }
                }
                None
            }
        }
    }

    /// Constructor of the class's datatype whose surface name heads `value`.
    fn ctor_from_head(&self, value: &str) -> Option<String> {
        let head = value_head(value);
        self.exec.ctx.is_constructor(head).map(|(_dt, ctor)| ctor)
    }

    /// Rendered value of a constructor-argument / selector-application term:
    /// datatype-sorted through the class assignment, anything else as a scalar.
    fn field_part(&mut self, term: TermId, depth: u32) -> Option<String> {
        let sort = self.exec.ctx.terms.sort(term).clone();
        if self.exec.datatype_sort_name(&sort).is_some() {
            self.class_value(self.dtm.rep(term), depth)
        } else {
            self.exec.dt_egraph_scalar_part(self.model, term, &sort)
        }
    }

    /// The `k`-th generated value of datatype `sort_name`, top-level heads
    /// restricted away from `ruled_out`: nullary constructors first (in
    /// declaration order), then a recursive "pump" constructor wrapped around
    /// the `(k - #nullary)`-th generated value of its first datatype field
    /// (other fields canonical defaults). Injective in `k`, so distinct `k`
    /// give distinct values. `None` when the sort runs out of candidates (a
    /// finite enumeration) or nesting exhausts `depth`.
    fn gen_value(
        &self,
        sort_name: &str,
        k: u64,
        ruled_out: &[String],
        depth: u32,
    ) -> Option<(String, Vec<String>, String)> {
        if depth == 0 {
            return None;
        }
        let ctors: Vec<String> = self
            .exec
            .ctx
            .datatype_iter()
            .find(|(n, _)| *n == sort_name)
            .map(|(_, cs)| cs.to_vec())?;
        let allowed: Vec<&String> = ctors.iter().filter(|c| !ruled_out.contains(c)).collect();
        let nullary: Vec<&String> = allowed
            .iter()
            .copied()
            .filter(|c| {
                self.exec
                    .ctx
                    .constructor_selector_info(c)
                    .is_none_or(|fs| fs.is_empty())
            })
            .collect();
        if (k as usize) < nullary.len() {
            let ctor = nullary[k as usize].clone();
            let v = self.exec.dt_surface(&ctor).to_string();
            return Some((ctor, Vec::new(), v));
        }
        let j = k - nullary.len() as u64;
        // First allowed constructor with a datatype-sorted field is the pump.
        let dt_pump = allowed.iter().find_map(|c| {
            let fs = self.exec.ctx.constructor_selector_info(c)?;
            fs.iter()
                .any(|(_, fsort)| self.exec.datatype_sort_name(fsort).is_some())
                .then(|| ((*c).clone(), fs.to_vec()))
        });
        let Some((pump, fields)) = dt_pump else {
            // No datatype-sorted field to pump: enumerate the first BOOL
            // field instead (`j` = 0 -> true, 1 -> false; injective, then
            // exhausted). Without this, a FINITE datatype built over scalars
            // — `(Opt Bool)`: onone / (osome true) / (osome false) — offers
            // only `#nullary + 1` generated values, so distinct-but-free
            // classes of such sorts (and of sorts nesting them, e.g.
            // `(Opt (Opt Bool))` with 4 inhabitants) can never separate and
            // the whole assignment fails closed (#mv-dt-single-source).
            let (pump, fields) = allowed.iter().find_map(|c| {
                let fs = self.exec.ctx.constructor_selector_info(c)?;
                fs.iter()
                    .any(|(_, fsort)| matches!(fsort, Sort::Bool))
                    .then(|| ((*c).clone(), fs.to_vec()))
            })?;
            if j > 1 {
                return None;
            }
            let bool_idx = fields
                .iter()
                .position(|(_, fsort)| matches!(fsort, Sort::Bool))?;
            let mut parts: Vec<String> = fields
                .iter()
                .map(|(_, fsort)| self.exec.canonical_default_value(fsort))
                .collect();
            parts[bool_idx] = if j == 0 { "true" } else { "false" }.to_string();
            let v = render_ctor(self.exec.dt_surface(&pump), &parts);
            return Some((pump, parts, v));
        };
        let dt_idx = fields
            .iter()
            .position(|(_, fsort)| self.exec.datatype_sort_name(fsort).is_some())?;
        let nested_sort = self.exec.datatype_sort_name(&fields[dt_idx].1)?;
        let mut parts: Vec<String> = fields
            .iter()
            .map(|(_, fsort)| self.exec.canonical_default_value(fsort))
            .collect();
        let (_, _, nested) = self.gen_value(&nested_sort, j, &[], depth - 1)?;
        parts[dt_idx] = nested;
        let v = render_ctor(self.exec.dt_surface(&pump), &parts);
        Some((pump, parts, v))
    }

    /// Selector congruence over RENDERED values: two selector applications
    /// whose arguments render equal must render equal themselves, and an
    /// application on a right-constructor argument must render the argument's
    /// field (that is how the validator will evaluate it). Free application
    /// classes are pinned to the committed value; forced-vs-forced conflicts
    /// are left for the totalization scan to drop fail-closed (wrong-ctor) or
    /// poisoned (right-ctor, where the printed argument value itself would
    /// mislead the validator). Returns whether anything changed.
    fn reconcile_congruence(
        &mut self,
        sel_apps_ordered: &[((TermId, String), TermId)],
        final_round: bool,
    ) -> bool {
        let mut changed = false;
        // (sel, rendered arg value) ->
        //     (canonical value, forced, source app rep, source ARG rep)
        let mut table: HashMap<(String, String), (String, bool, TermId, TermId)> =
            HashMap::default();
        for ((arg_rep, sel), app) in sel_apps_ordered {
            let Some(Some(arg_val)) = self.memo.get(arg_rep).cloned() else {
                continue;
            };
            // Only datatype-RETURNING selector applications participate: the
            // assignment does not own scalar values (they come from the
            // theory models and agree per term already).
            if self
                .exec
                .datatype_sort_name(self.exec.ctx.terms.sort(*app))
                .is_none()
            {
                continue;
            }
            let app_rep = self.dtm.rep(*app);
            let Some(Some(app_val)) = self.memo.get(&app_rep).cloned() else {
                continue;
            };
            // Right-constructor application: must equal the rendered field.
            let owner_expected: Option<String> = self.ctor_memo.get(arg_rep).and_then(|ctor| {
                let idx = self
                    .exec
                    .ctx
                    .constructor_selectors(ctor)?
                    .iter()
                    .position(|s| s == sel)?;
                self.fields_memo.get(arg_rep)?.get(idx).cloned()
            });
            if let Some(expected) = owner_expected {
                if app_val != expected {
                    changed |= self.pin_or_poison(
                        app_rep,
                        expected,
                        true,
                        final_round,
                        // On a forced-vs-forced right-ctor mismatch the ARG's
                        // printed value also misleads the validator.
                        Some(*arg_rep),
                        (*arg_rep, sel.clone()),
                    );
                }
                continue;
            }
            // Wrong-constructor application: one value per (sel, arg value).
            // FORCED means committed by a constructor-application merge (or an
            // already-forced pin) — those reflect asserted structural
            // equalities. A tester-only commitment is SOFT: the tester atom's
            // SAT value can be don't-care noise, so `pin_or_poison` demotes it
            // to free and pins it (the final structural self-check catches any
            // load-bearing tester this flips).
            let key = (sel.clone(), arg_val.clone());
            let app_forced = matches!(self.commit_of(app_rep), CtorCommit::App(..))
                || self.pins.get(&app_rep).is_some_and(|(_, forced)| *forced);
            match table.get(&key) {
                None => {
                    table.insert(key, (app_val, app_forced, app_rep, *arg_rep));
                }
                Some((canon, canon_forced, canon_app_rep, canon_arg_rep)) => {
                    if *canon == app_val {
                        continue;
                    }
                    let (canon, canon_forced, canon_app_rep, canon_arg_rep) =
                        (canon.clone(), *canon_forced, *canon_app_rep, *canon_arg_rep);
                    if !app_forced {
                        changed |= self.pin_or_poison(
                            app_rep,
                            canon,
                            canon_forced,
                            final_round,
                            None,
                            (*arg_rep, sel.clone()),
                        );
                    } else if !canon_forced {
                        changed |= self.pin_or_poison(
                            canon_app_rep,
                            app_val.clone(),
                            true,
                            final_round,
                            None,
                            (canon_arg_rep, sel.clone()),
                        );
                        table.insert(key, (app_val, true, app_rep, *arg_rep));
                    } else {
                        // Forced-vs-forced application values: the two
                        // committed applications only clash because their
                        // (distinct) ARGUMENT classes rendered the same value.
                        // Separate the arguments through a slack side instead
                        // of dropping the selector; unrepairable conflicts are
                        // left for the totalization scan to drop fail-closed.
                        if !final_round
                            && canon_arg_rep != *arg_rep
                            && self.separation_budget_ok(canon_arg_rep, *arg_rep)
                        {
                            if let Some((side, avoid_val)) =
                                self.find_separation_slack(canon_arg_rep, *arg_rep, 16)
                            {
                                changed |= self.avoid.entry(side).or_default().insert(avoid_val);
                                continue;
                            }
                        }
                        // Stale same-point pin (#dt-egraph-stale-point-repin):
                        // a "forced" side whose forcedness comes ONLY from a
                        // congruence/owner pin recorded at THIS very selector
                        // point is not a structural commitment — it carries a
                        // value from an earlier round (the argument's rendered
                        // constructor changed underneath it, e.g. a wrong-ctor
                        // chain like `(cdr (cdr null))` settling to `null`
                        // after first rendering as a `cons`, or the canon
                        // value rippled). Same-point re-pins update in place
                        // by provenance (#dt-egraph-pin-provenance), so adopt
                        // the other side's value instead of leaving the clash
                        // for the totalization scan to drop. Only taken when
                        // the pin update is admissible (free class, not
                        // avoid-ruled, not tester-ruled-out) — anything else
                        // keeps today's fail-closed stuck path.
                        let pin_only_from = |b: &Self, rep: TermId, point: &(TermId, String)| {
                            !matches!(b.commit_of(rep), CtorCommit::App(..))
                                && b.pins.get(&rep).is_some_and(|(_, forced)| *forced)
                                && b.pin_source.get(&rep) == Some(point)
                        };
                        let repin_ok = |b: &Self, rep: TermId, val: &String| {
                            b.is_free(rep)
                                && !b.avoid_hit(rep, val)
                                && !b.ruled_out.get(&rep).is_some_and(|ruled| {
                                    let head = value_head(val);
                                    ruled.iter().any(|c| b.exec.dt_surface(c) == head)
                                })
                        };
                        let app_point = (*arg_rep, sel.clone());
                        if pin_only_from(self, app_rep, &app_point)
                            && repin_ok(self, app_rep, &canon)
                        {
                            if std::env::var_os("AY_PHASE_TRACE").is_some() {
                                eprintln!(
                                    "c phase-trace dt-egraph-stale-repin sel={sel} rep={} \
                                     new={canon}",
                                    app_rep.0
                                );
                            }
                            self.pins.insert(app_rep, (canon, true));
                            changed = true;
                            continue;
                        }
                        let canon_point = (canon_arg_rep, sel.clone());
                        if pin_only_from(self, canon_app_rep, &canon_point)
                            && repin_ok(self, canon_app_rep, &app_val)
                        {
                            if std::env::var_os("AY_PHASE_TRACE").is_some() {
                                eprintln!(
                                    "c phase-trace dt-egraph-stale-repin sel={sel} rep={} \
                                     new={app_val}",
                                    canon_app_rep.0
                                );
                            }
                            self.pins.insert(canon_app_rep, (app_val.clone(), true));
                            table.insert(key, (app_val, true, app_rep, *arg_rep));
                            changed = true;
                            continue;
                        }
                        {
                            if std::env::var_os("AY_PHASE_TRACE").is_some() {
                                let describe = |b: &Self, rep: TermId| match b.commits.get(&rep) {
                                    Some(CtorCommit::App(c, _)) => format!("App({c})"),
                                    Some(CtorCommit::Tester(c)) => format!("Tester({c})"),
                                    Some(CtorCommit::Free) => "Free".to_string(),
                                    None => "Untracked".to_string(),
                                };
                                eprintln!(
                                    "c phase-trace dt-egraph-cong-stuck sel={sel} key={} \
                                     args=({}:{} vs {}:{}) apps=({}:{} vs {}:{})",
                                    key.1,
                                    canon_arg_rep.0,
                                    describe(self, canon_arg_rep),
                                    arg_rep.0,
                                    describe(self, *arg_rep),
                                    canon_app_rep.0,
                                    describe(self, canon_app_rep),
                                    app_rep.0,
                                    describe(self, app_rep),
                                );
                            }
                        }
                    }
                }
            }
        }
        changed
    }

    /// Pin a free class to `value` (or poison on the final round / when the
    /// class cannot take the pin). `extra_poison` is co-poisoned with the
    /// class when pinning is impossible. Returns whether state changed.
    fn pin_or_poison(
        &mut self,
        rep: TermId,
        value: String,
        forced: bool,
        final_round: bool,
        extra_poison: Option<TermId>,
        source: (TermId, String),
    ) -> bool {
        // A tester-committed class DEMOTES to free rather than failing: the
        // tester atom's SAT value can be don't-care noise, while the value we
        // are pinning comes from a real structural commitment. The final
        // structural self-check catches any load-bearing tester this flips.
        let mut changed_by_demote = false;
        if !final_round
            && !self.is_free(rep)
            && matches!(self.commits.get(&rep), Some(CtorCommit::Tester(_)))
        {
            changed_by_demote = self.demoted.insert(rep);
        }
        let pinnable = self.is_free(rep)
            && !self.avoid_hit(rep, &value)
            && !self.ruled_out.get(&rep).is_some_and(|ruled| {
                let head = value_head(&value);
                ruled.iter().any(|c| self.exec.dt_surface(c) == head)
            });
        if pinnable {
            match self.pins.get(&rep) {
                Some((existing, _)) if *existing == value => return changed_by_demote,
                Some((_, true)) if self.pin_source.get(&rep) != Some(&source) => {
                    // Forced pins from two DIFFERENT selector points:
                    // unrepairable. (A re-pin from the SAME point is not a
                    // conflict — it carries a rippled upstream value after a
                    // repair round re-chose slack feeding the point, and
                    // falls through to update the pin in place,
                    // #dt-egraph-pin-provenance.)
                    let mut changed = self.poisoned.insert(rep);
                    if let Some(extra) = extra_poison {
                        changed |= self.poisoned.insert(extra);
                    }
                    return changed || changed_by_demote;
                }
                _ => {
                    // A pin update is accepted on ANY round when it comes
                    // from the class's established source point — it is the
                    // coherent owner-derived value for that point, and the
                    // final rebuild re-renders with it (poisoning here used
                    // to guarantee failure whenever the value web was still
                    // settling on the last round; the structural self-check
                    // is the arbiter of the finished assignment, not the
                    // round budget, #dt-egraph-pin-provenance). A brand-NEW
                    // pin on the final round still fails closed below.
                    if !final_round || self.pin_source.get(&rep) == Some(&source) {
                        self.pins.insert(rep, (value, forced));
                        self.pin_source.insert(rep, source);
                        return true;
                    }
                }
            }
        }
        {
            if std::env::var_os("AY_PHASE_TRACE").is_some() {
                eprintln!(
                    "c phase-trace dt-egraph-poison site=pin rep={} value={value} \
                     final={final_round} free={} extra={:?}",
                    rep.0,
                    self.is_free(rep),
                    extra_poison.map(|t| t.0),
                );
            }
            let mut changed = self.poisoned.insert(rep);
            if let Some(extra) = extra_poison {
                changed |= self.poisoned.insert(extra);
            }
            changed || changed_by_demote
        }
    }

    /// Separate asserted-disequal classes whose values collided (see module
    /// docs). Returns whether anything changed.
    fn reconcile_diseqs(&mut self, final_round: bool) -> bool {
        let mut changed = false;
        let diseqs: Vec<(TermId, TermId)> = self.dtm.diseqs.clone();
        for (lhs, rhs) in diseqs {
            if self
                .exec
                .datatype_sort_name(self.exec.ctx.terms.sort(lhs))
                .is_none()
            {
                continue;
            }
            let (rl, rr) = (self.dtm.rep(lhs), self.dtm.rep(rhs));
            if rl == rr {
                // An asserted disequality inside ONE class can never be
                // satisfied by any value choice. The false equality atom may
                // itself be don't-care SAT noise, so leave the values as they
                // are: the structural self-check fails (and the totalizations
                // are withheld) exactly when the atom was load-bearing.
                continue;
            }
            let (Some(vl), Some(vr)) = (
                self.memo.get(&rl).cloned().flatten(),
                self.memo.get(&rr).cloned().flatten(),
            ) else {
                continue;
            };
            if vl != vr {
                continue;
            }
            if !final_round && self.separation_budget_ok(rl, rr) {
                if let Some((side, avoid_val)) = self.find_separation_slack(rl, rr, 16) {
                    changed |= self.avoid.entry(side).or_default().insert(avoid_val);
                    continue;
                }
            }
            // No separation slack: leave the collision in place rather than
            // poisoning — the disequality atom may be don't-care noise, and
            // the structural self-check arbitrates (fail-closed when it was
            // load-bearing).
            if std::env::var_os("AY_PHASE_TRACE").is_some() {
                eprintln!(
                    "c phase-trace dt-egraph-diseq-unseparated lhs={} rhs={} rl={} rr={} val={vl}",
                    lhs.0, rhs.0, rl.0, rr.0
                );
            }
        }
        changed
    }

    /// Whether the (unordered) class pair still has separation budget; a
    /// call consumes one attempt (see [`DT_PAIR_SEPARATION_ATTEMPTS`]).
    fn separation_budget_ok(&mut self, a: TermId, b: TermId) -> bool {
        let key = if a.0 <= b.0 { (a, b) } else { (b, a) };
        let n = self.separation_attempts.entry(key).or_insert(0);
        if *n >= DT_PAIR_SEPARATION_ATTEMPTS {
            return false;
        }
        *n += 1;
        true
    }

    /// Find slack that can SEPARATE two distinct equal-valued classes: a
    /// directly re-choosable side first; otherwise, when both are committed
    /// applications of the same constructor, descend into the (necessarily
    /// equal-valued) field pairs — e.g. `(node A)` vs `(node B)` separates by
    /// re-choosing `A` away from `B`'s value. Returns the class to constrain
    /// and the value it must avoid.
    fn find_separation_slack(
        &mut self,
        rl: TermId,
        rr: TermId,
        depth: u32,
    ) -> Option<(TermId, String)> {
        if depth == 0 || rl == rr {
            return None;
        }
        if let Some(side) = self.pick_repair_side(rl, rr) {
            let avoid_val = self.memo.get(&side).cloned().flatten()?;
            return Some((side, avoid_val));
        }
        if let (CtorCommit::App(cl, args_l), CtorCommit::App(cr, args_r)) =
            (self.commit_of(rl), self.commit_of(rr))
        {
            if cl == cr && args_l.len() == args_r.len() {
                for (&al, &ar) in args_l.iter().zip(args_r.iter()) {
                    let sort = self.exec.ctx.terms.sort(al);
                    if self.exec.datatype_sort_name(sort).is_none() {
                        continue;
                    }
                    let (ra, rb) = (self.dtm.rep(al), self.dtm.rep(ar));
                    if let Some(found) = self.find_separation_slack(ra, rb, depth - 1) {
                        return Some(found);
                    }
                }
            }
        }
        // Pin-provenance descent (#dt-egraph-pin-provenance): a side whose
        // value comes from a FORCED owner pin is not directly re-choosable —
        // the validator computes `sel(arg)` as the rendered field of `arg`'s
        // committed constructor application, so the pinned value is DERIVED:
        // it IS the rendered value of that application's field-argument
        // class. Separating the pinned side therefore reduces to separating
        // the field class from the other side; the next congruence round
        // re-pins this class from the same point with the re-chosen value
        // (same-source pins update in place, never conflict).
        for (rep, other) in [(rl, rr), (rr, rl)] {
            if !(self.is_free(rep) && self.pins.contains_key(&rep)) {
                continue;
            }
            let Some((arg_rep, sel)) = self.pin_source.get(&rep).cloned() else {
                continue;
            };
            let CtorCommit::App(ctor, args) = self.commit_of(arg_rep) else {
                continue;
            };
            let Some(idx) = self
                .exec
                .ctx
                .constructor_selectors(&ctor)
                .and_then(|sels| sels.iter().position(|s| *s == sel))
            else {
                // A wrong-constructor (canonicalization) pin: no owner field
                // to descend into.
                continue;
            };
            let Some(&arg_term) = args.get(idx) else {
                continue;
            };
            let field_rep = self.dtm.rep(arg_term);
            if field_rep != rep && field_rep != other {
                if let Some(found) = self.find_separation_slack(field_rep, other, depth - 1) {
                    return Some(found);
                }
            }
        }
        // SOFT-pinned free class (#dt-egraph-softpin-rechoose, part of the
        // mv-rerun-20260718 Barrett recovery): a congruence pin with
        // `forced == false` is a CANONICALIZATION choice (the class was free
        // and simply adopted the first value seen for its selector point),
        // not a structural commitment — it is definitionally re-choosable.
        // Drop the pin and avoid the colliding value; the next repair round
        // re-renders the class through `gen_value` away from it, unsticking
        // selector-congruence clashes over deep wrong-constructor chains
        // where every other tier has no slack. Candidate-model only: the
        // structural self-check and the fail-closed validation battery still
        // arbitrate the final assignment.
        for rep in [rl, rr] {
            if self.is_free(rep) && self.pins.get(&rep).is_some_and(|(_, forced)| !*forced) {
                let avoid_val = self.memo.get(&rep).cloned().flatten()?;
                self.pins.remove(&rep);
                self.pin_source.remove(&rep);
                return Some((rep, avoid_val));
            }
        }
        // Last resort: DEMOTE a tester-only committed side — the tester atom's
        // SAT value can be don't-care noise pinning the class to a value it
        // never needed (e.g. `Tester(null)` forcing a nullary collision). The
        // final structural self-check catches a load-bearing tester.
        for rep in [rl, rr] {
            if !self.demoted.contains(&rep)
                && matches!(self.commits.get(&rep), Some(CtorCommit::Tester(_)))
            {
                let avoid_val = self.memo.get(&rep).cloned().flatten()?;
                self.demoted.insert(rep);
                return Some((rep, avoid_val));
            }
        }
        None
    }

    /// Which side of a violated disequality to re-choose: an unpinned free
    /// class first, then a tester-committed class with at least one free
    /// datatype field; `None` when neither side has slack (both fail closed).
    fn pick_repair_side(&self, rl: TermId, rr: TermId) -> Option<TermId> {
        let unpinned_free = |rep: TermId| self.is_free(rep) && !self.pins.contains_key(&rep);
        let tester_slack = |rep: TermId| match &self.commit_of(rep) {
            CtorCommit::Tester(ctor) => {
                self.exec
                    .ctx
                    .constructor_selector_info(ctor)
                    .is_some_and(|fs| {
                        fs.iter().any(|(sel, fsort)| {
                            self.exec.datatype_sort_name(fsort).is_some()
                                && !self.sel_apps.contains_key(&(rep, sel.clone()))
                        })
                    })
            }
            _ => false,
        };
        if unpinned_free(rl) {
            return Some(rl);
        }
        if unpinned_free(rr) {
            return Some(rr);
        }
        if tester_slack(rl) {
            return Some(rl);
        }
        if tester_slack(rr) {
            return Some(rr);
        }
        None
    }
}

/// Top-level argument parts of a rendered constructor value:
/// `(cons (node null) null)` -> `["(node null)", "null"]`; a nullary value
/// (`null`) has no parts. Paren depth plus SMT-LIB string literals (`"…"`,
/// `""` escape) and `|…|`-quoted symbols are respected so scalar parts
/// containing spaces or parentheses never split. `None` on malformed input
/// (callers fail closed — no field view is populated).
fn split_value_parts(s: &str) -> Option<Vec<String>> {
    let t = s.trim();
    if !t.starts_with('(') {
        // Nullary rendering: bare head, no parts.
        return Some(Vec::new());
    }
    let inner = t.strip_prefix('(')?.strip_suffix(')')?;
    let mut parts: Vec<String> = Vec::new();
    let mut cur = String::new();
    let mut depth: u32 = 0;
    let mut in_str = false;
    let mut in_sym = false;
    let mut chars = inner.chars().peekable();
    while let Some(c) = chars.next() {
        if in_str {
            cur.push(c);
            if c == '"' {
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
                depth = depth.checked_sub(1)?;
                cur.push(c);
            }
            c if c.is_whitespace() && depth == 0 => {
                if !cur.is_empty() {
                    parts.push(std::mem::take(&mut cur));
                }
            }
            c => cur.push(c),
        }
    }
    if depth != 0 || in_str || in_sym {
        return None;
    }
    if !cur.is_empty() {
        parts.push(cur);
    }
    // The first token is the constructor head, not a field.
    if parts.is_empty() {
        return None;
    }
    parts.remove(0);
    Some(parts)
}

/// Head symbol of a rendered constructor value: `(cons a b)` -> `cons`,
/// `null` -> `null`.
fn value_head(s: &str) -> &str {
    let t = s.trim();
    let t = t.strip_prefix('(').unwrap_or(t).trim_start();
    let end = t
        .find(|c: char| c.is_whitespace() || c == ')' || c == '(')
        .unwrap_or(t.len());
    &t[..end]
}
