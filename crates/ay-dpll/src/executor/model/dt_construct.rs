// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Total datatype model construction (#dt-total-model).
//!
//! After a SAT verdict, the extracted model can leave FREE datatype-sorted
//! terms without concrete values: a query like `(= x (cons 1 y))` with `y`
//! unconstrained solves SAT internally, but `y` has no constructor value, so
//! every datatype (dis)equality over it stays non-ground and the
//! `#dt-bv-congruence` validation guard (correctly) fails the verdict closed
//! to `unknown`. Real SMT solvers run a datatype model-construction phase that
//! makes the model TOTAL; this module is that phase for AY.
//!
//! MECHANISM. Runs as the last completion phase (after the scalar phases of
//! `complete_model_for_validation`), BEFORE any validation gate reads the
//! model:
//!
//! 1. Build equivalence classes over the datatype-sorted terms of the
//!    assertions (union-find), merged on committed equalities (top-level
//!    asserted or SAT-model-true `=`, SAT-model-false `distinct` pairs,
//!    shared EUF elements) and closed under selector/constructor argument
//!    congruence (`(sel a)`/`(sel b)` merge when `a`/`b` are co-class; the
//!    `i`-th argument of a class's constructor application merges with the
//!    class of `(sel_i member)`).
//! 2. A class whose constructor is FORCED (a constructor-application member,
//!    or a committed tester) is constructed with that constructor, resolving
//!    each field recursively: datatype fields recurse into the field's class;
//!    scalar fields take the committed model value (constructor-argument
//!    value / selector-application value — all committed sources must AGREE,
//!    else the class fails closed) or the canonical scalar default when
//!    genuinely unconstrained.
//! 3. A FREE class (nothing forces a constructor) gets a WELL-FOUNDED default
//!    value — the datatype's base constructor, computed recursively — chosen
//!    to differ from every already-constructed disequality neighbour and to
//!    respect committed-false testers. Two same-sort classes whose committed
//!    SELECTOR OBSERVATIONS disagree (e.g. `(hd x) = 1` committed on `x`'s
//!    class but `(hd (tl x)) = 2` committed on `(tl x)`'s class) are given an
//!    implicit disequality edge first (#dt-free-selector-funcong): selectors
//!    are FUNCTIONS, so if the two classes received the SAME value the model
//!    could not interpret the selector at that value single-valuedly and the
//!    fail-closed gates would (correctly) reject it — a nested selector chain
//!    like `hd(x)=1 ∧ hd(tl x)=2` with `x` free would degrade a genuinely-SAT
//!    query to `unknown`. A free class also resolves its OBSERVED fields:
//!    committed scalar selector values are copied into the candidate's fields
//!    (#dt-pin-selector) and a datatype field read by a datatype-sorted
//!    selector application recurses into that application's class, so the
//!    projected field agrees with the class value the application itself pins.
//! 4. Selector applications are single-valued per application: every scalar
//!    selector application over a constructed class is pinned to ONE value
//!    (the projected field for the class's own constructor, the committed —
//!    or default — value for a wrong-constructor selector, identical across
//!    congruent applications), so selector congruence holds by construction.
//! 5. OCCURS-CHECK: construction is well-founded. A class whose value
//!    (transitively) requires the class itself — a cyclic constraint chain
//!    `x = cons(1, x)` — has NO finite value: construction FAILS for that
//!    class (and every class embedding it), the model stays partial there,
//!    and validation degrades the verdict exactly as before. A cyclic witness
//!    can NEVER receive a constructed value.
//!
//! SOUNDNESS. The constructed values are candidates only, committed into the
//! model (`Model::dt_ground` / `Model::dt_pins`) BEFORE the full validation
//! pipeline runs, so EVERY existing validator — the term evaluator, the
//! strict `DtOracle`, the `#dt-bv-congruence` ground check, the independent
//! fail-closed gate, and the emitted-model round-trip — sees the SAME total
//! assignment. Evaluating a fixed total assignment is just evaluation: if
//! every assertion evaluates true under it, the assignment IS a genuine
//! model (the verdict is a real SAT); if any assertion evaluates false or
//! cannot be evaluated, the existing gates degrade the verdict to `unknown`
//! (fail-closed) exactly as they do today. Construction never bypasses a
//! validator and never weakens a guard — it only makes the model total so the
//! guards can actually decide. Free-leaf defaults are principled model
//! completion (every SMT solver picks values for unconstrained variables),
//! not fabrication: a term whose value is UNDERDETERMINED-BUT-CONSTRAINED
//! either receives the committed value (all committed sources must agree) or
//! the class fails closed — a guessed value can never paper over a
//! constraint, because the constraint itself is re-evaluated under the
//! constructed assignment by the full pipeline.
//!
//! SCOPE. In addition to variables, constructors, and selectors, construction
//! accepts opaque datatype-valued applications only when their producer owns
//! the missing structure: an ordinary declared UF application or an array
//! `select`. Their equality classes come from committed equality atoms and the
//! extracted EUF model; the independent gate still re-derives UF and array
//! congruence over the completed values. Other datatype-valued applications
//! and datatype-valued `ite`s remain unsupported and make the phase bail
//! entirely (leaving the model unchanged).

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{string_literal, Sort, TermId};
use ay_model_check::{ArrayValue, ModelValue};
use num_bigint::BigInt;
use num_rational::BigRational;

use crate::executor_format::{format_bigint, format_bitvec, format_rational};

use super::dt_construct_budget::OpaqueDtConstructionBudget;
use super::{EvalValue, Model};
use crate::executor::Executor;

/// Hard cap on the number of datatype-sorted terms construction will attempt;
/// beyond it the phase bails (keeping today's behaviour) so the quadratic
/// congruence fixpoint cannot become a post-solve bottleneck.
const MAX_DT_TERMS: usize = 1024;

/// Fuel for recursive value construction (bounds nesting depth defensively on
/// top of the class-path occurs-check).
const MAX_DEPTH: u32 = 512;

/// How a collected datatype-sorted term participates in construction.
#[derive(Clone, Debug, PartialEq)]
enum DtTermKind {
    /// Plain variable / constant.
    Var,
    /// Constructor application `(C a0 .. ak)` (or a nullary-constructor
    /// constant stored as a `Var` whose name is the constructor).
    CtorApp { ctor: String, args: Vec<TermId> },
    /// Selector application `(sel t)` whose RESULT is datatype-sorted.
    SelApp { sel: String, arg: TermId },
    /// Datatype-valued ordinary UF application or array `select`.
    ///
    /// These are free class members here: committed equality/EUF-class evidence
    /// determines their class, while the independent model gate rechecks the
    /// originating function/array semantics after construction.  In
    /// particular, no observed constructor field is inferred at this boundary.
    OpaqueApp,
}

/// Render a constructed [`ModelValue`] as a canonical string: injective per
/// sort (two distinct values never produce the same string; the same value
/// always produces the same string), using INTERNAL constructor names and the
/// same scalar formatting the strict `DtOracle` ground resolution uses, so
/// pinned and strictly-resolved canonical forms agree.
pub(super) fn dt_canonical_string(mv: &ModelValue) -> String {
    match mv {
        ModelValue::Bool(b) => b.to_string(),
        ModelValue::Int(i) => format_bigint(i),
        ModelValue::Real(r) => format_rational(r),
        ModelValue::BitVec { width, value } => format_bitvec(value, *width),
        ModelValue::FloatingPoint {
            sign,
            exponent,
            significand,
            exponent_bits,
            significand_bits,
        } => format!(
            "(#fp {} {} {} {} {})",
            u8::from(*sign),
            exponent,
            significand,
            exponent_bits,
            significand_bits
        ),
        ModelValue::Str(s) => string_literal(s),
        ModelValue::Uninterpreted(tok) => tok.clone(),
        // Injective over the triple that determines the value: which root of
        // which polynomial, and which element of that extension.
        ModelValue::Algebraic(a) => {
            let poly =
                |cs: &[BigRational]| cs.iter().map(format_rational).collect::<Vec<_>>().join(",");
            let (lo, hi) = a.interval();
            format!(
                "(root-obj [{}] ({} {}) [{}])",
                poly(a.minimal_polynomial()),
                format_rational(lo),
                format_rational(hi),
                poly(a.representation())
            )
        }
        ModelValue::Array(av) => {
            let mut s = format!("(#arr {}", dt_canonical_string(&av.default));
            for (k, v) in &av.store {
                s.push_str(&format!(
                    " [{} {}]",
                    dt_canonical_string(k),
                    dt_canonical_string(v)
                ));
            }
            s.push(')');
            s
        }
        ModelValue::Seq(elems) => {
            let parts: Vec<String> = elems.iter().map(dt_canonical_string).collect();
            format!("(#seq {})", parts.join(" "))
        }
        ModelValue::Datatype { ctor, args } => {
            if args.is_empty() {
                ctor.clone()
            } else {
                let parts: Vec<String> = args.iter().map(dt_canonical_string).collect();
                format!("({} {})", ctor, parts.join(" "))
            }
        }
    }
}

/// Convert a constructed [`ModelValue`] into the [`EvalValue`] the term
/// evaluator pins: scalars map to their native variants; datatype values map
/// to `Element(canonical)` so datatype (dis)equalities compare by canonical
/// identity. Arrays/FP are not pinnable (`Unknown`, never pinned).
fn mv_to_eval(mv: &ModelValue) -> EvalValue {
    match mv {
        ModelValue::Bool(b) => EvalValue::Bool(*b),
        ModelValue::Int(i) => EvalValue::Rational(BigRational::from(i.clone())),
        ModelValue::Real(r) => EvalValue::Rational(r.clone()),
        ModelValue::BitVec { width, value } => EvalValue::BitVec {
            value: value.clone(),
            width: *width,
        },
        ModelValue::Str(s) => EvalValue::String(s.clone()),
        ModelValue::Uninterpreted(tok) => EvalValue::Element(tok.clone()),
        ModelValue::Datatype { .. } => EvalValue::Element(dt_canonical_string(mv)),
        ModelValue::Seq(elems) => {
            let converted: Vec<EvalValue> = elems.iter().map(mv_to_eval).collect();
            EvalValue::Seq(converted)
        }
        // Not pinnable. `EvalValue` has no algebraic variant, so pinning one
        // would require collapsing it to a rational -- which is exactly the
        // lossy step that loses `sqrt(2)`. Fail closed, as FP and arrays do.
        ModelValue::FloatingPoint { .. } | ModelValue::Array(_) | ModelValue::Algebraic(_) => {
            EvalValue::Unknown
        }
    }
}

/// Whether a structured datatype value has the exact scalar canonical form
/// carried by [`EvalValue::Element`]. Arrays, sequences, floating-point, and
/// algebraic values deliberately stay out of that comparison lane. They may
/// still remain as exact [`ModelValue`] trees in `dt_ground`, where structural
/// selector projection and the independent gate consume them without a lossy
/// conversion.
fn dt_canonical_pin_supported(value: &ModelValue) -> bool {
    let mut stack = vec![value];
    while let Some(value) = stack.pop() {
        match value {
            ModelValue::Bool(_)
            | ModelValue::Int(_)
            | ModelValue::Real(_)
            | ModelValue::BitVec { .. }
            | ModelValue::Str(_)
            | ModelValue::Uninterpreted(_) => {}
            ModelValue::Datatype { args, .. } => stack.extend(args),
            ModelValue::Array(_)
            | ModelValue::Seq(_)
            | ModelValue::FloatingPoint { .. }
            | ModelValue::Algebraic(_) => return false,
        }
    }
    true
}

/// Convert a committed scalar [`EvalValue`] into a [`ModelValue`] guided by
/// the term's sort. `None` when the value cannot be represented faithfully
/// (fail closed — the field/class is then left unconstructed).
pub(super) fn eval_to_mv(ev: &EvalValue, sort: &Sort) -> Option<ModelValue> {
    match (ev, sort) {
        (EvalValue::Bool(b), Sort::Bool) => Some(ModelValue::Bool(*b)),
        (EvalValue::Rational(r), Sort::Int) if r.is_integer() => {
            Some(ModelValue::Int(r.to_integer()))
        }
        (EvalValue::Rational(r), Sort::Real) => Some(ModelValue::Real(r.clone())),
        (EvalValue::BitVec { value, width }, Sort::BitVec(bv))
            if *width == bv.width
                && value.sign() != num_bigint::Sign::Minus
                && value.bits() <= u64::from(*width) =>
        {
            Some(ModelValue::bitvec(value.clone(), *width))
        }
        (EvalValue::String(s), Sort::String) => Some(ModelValue::Str(s.clone())),
        _ => None,
    }
}

/// Union-find with path compression.
fn uf_find(parent: &mut [usize], mut x: usize) -> usize {
    while parent[x] != x {
        parent[x] = parent[parent[x]];
        x = parent[x];
    }
    x
}

fn uf_union(parent: &mut [usize], a: usize, b: usize) -> bool {
    let ra = uf_find(parent, a);
    let rb = uf_find(parent, b);
    if ra == rb {
        return false;
    }
    // Deterministic: smaller index becomes the root.
    if ra < rb {
        parent[rb] = ra;
    } else {
        parent[ra] = rb;
    }
    true
}

/// Per-class constructor forcing state.
#[derive(Default, Clone)]
struct ClassInfo {
    /// Constructor forced by a ctor-app member or committed tester.
    forced: Option<String>,
    /// Constructors excluded by committed-false testers.
    excluded: Vec<String>,
    /// Set when committed evidence conflicts (two different forced
    /// constructors); the class is never constructed (fail closed).
    conflicted: bool,
}

struct DtBuilder<'a> {
    exec: &'a Executor,
    model: &'a Model,
    /// Collected datatype-sorted terms, deterministic order.
    terms: Vec<TermId>,
    kinds: Vec<DtTermKind>,
    index: HashMap<TermId, usize>,
    /// FINAL class id (root index) per term index.
    class_of: Vec<usize>,
    /// Members (term indices) per class root, sorted.
    members: HashMap<usize, Vec<usize>>,
    /// Forcing info per class root.
    info: HashMap<usize, ClassInfo>,
    /// Disequality edges between class roots (committed-true `distinct` /
    /// committed-false `=`).
    diseq: HashMap<usize, Vec<usize>>,
    /// ALL selector applications (any result sort): (app term, selector, arg).
    sel_apps: Vec<(TermId, String, TermId)>,
    /// Tester applications: (app term, ctor, arg).
    tester_apps: Vec<(TermId, String, TermId)>,
    /// Constructed value per class root; `None` = construction failed
    /// (cyclic / conflicting / unrepresentable): the class stays unpinned and
    /// validation fails closed exactly as today.
    values: HashMap<usize, Option<ModelValue>>,
    /// Active only when the newly-supported opaque application lane is used;
    /// exhaustion discards this builder before it can mutate the model.
    work_budget: OpaqueDtConstructionBudget,
}

impl Executor {
    /// Total datatype model construction (see module docs). Returns the number
    /// of datatype-sorted terms that received a constructed value.
    pub(super) fn construct_total_datatype_model(
        &self,
        model: &mut Model,
        extra_roots: &[TermId],
    ) -> usize {
        if self.ctx.datatype_iter().next().is_none() {
            return 0;
        }
        // Single-source arbitration (#mv-dt-single-source x #dt-total-model):
        // when the interactive DT lane EXPORTED its e-graph model — or the
        // lazy DT lane (D1/D2, `dt_lazy_splits` armed) is currently driving
        // the solve — the e-graph-derived per-class assignment is the
        // authority for every printed datatype value, and construction must
        // STEP ASIDE. The lazy lane's models deliberately leave selector
        // slack abstract (EUF elements), so running construction there pins
        // fabricated free-slack candidates (e.g. identical `(s z)` for
        // asserted-distinct constants whose `p` fields no theory model
        // constrains) into the model, where the strict definitive-false
        // oracle reads them FIRST and demotes the lane's genuinely-Sat
        // verdict, and the assignment builder inherits the collisions. The
        // e-graph path has its own fail-closed chain (builder self-check,
        // independent gate, printed-model backstop), so skipping here never
        // weakens a guard.
        if self.dt_theory_model.is_some() || self.dt_lazy_splits.is_some() {
            if !model.dt_pins.is_empty() || !model.dt_ground.is_empty() {
                model.dt_pins.clear();
                model.dt_ground.clear();
                super::eval_memo_clear();
            }
            return 0;
        }
        // Idempotency: rebuild from scratch on every completion pass so pins
        // never feed back into their own derivation.
        if !model.dt_pins.is_empty() || !model.dt_ground.is_empty() {
            model.dt_pins.clear();
            model.dt_ground.clear();
            super::eval_memo_clear();
        }

        let (ground, pins) = {
            let Some(mut builder) = self.dt_collect(model, extra_roots) else {
                return 0; // bail: unsupported shape — keep today's behaviour
            };
            if builder.terms.is_empty() {
                return 0;
            }
            builder.force_constructors();
            if builder.work_budget.exhausted() {
                return 0;
            }
            builder.add_observation_disequalities();
            if !builder.construct_all() {
                return 0;
            }
            let Some(result) = builder.finish() else {
                return 0;
            };
            result
        };
        let constructed = ground.len();
        for (t, mv) in ground {
            model.dt_ground.insert(t, mv);
        }
        for (t, v) in pins {
            model.dt_pins.insert(t, v);
        }
        if constructed > 0 {
            super::eval_memo_clear();
        }
        constructed
    }

    /// Collect datatype-sorted terms and datatype atoms from the assertions +
    /// `extra_roots`. Returns `None` (bail out entirely) when a
    /// datatype-sorted term of an unsupported kind is reachable.
    fn dt_collect<'a>(&'a self, model: &'a Model, extra_roots: &[TermId]) -> Option<DtBuilder<'a>> {
        let preflight = self.preflight_opaque_dt_collection(extra_roots)?;
        let (
            opaque_scope,
            datatype_guard,
            opaque_apps,
            mut datatype_names,
            datatype_members,
            strict_opaque_scope,
        ) = preflight.into_parts();
        if strict_opaque_scope {
            datatype_names = self.opaque_dt_constructible_names(
                extra_roots,
                &datatype_names,
                &datatype_members,
                &opaque_apps,
            )?;
        }
        let terms_store = &self.ctx.terms;
        let is_dt_sort = |t: TermId| {
            if !strict_opaque_scope {
                return self.datatype_sort_name(terms_store.sort(t)).is_some();
            }
            match terms_store.sort(t) {
                Sort::Datatype(datatype) if datatype.name.len() <= 256 => {
                    datatype_names.contains(&datatype.name)
                }
                Sort::Uninterpreted(name) if name.len() <= 256 => datatype_names.contains(name),
                _ => false,
            }
        };

        let roots: Vec<TermId> = self
            .ctx
            .assertions
            .iter()
            .copied()
            .chain(extra_roots.iter().copied())
            .collect();
        // Atoms directly under a top-level `not` are committed FALSE.
        let mut top_neg: HashSet<TermId> = HashSet::default();
        let top: HashSet<TermId> = roots.iter().copied().collect();
        for &r in &roots {
            if let TermData::Not(inner) = terms_store.get(r) {
                top_neg.insert(*inner);
            }
        }

        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = roots.clone();
        let mut dt_terms: Vec<TermId> = Vec::new();
        let mut kinds_by_term: HashMap<TermId, DtTermKind> = HashMap::default();
        let mut eq_atoms: Vec<(TermId, TermId, TermId)> = Vec::new();
        let mut distinct_atoms: Vec<(TermId, Vec<TermId>)> = Vec::new();
        let mut sel_apps: Vec<(TermId, String, TermId)> = Vec::new();
        let mut tester_apps: Vec<(TermId, String, TermId)> = Vec::new();

        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match terms_store.get(t) {
                TermData::Var(name, _) => {
                    if is_dt_sort(t) {
                        // A nullary-constructor constant is stored as a Var
                        // whose name is the constructor (#1745).
                        let kind = match (
                            if strict_opaque_scope {
                                datatype_members.get(name).copied()
                            } else {
                                self.ctx
                                    .exact_datatype_member_info(name)
                                    .map(|info| info.declaration_kind())
                            },
                            self.ctx.is_constructor(name),
                        ) {
                            (
                                Some(ay_frontend::DeclarationKind::DatatypeConstructor),
                                Some((_dt, ctor)),
                            ) if self
                                .ctx
                                .constructor_selector_info(&ctor)
                                .map_or(true, |f| f.is_empty()) =>
                            {
                                DtTermKind::CtorApp {
                                    ctor,
                                    args: Vec::new(),
                                }
                            }
                            _ => DtTermKind::Var,
                        };
                        dt_terms.push(t);
                        if dt_terms.len() > MAX_DT_TERMS {
                            return None;
                        }
                        kinds_by_term.insert(t, kind);
                    }
                }
                TermData::App(sym, args) => {
                    let name = sym.name();
                    let declaration_kind = if strict_opaque_scope {
                        datatype_members.get(name).copied()
                    } else {
                        self.ctx
                            .exact_datatype_member_info(name)
                            .map(|info| info.declaration_kind())
                    };
                    if is_dt_sort(t) {
                        let kind = if declaration_kind
                            == Some(ay_frontend::DeclarationKind::DatatypeConstructor)
                        {
                            DtTermKind::CtorApp {
                                ctor: name.to_string(),
                                args: args.clone(),
                            }
                        } else if args.len() == 1
                            && declaration_kind
                                == Some(ay_frontend::DeclarationKind::DatatypeSelector)
                        {
                            DtTermKind::SelApp {
                                sel: name.to_string(),
                                arg: args[0],
                            }
                        } else if opaque_apps.contains(&t) {
                            // Model-completion producers for both shapes already
                            // carry exact equality-class evidence.  Treat the
                            // result as a free datatype class; downstream
                            // validation independently checks UF/array
                            // congruence against the constructed value.
                            DtTermKind::OpaqueApp
                        } else if !strict_opaque_scope {
                            // The bounded discovery pass was indeterminate or
                            // found no admissible widening. Preserve the
                            // legacy collector's fail-closed behavior for
                            // every non-member datatype-result application.
                            return None;
                        } else {
                            // Other theory applications have semantics this
                            // phase cannot reconstruct independently.
                            return None;
                        };
                        dt_terms.push(t);
                        if dt_terms.len() > MAX_DT_TERMS {
                            return None;
                        }
                        kinds_by_term.insert(t, kind);
                    } else if args.len() == 1
                        && declaration_kind == Some(ay_frontend::DeclarationKind::DatatypeSelector)
                        && is_dt_sort(args[0])
                    {
                        // Scalar-result selector application (pinned later).
                        sel_apps.push((t, name.to_string(), args[0]));
                    }
                    if declaration_kind == Some(ay_frontend::DeclarationKind::DatatypeTester) {
                        if let Some(ctor) = name.strip_prefix("is-") {
                            if args.len() == 1 && is_dt_sort(args[0]) {
                                tester_apps.push((t, ctor.to_string(), args[0]));
                            }
                        }
                    }
                    if name == "=" && args.len() == 2 && is_dt_sort(args[0]) && is_dt_sort(args[1])
                    {
                        eq_atoms.push((t, args[0], args[1]));
                    }
                    if name == "distinct" && args.iter().all(|&a| is_dt_sort(a)) {
                        distinct_atoms.push((t, args.clone()));
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => {
                    if is_dt_sort(t) {
                        return None; // datatype-valued ite: bail
                    }
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                // Quantifier / let bodies are not ground model terms; do not
                // descend (their datatype terms are left to the existing
                // quantifier validation paths, unchanged).
                TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..) => {}
                _ => {
                    if is_dt_sort(t) {
                        return None; // datatype-sorted constant of another kind
                    }
                }
            }
        }
        // Record dt-sorted SELECTOR apps in sel_apps too (needed for
        // wrong-constructor congruence and field projection).
        for &t in &dt_terms {
            if let Some(DtTermKind::SelApp { sel, arg }) = kinds_by_term.get(&t) {
                sel_apps.push((t, sel.clone(), *arg));
            }
        }

        dt_terms.sort_by_key(|t| t.index());
        dt_terms.dedup();
        let mut index: HashMap<TermId, usize> = HashMap::default();
        for (i, &t) in dt_terms.iter().enumerate() {
            index.insert(t, i);
        }
        let kinds: Vec<DtTermKind> = dt_terms
            .iter()
            .map(|t| kinds_by_term.get(t).cloned().unwrap_or(DtTermKind::Var))
            .collect();
        let opaque_terms = kinds
            .iter()
            .filter(|kind| matches!(kind, DtTermKind::OpaqueApp))
            .count();
        match (opaque_scope, opaque_terms) {
            (None, 0) => {}
            (Some(scope), count) if scope.opaque_terms() == count => {}
            _ => return None,
        }
        if opaque_terms != 0 {
            let guard = datatype_guard.as_ref()?;
            // Registered bounded schemas, not the exact rendered fragment: see
            // `RenderedDatatypeGuard::is_registered` for why requiring
            // exactness here silently degraded scalar-payload datatypes.
            if dt_terms
                .iter()
                .any(|term| !guard.is_registered(self.ctx.terms.sort(*term)))
            {
                return None;
            }
        }
        let work_budget = OpaqueDtConstructionBudget::new(opaque_terms)?;

        // ---- committed truth of an atom under the model ----
        let committed = |atom: TermId| -> Option<bool> {
            if top.contains(&atom) {
                return Some(true);
            }
            if top_neg.contains(&atom) {
                return Some(false);
            }
            self.term_value(&model.sat_model, &model.term_to_var, atom)
        };

        // ---- union-find over dt terms ----
        let n = dt_terms.len();
        let mut parent: Vec<usize> = (0..n).collect();
        let mut diseq_pairs: Vec<(usize, usize)> = Vec::new();
        for &(atom, a, b) in &eq_atoms {
            let (Some(&ia), Some(&ib)) = (index.get(&a), index.get(&b)) else {
                continue;
            };
            match committed(atom) {
                Some(true) => {
                    uf_union(&mut parent, ia, ib);
                }
                Some(false) => diseq_pairs.push((ia, ib)),
                None => {}
            }
        }
        for (atom, args) in &distinct_atoms {
            let idxs: Vec<Option<&usize>> = args.iter().map(|a| index.get(a)).collect();
            match committed(*atom) {
                Some(true) => {
                    for i in 0..idxs.len() {
                        for j in (i + 1)..idxs.len() {
                            if let (Some(&ia), Some(&ib)) = (idxs[i], idxs[j]) {
                                diseq_pairs.push((ia, ib));
                            }
                        }
                    }
                }
                Some(false) if args.len() == 2 => {
                    if let (Some(&ia), Some(&ib)) = (idxs[0], idxs[1]) {
                        uf_union(&mut parent, ia, ib);
                    }
                }
                _ => {}
            }
        }
        // Shared EUF element => committed equal.
        if let Some(euf) = model.euf_model.as_ref() {
            let mut by_elem: HashMap<(String, String), usize> = HashMap::default();
            for (i, &t) in dt_terms.iter().enumerate() {
                if let Some(elem) = euf.term_values.get(&t) {
                    let sort_name = self
                        .exact_collected_datatype_sort_name(terms_store.sort(t), &datatype_names)
                        .unwrap_or_default();
                    let key = (sort_name, elem.clone());
                    match by_elem.get(&key) {
                        Some(&j) => {
                            uf_union(&mut parent, i, j);
                        }
                        None => {
                            by_elem.insert(key, i);
                        }
                    }
                }
            }
        }
        // ---- congruence closure fixpoint ----
        // (a) selector-argument congruence: (sel a) ~ (sel b) when a ~ b;
        // (b) constructor-argument congruence: co-class ctor apps of the same
        //     ctor merge corresponding datatype args;
        // (c) selector-vs-argument: `(sel_i t)` merges with the i-th argument
        //     of a co-class constructor application owning `sel_i`.
        let dt_sel_apps: Vec<(usize, String, usize)> = dt_terms
            .iter()
            .enumerate()
            .filter_map(|(i, _)| match &kinds[i] {
                DtTermKind::SelApp { sel, arg } => index.get(arg).map(|&ai| (i, sel.clone(), ai)),
                _ => None,
            })
            .collect();
        // Scalar selector apps participate via pinning later; dt-sorted ones
        // join the union-find here.
        let ctor_apps: Vec<(usize, String, Vec<TermId>)> = dt_terms
            .iter()
            .enumerate()
            .filter_map(|(i, _)| match &kinds[i] {
                DtTermKind::CtorApp { ctor, args } => Some((i, ctor.clone(), args.clone())),
                _ => None,
            })
            .collect();
        for _round in 0..64 {
            let mut changed = false;
            // (a)
            for x in 0..dt_sel_apps.len() {
                for y in (x + 1)..dt_sel_apps.len() {
                    if dt_sel_apps[x].1 == dt_sel_apps[y].1 {
                        let (ax, ay) = (dt_sel_apps[x].2, dt_sel_apps[y].2);
                        if uf_find(&mut parent, ax) == uf_find(&mut parent, ay)
                            && uf_union(&mut parent, dt_sel_apps[x].0, dt_sel_apps[y].0)
                        {
                            changed = true;
                        }
                    }
                }
            }
            // (b)
            for x in 0..ctor_apps.len() {
                for y in (x + 1)..ctor_apps.len() {
                    let (ix, ref cx, ref ax) = ctor_apps[x];
                    let (iy, ref cy, ref ay) = ctor_apps[y];
                    if cx != cy || ax.len() != ay.len() {
                        continue;
                    }
                    if uf_find(&mut parent, ix) != uf_find(&mut parent, iy) {
                        continue;
                    }
                    for k in 0..ax.len() {
                        if let (Some(&pa), Some(&pb)) = (index.get(&ax[k]), index.get(&ay[k])) {
                            if uf_union(&mut parent, pa, pb) {
                                changed = true;
                            }
                        }
                    }
                }
            }
            // (c)
            for &(si, ref sel, sarg) in &dt_sel_apps {
                let sarg_root = uf_find(&mut parent, sarg);
                for &(ci, ref ctor, ref cargs) in &ctor_apps {
                    if uf_find(&mut parent, ci) != sarg_root {
                        continue;
                    }
                    let Some(selectors) = self.ctx.constructor_selectors(ctor) else {
                        continue;
                    };
                    let Some(fidx) = selectors.iter().position(|s| s == sel) else {
                        continue;
                    };
                    if let Some(&arg_idx) = cargs.get(fidx).and_then(|a| index.get(a)) {
                        if uf_union(&mut parent, si, arg_idx) {
                            changed = true;
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }

        // Finalize classes.
        let class_of: Vec<usize> = (0..n).map(|i| uf_find(&mut parent, i)).collect();
        let mut members: HashMap<usize, Vec<usize>> = HashMap::default();
        for (i, &r) in class_of.iter().enumerate() {
            members.entry(r).or_default().push(i);
        }
        for v in members.values_mut() {
            v.sort_unstable();
        }
        let mut diseq: HashMap<usize, Vec<usize>> = HashMap::default();
        for (a, b) in diseq_pairs {
            let (ra, rb) = (class_of[a], class_of[b]);
            if ra != rb {
                diseq.entry(ra).or_default().push(rb);
                diseq.entry(rb).or_default().push(ra);
            }
            // ra == rb: the model commits both `a = b` and `a != b`; the
            // equal constructed values make the disequality evaluate false and
            // validation degrades (fail closed) — nothing to record here.
        }

        Some(DtBuilder {
            exec: self,
            model,
            terms: dt_terms,
            kinds,
            index,
            class_of,
            members,
            info: HashMap::default(),
            diseq,
            sel_apps,
            tester_apps,
            values: HashMap::default(),
            work_budget,
        })
    }

    /// Keep opaque completion component-local when another datatype sort in
    /// the same query has an unsupported producer.
    ///
    /// The collector used to bail out globally: one inexact datatype-valued
    /// array read (for example `select` from `Array<BV64, PbTerm>` where
    /// `PbTerm` itself contains an `Array<BV64, PbLit>`) prevented an unrelated
    /// `Result<BV128, E>`-valued UF disequality from receiving any model
    /// values. The SAT search then published the same completion default for
    /// both Result applications and the independent gate correctly rejected
    /// the model.
    ///
    /// This pass removes only the unsupported producer's registered datatype
    /// sort and datatypes whose constructor fields depend on it. Other
    /// components retain the exact pre-existing construction algorithm and all
    /// downstream validation. A same-sort or schema-dependent unsupported term
    /// still removes the opaque applications from collection, causing the
    /// preflight/count match to fail closed exactly as before.
    fn opaque_dt_constructible_names(
        &self,
        extra_roots: &[TermId],
        all_names: &HashSet<String>,
        datatype_members: &HashMap<String, ay_frontend::DeclarationKind>,
        opaque_apps: &HashSet<TermId>,
    ) -> Option<HashSet<String>> {
        let registered_name = |term: TermId| match self.ctx.terms.sort(term) {
            Sort::Uninterpreted(name) if all_names.contains(name) => Some(name.as_str()),
            Sort::Datatype(datatype) if all_names.contains(&datatype.name) => {
                Some(datatype.name.as_str())
            }
            _ => None,
        };

        let mut blocked = HashSet::default();
        let mut seen = HashSet::default();
        let mut stack: Vec<TermId> = self
            .ctx
            .assertions
            .iter()
            .copied()
            .chain(extra_roots.iter().copied())
            .collect();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            let result_name = registered_name(term);
            match self.ctx.terms.get(term) {
                TermData::Var(_, _) => {}
                TermData::App(symbol, args) => {
                    if let Some(name) = result_name {
                        let kind = datatype_members.get(symbol.name()).copied();
                        let supported = kind
                            == Some(ay_frontend::DeclarationKind::DatatypeConstructor)
                            || (args.len() == 1
                                && kind == Some(ay_frontend::DeclarationKind::DatatypeSelector))
                            || opaque_apps.contains(&term);
                        if !supported {
                            blocked.insert(name.to_string());
                        }
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(condition, then_term, else_term) => {
                    if let Some(name) = result_name {
                        blocked.insert(name.to_string());
                    }
                    stack.push(*condition);
                    stack.push(*then_term);
                    stack.push(*else_term);
                }
                TermData::Forall(..) | TermData::Exists(..) => {}
                TermData::Let(..) => {
                    // The ground collector deliberately does not interpret
                    // binder environments.  A datatype-valued `let` is
                    // therefore an unsupported producer in this lane and
                    // must block its component just like a datatype-valued
                    // `ite`; retaining the sort here would let the preflight
                    // count a term that collection silently omits.
                    if let Some(name) = result_name {
                        blocked.insert(name.to_string());
                    }
                }
                _ => {
                    if let Some(name) = result_name {
                        blocked.insert(name.to_string());
                    }
                }
            }
        }

        // Reverse schema dependencies once, then close the blocked set toward
        // datatypes whose constructor values would embed a blocked datatype.
        // The rendered-schema preflight already bounded every descriptor to 32
        // levels / 1024 nodes; repeat those exact caps while borrowing them.
        let mut reverse: HashMap<String, Vec<String>> = HashMap::default();
        let mut sort_nodes = 0usize;
        for owner in all_names {
            for constructor in self.ctx.datatype_constructors(owner)? {
                for (_, field_sort) in self.ctx.constructor_selector_info(constructor)? {
                    let mut sorts = vec![(field_sort, 0usize)];
                    while let Some((sort, depth)) = sorts.pop() {
                        if depth > 32 {
                            return None;
                        }
                        sort_nodes = sort_nodes.checked_add(1)?;
                        if sort_nodes > 1024 {
                            return None;
                        }
                        match sort {
                            Sort::Uninterpreted(name) if all_names.contains(name) => {
                                reverse.entry(name.clone()).or_default().push(owner.clone());
                            }
                            Sort::Datatype(datatype) if all_names.contains(&datatype.name) => {
                                reverse
                                    .entry(datatype.name.clone())
                                    .or_default()
                                    .push(owner.clone());
                            }
                            // Array/sequence fields are extensional model
                            // boundaries, not direct constructor recursion.
                            // A separately unsupported producer of their
                            // element datatype does not make the owner
                            // unconstructible: the owner retains the exact
                            // structured container value, and the independent
                            // array/sequence gate checks every observed cell.
                            // Propagating through these carriers discarded
                            // `PbObjective` merely because one `PbTerm` array
                            // read was outside completion, hiding the objective's
                            // otherwise exact `terms` projection.
                            Sort::Array(_) | Sort::Seq(_) => {}
                            _ => {}
                        }
                    }
                }
            }
        }
        let mut pending: Vec<String> = blocked.iter().cloned().collect();
        while let Some(name) = pending.pop() {
            for dependent in reverse.get(&name).into_iter().flatten() {
                if blocked.insert(dependent.clone()) {
                    pending.push(dependent.clone());
                }
            }
        }

        Some(
            all_names
                .iter()
                .filter(|name| !blocked.contains(*name))
                .cloned()
                .collect(),
        )
    }

    fn exact_collected_datatype_sort_name(
        &self,
        sort: &Sort,
        datatype_names: &HashSet<String>,
    ) -> Option<String> {
        match sort {
            Sort::Datatype(datatype) if datatype_names.is_empty() => Some(datatype.name.clone()),
            Sort::Datatype(datatype) if datatype_names.contains(&datatype.name) => {
                Some(datatype.name.clone())
            }
            Sort::Uninterpreted(name) if datatype_names.is_empty() => Some(name.clone()),
            Sort::Uninterpreted(name) if datatype_names.contains(name) => Some(name.clone()),
            _ => None,
        }
    }
}

impl DtBuilder<'_> {
    /// The datatype sort name of a class (all members share one sort).
    fn class_sort_name(&self, root: usize) -> Option<String> {
        let &first = self.members.get(&root)?.first()?;
        match self.exec.ctx.terms.sort(self.terms[first]) {
            Sort::Datatype(datatype) => Some(datatype.name.clone()),
            Sort::Uninterpreted(name) => Some(name.clone()),
            _ => None,
        }
    }

    /// Committed truth of an atom (top-level assertions were folded into the
    /// collection walk; here only the SAT model matters — testers).
    fn committed(&self, atom: TermId) -> Option<bool> {
        if self.exec.ctx.assertions.contains(&atom) {
            return Some(true);
        }
        self.exec
            .term_value(&self.model.sat_model, &self.model.term_to_var, atom)
    }

    /// Determine each class's forced constructor / exclusions.
    fn force_constructors(&mut self) {
        let roots: Vec<usize> = self.members.keys().copied().collect();
        for root in roots {
            let mut ci = ClassInfo::default();
            let members = self.members.get(&root).cloned().unwrap_or_default();
            for &m in &members {
                if let DtTermKind::CtorApp { ctor, .. } = &self.kinds[m] {
                    match &ci.forced {
                        Some(c) if c != ctor => ci.conflicted = true,
                        _ => ci.forced = Some(ctor.clone()),
                    }
                }
            }
            self.info.insert(root, ci);
        }
        // Testers.
        let tester_apps = self.tester_apps.clone();
        for (atom, ctor, arg) in tester_apps {
            let Some(&ai) = self.index.get(&arg) else {
                continue;
            };
            let root = self.class_of[ai];
            let Some(truth) = self.committed(atom) else {
                continue;
            };
            let ci = self.info.entry(root).or_default();
            if truth {
                match &ci.forced {
                    Some(c) if *c != ctor => ci.conflicted = true,
                    _ => ci.forced = Some(ctor.clone()),
                }
            } else if !ci.excluded.contains(&ctor) {
                ci.excluded.push(ctor.clone());
            }
        }
        // Post-process exclusions: forced-but-excluded => conflict; all-but-one
        // excluded => forced.
        let roots: Vec<usize> = self.info.keys().copied().collect();
        for root in roots {
            let Some(sort_name) = self.class_sort_name(root) else {
                continue;
            };
            let Some(ctors) = self.exec.ctx.datatype_constructors(&sort_name) else {
                continue;
            };
            let exclusions = self.info.get(&root).map_or(0, |class| class.excluded.len());
            if !self
                .work_budget
                .charge_constructor_filter(ctors.len(), exclusions)
            {
                return;
            }
            let ci = self.info.get_mut(&root).expect("inserted above");
            if let Some(f) = &ci.forced {
                if ci.excluded.contains(f) {
                    ci.conflicted = true;
                }
                continue;
            }
            let mut remaining = ctors.iter().filter(|c| !ci.excluded.contains(c));
            let first = remaining.next();
            match (first, remaining.next()) {
                (None, _) => ci.conflicted = true,
                (Some(constructor), None) => {
                    if !self.work_budget.charge_name_clone(constructor) {
                        return;
                    }
                    ci.forced = Some(constructor.clone());
                }
                _ => {}
            }
        }
    }

    /// Collect the committed SELECTOR OBSERVATIONS of class `root` into `out`
    /// as sorted `(path, value)` pairs (#dt-free-selector-funcong).
    ///
    /// A path is a `\u{1}`-joined chain of selector names applied to the class
    /// (e.g. `tl\u{1}hd` for `(hd (tl x))` observed through `x`'s class); the
    /// value is the canonical string the pinning phase would give that
    /// application: the first committed scalar value of the application group,
    /// else the result sort's base default (mirroring `finish()`), so two
    /// classes CONFLICT exactly when — were they constructed to the same value
    /// — the selector could not be interpreted as a function at that value.
    /// Datatype-sorted selector applications recurse into the application's
    /// class (path-visited guard against merged-class cycles); a forced
    /// constructor on a sub-path class is recorded as a `#ctor` observation so
    /// forced-`nil` vs forced-`cons` sub-lists also conflict.
    ///
    /// Bounded: depth (selector-chain length) and total observation count are
    /// capped, so this can never loop or blow up on recursive datatypes; a
    /// missed deep observation only means a missed implicit disequality —
    /// exactly today's behaviour (validation still fail-closes).
    fn selector_observations(
        &self,
        root: usize,
        prefix: &str,
        depth: u32,
        visited: &mut Vec<usize>,
        out: &mut Vec<(String, String)>,
    ) {
        const MAX_OBS: usize = 64;
        if depth == 0 || out.len() >= MAX_OBS || visited.contains(&root) {
            return;
        }
        visited.push(root);
        // Forced constructor of a SUB-path class is itself an observation.
        if !prefix.is_empty() {
            if let Some(ci) = self.info.get(&root) {
                if let Some(f) = &ci.forced {
                    out.push((format!("{prefix}\u{1}#ctor"), f.clone()));
                }
            }
        }
        let member_terms: HashSet<TermId> = self
            .members
            .get(&root)
            .into_iter()
            .flatten()
            .map(|&m| self.terms[m])
            .collect();
        // Group this class's selector applications by selector name,
        // deterministic order (selector name, then app index).
        let mut apps_here: Vec<(&String, TermId)> = self
            .sel_apps
            .iter()
            .filter(|(_, _, arg)| member_terms.contains(arg))
            .map(|(app, sel, _)| (sel, *app))
            .collect();
        apps_here.sort_by(|a, b| (a.0, a.1.index()).cmp(&(b.0, b.1.index())));
        let mut i = 0;
        while i < apps_here.len() {
            let sel = apps_here[i].0;
            let mut group: Vec<TermId> = Vec::new();
            while i < apps_here.len() && apps_here[i].0 == sel {
                group.push(apps_here[i].1);
                i += 1;
            }
            let path = if prefix.is_empty() {
                sel.clone()
            } else {
                format!("{prefix}\u{1}{sel}")
            };
            // Datatype-sorted application: recurse into its class (all
            // congruent applications share one class after the fixpoint).
            if let Some(&ti) = group.iter().find_map(|a| self.index.get(a)) {
                let fc = self.class_of[ti];
                self.selector_observations(fc, &path, depth - 1, visited, out);
                continue;
            }
            // Scalar application group: committed value, else base default —
            // the exact value `finish()` would pin for a wrong-constructor
            // selector over this class.
            let mut committed: Option<EvalValue> = None;
            for app in &group {
                let v = self.scalar_term_value(*app);
                if !matches!(v, EvalValue::Unknown) {
                    committed = Some(v);
                    break;
                }
            }
            let sort = self.exec.ctx.terms.sort(group[0]).clone();
            let canon = match committed {
                Some(ev) => eval_to_mv(&ev, &sort).map(|mv| dt_canonical_string(&mv)),
                None => self
                    .base_default(&sort, &mut Vec::new())
                    .map(|mv| dt_canonical_string(&mv)),
            };
            if let Some(canon) = canon {
                if out.len() < MAX_OBS {
                    out.push((path, canon));
                }
            }
        }
        visited.pop();
    }

    /// Add an implicit disequality edge between every pair of same-sort
    /// classes whose selector observations CONFLICT — a common observation
    /// path carrying different values (#dt-free-selector-funcong).
    ///
    /// Rationale: selectors are total FUNCTIONS. If two classes with
    /// conflicting observations were constructed to the same value `v`, the
    /// model would need `sel(v)` to take two different values, so every
    /// validator keying applications by argument VALUE (the independent gate's
    /// `uf_graph`) rejects it and the verdict fail-closes to `unknown`. The
    /// edge steers `construct_free`'s candidate choice away from the
    /// collision; it can never contradict a committed equality between the two
    /// classes, because committed-equal terms were already MERGED into one
    /// class by the union-find (an edge is only ever added between distinct
    /// roots). Forced classes ignore disequality edges, exactly as today.
    ///
    /// Bounded: skipped entirely when more than `MAX_OBS_ROOTS` classes carry
    /// observations (keeping today's behaviour verbatim), so the pairwise
    /// comparison cannot become a post-solve bottleneck.
    fn add_observation_disequalities(&mut self) {
        const MAX_OBS_ROOTS: usize = 256;
        let mut roots: Vec<usize> = self.members.keys().copied().collect();
        roots.sort_unstable();
        let mut obs: Vec<(usize, String, Vec<(String, String)>)> = Vec::new();
        for &r in &roots {
            let Some(sort_name) = self.class_sort_name(r) else {
                continue;
            };
            let mut o: Vec<(String, String)> = Vec::new();
            self.selector_observations(r, "", 8, &mut Vec::new(), &mut o);
            if o.is_empty() {
                continue;
            }
            o.sort();
            o.dedup();
            obs.push((r, sort_name, o));
            if obs.len() > MAX_OBS_ROOTS {
                return; // bail: keep today's behaviour on huge instances
            }
        }
        for i in 0..obs.len() {
            for j in (i + 1)..obs.len() {
                if obs[i].1 != obs[j].1 {
                    continue; // different sorts can never collide in value
                }
                if !Self::observations_conflict(&obs[i].2, &obs[j].2) {
                    continue;
                }
                let (ra, rb) = (obs[i].0, obs[j].0);
                self.diseq.entry(ra).or_default().push(rb);
                self.diseq.entry(rb).or_default().push(ra);
            }
        }
    }

    /// True when two sorted observation lists share a path with different
    /// values (merge-join; duplicates are harmless).
    fn observations_conflict(a: &[(String, String)], b: &[(String, String)]) -> bool {
        let (mut i, mut j) = (0, 0);
        while i < a.len() && j < b.len() {
            match a[i].0.cmp(&b[j].0) {
                std::cmp::Ordering::Less => i += 1,
                std::cmp::Ordering::Greater => j += 1,
                std::cmp::Ordering::Equal => {
                    // Compare every value pair for this path.
                    let path = &a[i].0;
                    let (is, js) = (i, j);
                    while i < a.len() && a[i].0 == *path {
                        i += 1;
                    }
                    while j < b.len() && b[j].0 == *path {
                        j += 1;
                    }
                    for x in &a[is..i] {
                        for y in &b[js..j] {
                            if x.1 != y.1 {
                                return true;
                            }
                        }
                    }
                }
            }
        }
        false
    }

    /// Construct every class value (constrained classes first for better
    /// disequality-freshness choices; order does not affect soundness).
    fn construct_all(&mut self) -> bool {
        let mut roots: Vec<usize> = self.members.keys().copied().collect();
        roots.sort_unstable();
        let constrained: Vec<usize> = roots
            .iter()
            .copied()
            .filter(|r| self.info.get(r).is_some_and(|ci| ci.forced.is_some()))
            .collect();
        let free: Vec<usize> = roots
            .iter()
            .copied()
            .filter(|r| self.info.get(r).is_none_or(|ci| ci.forced.is_none()))
            .collect();
        let mut path: Vec<usize> = Vec::new();
        for r in constrained.into_iter().chain(free) {
            self.construct_class(r, &mut path, MAX_DEPTH);
            debug_assert!(path.is_empty());
            if self.work_budget.exhausted() {
                return false;
            }
        }
        true
    }

    /// Construct (and memoize) the value of class `root`. `path` is the
    /// occurs-check: a class re-entered while its own value is being built is
    /// CYCLIC and has no finite value (returns `None` without memoizing at the
    /// re-entry point; the enclosing construction then fails and memoizes).
    fn construct_class(
        &mut self,
        root: usize,
        path: &mut Vec<usize>,
        fuel: u32,
    ) -> Option<ModelValue> {
        if let Some(v) = self.values.get(&root) {
            if let Some(value) = v.as_ref() {
                if !self.work_budget.charge_value(value) {
                    return None;
                }
            }
            return v.clone();
        }
        if fuel == 0 || path.contains(&root) {
            // Occurs-check hit: the value under construction would contain
            // itself. No finite completion exists along this path.
            return None;
        }
        if !self.work_budget.charge_class() {
            return None;
        }
        path.push(root);
        let result = self.construct_class_inner(root, path, fuel);
        path.pop();
        if let Some(value) = result.as_ref() {
            if !self.work_budget.charge_value(value) {
                self.values.insert(root, None);
                return None;
            }
        }
        self.values.insert(root, result.clone());
        result
    }

    fn construct_class_inner(
        &mut self,
        root: usize,
        path: &mut Vec<usize>,
        fuel: u32,
    ) -> Option<ModelValue> {
        let ci = self.info.get(&root).cloned().unwrap_or_default();
        if ci.conflicted {
            return None;
        }
        match ci.forced {
            Some(ctor) => self.construct_forced(root, &ctor, path, fuel),
            None => self.construct_free(root, &ci.excluded, path, fuel),
        }
    }

    /// Construct a class whose constructor is forced.
    fn construct_forced(
        &mut self,
        root: usize,
        ctor: &str,
        path: &mut Vec<usize>,
        fuel: u32,
    ) -> Option<ModelValue> {
        let fields = self.exec.ctx.constructor_selector_info(ctor)?;
        let member_idxs: Vec<usize> = self.members.get(&root)?.clone();
        self.precharge_forced_field_scans(ctor, fields.len(), &member_idxs)?;
        let fields = fields.to_vec();
        // Constructor-application members supply field argument terms.
        let ctor_arg_lists: Vec<Vec<TermId>> = member_idxs
            .iter()
            .filter_map(|&m| match &self.kinds[m] {
                DtTermKind::CtorApp { ctor: c, args }
                    if c == ctor && args.len() == fields.len() =>
                {
                    Some(args.clone())
                }
                _ => None,
            })
            .collect();
        // Selector applications over members, by field name.
        let member_terms: HashSet<TermId> = member_idxs.iter().map(|&m| self.terms[m]).collect();
        let mut args_out: Vec<ModelValue> = Vec::with_capacity(fields.len());
        for (fidx, (fname, fsort)) in fields.iter().enumerate() {
            let field_sel_apps: Vec<TermId> = self
                .sel_apps
                .iter()
                .filter(|(_, s, a)| s == fname && member_terms.contains(a))
                .map(|(app, _, _)| *app)
                .collect();
            if exact_datatype_sort_name(fsort).is_some() {
                let value = self.construct_forced_datatype_field(
                    fidx,
                    fsort,
                    &ctor_arg_lists,
                    &field_sel_apps,
                    path,
                    fuel,
                )?;
                args_out.push(value);
            } else {
                // Scalar field: every committed source must agree.
                let mut chosen: Option<ModelValue> = None;
                let mut sources: Vec<TermId> = Vec::new();
                for args in &ctor_arg_lists {
                    sources.push(args[fidx]);
                }
                sources.extend(field_sel_apps.iter().copied());
                for src in &sources {
                    let ev = self.scalar_term_value(*src);
                    if matches!(ev, EvalValue::Unknown) {
                        continue;
                    }
                    let Some(mv) = eval_to_mv(&ev, fsort) else {
                        // EUF extraction represents an array/sequence-sorted
                        // selector by an opaque element token.  That token is
                        // equality-class bookkeeping, not an exact container
                        // value, so it must not poison an otherwise exact
                        // constructor tree.  Treat only this sort-appropriate
                        // opaque placeholder as absent and let the canonical
                        // extensional default below own the field; observed
                        // cells and congruence are rechecked independently.
                        // Every other sort/value mismatch remains a hard
                        // fail-closed conflict.
                        if matches!(ev, EvalValue::Element(_))
                            && matches!(fsort, Sort::Array(_) | Sort::Seq(_))
                        {
                            continue;
                        }
                        return None; // unrepresentable committed value
                    };
                    match &chosen {
                        Some(prev) if dt_canonical_string(prev) != dt_canonical_string(&mv) => {
                            // Committed sources conflict: congruence is
                            // violated in the committed model; fail closed.
                            return None;
                        }
                        Some(_) => {}
                        None => chosen = Some(mv),
                    }
                }
                let v = match chosen {
                    Some(v) => v,
                    // Genuinely unconstrained scalar field: canonical default.
                    None => self.base_default(fsort, &mut Vec::new())?,
                };
                args_out.push(v);
            }
        }
        Some(ModelValue::Datatype {
            ctor: ctor.to_string(),
            args: args_out,
        })
    }

    fn construct_forced_datatype_field(
        &mut self,
        field: usize,
        sort: &Sort,
        constructor_args: &[Vec<TermId>],
        selector_apps: &[TermId],
        path: &mut Vec<usize>,
        fuel: u32,
    ) -> Option<ModelValue> {
        let field_class = constructor_args
            .iter()
            .filter_map(|args| self.index.get(&args[field]))
            .chain(selector_apps.iter().filter_map(|app| self.index.get(app)))
            .next()
            .map(|&index| self.class_of[index]);
        match field_class {
            Some(class) => self.construct_class(class, path, fuel - 1),
            None => self.base_default(sort, &mut Vec::new()),
        }
    }

    fn precharge_forced_field_scans(
        &mut self,
        ctor: &str,
        fields: usize,
        members: &[usize],
    ) -> Option<()> {
        let constructor_rows = members
            .iter()
            .filter(|&&member| {
                matches!(&self.kinds[member],
                    DtTermKind::CtorApp { ctor: candidate, args }
                        if candidate == ctor && args.len() == fields)
            })
            .count();
        self.work_budget
            .charge_field_scans(fields, self.sel_apps.len(), constructor_rows)
            .then_some(())
    }

    /// Construct a FREE class: the well-founded default, distinct from every
    /// already-constructed disequality neighbour and avoiding excluded root
    /// constructors.
    fn construct_free(
        &mut self,
        root: usize,
        excluded: &[String],
        path: &mut Vec<usize>,
        fuel: u32,
    ) -> Option<ModelValue> {
        let sort_name = self.class_sort_name(root)?;
        let mut used: HashSet<String> = HashSet::default();
        if let Some(neighbors) = self.diseq.get(&root) {
            for nb in neighbors.clone() {
                if let Some(Some(v)) = self.values.get(&nb) {
                    if !self.work_budget.charge_render(v) {
                        return None;
                    }
                    let canonical = dt_canonical_string(v);
                    if !self.work_budget.charge_bytes(canonical.len()) {
                        return None;
                    }
                    used.insert(canonical);
                }
            }
        }
        let budget = used.len() + 16;
        for k in 0..budget {
            if !self.work_budget.charge_candidate(k) {
                return None;
            }
            let cand = self.free_candidate(&sort_name, k, excluded)?;
            // Honor pinned fields (#dt-pin-selector). `free_candidate` fills a
            // constructor's scalar fields with base defaults; when a member of
            // this class has a selector application `(sel member)` the raw model
            // COMMITTED a value to (an asserted `(= (sel member) v)`), that field
            // is pinned and the base default would falsify the assertion. This
            // is exactly the case where distinctness forces a free class onto a
            // non-base constructor (`x=nil` taken, so `y` must be `cons ..`): the
            // pinned `hd` must be honored, not defaulted to 0 (GAP-2).
            // Datatype fields observed through a datatype-sorted selector
            // application recurse into that application's class, so a nested
            // chain (`(hd (tl x)) = 3` under a `cons` candidate for `x`'s
            // class) projects the same value the inner class pins
            // (#dt-free-selector-funcong).
            let cand = self.apply_committed_fields(root, cand, path, fuel);
            if self.work_budget.exhausted() {
                return None;
            }
            if !self.work_budget.charge_render(&cand) {
                return None;
            }
            if !used.contains(&dt_canonical_string(&cand)) {
                return Some(cand);
            }
        }
        None
    }

    /// Overwrite the OBSERVED fields of a free-class constructor candidate
    /// with the values the model already carries for them (#dt-pin-selector,
    /// #dt-free-selector-funcong).
    ///
    /// A free class defaults its constructor fields (via `free_candidate`) to
    /// the base value; but a field read by a committed selector application is
    /// PINNED by an assertion, so the pinned value — not the default — must be
    /// used, otherwise the constructed model falsifies that selector equality
    /// and validation degrades a genuinely-SAT query to `unknown`. Scalar
    /// fields take the committed model scalar of a `(sel member)` application;
    /// a DATATYPE field observed through a datatype-sorted selector
    /// application recurses into that application's class (occurs-check /
    /// fuel-bounded via `construct_class`, exactly like `construct_forced`'s
    /// field resolution), so the projected field and the application's own
    /// class pin agree; an unobserved or unconstructible (cyclic) field keeps
    /// `free_candidate`'s well-founded default (today's behaviour). SOUND: the
    /// value written is exactly what the raw model already committed for the
    /// selector application (or the observed class's constructed value), and
    /// the full validation pipeline re-checks every assertion under the
    /// result, so a mismatched/conflicting commit degrades to `unknown`
    /// (fail-closed), never a wrong SAT. Congruent applications that committed
    /// DIFFERENT values leave the candidate's default in place (the
    /// disagreement makes the model fail closed at validation just as before).
    fn apply_committed_fields(
        &mut self,
        root: usize,
        mv: ModelValue,
        path: &mut Vec<usize>,
        fuel: u32,
    ) -> ModelValue {
        let ModelValue::Datatype { ctor, mut args } = mv else {
            return mv;
        };
        let Some(fields) = self.exec.ctx.constructor_selector_info(&ctor) else {
            return ModelValue::Datatype { ctor, args };
        };
        if !self
            .work_budget
            .charge_field_scans(fields.len(), self.sel_apps.len(), 0)
        {
            return ModelValue::Datatype { ctor, args };
        }
        let fields = fields.to_vec();
        let member_terms: HashSet<TermId> = self
            .members
            .get(&root)
            .into_iter()
            .flatten()
            .map(|&m| self.terms[m])
            .collect();
        for (fidx, (fname, fsort)) in fields.iter().enumerate() {
            // A datatype field observed through a dt-sorted selector
            // application resolves to that application's class value.
            if exact_datatype_sort_name(fsort).is_some() {
                let field_class: Option<usize> = self
                    .sel_apps
                    .iter()
                    .filter(|(_, s, a)| s == fname && member_terms.contains(a))
                    .find_map(|(app, _, _)| self.index.get(app).copied())
                    .map(|ti| self.class_of[ti]);
                if let Some(fc) = field_class {
                    if let Some(v) = self.construct_class(fc, path, fuel.saturating_sub(1)) {
                        if let Some(slot) = args.get_mut(fidx) {
                            *slot = v;
                        }
                    }
                    // None (cyclic / unconstructible): keep the candidate's
                    // well-founded default — today's behaviour, fail-closed at
                    // validation if actually inconsistent.
                }
                continue;
            }
            let mut committed: Option<ModelValue> = None;
            for (app, sel, arg) in &self.sel_apps {
                if sel != fname || !member_terms.contains(arg) {
                    continue;
                }
                let ev = self.scalar_term_value(*app);
                if matches!(ev, EvalValue::Unknown) {
                    continue;
                }
                let Some(cmv) = eval_to_mv(&ev, fsort) else {
                    continue;
                };
                match &committed {
                    // Congruent apps committed different values: leave the
                    // default; validation fails the model closed.
                    Some(prev) if dt_canonical_string(prev) != dt_canonical_string(&cmv) => {
                        committed = None;
                        break;
                    }
                    Some(_) => {}
                    None => committed = Some(cmv),
                }
            }
            if let (Some(cmv), Some(slot)) = (committed, args.get_mut(fidx)) {
                *slot = cmv;
            }
        }
        ModelValue::Datatype { ctor, args }
    }

    /// The k-th candidate value of datatype `dt_name` (deterministic,
    /// pairwise-distinct enumeration), skipping excluded root constructors.
    fn free_candidate(
        &mut self,
        dt_name: &str,
        k: usize,
        excluded: &[String],
    ) -> Option<ModelValue> {
        let ctors = self.exec.ctx.datatype_constructors(dt_name)?;
        if !self
            .work_budget
            .charge_constructor_filter(ctors.len(), excluded.len())
        {
            return None;
        }
        let allowed: Vec<&String> = ctors.iter().filter(|c| !excluded.contains(c)).collect();
        if allowed.is_empty() {
            return None;
        }
        // Prefer well-founded ordering: nullary constructors first.
        let mut nullary: Vec<&String> = Vec::new();
        let mut non_nullary: Vec<&String> = Vec::new();
        for c in &allowed {
            if self
                .exec
                .ctx
                .constructor_selector_info(c)
                .map_or(true, |f| f.is_empty())
            {
                nullary.push(c);
            } else {
                non_nullary.push(c);
            }
        }
        if k < nullary.len() {
            return Some(ModelValue::Datatype {
                ctor: nullary[k].clone(),
                args: Vec::new(),
            });
        }
        let mut j = k - nullary.len();
        // A constructor can be perfectly inhabitable without carrying one of
        // the variation sources below.  In particular, an array/sequence field
        // has a canonical extensional default even though this completion lane
        // deliberately does not invent distinct array/sequence values.  Give
        // every such constructor its one exact base candidate before declaring
        // the finite enumeration exhausted.  Different constructors remain
        // pairwise-distinct by constructor identity; a second class requiring
        // another value of the same constructor still fails closed.
        for c in &non_nullary {
            let fields = self.exec.ctx.constructor_selector_info(c)?;
            let has_direct_recursion = fields
                .iter()
                .any(|(_, fs)| exact_datatype_sort_name(fs) == Some(dt_name));
            let has_variable_scalar = fields.iter().any(|(_, fs)| {
                matches!(fs, Sort::Int | Sort::Real | Sort::String | Sort::BitVec(_))
            });
            if has_direct_recursion || has_variable_scalar {
                continue;
            }
            let args = fields
                .iter()
                .map(|(_, field_sort)| self.base_default(field_sort, &mut Vec::new()))
                .collect::<Option<Vec<_>>>();
            let Some(args) = args else {
                continue;
            };
            if j == 0 {
                return Some(ModelValue::Datatype {
                    ctor: (*c).clone(),
                    args,
                });
            }
            j -= 1;
        }
        // Variation constructor: prefer one with a directly-recursive field
        // (unbounded depth chain), else one with a variable scalar field.
        let mut visited = Vec::new();
        for c in &non_nullary {
            let fields = self.exec.ctx.constructor_selector_info(c)?;
            // Directly-recursive field?
            if let Some(rec_idx) = fields
                .iter()
                .position(|(_, fs)| exact_datatype_sort_name(fs) == Some(dt_name))
            {
                let base =
                    self.base_default(&Sort::Uninterpreted(dt_name.to_string()), &mut visited)?;
                let mut chain = base;
                for _ in 0..=j {
                    let mut args = Vec::with_capacity(fields.len());
                    for (i, (_, fs)) in fields.iter().enumerate() {
                        if i == rec_idx {
                            args.push(chain.clone());
                        } else {
                            args.push(self.base_default(fs, &mut Vec::new())?);
                        }
                    }
                    chain = ModelValue::Datatype {
                        ctor: (*c).clone(),
                        args,
                    };
                }
                return Some(chain);
            }
            // Variable scalar field?
            if let Some(var_idx) = fields.iter().position(|(_, fs)| {
                matches!(fs, Sort::Int | Sort::Real | Sort::String) || matches!(fs, Sort::BitVec(_))
            }) {
                return self.variable_scalar_candidate(c, fields, var_idx, j);
            }
        }
        // Finite enumeration exhausted.
        None
    }

    fn variable_scalar_candidate(
        &self,
        ctor: &str,
        fields: &[(String, Sort)],
        var_idx: usize,
        variant: usize,
    ) -> Option<ModelValue> {
        let (_, sort) = &fields[var_idx];
        let varied = match sort {
            Sort::Int => ModelValue::Int(BigInt::from(variant as u64)),
            Sort::Real => ModelValue::Real(BigRational::from(BigInt::from(variant as u64))),
            Sort::String => ModelValue::Str(format!("v{variant}")),
            Sort::BitVec(bv) => {
                // Only 2^width distinct values exist.
                if bv.width < 63 && (variant as u64) >= (1u64 << bv.width) {
                    return None;
                }
                ModelValue::bitvec(BigInt::from(variant as u64), bv.width)
            }
            _ => return None,
        };
        let mut args = Vec::with_capacity(fields.len());
        for (index, (_, field_sort)) in fields.iter().enumerate() {
            if index == var_idx {
                args.push(varied.clone());
            } else {
                args.push(self.base_default(field_sort, &mut Vec::new())?);
            }
        }
        Some(ModelValue::Datatype {
            ctor: ctor.to_string(),
            args,
        })
    }

    /// The canonical, WELL-FOUNDED base default value of any supported sort:
    /// scalars use the standard completion defaults; a datatype prefers a
    /// nullary constructor, else a constructor whose fields do not revisit a
    /// datatype already on the recursion path (so the value is finite by
    /// construction). `None` for sorts this phase cannot default (FP, ...).
    fn base_default(&self, sort: &Sort, visited: &mut Vec<String>) -> Option<ModelValue> {
        match sort {
            Sort::Bool => Some(ModelValue::Bool(false)),
            Sort::Int => Some(ModelValue::Int(BigInt::from(0))),
            Sort::Real => Some(ModelValue::Real(BigRational::from(BigInt::from(0)))),
            Sort::BitVec(bv) => Some(ModelValue::bitvec(BigInt::from(0), bv.width)),
            Sort::String => Some(ModelValue::Str(String::new())),
            Sort::Seq(_) => Some(ModelValue::Seq(Vec::new())),
            Sort::Array(arr) => {
                let default = self.base_default(&arr.element_sort, visited)?;
                Some(ModelValue::Array(Box::new(ArrayValue {
                    default,
                    store: Vec::new(),
                })))
            }
            _ => {
                let dt_name = exact_datatype_sort_name(sort)?;
                self.base_default_datatype(dt_name, visited)
            }
        }
    }

    fn base_default_datatype(
        &self,
        dt_name: &str,
        visited: &mut Vec<String>,
    ) -> Option<ModelValue> {
        if visited.iter().any(|s| s == dt_name) {
            return None; // would not be well-founded along this path
        }
        let ctors = self.exec.ctx.datatype_constructors(dt_name)?;
        // Nullary constructor: the smallest inhabitant.
        for c in ctors {
            if self
                .exec
                .ctx
                .constructor_selector_info(c)
                .map_or(true, |f| f.is_empty())
            {
                return Some(ModelValue::Datatype {
                    ctor: c.clone(),
                    args: Vec::new(),
                });
            }
        }
        visited.push(dt_name.to_string());
        // First constructor whose fields all construct (recursively
        // well-founded thanks to the visited set).
        let mut result = None;
        'ctors: for c in ctors {
            let Some(fields) = self.exec.ctx.constructor_selector_info(c) else {
                continue;
            };
            let mut args = Vec::with_capacity(fields.len());
            for (_, fs) in fields {
                match self.base_default(fs, visited) {
                    Some(v) => args.push(v),
                    None => continue 'ctors,
                }
            }
            result = Some(ModelValue::Datatype {
                ctor: c.clone(),
                args,
            });
            break;
        }
        visited.pop();
        result
    }

    /// The committed scalar value of a term (constructor argument or selector
    /// application) under the RAW model — never consults construction pins
    /// (they are committed only after building completes).
    fn scalar_term_value(&self, t: TermId) -> EvalValue {
        let v = self.exec.evaluate_term(self.model, t);
        if !matches!(v, EvalValue::Unknown) {
            return v;
        }
        if matches!(self.exec.ctx.terms.get(t), TermData::Const(_)) {
            return EvalValue::Unknown; // a constant evaluates directly or not at all
        }
        self.exec.lookup_term_value(self.model, t)
    }

    /// Produce the constructed ground values and evaluation pins to commit
    /// into the model: `(ground, pins)` where `ground` maps datatype-sorted
    /// terms to their structured values and `pins` carries every evaluation
    /// pin (canonical Elements, scalar selector projections, tester Bools).
    fn finish(&mut self) -> Option<(Vec<(TermId, ModelValue)>, Vec<(TermId, EvalValue)>)> {
        // All pins are computed before any is inserted, so committed lookups
        // cannot read half-committed state.
        let mut pins = self.finish_scalar_selector_pins()?;
        pins.extend(self.finish_tester_pins()?);
        let ground = self.finish_ground_values(&mut pins)?;
        Some((ground, pins))
    }

    fn scalar_selector_groups(&self) -> HashMap<(String, usize), Vec<TermId>> {
        let mut groups: HashMap<(String, usize), Vec<TermId>> = HashMap::default();
        for (app, sel, arg) in &self.sel_apps {
            if self.index.contains_key(app) {
                continue; // datatype-sorted selector app: valued via its class
            }
            let Some(&ai) = self.index.get(arg) else {
                continue;
            };
            let root = self.class_of[ai];
            groups.entry((sel.clone(), root)).or_default().push(*app);
        }
        groups
    }

    fn finish_scalar_selector_pins(&mut self) -> Option<Vec<(TermId, EvalValue)>> {
        let mut pins = Vec::new();
        let mut groups = self.scalar_selector_groups();
        let mut group_keys: Vec<(String, usize)> = groups.keys().cloned().collect();
        group_keys.sort();
        for key in group_keys {
            let mut apps = groups.remove(&key).unwrap_or_default();
            apps.sort_by_key(|t| t.index());
            apps.dedup();
            let Some(pin) = self.scalar_selector_group_pin(&key.0, key.1, &apps)? else {
                continue;
            };
            for app in apps {
                if !self.work_budget.charge_scalar_pin(&pin) {
                    return None;
                }
                pins.push((app, pin.clone()));
            }
        }
        Some(pins)
    }

    fn scalar_selector_group_pin(
        &mut self,
        selector: &str,
        root: usize,
        apps: &[TermId],
    ) -> Option<Option<EvalValue>> {
        let Some(Some(ModelValue::Datatype { ctor, args })) = self.values.get(&root) else {
            return Some(None);
        };
        let selectors = self.exec.ctx.constructor_selectors(ctor).unwrap_or(&[]);
        if let Some(field) = selectors
            .iter()
            .position(|candidate| candidate == selector)
            .and_then(|index| args.get(index))
        {
            if !self.work_budget.charge_value(field) {
                return None;
            }
            let pin = mv_to_eval(field);
            // `EvalValue` cannot carry an array and the active opaque lane
            // deliberately does not admit sequence-valued scalar pins.  Do
            // not let one such selector discard the completed datatype model
            // for every independent component: retain the exact structured
            // field in `dt_ground`, where the independent gate projects it
            // from the constructor value itself, and omit only the lossy
            // evaluator pin.  No value is coerced or defaulted here.
            return Some(
                matches!(
                    &pin,
                    EvalValue::Bool(_)
                        | EvalValue::BitVec { .. }
                        | EvalValue::Rational(_)
                        | EvalValue::Element(_)
                        | EvalValue::String(_)
                )
                .then_some(pin),
            );
        }
        for &app in apps {
            let value = self.scalar_term_value(app);
            if !matches!(value, EvalValue::Unknown) {
                return self
                    .work_budget
                    .charge_scalar_pin(&value)
                    .then_some(Some(value));
            }
        }
        let Some(&first) = apps.first() else {
            return Some(None);
        };
        let sort = self.exec.ctx.terms.sort(first).clone();
        let Some(value) = self.base_default(&sort, &mut Vec::new()) else {
            return Some(None);
        };
        if !self.work_budget.charge_value(&value) {
            return None;
        }
        let pin = mv_to_eval(&value);
        Some(
            matches!(
                &pin,
                EvalValue::Bool(_)
                    | EvalValue::BitVec { .. }
                    | EvalValue::Rational(_)
                    | EvalValue::Element(_)
                    | EvalValue::String(_)
            )
            .then_some(pin),
        )
    }

    fn finish_tester_pins(&mut self) -> Option<Vec<(TermId, EvalValue)>> {
        let mut pins = Vec::new();
        for (app, ctor, arg) in &self.tester_apps {
            let Some(&ai) = self.index.get(arg) else {
                continue;
            };
            let root = self.class_of[ai];
            if let Some(Some(ModelValue::Datatype { ctor: assigned, .. })) = self.values.get(&root)
            {
                if !self.work_budget.charge_bytes(1) {
                    return None;
                }
                pins.push((*app, EvalValue::Bool(assigned == ctor)));
            }
        }
        Some(pins)
    }

    fn finish_ground_values(
        &mut self,
        pins: &mut Vec<(TermId, EvalValue)>,
    ) -> Option<Vec<(TermId, ModelValue)>> {
        let mut ground: Vec<(TermId, ModelValue)> = Vec::new();
        let mut roots: Vec<usize> = self.values.keys().copied().collect();
        roots.sort_unstable();
        for root in roots {
            let Some(Some(value)) = self.values.get(&root) else {
                continue;
            };
            let canon = if dt_canonical_pin_supported(value) {
                if !self.work_budget.charge_render(value) {
                    return None;
                }
                Some(dt_canonical_string(value))
            } else {
                None
            };
            for &m in self.members.get(&root).into_iter().flatten() {
                let t = self.terms[m];
                if !self.work_budget.charge_value(value) {
                    return None;
                }
                ground.push((t, value.clone()));
                if let Some(canon) = &canon {
                    if !self.work_budget.charge_bytes(canon.len()) {
                        return None;
                    }
                    pins.push((t, EvalValue::Element(canon.clone())));
                }
            }
        }
        Some(ground)
    }
}

fn exact_datatype_sort_name(sort: &Sort) -> Option<&str> {
    match sort {
        Sort::Datatype(datatype) => Some(&datatype.name),
        Sort::Uninterpreted(name) => Some(name),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_frontend::parse;

    fn loaded(input: &str) -> Executor {
        let commands = parse(input).expect("valid SMT-LIB fixture");
        let mut exec = Executor::new();
        for command in &commands {
            assert!(
                exec.execute(command).expect("fixture executes").is_none(),
                "fixture must not contain a query"
            );
        }
        exec
    }

    #[test]
    fn singleton_datatype_disequality_cannot_receive_two_values() {
        let exec = loaded(
            r#"
                (declare-datatypes ((Only 0)) (((only))))
                (declare-fun f ((_ BitVec 1)) Only)
                (declare-fun g ((_ BitVec 1)) Only)
                (assert (not (= (f #b0) (g #b0))))
            "#,
        );
        let mut model = Model::empty();
        assert!(
            exec.dt_collect(&model, &[]).is_some(),
            "the singleton fixture must enter datatype construction"
        );

        let mut apps: HashMap<String, TermId> = HashMap::default();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack = exec.ctx.assertions.clone();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            match exec.ctx.terms.get(term) {
                TermData::App(sym, args) => {
                    if matches!(sym.name(), "f" | "g") {
                        apps.insert(sym.name().to_string(), term);
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
                _ => {}
            }
        }
        let f = *apps.get("f").expect("f application");
        let g = *apps.get("g").expect("g application");

        let constructed = exec.construct_total_datatype_model(&mut model, &[]);
        let app_values: Vec<_> = [f, g]
            .into_iter()
            .filter_map(|term| model.dt_ground.get(&term))
            .collect();
        assert!(
            constructed > 0 && !app_values.is_empty(),
            "the admitted fixture must produce concrete ground evidence"
        );
        assert!(
            app_values.len() == 1
                || (app_values.len() == 2
                    && dt_canonical_string(app_values[0]) == dt_canonical_string(app_values[1])),
            "a singleton sort cannot supply two distinct application values: {app_values:?}"
        );
    }

    #[test]
    fn datatype_valued_let_blocks_same_sort_opaque_completion() {
        let mut exec = loaded(
            r#"
                (declare-datatype D ((D_zero) (D_one)))
                (declare-fun opaque ((_ BitVec 1)) D)
                (assert (= (opaque #b0) D_zero))
            "#,
        );
        let mut seen = HashSet::default();
        let mut stack = exec.ctx.assertions.clone();
        let mut opaque = None;
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            match exec.ctx.terms.get(term) {
                TermData::App(symbol, args) => {
                    if symbol.name() == "opaque" {
                        opaque = Some(term);
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(condition, then_term, else_term) => {
                    stack.extend([*condition, *then_term, *else_term]);
                }
                _ => {}
            }
        }
        let opaque = opaque.expect("fixture must contain the datatype-valued UF application");
        // Parser elaboration normally substitutes source `let`s.  Inject the
        // low-level form adversarially because internal rewrites can still
        // construct it and the collector must fail closed for every TermData.
        let opaque_let = exec.ctx.terms.mk_let(Vec::new(), opaque);
        let extra_root = exec.ctx.terms.mk_eq(opaque_let, opaque);

        let preflight = exec
            .preflight_opaque_dt_collection(&[extra_root])
            .expect("bounded adversarial fixture must pass resource preflight");
        let (_, _, opaque_apps, names, members, strict) = preflight.into_parts();
        assert!(strict, "fixture must exercise strict opaque collection");
        assert!(opaque_apps.contains(&opaque));
        let retained = exec
            .opaque_dt_constructible_names(&[extra_root], &names, &members, &opaque_apps)
            .expect("bounded datatype inventory must classify exactly");
        assert!(
            !retained.contains("D"),
            "an unsupported datatype-valued let must block its same-sort component: {retained:?}"
        );
        assert!(
            exec.dt_collect(&Model::empty(), &[extra_root]).is_none(),
            "collection must fail closed instead of omitting the datatype-valued let"
        );
    }

    #[test]
    fn opaque_completion_retains_structured_datatype_for_gate_projection() {
        let exec = loaded(
            r#"
                (declare-datatypes
                    ((PbLit 0) (PbTerm 0) (PbObjective 0) (EvalError 0) (Result 0))
                    (
                        ((PbLit_mk
                            (PbLit_var (_ BitVec 32))
                            (PbLit_negated Bool)))
                        ((PbTerm_mk
                            (PbTerm_coeff (_ BitVec 128))
                            (PbTerm_lits (Array (_ BitVec 64) PbLit))))
                        ((PbObjective_empty)
                         (PbObjective_mk
                            (PbObjective_terms (Array (_ BitVec 64) PbTerm))))
                        ((EvalError_overflow))
                        ((Result_ok (Result_value (_ BitVec 128)))
                         (Result_err (Result_error EvalError)))
                    ))
                (declare-const objective PbObjective)
                (declare-const term PbTerm)
                (declare-const assignment (Array (_ BitVec 64) Bool))
                (declare-const result Result)
                (declare-fun checked
                    ((Array (_ BitVec 64) PbTerm) (Array (_ BitVec 64) Bool))
                    Result)
                (assert (= result
                    (checked (PbObjective_terms objective) assignment)))
                (assert ((_ is PbObjective_mk) objective))
                (assert (= term
                    (select (PbObjective_terms objective) #x0000000000000000)))
            "#,
        );
        let preflight = exec
            .preflight_opaque_dt_collection(&[])
            .expect("bounded opaque fixture must pass preflight");
        let (_, _, opaque_apps, names, members, strict) = preflight.into_parts();
        assert!(strict, "the fixture must exercise strict opaque collection");
        let retained = exec
            .opaque_dt_constructible_names(&[], &names, &members, &opaque_apps)
            .expect("bounded schemas must classify exactly");

        assert!(
            retained.contains("Result") && retained.contains("EvalError"),
            "the unrelated scalar Result component must remain constructible: {retained:?}"
        );
        assert!(retained.contains("PbLit"));
        assert!(
            retained.contains("PbTerm"),
            "an exactly typed canonical array select retains its structured datatype result: \
             {retained:?}"
        );
        assert!(
            retained.contains("PbObjective"),
            "an array carrier is an extensional boundary, so its owner remains constructible: \
             {retained:?}"
        );

        let probe_model = Model::empty();
        let mut probe = exec
            .dt_collect(&probe_model, &[])
            .expect("the classified fixture must collect");
        probe.force_constructors();
        probe.add_observation_disequalities();
        assert!(probe.construct_all(), "bounded fixture must construct");
        let class_schemas: Vec<String> = probe
            .members
            .keys()
            .map(|root| {
                let sort_name = probe.class_sort_name(*root);
                let constructors: Vec<String> = sort_name
                    .as_ref()
                    .and_then(|name| exec.ctx.datatype_constructors(name))
                    .into_iter()
                    .flatten()
                    .map(|constructor| {
                        format!(
                            "{constructor}:{:?}",
                            exec.ctx.constructor_selector_info(constructor)
                        )
                    })
                    .collect();
                let members: Vec<_> = probe
                    .members
                    .get(root)
                    .into_iter()
                    .flatten()
                    .map(|member| {
                        let term = probe.terms[*member];
                        (term, exec.ctx.terms.sort(term).clone())
                    })
                    .collect();
                format!("root={root} sort={sort_name:?} ctors={constructors:?} members={members:?}")
            })
            .collect();
        let mut assertion_seen = HashSet::default();
        let mut assertion_stack = exec.ctx.assertions.clone();
        let mut assertion_rows = Vec::new();
        while let Some(term) = assertion_stack.pop() {
            if !assertion_seen.insert(term) {
                continue;
            }
            assertion_rows.push(format!(
                "{term:?} sort={:?} data={:?}",
                exec.ctx.terms.sort(term),
                exec.ctx.terms.get(term)
            ));
            match exec.ctx.terms.get(term) {
                TermData::App(_, args) => assertion_stack.extend(args.iter().copied()),
                TermData::Not(inner) => assertion_stack.push(*inner),
                TermData::Ite(condition, then_term, else_term) => {
                    assertion_stack.extend([*condition, *then_term, *else_term]);
                }
                _ => {}
            }
        }
        let (objective_root, objective_ctor, objective_selector) = probe
            .members
            .keys()
            .find_map(|root| {
                let sort_name = probe.class_sort_name(*root)?;
                let constructors = exec.ctx.datatype_constructors(&sort_name)?;
                constructors.iter().find_map(|constructor| {
                    let fields = exec.ctx.constructor_selector_info(constructor)?;
                    let [(selector, Sort::Array(_))] = fields else {
                        return None;
                    };
                    Some((*root, constructor.clone(), selector.clone()))
                })
            })
            .unwrap_or_else(|| {
                panic!(
                    "collector must retain the unique one-array-field class: names={names:?} \
                     retained={retained:?} classes={class_schemas:#?} \
                     assertions={assertion_rows:#?}"
                )
            });
        let objective_sources: Vec<_> = probe
            .sel_apps
            .iter()
            .filter(|(_, selector, argument)| {
                selector == &objective_selector
                    && probe
                        .index
                        .get(argument)
                        .is_some_and(|index| probe.class_of[*index] == objective_root)
            })
            .map(|(app, _, _)| (*app, probe.scalar_term_value(*app)))
            .collect();
        assert!(
            matches!(
                probe.values.get(&objective_root),
                Some(Some(ModelValue::Datatype { ctor, args }))
                    if ctor == &objective_ctor
                        && matches!(args.as_slice(), [ModelValue::Array(_)])
            ),
            "objective class must construct exactly: forced={:?} conflicted={} sources={:?} value={:?}",
            probe
                .info
                .get(&objective_root)
                .and_then(|info| info.forced.as_deref()),
            probe
                .info
                .get(&objective_root)
                .is_some_and(|info| info.conflicted),
            objective_sources,
            probe.values.get(&objective_root),
        );

        let mut model = Model::empty();
        assert!(
            exec.construct_total_datatype_model(&mut model, &[]) > 0,
            "structured schema must not discard unrelated opaque completion"
        );
        let (objective, objective_value) = model
            .dt_ground
            .iter()
            .find(|(_, value)| {
                matches!(
                    value,
                    ModelValue::Datatype { ctor, args }
                        if ctor == &objective_ctor
                            && matches!(args.as_slice(), [ModelValue::Array(_)])
                )
            })
            .unwrap_or_else(|| {
                panic!(
                    "objective must retain its exact constructor/array value: {:?}",
                    model.dt_ground
                )
            });
        assert!(
            matches!(
                objective_value,
                ModelValue::Datatype { ctor, args }
                    if ctor == &objective_ctor
                        && matches!(args.as_slice(), [ModelValue::Array(_)])
            ),
            "objective must retain its exact constructor/array value: {:?}",
            objective_value
        );
        assert!(
            !model
                .dt_pins
                .keys()
                .any(|term| matches!(exec.ctx.terms.sort(*term), Sort::Array(_))),
            "an array term has no lossless EvalValue pin; the structured gate path owns it"
        );
        assert!(
            !model.dt_pins.contains_key(objective),
            "an array-containing datatype has no scalar canonical pin; its exact dt_ground tree owns it"
        );
        let pbterm_values: Vec<_> = model
            .dt_ground
            .iter()
            .filter(|(term, _)| {
                exec.datatype_sort_name(exec.ctx.terms.sort(**term))
                    .as_deref()
                    == Some("PbTerm")
            })
            .map(|(_, value)| value)
            .collect();
        assert!(
            pbterm_values.len() >= 2
                && pbterm_values.iter().all(|value| {
                    matches!(
                        value,
                        ModelValue::Datatype { ctor, args }
                            if ctor == "PbTerm_mk"
                                && matches!(
                                    args.as_slice(),
                                    [ModelValue::BitVec { width: 128, .. }, ModelValue::Array(_)]
                                )
                    )
                })
                && pbterm_values
                    .windows(2)
                    .all(|pair| dt_canonical_string(pair[0]) == dt_canonical_string(pair[1])),
            "the seed and canonical select must share one exact constructor/arity value: \
             {pbterm_values:?}"
        );
    }

    #[test]
    fn single_constructor_array_owner_flattens_to_validated_field_representation() {
        let mut exec = loaded(
            r#"
                (declare-datatypes
                    ((PbLit 0) (PbTerm 0) (PbObjective 0) (Result 0))
                    (
                        ((PbLit_mk
                            (PbLit_var (_ BitVec 32))
                            (PbLit_negated Bool)))
                        ((PbTerm_mk
                            (PbTerm_coeff (_ BitVec 128))
                            (PbTerm_lits (Array (_ BitVec 64) PbLit))))
                        ((PbObjective_mk
                            (PbObjective_terms (Array (_ BitVec 64) PbTerm))))
                        ((Result_ok (Result_value (_ BitVec 128)))
                         (Result_err))
                    ))
                (declare-const objective PbObjective)
                (declare-const assignment (Array (_ BitVec 64) Bool))
                (declare-const result Result)
                (declare-fun checked
                    ((Array (_ BitVec 64) PbTerm) (Array (_ BitVec 64) Bool))
                    Result)
                (assert (= result
                    (checked (PbObjective_terms objective) assignment)))
            "#,
        );

        let (owner_name, field_sort) = exec
            .ctx
            .datatype_iter()
            .find_map(|(name, constructors)| {
                let [constructor] = constructors else {
                    return None;
                };
                let fields = exec.ctx.constructor_selector_info(constructor)?;
                let [(_, field_sort @ Sort::Array(_))] = fields else {
                    return None;
                };
                Some((name.to_string(), field_sort.clone()))
            })
            .expect("fixture must contain one single-array-field datatype");

        let mut seen = HashSet::default();
        let mut stack = exec.ctx.assertions.clone();
        let mut saw_owner = false;
        let mut saw_exact_field = false;
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            saw_owner |= matches!(
                exec.ctx.terms.sort(term),
                Sort::Uninterpreted(name) if name == &owner_name
            );
            saw_exact_field |= exec.ctx.terms.sort(term) == &field_sort;
            match exec.ctx.terms.get(term) {
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(condition, then_term, else_term) => {
                    stack.extend([*condition, *then_term, *else_term]);
                }
                _ => {}
            }
        }
        assert!(
            !saw_owner && saw_exact_field,
            "single-constructor lowering must validate the exact field array, not fabricate an \
             absent {owner_name} owner (owner={saw_owner}, field={saw_exact_field})"
        );

        let probe_model = Model::empty();
        let probe = exec
            .dt_collect(&probe_model, &[])
            .expect("flattened opaque fixture must still collect its Result component");
        assert!(
            probe
                .members
                .keys()
                .all(|root| probe.class_sort_name(*root).as_deref() != Some(&owner_name)),
            "completion must not synthesize a datatype owner absent from the lowered query"
        );

        let result = exec.check_sat().expect("tiny flattened fixture must solve");
        assert_eq!(result, crate::executor_types::SolveResult::Sat);
        assert!(
            exec.last_model_validated,
            "the exact flattened field-array representation must receive sealed independent \
             model-validation evidence"
        );
    }

    #[test]
    fn structured_ground_finalization_exhaustion_is_atomic() {
        let exec = loaded(
            r#"
                (declare-datatype Box
                    ((Box_empty)
                     (Box_mk (Box_payload (Array Int Int)))))
                (declare-const input (Array Int Int))
                (declare-fun opaque_box ((Array Int Int)) Box)
                (assert ((_ is Box_mk) (opaque_box input)))
            "#,
        );
        let model = Model::empty();
        {
            let mut builder = exec
                .dt_collect(&model, &[])
                .expect("bounded opaque fixture must enter construction");
            assert!(!builder.terms.is_empty());
            builder.force_constructors();
            builder.add_observation_disequalities();
            assert!(builder.construct_all());

            // Exhaust exactly at the first retained ground clone. `finish`
            // assembles into local vectors and must return no partial result;
            // the caller cannot mutate the model until all charges succeed.
            builder.work_budget = OpaqueDtConstructionBudget::with_limit(0);
            assert!(builder.finish().is_none());
        }
        assert!(model.dt_ground.is_empty());
        assert!(model.dt_pins.is_empty());
    }
}
