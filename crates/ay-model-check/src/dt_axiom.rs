// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-INDEPENDENT datatype + Boolean TAUTOLOGY checker for the independent
//! model-check gate.
//!
//! The gate (`confirm_model`) re-evaluates each asserted formula under the model
//! and degrades a `Sat` to `Unknown` on any assertion it computes to
//! `Bool(false)` — or that it cannot ground-evaluate at all (a coverage gap).
//! But the eager DT+BV route injects DATATYPE-CONGRUENCE / tester / selector
//! axioms (e.g. `(= (is-Ctor Y) (= Y (Ctor (sel_i Y)..)))`, the `= through ite`
//! variants, and selector-over-constructor round-trips
//! `(= a (sel_i (Ctor .. a ..)))`) that are TAUTOLOGIES — they hold in EVERY
//! model — yet whose datatype-carrying-array operands (or unpinned scalar
//! leaves) the model evaluator cannot canonicalize / pin, so it either wrongly
//! computes them `Bool(false)` OR leaves them unevaluable, and the gate would
//! reject a genuine `Sat`.
//!
//! [`dt_axiom_bool`] proves such an assertion `true` from the FREE datatype +
//! Boolean theory ALONE — selector/tester-over-constructor reduction,
//! constructor injectivity/distinctness, reflexivity, Boolean folding, and a
//! branch-agnostic `ite` rule — with NO model and NO array canonicalization. A
//! `Some(true)` is therefore a PROOF the assertion is satisfied in every model,
//! so the gate may CONFIRM it (skip `ModelViolates`, or treat a coverage gap as
//! satisfied). `Some(false)`/`None` change nothing (the gate keeps its
//! decision), so a genuine violation is NEVER suppressed and no wrong `Sat` can
//! be confirmed. Mirrors the same sound guard in ay-dpll's strict-oracle
//! `check_definitive_false`.
//!
//! DATATYPE RESOLUTION. Some front-ends abstract algebraic datatypes to
//! `Sort::Uninterpreted(name)` (the eager DtAufbv path), so a constructor
//! application like `(Vec_mk ..)` carries `Sort::Uninterpreted("Vec")` rather
//! than `Sort::Datatype`. A [`DtResolve`] closure (built from the gate's
//! `ModelView::datatype_def` registry, itself derived from the front-end
//! declaration tables — model-independent) maps such a sort back to its
//! `DatatypeSort`, so the axioms apply uniformly to native and UF-abstracted
//! datatypes. The resolution table only affects WHICH free-datatype axioms fire;
//! the axioms themselves are valid regardless of representation, so soundness is
//! unchanged.

use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{DatatypeSort, Sort, TermId, TermStore};

const MAX_DEPTH: u32 = 4000;

/// Resolve a sort to its datatype definition. `Sort::Datatype` resolves
/// directly; `Sort::Uninterpreted(name)` is resolved through the registry
/// closure; anything else is not a datatype.
pub type DtResolve<'a> = dyn Fn(&str) -> Option<DatatypeSort> + 'a;

fn sort_dt(sort: &Sort, resolve: &DtResolve<'_>) -> Option<DatatypeSort> {
    match sort {
        Sort::Datatype(dt) => Some(dt.clone()),
        Sort::Uninterpreted(name) => resolve(name),
        _ => None,
    }
}

/// The constructor NAME of `term` if it is a constructor application whose sort
/// resolves to the owning datatype (keyed off the sort, so a UF sharing a ctor
/// name is not misread).
fn constructor_name(terms: &TermStore, term: TermId, resolve: &DtResolve<'_>) -> Option<String> {
    if let TermData::App(Symbol::Named(name), _) = terms.get(term) {
        if let Some(dt) = sort_dt(terms.sort(term), resolve) {
            if dt.constructors.iter().any(|c| c.name == *name) {
                return Some(name.clone());
            }
        }
    }
    None
}

/// Fold a chain of selector-over-constructor applications:
/// `sel_i(Ctor(a0..an)) -> a_i`, recursively on the argument first. Returns the
/// term unchanged when the head is not a selector of the argument's constructor.
fn reduce_selector_chain(terms: &TermStore, term: TermId, resolve: &DtResolve<'_>) -> TermId {
    if let TermData::App(Symbol::Named(sel), args) = terms.get(term) {
        if args.len() == 1 {
            let reduced_arg = reduce_selector_chain(terms, args[0], resolve);
            if let TermData::App(Symbol::Named(ctor), cargs) = terms.get(reduced_arg) {
                if let Some(dt) = sort_dt(terms.sort(reduced_arg), resolve) {
                    if let Some(c) = dt.constructors.iter().find(|c| c.name == *ctor) {
                        if let Some(idx) = c.fields.iter().position(|f| f.name == *sel) {
                            if let Some(&field) = cargs.get(idx) {
                                return field;
                            }
                        }
                    }
                }
            }
        }
    }
    term
}

/// Bounded structural (syntactic) equality — identical `TermData` shape with
/// recursively-equal children. A SOUND witness of semantic equality in every
/// model (reflexivity). `false` on depth exhaustion (never a false positive).
fn terms_structurally_equal(terms: &TermStore, a: TermId, b: TermId, depth: u32) -> bool {
    if a == b {
        return true;
    }
    if depth == 0 {
        return false;
    }
    match (terms.get(a), terms.get(b)) {
        (TermData::Var(x, sx), TermData::Var(y, sy)) => x == y && sx == sy,
        (TermData::Const(cx), TermData::Const(cy)) => cx == cy,
        (TermData::App(sa, aa), TermData::App(sb, ab)) => {
            sym_eq(sa, sb)
                && aa.len() == ab.len()
                && aa
                    .iter()
                    .zip(ab.iter())
                    .all(|(&x, &y)| terms_structurally_equal(terms, x, y, depth - 1))
        }
        (TermData::Not(x), TermData::Not(y)) => terms_structurally_equal(terms, *x, *y, depth - 1),
        (TermData::Ite(cx, tx, ex), TermData::Ite(cy, ty, ey)) => {
            terms_structurally_equal(terms, *cx, *cy, depth - 1)
                && terms_structurally_equal(terms, *tx, *ty, depth - 1)
                && terms_structurally_equal(terms, *ex, *ey, depth - 1)
        }
        _ => false,
    }
}

fn sym_eq(a: &Symbol, b: &Symbol) -> bool {
    match (a, b) {
        (Symbol::Named(x), Symbol::Named(y)) => x == y,
        _ => a == b,
    }
}

/// Decide a datatype/scalar `=` between two operands purely by datatype axioms
/// (selector reduction, reflexivity, constructor injectivity/distinctness, and a
/// branch-agnostic `ite`). `Some(_)` is a PROOF; `None` = cannot decide. Sound.
fn dt_reduced_eq(
    terms: &TermStore,
    a: TermId,
    b: TermId,
    depth: u32,
    resolve: &DtResolve<'_>,
) -> Option<bool> {
    if depth == 0 {
        return None;
    }
    let ra = reduce_selector_chain(terms, a, resolve);
    let rb = reduce_selector_chain(terms, b, resolve);
    if terms_structurally_equal(terms, ra, rb, MAX_DEPTH) {
        return Some(true);
    }
    // `(= X (ite c T E))` = `(ite c (= X T) (= X E))`: if both branch-equalities
    // decide the SAME value, the equality has that value regardless of `c`.
    for (p, q) in [(ra, rb), (rb, ra)] {
        if let TermData::Ite(_, t, e) = terms.get(p) {
            if let (Some(x), Some(y)) = (
                dt_reduced_eq(terms, *t, q, depth - 1, resolve),
                dt_reduced_eq(terms, *e, q, depth - 1, resolve),
            ) {
                if x == y {
                    return Some(x);
                }
            }
        }
    }
    // Constructor injectivity / distinctness.
    let (TermData::App(_, aa), TermData::App(_, ab)) = (terms.get(ra), terms.get(rb)) else {
        return None;
    };
    let (Some(ca), Some(cb)) = (
        constructor_name(terms, ra, resolve),
        constructor_name(terms, rb, resolve),
    ) else {
        return None;
    };
    let (Some(dta), Some(dtb)) = (
        sort_dt(terms.sort(ra), resolve),
        sort_dt(terms.sort(rb), resolve),
    ) else {
        return None;
    };
    if dta.name != dtb.name {
        return None; // ill-typed comparison; stay safe
    }
    if ca != cb {
        return Some(false); // distinct constructors of the same datatype
    }
    if aa.len() != ab.len() {
        return None;
    }
    let (aa, ab) = (aa.clone(), ab.clone());
    let mut all_true = true;
    for (&x, &y) in aa.iter().zip(ab.iter()) {
        let field_eq = if *terms.sort(x) == Sort::Bool {
            match (
                dt_axiom_bool_inner(terms, x, depth - 1, resolve),
                dt_axiom_bool_inner(terms, y, depth - 1, resolve),
            ) {
                (Some(bx), Some(by)) => Some(bx == by),
                _ => None,
            }
        } else {
            dt_reduced_eq(terms, x, y, depth - 1, resolve)
        };
        match field_eq {
            Some(false) => return Some(false),
            Some(true) => {}
            None => all_true = false,
        }
    }
    if all_true {
        Some(true)
    } else {
        None
    }
}

/// Decide a Bool-sorted assertion purely by datatype + Boolean axioms.
/// `Some(true)` ⇒ the assertion is a TAUTOLOGY (holds in every model);
/// `Some(false)` ⇒ provably false; `None` ⇒ cannot decide. Model-independent
/// and SOUND — used only to CONFIRM a satisfied assertion, never to refute one.
fn dt_axiom_bool_inner(
    terms: &TermStore,
    term: TermId,
    depth: u32,
    resolve: &DtResolve<'_>,
) -> Option<bool> {
    if depth == 0 {
        return None;
    }
    match terms.get(term) {
        TermData::Const(Constant::Bool(b)) => Some(*b),
        TermData::Not(inner) => dt_axiom_bool_inner(terms, *inner, depth - 1, resolve).map(|b| !b),
        TermData::Ite(c, t, e) => match dt_axiom_bool_inner(terms, *c, depth - 1, resolve) {
            Some(true) => dt_axiom_bool_inner(terms, *t, depth - 1, resolve),
            Some(false) => dt_axiom_bool_inner(terms, *e, depth - 1, resolve),
            None => match (
                dt_axiom_bool_inner(terms, *t, depth - 1, resolve),
                dt_axiom_bool_inner(terms, *e, depth - 1, resolve),
            ) {
                (Some(x), Some(y)) if x == y => Some(x),
                _ => None,
            },
        },
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "not" if args.len() == 1 => {
                dt_axiom_bool_inner(terms, args[0], depth - 1, resolve).map(|b| !b)
            }
            "ite" if args.len() == 3 => {
                match dt_axiom_bool_inner(terms, args[0], depth - 1, resolve) {
                    Some(true) => dt_axiom_bool_inner(terms, args[1], depth - 1, resolve),
                    Some(false) => dt_axiom_bool_inner(terms, args[2], depth - 1, resolve),
                    None => match (
                        dt_axiom_bool_inner(terms, args[1], depth - 1, resolve),
                        dt_axiom_bool_inner(terms, args[2], depth - 1, resolve),
                    ) {
                        (Some(x), Some(y)) if x == y => Some(x),
                        _ => None,
                    },
                }
            }
            "and" => {
                let mut all_true = true;
                for &a in args {
                    match dt_axiom_bool_inner(terms, a, depth - 1, resolve) {
                        Some(false) => return Some(false),
                        Some(true) => {}
                        None => all_true = false,
                    }
                }
                if all_true {
                    Some(true)
                } else {
                    None
                }
            }
            "or" => {
                let mut all_false = true;
                for &a in args {
                    match dt_axiom_bool_inner(terms, a, depth - 1, resolve) {
                        Some(true) => return Some(true),
                        Some(false) => {}
                        None => all_false = false,
                    }
                }
                if all_false {
                    Some(false)
                } else {
                    None
                }
            }
            // Tester `(is-Ctor X)`: reduce X; decided by constructor-name identity.
            n if n
                .strip_prefix("is-")
                .is_some_and(|want| tester_target_is_ctor(terms, args, want, resolve))
                && args.len() == 1 =>
            {
                let want = n.strip_prefix("is-").unwrap();
                let red = reduce_selector_chain(terms, args[0], resolve);
                constructor_name(terms, red, resolve).map(|cn| cn == want)
            }
            "=" if args.len() == 2 => {
                if *terms.sort(args[0]) == Sort::Bool {
                    match (
                        dt_axiom_bool_inner(terms, args[0], depth - 1, resolve),
                        dt_axiom_bool_inner(terms, args[1], depth - 1, resolve),
                    ) {
                        (Some(x), Some(y)) => Some(x == y),
                        _ => None,
                    }
                } else {
                    dt_reduced_eq(terms, args[0], args[1], depth - 1, resolve)
                }
            }
            "distinct" if args.len() == 2 => {
                dt_reduced_eq(terms, args[0], args[1], depth - 1, resolve).map(|b| !b)
            }
            _ => None,
        },
        _ => None,
    }
}

/// Whether `is-<want>`'s single argument is datatype-sorted with a constructor
/// named `want` (so the head is genuinely a tester, not a UF).
fn tester_target_is_ctor(
    terms: &TermStore,
    args: &[TermId],
    want: &str,
    resolve: &DtResolve<'_>,
) -> bool {
    args.len() == 1
        && sort_dt(terms.sort(args[0]), resolve)
            .is_some_and(|dt| dt.constructors.iter().any(|c| c.name == want))
}

/// Public entry (native `Sort::Datatype` only — no UF-abstraction registry).
/// Decide a Bool-sorted assertion by datatype + Boolean axioms.
#[must_use]
pub fn dt_axiom_bool(terms: &TermStore, term: TermId, depth: u32) -> Option<bool> {
    dt_axiom_bool_inner(terms, term, depth, &|_| None)
}

/// Registry-aware variant: `resolve` maps an uninterpreted sort name to its
/// datatype definition (for datatypes abstracted to `Sort::Uninterpreted`).
#[must_use]
pub fn dt_axiom_bool_with(
    terms: &TermStore,
    term: TermId,
    depth: u32,
    resolve: &DtResolve<'_>,
) -> Option<bool> {
    dt_axiom_bool_inner(terms, term, depth, resolve)
}

/// Public entry: is `term` a datatype tautology (holds in every model)?
/// Native `Sort::Datatype` only.
#[must_use]
pub fn is_datatype_tautology(terms: &TermStore, term: TermId) -> bool {
    matches!(
        dt_axiom_bool_inner(terms, term, MAX_DEPTH, &|_| None),
        Some(true)
    )
}

/// Registry-aware `is_datatype_tautology`: resolves datatypes abstracted to
/// `Sort::Uninterpreted` through `resolve` (see [`DtResolve`]).
///
/// Two independent, SOUND, model-INDEPENDENT decision procedures are tried; the
/// term is a tautology if EITHER proves it:
/// 1. [`dt_axiom_bool_inner`] — selector/tester reduction + injectivity/
///    distinctness + Boolean folding (the classic path).
/// 2. [`norm::is_valid`] — a boolean+datatype NORMALIZER that additionally
///    decides the CONSTRUCTOR-CHARACTERIZATION biconditional
///    `(= (C f1..fn) X) ⟺ (is-C X ∧ ⋀ fi = sel_i(X))` (and its `is-C`/round-trip
///    corollaries, the sole-constructor tester tautology, and nullary-constructor
///    equalities). Every rewrite it applies is a VALID identity of the free
///    datatype + Boolean theory, so a `true` verdict is a proof the assertion
///    holds in EVERY model — it never consults the candidate model, hence can
///    never be fooled by a wrong witness. Incompleteness (a residual it cannot
///    prove) is safe: it returns `false`, so the gate fails closed.
#[must_use]
pub fn is_datatype_tautology_with(
    terms: &TermStore,
    term: TermId,
    resolve: &DtResolve<'_>,
) -> bool {
    if matches!(
        dt_axiom_bool_inner(terms, term, MAX_DEPTH, resolve),
        Some(true)
    ) {
        return true;
    }
    if read_over_eq_congruence(terms, term) {
        return true;
    }
    norm::is_valid(terms, term, resolve)
}

/// Whether `x` and `y` are congruent MODULO the pair `(a, b)`: structurally
/// identical except that, at differing positions, one side holds `a` and the
/// other `b` (in either order). If so, then GIVEN `a = b`, congruence yields
/// `x = y` — for ANY surrounding context. Sound and model-independent: a `true`
/// result is a proof that `(= a b) ⟹ (= x y)` holds in every model.
fn cong_eq(terms: &TermStore, x: TermId, y: TermId, a: TermId, b: TermId, depth: u32) -> bool {
    if depth == 0 {
        return false;
    }
    if x == y {
        return true;
    }
    if (x == a && y == b) || (x == b && y == a) {
        return true;
    }
    match (terms.get(x), terms.get(y)) {
        (TermData::App(sx, ax), TermData::App(sy, ay)) => {
            sx == sy
                && ax.len() == ay.len()
                && ax
                    .iter()
                    .zip(ay.iter())
                    .all(|(&xi, &yi)| cong_eq(terms, xi, yi, a, b, depth - 1))
        }
        (TermData::Not(xi), TermData::Not(yi)) => cong_eq(terms, *xi, *yi, a, b, depth - 1),
        (TermData::Ite(xc, xt, xe), TermData::Ite(yc, yt, ye)) => {
            cong_eq(terms, *xc, *yc, a, b, depth - 1)
                && cong_eq(terms, *xt, *yt, a, b, depth - 1)
                && cong_eq(terms, *xe, *ye, a, b, depth - 1)
        }
        _ => false,
    }
}

/// Recognize the READ-OVER-EQUALITY / congruence tautology shape
/// `(or (not (= a b)) (= t1 t2))` (and the `(=> (= a b) (= t1 t2))` form) where
/// `t1` and `t2` are congruent modulo `a ↔ b`. This is exactly the McCarthy /
/// EUF congruence lemma `a = b ⟹ E[a] = E[b]` — e.g. the datatype-array read
/// congruence `(or (not (= arrA arrB)) (= (fld (select arrA i)) (fld (select
/// arrB i))))` the solver injects — and is VALID IN EVERY MODEL. Recognizing it
/// here lets the fail-closed gate CONFIRM such an assertion structurally, without
/// having to reconstruct the (possibly free / inconsistent) arrays it mentions.
/// SOUNDNESS: purely structural; a `true` result is `(= a b) ⟹ (= t1 t2)` by
/// congruence, so the whole disjunction/implication is a tautology. It never
/// reads a model and can only ever prove a genuine congruence lemma true.
fn read_over_eq_congruence(terms: &TermStore, term: TermId) -> bool {
    let get_eq = |t: TermId| -> Option<(TermId, TermId)> {
        if let TermData::App(sym, args) = terms.get(t) {
            if sym.name() == "=" && args.len() == 2 {
                return Some((args[0], args[1]));
            }
        }
        None
    };
    let strip_not = |t: TermId| -> Option<TermId> {
        match terms.get(t) {
            TermData::Not(inner) => Some(*inner),
            TermData::App(sym, args) if sym.name() == "not" && args.len() == 2 - 1 => Some(args[0]),
            _ => None,
        }
    };
    // Candidate (antecedent-eq, consequent-eq) pairs from `or`/`=>` shapes.
    let cands: Vec<(TermId, TermId)> = match terms.get(term) {
        TermData::App(sym, args) if sym.name() == "or" && args.len() == 2 => {
            let (d0, d1) = (args[0], args[1]);
            let mut v = Vec::new();
            if let Some(inner) = strip_not(d0) {
                v.push((inner, d1));
            }
            if let Some(inner) = strip_not(d1) {
                v.push((inner, d0));
            }
            v
        }
        TermData::App(sym, args) if sym.name() == "=>" && args.len() == 2 => {
            vec![(args[0], args[1])]
        }
        _ => Vec::new(),
    };
    for (ante, cons) in cands {
        if let (Some((a, b)), Some((t1, t2))) = (get_eq(ante), get_eq(cons)) {
            if cong_eq(terms, t1, t2, a, b, MAX_DEPTH) {
                return true;
            }
        }
    }
    false
}

/// Boolean + free-datatype NORMALIZER — a model-independent validity checker.
///
/// It rewrites a Boolean assertion into a canonical Boolean normal form `NB`
/// using only VALID identities of the free datatype + Boolean theory, and reports
/// the assertion valid iff that normal form is the constant `true`. The load-
/// bearing rewrite is the constructor characterization
/// `(= (C f1..fn) X) ⟺ is-C(X) ∧ ⋀ fi = sel_i(X)`, which makes ay's injected
/// datatype-congruence axioms (`(= (= (C f) X) (and (is-C X) (= fi (sel_i X))..))`,
/// the `is-C`/round-trip corollaries, and their `ite`-nested variants) reduce to
/// `(= P P)` and fold to `true`.
///
/// SOUNDNESS. Every constructor of `NB` and every rewrite below is a standard
/// equivalence that holds in every model:
/// * selector-over-constructor reduction, constructor injectivity/distinctness;
/// * `(= (C f) X) ⟺ is-C(X) ∧ ⋀ fi = sel_i(X)` (constructor characterization);
/// * `is-C(X) = true` when `C` is the datatype's SOLE constructor;
/// * a nullary-constructor term `N` denotes that constructor, so `is-N(N)=true`
///   and `is-C(N)=(C==N)`;
/// * ordinary Boolean simplification (and/or/not/iff folding, absorption of
///   `true`/`false`, dedup).
///
/// Atoms are keyed by a faithful STRUCTURAL serialization ([`tkey`]) of the
/// (selector-reduced) subterm, so two atoms share a key ONLY when the subterms
/// are structurally identical — hence semantically equal. No non-equal terms are
/// ever conflated, so a `true` verdict is always a genuine proof; anything it
/// cannot decide simplifies to a non-`true` form and the gate fails closed.
mod norm {
    use super::{sort_dt, DtResolve};
    use ay_core::term::{Symbol, TermData};
    use ay_core::{Sort, TermId, TermStore};

    const DEPTH: u32 = 400;

    /// Canonical Boolean normal form.
    #[derive(Clone, PartialEq, Eq)]
    enum NB {
        T,
        F,
        Atom(String),
        Not(Box<NB>),
        And(Vec<NB>),
        Or(Vec<NB>),
    }

    /// Public entry: is `term` a datatype+Boolean tautology?
    pub(super) fn is_valid(terms: &TermStore, term: TermId, resolve: &DtResolve<'_>) -> bool {
        // Only Bool-sorted assertions can be tautologies.
        if *terms.sort(term) != Sort::Bool {
            return false;
        }
        matches!(nb(terms, term, resolve, DEPTH), Some(NB::T))
    }

    /// Canonical key of a normal form — children sorted so semantically-equal
    /// forms serialize identically.
    fn key(n: &NB) -> String {
        match n {
            NB::T => "T".to_string(),
            NB::F => "F".to_string(),
            NB::Atom(s) => format!("a[{s}]"),
            NB::Not(x) => format!("!{}", key(x)),
            NB::And(v) => {
                let mut ks: Vec<String> = v.iter().map(key).collect();
                ks.sort();
                format!("&({})", ks.join(","))
            }
            NB::Or(v) => {
                let mut ks: Vec<String> = v.iter().map(key).collect();
                ks.sort();
                format!("|({})", ks.join(","))
            }
        }
    }

    fn mk_not(x: NB) -> NB {
        match x {
            NB::T => NB::F,
            NB::F => NB::T,
            NB::Not(y) => *y,
            other => NB::Not(Box::new(other)),
        }
    }

    fn mk_and(children: Vec<NB>) -> NB {
        let mut flat: Vec<NB> = Vec::new();
        for c in children {
            match c {
                NB::T => {}
                NB::F => return NB::F,
                NB::And(v) => flat.extend(v),
                other => flat.push(other),
            }
        }
        // Contradiction detection + dedup by canonical key.
        let mut seen = std::collections::BTreeMap::new();
        for c in flat {
            let k = key(&c);
            let nk = key(&mk_not(c.clone()));
            if seen.contains_key(&nk) {
                return NB::F; // x ∧ ¬x
            }
            seen.entry(k).or_insert(c);
        }
        let mut out: Vec<NB> = seen.into_values().collect();
        match out.len() {
            0 => NB::T,
            1 => out.pop().unwrap(),
            _ => NB::And(out),
        }
    }

    fn mk_or(children: Vec<NB>) -> NB {
        let mut flat: Vec<NB> = Vec::new();
        for c in children {
            match c {
                NB::F => {}
                NB::T => return NB::T,
                NB::Or(v) => flat.extend(v),
                other => flat.push(other),
            }
        }
        let mut seen = std::collections::BTreeMap::new();
        for c in flat {
            let k = key(&c);
            let nk = key(&mk_not(c.clone()));
            if seen.contains_key(&nk) {
                return NB::T; // x ∨ ¬x
            }
            seen.entry(k).or_insert(c);
        }
        let mut out: Vec<NB> = seen.into_values().collect();
        match out.len() {
            0 => NB::F,
            1 => out.pop().unwrap(),
            _ => NB::Or(out),
        }
    }

    /// `a ⟺ b` as a normal form.
    fn mk_iff(a: NB, b: NB) -> NB {
        if key(&a) == key(&b) {
            return NB::T;
        }
        if key(&mk_not(a.clone())) == key(&b) {
            return NB::F;
        }
        match (&a, &b) {
            (NB::T, _) => b,
            (_, NB::T) => a,
            (NB::F, _) => mk_not(b),
            (_, NB::F) => mk_not(a),
            // (a∧b) ∨ (¬a∧¬b)
            _ => mk_or(vec![
                mk_and(vec![a.clone(), b.clone()]),
                mk_and(vec![mk_not(a), mk_not(b)]),
            ]),
        }
    }

    /// Is `t` a constructor application (name is a constructor of its resolved
    /// datatype sort)? Returns `(ctor_name, DatatypeSort, field_terms)`.
    fn ctor_app(
        terms: &TermStore,
        t: TermId,
        resolve: &DtResolve<'_>,
    ) -> Option<(String, ay_core::DatatypeSort, Vec<TermId>)> {
        // Handle both `App(name, args)` (incl. nullary) forms.
        if let TermData::App(Symbol::Named(name), args) = terms.get(t) {
            if let Some(dt) = sort_dt(terms.sort(t), resolve) {
                if let Some(c) = dt.constructors.iter().find(|c| c.name == *name) {
                    if c.fields.len() == args.len() {
                        return Some((name.clone(), dt.clone(), args.clone()));
                    }
                }
            }
        }
        // A nullary constructor may surface as a bare `Var` whose NAME is the
        // constructor (the front-end lowered `(None)` to a constant). It is a
        // genuine constructor term (no separate declaration shadows it), so treat
        // it as the 0-ary application.
        if let TermData::Var(name, _) = terms.get(t) {
            if let Some(dt) = sort_dt(terms.sort(t), resolve) {
                if let Some(c) = dt.constructors.iter().find(|c| c.name == *name) {
                    if c.fields.is_empty() {
                        return Some((name.clone(), dt.clone(), Vec::new()));
                    }
                }
            }
        }
        None
    }

    /// Selector-over-constructor reduction: `sel_i(C(a..)) -> a_i`, recursively.
    fn reduce(terms: &TermStore, t: TermId, resolve: &DtResolve<'_>, depth: u32) -> TermId {
        if depth == 0 {
            return t;
        }
        if let TermData::App(Symbol::Named(sel), args) = terms.get(t) {
            if args.len() == 1 {
                let ra = reduce(terms, args[0], resolve, depth - 1);
                if let Some((cname, dt, cargs)) = ctor_app(terms, ra, resolve) {
                    if let Some(c) = dt.constructors.iter().find(|c| c.name == cname) {
                        if let Some(idx) = c.fields.iter().position(|f| f.name == *sel) {
                            if let Some(&field) = cargs.get(idx) {
                                return field;
                            }
                        }
                    }
                }
            }
        }
        t
    }

    /// Faithful structural key of a (selector-reduced) term — atom identity.
    fn tkey(terms: &TermStore, t: TermId, resolve: &DtResolve<'_>, depth: u32) -> String {
        if depth == 0 {
            return format!("#{}", t.0);
        }
        let r = reduce(terms, t, resolve, depth);
        match terms.get(r) {
            TermData::Var(name, id) => format!("V:{name}:{id}"),
            TermData::Const(c) => format!("K:{c:?}"),
            TermData::App(sym, args) => {
                let parts: Vec<String> = args
                    .iter()
                    .map(|&a| tkey(terms, a, resolve, depth - 1))
                    .collect();
                format!("({} {})", sym, parts.join(" "))
            }
            TermData::Not(x) => format!("(not {})", tkey(terms, *x, resolve, depth - 1)),
            TermData::Ite(c, a, b) => format!(
                "(ite {} {} {})",
                tkey(terms, *c, resolve, depth - 1),
                tkey(terms, *a, resolve, depth - 1),
                tkey(terms, *b, resolve, depth - 1)
            ),
            _ => format!("#{}", r.0),
        }
    }

    /// Normalize a BOOL-sorted term.
    fn nb(terms: &TermStore, t: TermId, resolve: &DtResolve<'_>, depth: u32) -> Option<NB> {
        if depth == 0 {
            return None;
        }
        match terms.get(t) {
            TermData::Const(ay_core::term::Constant::Bool(b)) => {
                Some(if *b { NB::T } else { NB::F })
            }
            TermData::Not(x) => Some(mk_not(nb(terms, *x, resolve, depth - 1)?)),
            TermData::Ite(c, a, b) => {
                let nc = nb(terms, *c, resolve, depth - 1)?;
                let na = nb(terms, *a, resolve, depth - 1)?;
                let nbb = nb(terms, *b, resolve, depth - 1)?;
                Some(mk_or(vec![
                    mk_and(vec![nc.clone(), na]),
                    mk_and(vec![mk_not(nc), nbb]),
                ]))
            }
            TermData::App(Symbol::Named(name), args) => {
                nb_app(terms, t, name, args, resolve, depth)
            }
            _ => Some(NB::Atom(format!("A:{}", tkey(terms, t, resolve, depth)))),
        }
    }

    fn nb_app(
        terms: &TermStore,
        t: TermId,
        name: &str,
        args: &[TermId],
        resolve: &DtResolve<'_>,
        depth: u32,
    ) -> Option<NB> {
        match name {
            "not" if args.len() == 1 => Some(mk_not(nb(terms, args[0], resolve, depth - 1)?)),
            "and" => {
                let mut v = Vec::with_capacity(args.len());
                for &a in args {
                    v.push(nb(terms, a, resolve, depth - 1)?);
                }
                Some(mk_and(v))
            }
            "or" => {
                let mut v = Vec::with_capacity(args.len());
                for &a in args {
                    v.push(nb(terms, a, resolve, depth - 1)?);
                }
                Some(mk_or(v))
            }
            "ite" if args.len() == 3 => {
                let nc = nb(terms, args[0], resolve, depth - 1)?;
                let na = nb(terms, args[1], resolve, depth - 1)?;
                let nbb = nb(terms, args[2], resolve, depth - 1)?;
                Some(mk_or(vec![
                    mk_and(vec![nc.clone(), na]),
                    mk_and(vec![mk_not(nc), nbb]),
                ]))
            }
            "xor" if args.len() == 2 => {
                let a = nb(terms, args[0], resolve, depth - 1)?;
                let b = nb(terms, args[1], resolve, depth - 1)?;
                Some(mk_not(mk_iff(a, b)))
            }
            "=>" if args.len() == 2 => {
                let a = nb(terms, args[0], resolve, depth - 1)?;
                let b = nb(terms, args[1], resolve, depth - 1)?;
                Some(mk_or(vec![mk_not(a), b]))
            }
            "=" if args.len() == 2 => nb_eq(terms, args[0], args[1], resolve, depth),
            "distinct" if args.len() == 2 => {
                Some(mk_not(nb_eq(terms, args[0], args[1], resolve, depth)?))
            }
            // Tester `(is-C X)`.
            n if n.strip_prefix("is-").is_some() && args.len() == 1 => {
                let want = n.strip_prefix("is-").unwrap();
                // Genuine tester only if the argument's sort is the datatype that
                // declares `want`.
                let Some(dt) = sort_dt(terms.sort(args[0]), resolve) else {
                    return Some(NB::Atom(format!("A:{}", tkey(terms, t, resolve, depth))));
                };
                if !dt.constructors.iter().any(|c| c.name == want) {
                    return Some(NB::Atom(format!("A:{}", tkey(terms, t, resolve, depth))));
                }
                let xr = reduce(terms, args[0], resolve, depth);
                if let Some((cn, _, _)) = ctor_app(terms, xr, resolve) {
                    return Some(if cn == want { NB::T } else { NB::F });
                }
                let xkey = tkey(terms, args[0], resolve, depth);
                Some(tester_nb(&dt, want, &xkey))
            }
            _ => Some(NB::Atom(format!("A:{}", tkey(terms, t, resolve, depth)))),
        }
    }

    /// Normalize an equality `(= a b)`.
    fn nb_eq(
        terms: &TermStore,
        a: TermId,
        b: TermId,
        resolve: &DtResolve<'_>,
        depth: u32,
    ) -> Option<NB> {
        // Boolean equality is a biconditional.
        if *terms.sort(a) == Sort::Bool {
            let na = nb(terms, a, resolve, depth - 1)?;
            let nbb = nb(terms, b, resolve, depth - 1)?;
            return Some(mk_iff(na, nbb));
        }
        deq(terms, a, b, resolve, depth)
    }

    /// One operand of a datatype equality: either a REAL term, or a SYNTHETIC
    /// selector-path `sel_k(..sel_1(X)..)` produced while characterizing a nested
    /// constructor field. A path carries its canonical [`tkey`]-format key (so it
    /// compares identical to the real `(sel X)` term the encoder emitted) and its
    /// declared sort (so testers/characterization know its datatype).
    enum Side {
        Term(TermId),
        Path(String, Sort),
    }

    fn side_key(terms: &TermStore, s: &Side, resolve: &DtResolve<'_>, depth: u32) -> String {
        match s {
            Side::Term(t) => tkey(terms, *t, resolve, depth),
            Side::Path(k, _) => k.clone(),
        }
    }

    fn side_sort(terms: &TermStore, s: &Side) -> Sort {
        match s {
            Side::Term(t) => terms.sort(*t).clone(),
            Side::Path(_, srt) => srt.clone(),
        }
    }

    /// Constructor application of a side. Only a REAL term can be a syntactic
    /// constructor; a selector path never is (its head is a selector). Fields are
    /// returned as `Side::Term`.
    fn side_ctor_app(
        terms: &TermStore,
        s: &Side,
        resolve: &DtResolve<'_>,
        depth: u32,
    ) -> Option<(String, ay_core::DatatypeSort, Vec<Side>)> {
        match s {
            Side::Term(t) => {
                let r = reduce(terms, *t, resolve, depth);
                ctor_app(terms, r, resolve)
                    .map(|(n, dt, args)| (n, dt, args.into_iter().map(Side::Term).collect()))
            }
            Side::Path(_, _) => None,
        }
    }

    /// Canonical normal form of a genuine tester `is-C(X)` when `X` is not a
    /// syntactic constructor. Uses two VALID free-datatype identities:
    /// * a datatype with a SOLE constructor has `is-C(X) = true`;
    /// * a datatype with EXACTLY TWO constructors satisfies "exactly one holds",
    ///   so `is-C1(X) ⟺ ¬is-C0(X)` — encode both against ONE shared atom
    ///   (`dt2:<dt>:<X>` meaning "X is the first constructor"), the first
    ///   constructor as the atom and the second as its negation. This lets the
    ///   normalizer fold ay's structural-equality characterization
    ///   `(= (= None X) (and (= (is-None X)(is-None None)) (= (is-Some X) …) …))`.
    ///
    /// For `>2` constructors, distinct per-constructor atoms are used (sound but
    /// incomplete: exclusivity/exhaustiveness across ≥3 testers is not encoded).
    fn tester_nb(dt: &ay_core::DatatypeSort, ctor: &str, xkey: &str) -> NB {
        let n = dt.constructors.len();
        if n == 1 {
            return NB::T;
        }
        if n == 2 {
            let idx = dt.constructors.iter().position(|c| c.name == ctor);
            let shared = format!("dt2:{}:{xkey}", dt.name);
            return match idx {
                Some(0) => NB::Atom(shared),
                Some(1) => mk_not(NB::Atom(shared)),
                _ => NB::Atom(format!("is:{ctor}:{xkey}")),
            };
        }
        NB::Atom(format!("is:{ctor}:{xkey}"))
    }

    /// Normalize a Boolean SIDE (a bool field or the synthetic `sel(X)` of a bool
    /// field). A real term normalizes through `nb`; a selector path is the opaque
    /// atom `A:<path-key>`, matching `nb`'s handling of the real `(sel X)` term.
    fn nb_side_bool(
        terms: &TermStore,
        s: &Side,
        resolve: &DtResolve<'_>,
        depth: u32,
    ) -> Option<NB> {
        match s {
            Side::Term(t) => nb(terms, *t, resolve, depth),
            Side::Path(k, _) => Some(NB::Atom(format!("A:{k}"))),
        }
    }

    /// Datatype / scalar equality as a normal form, applying the constructor
    /// characterization / injectivity / distinctness axioms — over `Side`s so a
    /// nested constructor field recurses against the synthetic selector path.
    fn deq(
        terms: &TermStore,
        a: TermId,
        b: TermId,
        resolve: &DtResolve<'_>,
        depth: u32,
    ) -> Option<NB> {
        deq_side(terms, &Side::Term(a), &Side::Term(b), resolve, depth)
    }

    fn deq_side(
        terms: &TermStore,
        a: &Side,
        b: &Side,
        resolve: &DtResolve<'_>,
        depth: u32,
    ) -> Option<NB> {
        if depth == 0 {
            return None;
        }
        let ka = side_key(terms, a, resolve, depth);
        let kb = side_key(terms, b, resolve, depth);
        if ka == kb {
            return Some(NB::T); // reflexivity
        }
        let ca = side_ctor_app(terms, a, resolve, depth);
        let cb = side_ctor_app(terms, b, resolve, depth);
        match (ca, cb) {
            (Some((na, dta, aa)), Some((nb_, dtb, ab))) => {
                if dta.name != dtb.name {
                    return None; // ill-typed; stay safe
                }
                if na != nb_ {
                    return Some(NB::F); // distinct constructors
                }
                if aa.len() != ab.len() {
                    return None;
                }
                let mut conj = Vec::with_capacity(aa.len());
                for (x, y) in aa.iter().zip(ab.iter()) {
                    conj.push(field_eq(terms, x, y, resolve, depth - 1)?);
                }
                Some(mk_and(conj))
            }
            // Characterization: `(= (C f) X) ⟺ is-C(X) ∧ ⋀ fi = sel_i(X)`.
            (Some((cn, dt, fields)), None) => {
                characterize(terms, &cn, &dt, &fields, b, resolve, depth)
            }
            (None, Some((cn, dt, fields))) => {
                characterize(terms, &cn, &dt, &fields, a, resolve, depth)
            }
            (None, None) => {
                // Opaque equality between two non-constructor sides: a stable atom
                // keyed by the unordered pair.
                let (lo, hi) = if ka <= kb { (ka, kb) } else { (kb, ka) };
                Some(NB::Atom(format!("eq:{lo}::{hi}")))
            }
        }
    }

    /// Field equality inside injectivity/characterization: Boolean fields fold via
    /// `mk_iff`, everything else recurses through `deq_side`.
    fn field_eq(
        terms: &TermStore,
        x: &Side,
        y: &Side,
        resolve: &DtResolve<'_>,
        depth: u32,
    ) -> Option<NB> {
        if side_sort(terms, x) == Sort::Bool {
            let nx = nb_side_bool(terms, x, resolve, depth)?;
            let ny = nb_side_bool(terms, y, resolve, depth)?;
            Some(mk_iff(nx, ny))
        } else {
            deq_side(terms, x, y, resolve, depth - 1)
        }
    }

    /// Build `is-C(X) ∧ ⋀ fi = sel_i(X)` as a normal form. The `sel_i(X)` operands
    /// are SYNTHETIC selector paths keyed to match the structural key of the real
    /// `(sel_i X)` term, so ay's injected `(and (is-C X) (= fi (sel_i X))..)`
    /// normalizes IDENTICALLY — recursively through nested constructor fields.
    fn characterize(
        terms: &TermStore,
        ctor: &str,
        dt: &ay_core::DatatypeSort,
        fields: &[Side],
        x: &Side,
        resolve: &DtResolve<'_>,
        depth: u32,
    ) -> Option<NB> {
        let c = dt.constructors.iter().find(|c| c.name == ctor)?;
        if c.fields.len() != fields.len() {
            return None;
        }
        let xkey = side_key(terms, x, resolve, depth);
        // is-C(X): X already a constructor ⇒ decided; else the canonical tester
        // normal form (sole-ctor ⇒ T; 2-ctor ⇒ mutually-exclusive atom pair).
        let is_c = if let Some((xn, _, _)) = side_ctor_app(terms, x, resolve, depth) {
            if xn == ctor {
                NB::T
            } else {
                NB::F
            }
        } else {
            tester_nb(dt, ctor, &xkey)
        };
        let mut conj = vec![is_c];
        for (i, fi) in fields.iter().enumerate() {
            let sel = &c.fields[i].name;
            let fsort = c.fields[i].sort.clone();
            // Synthetic `(sel_i X)` — key format identical to `tkey` of the real
            // unary application, so it matches the encoder's `(sel_i X)` term.
            let sel_path = Side::Path(format!("({sel} {xkey})"), fsort);
            conj.push(field_eq(terms, fi, &sel_path, resolve, depth)?);
        }
        Some(mk_and(conj))
    }
}
