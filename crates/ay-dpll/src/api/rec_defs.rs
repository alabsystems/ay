// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Check-time bounded expansion of recursive function definitions.
//!
//! This is the Term-level twin of the SMT-LIB `fun_defs` machinery in
//! `ay-frontend` (`define-fun-rec` macro expansion at elaboration): every
//! application of a defined recursive function inside a set of root terms is
//! repeatedly replaced by the definition body with the actual arguments
//! substituted for the parameters, until no application remains or a bound is
//! exceeded. Substitution goes through [`ay_core::TermStore::substitute`],
//! whose eager fold-on-rebuild collapses constant `ite` guards, so the untaken
//! recursive branch disappears before it is expanded further — exactly the
//! property that makes the elaborator's expansion terminate on ground calls.
//!
//! # Fail-closed contract
//!
//! `Ok(_)` from [`Solver::try_expand_rec_defs`] GUARANTEES that the returned
//! roots contain zero applications of any defined function outside quantifier
//! trigger (pattern) positions — patterns are semantically inert instantiation
//! hints, never verdict-bearing formulas. Every situation this module cannot
//! prove it handles faithfully returns `Err(_)` instead, and the caller must
//! fail closed (keep the quantified defining axioms and refuse to release a
//! `sat` verdict). In particular, the following are all `Err`, never a silent
//! mis-substitution:
//!
//! * depth (`max_rounds`) or work-budget exhaustion, and frontiers larger than
//!   [`MAX_FRONTIER_PER_ROUND`] (breadth blowup);
//! * an application of a defined name with the wrong arity, argument sorts, or
//!   result sort (a same-name redeclaration must never be spliced unfaithfully);
//! * an actual argument whose variable names intersect the binder names inside
//!   the definition body (`substitute` is not capture-avoiding);
//! * a goal binder (`forall`/`exists`/`let`) that rebinds a defined name or any
//!   name the definition bodies mention free (AY interns variables by NAME, so
//!   splicing a body under such a binder would capture);
//! * a round that makes no progress (a definition that reproduces its own
//!   application verbatim would otherwise spin);
//! * a definition marked non-expandable at registration (its body's binders
//!   shadow a parameter name).

use std::collections::{HashMap, HashSet};
use std::time::Instant;

use ay_core::{Sort, Symbol, TermData, TermId, TermStore};

use super::{Solver, Term};

/// Hard cap on the number of distinct applications expanded in one round.
///
/// A frontier past this size is a breadth explosion (e.g. a Fibonacci-style
/// definition applied to a symbolic argument); expansion fails closed instead
/// of hanging inside a decision call.
pub const MAX_FRONTIER_PER_ROUND: usize = 4096;

/// Names that AY's term layer or elaborator matches STRUCTURALLY as builtin
/// interpreted operators even though they are user-declarable as plain
/// uninterpreted functions (they are the `EXCLUDED_DECLARABLE_OP_NAMES` of
/// `ay-frontend`, kept declarable there because `(_ map +)` targets must be
/// declared symbols).
///
/// A RECURSIVE definition of such a name is a soundness trap: AY represents
/// builtin arithmetic/logic as `App(Symbol::Named("+"), args)`, so a
/// registered rec def named `+` would make the expander splice a user body
/// into every builtin `+` node — a confirmed wrong-`sat`/wrong-`unsat` class
/// (e.g. `'+' := '*'` made `2+3==6` sat with an invalid model). Rec-def
/// registration and expansion refuse every name on this list (and every
/// `ay_frontend::is_reserved_symbol` name); see
/// [`rec_def_name_conflates_with_builtin`].
///
/// Kept in sync by hand with `EXCLUDED_DECLARABLE_OP_NAMES`
/// (`crates/ay-frontend/src/elaborate/mod.rs`); entries that are indexed-only
/// or shadowable are still listed — over-blocking a rec-def NAME only costs an
/// honest error, while under-blocking is a wrong verdict.
#[rustfmt::skip]
const REC_DEF_BUILTIN_CONFLATION_NAMES: &[&str] = &[
    // SMT-LIB Core connectives (bare-matched by the term layer / elaborator).
    "and", "or", "not", "xor", "=>", "implies", "=", "distinct", "ite",
    "true", "false",
    // Ints/Reals operators (bare-matched).
    "+", "-", "*", "/", "^", "div", "mod", "rem", "abs", "min", "max",
    "<", "<=", ">", ">=", "to_int", "to_real", "is_int",
    // Indexed-form / qualified-path identifiers (blocked conservatively: a
    // recursive definition of these names has no legitimate use, and any
    // future bare-matching arm would silently conflate).
    "map", "is", "divisible", "at-most", "at-least", "pble", "pbge", "pbeq",
    "re.^", "update-field",
    "partial-order", "linear-order", "tree-order", "piecewise-linear-order",
    "+zero", "-zero", "+oo", "-oo", "NaN", "_", "const",
    "set.subset", "map.dom", "map.subset", "multiset.subset",
];

/// Whether `name` must never carry a recursive definition because AY matches
/// it structurally as a builtin operator (splicing a user body into it would
/// rewrite builtin semantics — a wrong-verdict class). Union of
/// `ay_frontend::is_reserved_symbol` (theory ops AY refuses to declare at all)
/// and [`REC_DEF_BUILTIN_CONFLATION_NAMES`] (ops that stay declarable as plain
/// UFs for `(_ map f)` but are structurally matched when applied).
#[must_use]
pub fn rec_def_name_conflates_with_builtin(name: &str) -> bool {
    ay_frontend::is_reserved_symbol(name) || REC_DEF_BUILTIN_CONFLATION_NAMES.contains(&name)
}

/// One registered recursive definition (`Z3_add_rec_def` semantics).
///
/// Built by [`Solver::make_rec_fun_def`] so every capture-relevant name set is
/// computed against the solver's real term store. Fields are private: the only
/// consumers are the expansion routines in this module.
#[derive(Debug, Clone)]
pub struct RecFunDef {
    /// Parameter terms (distinct `Var`s), one per parameter.
    params: Vec<TermId>,
    /// Term-level sorts of the parameters, index-aligned with `params`.
    param_sorts: Vec<Sort>,
    /// The definition body, built over the params (+ globals).
    body: TermId,
    /// Term-level sort of `body`.
    body_sort: Sort,
    /// Names bound by any `Forall`/`Exists`/`Let` inside `body`. An actual
    /// argument whose variables intersect this set would be captured.
    body_binder_names: HashSet<String>,
    /// Names a GOAL binder must not rebind when this body is spliced under it:
    /// the body's variable names minus the parameters (parameters are fully
    /// substituted away), plus the body's own binder names.
    capture_risk_names: HashSet<String>,
    /// `false` when the body's binders shadow a parameter name (or a parameter
    /// is not a distinct `Var`): substitution could capture, so the definition
    /// is registered for residual fail-close detection only.
    expandable: bool,
}

impl RecFunDef {
    /// Whether check-time expansion of this definition is capture-safe.
    #[must_use]
    pub fn is_expandable(&self) -> bool {
        self.expandable
    }
}

/// Why bounded expansion could not produce a fully-expanded goal.
///
/// Every variant means the caller must FAIL CLOSED: solve with the original
/// goal plus the quantified defining axioms and never release `sat`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecExpandError {
    /// The nesting-depth limit (`max_rounds`, mirroring the SMT-LIB path's
    /// `MAX_FUN_EXPANSION_DEPTH = 1000`) was reached with work remaining.
    DepthExceeded(usize),
    /// The work budget (DAG nodes visited plus per-round scan×frontier
    /// substitution cost) or the per-round frontier cap was exceeded.
    BudgetExceeded(usize),
    /// The wall-clock deadline passed. The work budget's unit-to-time ratio is
    /// shape-dependent (ground ADT guards never fold, so each round rescans a
    /// GROWING dag whose real per-node cost the unit count under-states — the
    /// measured multi-minute grind class), so expansion is additionally bounded
    /// by real elapsed time and fails closed when it is exceeded.
    TimeExceeded(u64),
    /// A shape this module refuses to expand (arity/sort mismatch, capture
    /// risk, rebinding goal binder, non-expandable definition, no progress).
    UnsupportedShape(String),
}

impl std::fmt::Display for RecExpandError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DepthExceeded(rounds) => {
                write!(
                    f,
                    "recursion depth limit ({rounds}) exceeded during function expansion"
                )
            }
            Self::BudgetExceeded(work) => {
                write!(f, "expansion work budget exceeded ({work} units)")
            }
            Self::TimeExceeded(ms) => {
                write!(f, "expansion wall-clock budget exceeded ({ms} ms)")
            }
            Self::UnsupportedShape(reason) => write!(f, "unsupported shape: {reason}"),
        }
    }
}

/// Result of one frontier scan over the current roots.
struct RoundScan {
    /// Distinct rec-defined applications found (deduplicated, in deterministic
    /// discovery order).
    frontier: Vec<TermId>,
    /// Distinct (node, capture-flag) states visited — the scan's work measure.
    visited_nodes: usize,
}

/// The name sets of one term DAG, plus whether the walk saw every node kind
/// it knows how to enumerate.
struct NameScan {
    var_names: HashSet<String>,
    binder_names: HashSet<String>,
    /// `false` when an unknown (future) `TermData` variant was encountered —
    /// the name sets may then be UNDER-approximate, and every consumer must
    /// fail closed rather than trust them.
    complete: bool,
}

/// Collect every variable name and every binder-bound name in `root`'s DAG.
///
/// Descends ALL structure including quantifier trigger lists (conservative:
/// used for capture-risk sets, where over-approximation only fails closed).
fn collect_var_and_binder_names(store: &TermStore, root: TermId) -> NameScan {
    let mut var_names = HashSet::new();
    let mut binder_names = HashSet::new();
    let mut complete = true;
    let mut visited: HashSet<TermId> = HashSet::new();
    let mut stack = vec![root];
    while let Some(id) = stack.pop() {
        if !visited.insert(id) {
            continue;
        }
        match store.get(id) {
            TermData::Const(_) => {}
            TermData::Var(name, _) => {
                var_names.insert(name.clone());
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Let(bindings, body) => {
                for (name, value) in bindings {
                    binder_names.insert(name.clone());
                    stack.push(*value);
                }
                stack.push(*body);
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => {
                stack.push(*c);
                stack.push(*t);
                stack.push(*e);
            }
            TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                for (name, _) in vars {
                    binder_names.insert(name.clone());
                }
                stack.push(*body);
                for group in triggers {
                    stack.extend(group.iter().copied());
                }
            }
            // `TermData` is #[non_exhaustive]: an unknown future variant may
            // carry names this walk cannot see. Record incompleteness so the
            // consumers fail closed instead of trusting a partial set.
            _ => complete = false,
        }
    }
    NameScan {
        var_names,
        binder_names,
        complete,
    }
}

/// Classify `id` against the registry: `Ok(true)` = a faithful, expandable
/// application of a defined function; `Ok(false)` = not a defined-function
/// occurrence; `Err(_)` = an occurrence that CANNOT be expanded faithfully
/// (wrong arity/sorts, indexed symbol, non-expandable def) — fail closed.
fn classify_candidate(
    store: &TermStore,
    defs: &HashMap<String, RecFunDef>,
    id: TermId,
) -> Result<bool, RecExpandError> {
    match store.get(id) {
        TermData::Var(name, _) => {
            let Some(def) = defs.get(name) else {
                return Ok(false);
            };
            if !def.params.is_empty() {
                return Err(RecExpandError::UnsupportedShape(format!(
                    "constant occurrence of {name}, which is defined with arity {}",
                    def.params.len()
                )));
            }
            if !def.expandable {
                return Err(RecExpandError::UnsupportedShape(format!(
                    "definition of {name} is not capture-safe to expand"
                )));
            }
            if store.sort(id) != &def.body_sort {
                return Err(RecExpandError::UnsupportedShape(format!(
                    "occurrence of {name} has a different sort than its definition body"
                )));
            }
            Ok(true)
        }
        TermData::App(sym, args) => {
            let name = sym.name();
            let Some(def) = defs.get(name) else {
                return Ok(false);
            };
            if matches!(sym, Symbol::Indexed(_, _)) {
                return Err(RecExpandError::UnsupportedShape(format!(
                    "indexed application of recursively defined {name}"
                )));
            }
            if !def.expandable {
                return Err(RecExpandError::UnsupportedShape(format!(
                    "definition of {name} is not capture-safe to expand"
                )));
            }
            if args.len() != def.params.len() {
                return Err(RecExpandError::UnsupportedShape(format!(
                    "application of {name} with {} arguments, definition has {}",
                    args.len(),
                    def.params.len()
                )));
            }
            for (arg, expected) in args.iter().zip(&def.param_sorts) {
                if store.sort(*arg) != expected {
                    return Err(RecExpandError::UnsupportedShape(format!(
                        "application of {name} with an argument sort differing from the \
                         definition's parameter sort"
                    )));
                }
            }
            if store.sort(id) != &def.body_sort {
                return Err(RecExpandError::UnsupportedShape(format!(
                    "application of {name} has a different result sort than its definition body"
                )));
            }
            Ok(true)
        }
        _ => Ok(false),
    }
}

/// One frontier scan: find every defined-function application in `roots`.
///
/// Traversal deliberately SKIPS quantifier trigger lists (patterns are
/// semantically inert and `TermStore::substitute` does not rewrite them, so a
/// trigger-only occurrence must not count as residual — it can never affect a
/// verdict). It tracks whether the walk is under a binder that rebinds a
/// forbidden name; a defined-function occurrence under such a binder is
/// refused (splicing a body there could capture).
fn scan_round(
    store: &TermStore,
    roots: &[TermId],
    defs: &HashMap<String, RecFunDef>,
    forbidden_binder_names: &HashSet<&str>,
) -> Result<RoundScan, RecExpandError> {
    let mut frontier: Vec<TermId> = Vec::new();
    let mut in_frontier: HashSet<TermId> = HashSet::new();
    let mut visited: HashSet<(TermId, bool)> = HashSet::new();
    let mut stack: Vec<(TermId, bool)> = roots.iter().map(|&r| (r, false)).collect();
    // Deterministic order: process roots first-to-last (stack holds them
    // reversed relative to push order, which is fine — the frontier is a SET
    // handed to simultaneous substitution; ordering never changes the result).
    while let Some((id, under_capture_risk)) = stack.pop() {
        if !visited.insert((id, under_capture_risk)) {
            continue;
        }
        if classify_candidate(store, defs, id)? {
            if under_capture_risk {
                return Err(RecExpandError::UnsupportedShape(
                    "a recursively defined function occurs under a binder that rebinds its \
                     name or a name its definition body mentions"
                        .to_string(),
                ));
            }
            if in_frontier.insert(id) {
                frontier.push(id);
            }
            // An application's ARGUMENTS may contain further applications
            // (e.g. `ack(m-1, ack(m, n-1))`); keep descending.
        }
        match store.get(id) {
            TermData::Const(_) | TermData::Var(_, _) => {}
            TermData::App(_, args) => {
                stack.extend(args.iter().map(|&a| (a, under_capture_risk)));
            }
            TermData::Let(bindings, body) => {
                let rebinds = bindings
                    .iter()
                    .any(|(name, _)| forbidden_binder_names.contains(name.as_str()));
                let inner = under_capture_risk || rebinds;
                // Binding VALUES are evaluated outside the new bindings in
                // SMT-LIB `let`, but AY's name-interned store cannot separate
                // the scopes, so treat them at the inner (conservative) level.
                stack.extend(bindings.iter().map(|(_, v)| (*v, inner)));
                stack.push((*body, inner));
            }
            TermData::Not(inner) => stack.push((*inner, under_capture_risk)),
            TermData::Ite(c, t, e) => {
                stack.push((*c, under_capture_risk));
                stack.push((*t, under_capture_risk));
                stack.push((*e, under_capture_risk));
            }
            TermData::Forall(vars, body, _triggers) | TermData::Exists(vars, body, _triggers) => {
                let rebinds = vars
                    .iter()
                    .any(|(name, _)| forbidden_binder_names.contains(name.as_str()));
                stack.push((*body, under_capture_risk || rebinds));
                // Triggers deliberately NOT descended (see doc above).
            }
            // `TermData` is #[non_exhaustive]: an unknown future variant could
            // hide a defined-function application this scan cannot see, which
            // would break the Ok(_) guarantee. Fail closed.
            _ => {
                return Err(RecExpandError::UnsupportedShape(
                    "goal contains a term variant the expansion scanner does not know".to_string(),
                ))
            }
        }
    }
    Ok(RoundScan {
        frontier,
        visited_nodes: visited.len(),
    })
}

impl Solver {
    /// Build a [`RecFunDef`] for registration, computing every capture-relevant
    /// name set against this solver's term store.
    ///
    /// Never fails: a definition whose parameters are not distinct `Var`s or
    /// whose body binders shadow a parameter name is returned with
    /// `expandable = false`, so uses of it are DETECTED at expansion time (and
    /// fail closed) without ever being mis-substituted.
    #[must_use]
    pub fn make_rec_fun_def(&self, params: &[Term], body: Term) -> RecFunDef {
        let store = self.terms();
        let mut param_ids = Vec::with_capacity(params.len());
        let mut param_sorts = Vec::with_capacity(params.len());
        let mut param_names: HashSet<String> = HashSet::new();
        let mut params_are_distinct_vars = true;
        for &p in params {
            param_ids.push(p.0);
            param_sorts.push(store.sort(p.0).clone());
            match store.get(p.0) {
                TermData::Var(name, _) => {
                    if !param_names.insert(name.clone()) {
                        params_are_distinct_vars = false;
                    }
                }
                _ => params_are_distinct_vars = false,
            }
        }
        let body_scan = collect_var_and_binder_names(store, body.0);
        // An incomplete body scan means the capture-risk sets may miss names:
        // never expand such a definition (fail closed at every use instead).
        let expandable = params_are_distinct_vars
            && body_scan.complete
            && param_names.is_disjoint(&body_scan.binder_names);
        let mut capture_risk_names: HashSet<String> = body_scan
            .var_names
            .difference(&param_names)
            .cloned()
            .collect();
        capture_risk_names.extend(body_scan.binder_names.iter().cloned());
        RecFunDef {
            params: param_ids,
            param_sorts,
            body: body.0,
            body_sort: store.sort(body.0).clone(),
            body_binder_names: body_scan.binder_names,
            capture_risk_names,
            expandable,
        }
    }

    /// Whether any of `roots` mentions a registered recursive definition —
    /// by name, anywhere (arguments, binder bodies, AND trigger lists), with
    /// no shape validation. Deliberately over-approximate: used by surfaces
    /// that FAIL CLOSED on any mention (fixedpoint queries, Optimize SAT).
    #[must_use]
    pub fn contains_rec_fun_apps(&self, roots: &[Term], defs: &HashMap<String, RecFunDef>) -> bool {
        if defs.is_empty() {
            return false;
        }
        let store = self.terms();
        let mut visited: HashSet<TermId> = HashSet::new();
        let mut stack: Vec<TermId> = roots.iter().map(|t| t.0).collect();
        while let Some(id) = stack.pop() {
            if !visited.insert(id) {
                continue;
            }
            match store.get(id) {
                TermData::Const(_) => {}
                TermData::Var(name, _) => {
                    if defs.contains_key(name) {
                        return true;
                    }
                }
                TermData::App(sym, args) => {
                    if defs.contains_key(sym.name()) {
                        return true;
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, v)| *v));
                    stack.push(*body);
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                    if vars.iter().any(|(name, _)| defs.contains_key(name)) {
                        // A binder rebinding a defined name is itself a
                        // rec-def-sensitive shape: report a mention.
                        return true;
                    }
                    stack.push(*body);
                    for group in triggers {
                        stack.extend(group.iter().copied());
                    }
                }
                // Unknown future variant: this predicate's consumers FAIL
                // CLOSED on `true`, so over-report rather than miss a mention.
                _ => return true,
            }
        }
        false
    }

    /// Whether any of `roots` mentions (App symbol or Var name, anywhere,
    /// including binder bodies and trigger lists) a name in `names`.
    /// Deliberately over-approximate — consumers FAIL CLOSED on `true`; an
    /// unknown future `TermData` variant likewise reports `true`.
    #[must_use]
    pub fn terms_mention_names(&self, roots: &[Term], names: &HashSet<String>) -> bool {
        if names.is_empty() {
            return false;
        }
        let store = self.terms();
        let mut visited: HashSet<TermId> = HashSet::new();
        let mut stack: Vec<TermId> = roots.iter().map(|t| t.0).collect();
        while let Some(id) = stack.pop() {
            if !visited.insert(id) {
                continue;
            }
            match store.get(id) {
                TermData::Const(_) => {}
                TermData::Var(name, _) => {
                    if names.contains(name) {
                        return true;
                    }
                }
                TermData::App(sym, args) => {
                    if names.contains(sym.name()) {
                        return true;
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, v)| *v));
                    stack.push(*body);
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                    stack.push(*body);
                    for group in triggers {
                        stack.extend(group.iter().copied());
                    }
                }
                // Unknown future variant: over-report (consumers fail closed).
                _ => return true,
            }
        }
        false
    }

    /// The defined names whose bodies can REACH (mention directly, or through
    /// a chain of other definitions' bodies) any name in `targets`.
    ///
    /// Used for the undefined-recursive-declaration gate: a goal that uses a
    /// defined function whose unfolding would surface a rec-DECLARED-but-
    /// UNDEFINED function must fail closed — real z3 treats a forced unfold
    /// through an undefined recfun as inconsistent (`unsat`), while a plain-UF
    /// reading answers `sat`; AY releases neither (measured divergence,
    /// skeptic finding 2). Over-approximate by construction (name-level, all
    /// positions including triggers): over-taint only fail-closes.
    #[must_use]
    pub fn rec_def_names_reaching(
        &self,
        defs: &HashMap<String, RecFunDef>,
        targets: &HashSet<String>,
    ) -> HashSet<String> {
        if defs.is_empty() || targets.is_empty() {
            return HashSet::new();
        }
        // Names each definition's body mentions (App symbols + Vars).
        let store = self.terms();
        let mut mentions: HashMap<&str, HashSet<String>> = HashMap::new();
        for (name, def) in defs {
            let scan = collect_var_and_binder_names(store, def.body);
            let mut m = scan.var_names;
            // `collect_var_and_binder_names` gathers Var names but not App
            // symbols; walk once more for application heads.
            let mut visited: HashSet<TermId> = HashSet::new();
            let mut stack = vec![def.body];
            while let Some(id) = stack.pop() {
                if !visited.insert(id) {
                    continue;
                }
                match store.get(id) {
                    TermData::App(sym, args) => {
                        m.insert(sym.name().to_string());
                        stack.extend(args.iter().copied());
                    }
                    TermData::Let(bindings, body) => {
                        stack.extend(bindings.iter().map(|(_, v)| *v));
                        stack.push(*body);
                    }
                    TermData::Not(inner) => stack.push(*inner),
                    TermData::Ite(c, t, e) => {
                        stack.push(*c);
                        stack.push(*t);
                        stack.push(*e);
                    }
                    TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                        stack.push(*body);
                        for group in triggers {
                            stack.extend(group.iter().copied());
                        }
                    }
                    _ => {}
                }
            }
            if !scan.complete {
                // The body carries a term variant the walk cannot enumerate:
                // conservatively treat it as reaching everything (fail closed).
                m.extend(targets.iter().cloned());
            }
            mentions.insert(name.as_str(), m);
        }
        // Fixpoint: tainted = mentions a target, or mentions a tainted def.
        let mut tainted: HashSet<String> = HashSet::new();
        loop {
            let mut changed = false;
            for (name, m) in &mentions {
                if tainted.contains(*name) {
                    continue;
                }
                let hits = m
                    .iter()
                    .any(|n| targets.contains(n) || (tainted.contains(n) && defs.contains_key(n)));
                if hits {
                    tainted.insert((*name).to_string());
                    changed = true;
                }
            }
            if !changed {
                return tainted;
            }
        }
    }

    /// Bounded `fun_defs`-style unfolding of every application of a defined
    /// recursive function inside `roots`.
    ///
    /// `Ok(_)` GUARANTEES zero residual defined-function applications outside
    /// trigger positions (the return value is produced only by a clean scan).
    /// `Err(_)` means the caller MUST fail closed. See the module docs for the
    /// exhaustive list of refused shapes.
    ///
    /// `max_rounds` bounds the nesting depth (one round expands one level, so
    /// `1000` mirrors the SMT-LIB path's `MAX_FUN_EXPANSION_DEPTH`);
    /// `work_budget` bounds total WORK — DAG nodes visited by scans plus each
    /// round's `scan_nodes × frontier_size` substitution cost; `deadline`
    /// bounds real elapsed time (checked every round AND between frontier
    /// items / root substitutions, because the work-unit-to-time ratio is
    /// shape-dependent: ground ADT constructor guards never fold, so the dag
    /// grows every round and the unit count under-states real cost — the
    /// measured multi-minute grind class). Together they guarantee expansion
    /// can never turn one decision call into a multi-minute hang before
    /// failing closed.
    pub fn try_expand_rec_defs(
        &mut self,
        roots: &[Term],
        defs: &HashMap<String, RecFunDef>,
        max_rounds: usize,
        work_budget: usize,
        deadline: Option<Instant>,
    ) -> Result<Vec<Term>, RecExpandError> {
        if defs.is_empty() {
            return Ok(roots.to_vec());
        }
        // Builtin-conflation belt (defense in depth behind the registration
        // guard): a registered definition of a name AY matches structurally as
        // a builtin operator must NEVER be spliced — `classify_candidate`
        // would treat every builtin `+`/`and`/… node as a user application and
        // rewrite builtin semantics (a confirmed wrong-verdict class).
        for name in defs.keys() {
            if rec_def_name_conflates_with_builtin(name) {
                return Err(RecExpandError::UnsupportedShape(format!(
                    "recursive definition of builtin operator name {name}"
                )));
            }
        }
        let deadline_exceeded = |start: Instant| -> Option<RecExpandError> {
            deadline.and_then(|d| {
                (Instant::now() > d)
                    .then(|| RecExpandError::TimeExceeded(start.elapsed().as_millis() as u64))
            })
        };
        let start = Instant::now();
        // Names a goal binder must not rebind: every defined name plus every
        // name any definition body could splice in free.
        let mut forbidden_binder_names: HashSet<&str> = HashSet::new();
        for (name, def) in defs {
            forbidden_binder_names.insert(name.as_str());
            for n in &def.capture_risk_names {
                forbidden_binder_names.insert(n.as_str());
            }
        }

        let mut current: Vec<TermId> = roots.iter().map(|t| t.0).collect();
        let mut work: usize = 0;
        let mut rounds: usize = 0;
        loop {
            if let Some(e) = deadline_exceeded(start) {
                return Err(e);
            }
            let scan = scan_round(self.terms(), &current, defs, &forbidden_binder_names)?;
            work = work.saturating_add(scan.visited_nodes);
            if work > work_budget {
                return Err(RecExpandError::BudgetExceeded(work));
            }
            if scan.frontier.is_empty() {
                // The Ok contract: defined by exactly this clean scan.
                return Ok(current.into_iter().map(Term).collect());
            }
            if rounds >= max_rounds {
                return Err(RecExpandError::DepthExceeded(max_rounds));
            }
            if scan.frontier.len() > MAX_FRONTIER_PER_ROUND {
                return Err(RecExpandError::BudgetExceeded(
                    work.saturating_add(scan.frontier.len()),
                ));
            }
            // Bound this round's simultaneous-substitution cost BEFORE paying
            // it: `substitute` linearly scans the from-list at every node.
            work = work.saturating_add(scan.visited_nodes.saturating_mul(scan.frontier.len()));
            if work > work_budget {
                return Err(RecExpandError::BudgetExceeded(work));
            }

            let mut expandeds: Vec<TermId> = Vec::with_capacity(scan.frontier.len());
            for &app in &scan.frontier {
                if let Some(e) = deadline_exceeded(start) {
                    return Err(e);
                }
                expandeds.push(self.expand_one_application(app, defs, &mut work, work_budget)?);
            }

            let mut next = Vec::with_capacity(current.len());
            let mut progressed = false;
            for &root in &current {
                if let Some(e) = deadline_exceeded(start) {
                    return Err(e);
                }
                let new_root = self
                    .terms_mut()
                    .substitute(root, &scan.frontier, &expandeds);
                progressed |= new_root != root;
                next.push(new_root);
            }
            if !progressed {
                return Err(RecExpandError::UnsupportedShape(
                    "expansion made no progress (a definition reproduces its own application)"
                        .to_string(),
                ));
            }
            current = next;
            rounds += 1;
        }
    }

    /// Expand ONE already-classified frontier application: capture-check the
    /// actual arguments, then substitute them for the parameters in the body.
    fn expand_one_application(
        &mut self,
        app: TermId,
        defs: &HashMap<String, RecFunDef>,
        work: &mut usize,
        work_budget: usize,
    ) -> Result<TermId, RecExpandError> {
        let (name, args): (String, Vec<TermId>) = match self.terms().get(app) {
            TermData::Var(n, _) => (n.clone(), Vec::new()),
            TermData::App(sym, args) => (sym.name().to_string(), args.clone()),
            // The frontier only ever contains Var/App nodes (see scan_round).
            _ => {
                return Err(RecExpandError::UnsupportedShape(
                    "internal: non-application in expansion frontier".to_string(),
                ))
            }
        };
        let Some(def) = defs.get(&name) else {
            return Err(RecExpandError::UnsupportedShape(format!(
                "internal: frontier entry {name} has no definition"
            )));
        };
        if args.is_empty() {
            // 0-ary (both the `Var` and `App(name, [])` shapes): the body IS
            // the expansion.
            return Ok(def.body);
        }
        // Capture guard: an actual argument whose variables intersect the
        // body's binder names would be captured by `substitute` (which is not
        // capture-avoiding). Fail closed instead.
        if !def.body_binder_names.is_empty() {
            for &arg in &args {
                let arg_scan = collect_var_and_binder_names(self.terms(), arg);
                *work = work.saturating_add(arg_scan.var_names.len().max(1));
                if *work > work_budget {
                    return Err(RecExpandError::BudgetExceeded(*work));
                }
                if !arg_scan.complete {
                    return Err(RecExpandError::UnsupportedShape(format!(
                        "an argument of {name} contains a term variant the capture check \
                         cannot enumerate"
                    )));
                }
                if !arg_scan.var_names.is_disjoint(&def.body_binder_names) {
                    return Err(RecExpandError::UnsupportedShape(format!(
                        "an argument of {name} would be captured by a binder inside the \
                         definition body"
                    )));
                }
            }
        }
        Ok(self.terms_mut().substitute(def.body, &def.params, &args))
    }
}

#[cfg(test)]
#[allow(clippy::panic, clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use super::super::{Logic, Solver, Term};
    use super::*;

    const ROUNDS: usize = 1000;
    const BUDGET: usize = 5_000_000;

    fn solver() -> Solver {
        Solver::new(Logic::All)
    }

    fn int(s: &mut Solver, v: i64) -> Term {
        s.int_const(v)
    }

    /// def fact(x) := ite(x <= 0, 1, x * fact(x - 1))
    fn define_fact(s: &mut Solver) -> (HashMap<String, RecFunDef>, super::super::FuncDecl) {
        let fact = s.declare_fun("fact", &[Sort::Int], Sort::Int);
        let x = s.declare_const("x", Sort::Int);
        let zero = int(s, 0);
        let one = int(s, 1);
        let guard = s.try_le(x, zero).unwrap();
        let xm1 = s.try_sub(x, one).unwrap();
        let rec = s.try_apply(&fact, &[xm1]).unwrap();
        let x_times = s.try_mul(x, rec).unwrap();
        let body = s.try_ite(guard, one, x_times).unwrap();
        let def = s.make_rec_fun_def(&[x], body);
        assert!(def.is_expandable());
        let mut defs = HashMap::new();
        defs.insert("fact".to_string(), def);
        (defs, fact)
    }

    #[test]
    fn factorial_ground_expansion_folds_to_truth() {
        let mut s = solver();
        let (defs, fact) = define_fact(&mut s);
        let five = int(&mut s, 5);
        let call = s.try_apply(&fact, &[five]).unwrap();
        let target = int(&mut s, 120);
        let goal = s.try_eq(call, target).unwrap();
        let out = s
            .try_expand_rec_defs(&[goal], &defs, ROUNDS, BUDGET, None)
            .expect("ground factorial must fully expand");
        let truth = s.bool_const(true);
        assert_eq!(out, vec![truth], "fact(5) == 120 must fold to true");

        let wrong = int(&mut s, 121);
        let goal2 = s.try_eq(call, wrong).unwrap();
        let out2 = s
            .try_expand_rec_defs(&[goal2], &defs, ROUNDS, BUDGET, None)
            .expect("ground factorial must fully expand");
        let falsity = s.bool_const(false);
        assert_eq!(out2, vec![falsity], "fact(5) == 121 must fold to false");
    }

    #[test]
    fn non_recursive_def_with_symbolic_arg_expands() {
        let mut s = solver();
        let f = s.declare_fun("f", &[Sort::Int], Sort::Int);
        let x = s.declare_const("x", Sort::Int);
        let one = int(&mut s, 1);
        let body = s.try_add(x, one).unwrap();
        let def = s.make_rec_fun_def(&[x], body);
        let mut defs = HashMap::new();
        defs.insert("f".to_string(), def);

        let n = s.declare_const("n", Sort::Int);
        let call = s.try_apply(&f, &[n]).unwrap();
        let out = s
            .try_expand_rec_defs(&[call], &defs, ROUNDS, BUDGET, None)
            .expect("non-recursive body expands in one round");
        let expected = s.try_add(n, one).unwrap();
        assert_eq!(out, vec![expected], "f(n) must expand to n + 1");
    }

    #[test]
    fn mutual_even_odd_ground_expansion() {
        let mut s = solver();
        let even = s.declare_fun("even", &[Sort::Int], Sort::Bool);
        let odd = s.declare_fun("odd", &[Sort::Int], Sort::Bool);
        let x = s.declare_const("x", Sort::Int);
        let zero = int(&mut s, 0);
        let one = int(&mut s, 1);
        let t = s.bool_const(true);
        let f_ = s.bool_const(false);
        let xm1 = s.try_sub(x, one).unwrap();
        let guard = s.try_le(x, zero).unwrap();
        let odd_call = s.try_apply(&odd, &[xm1]).unwrap();
        let even_body = s.try_ite(guard, t, odd_call).unwrap();
        let even_call = s.try_apply(&even, &[xm1]).unwrap();
        let odd_body = s.try_ite(guard, f_, even_call).unwrap();
        let mut defs = HashMap::new();
        defs.insert("even".to_string(), s.make_rec_fun_def(&[x], even_body));
        defs.insert("odd".to_string(), s.make_rec_fun_def(&[x], odd_body));

        let four = int(&mut s, 4);
        let call4 = s.try_apply(&even, &[four]).unwrap();
        let out = s
            .try_expand_rec_defs(&[call4], &defs, ROUNDS, BUDGET, None)
            .expect("even(4) must fully expand");
        assert_eq!(out, vec![t], "even(4) must fold to true");

        let three = int(&mut s, 3);
        let call3 = s.try_apply(&even, &[three]).unwrap();
        let out3 = s
            .try_expand_rec_defs(&[call3], &defs, ROUNDS, BUDGET, None)
            .expect("even(3) must fully expand");
        assert_eq!(out3, vec![f_], "even(3) must fold to false");
    }

    #[test]
    fn divergent_definition_fails_closed_with_depth() {
        let mut s = solver();
        let d = s.declare_fun("d", &[Sort::Int], Sort::Int);
        let x = s.declare_const("x", Sort::Int);
        let one = int(&mut s, 1);
        let rec = s.try_apply(&d, &[x]).unwrap();
        let body = s.try_add(one, rec).unwrap();
        let def = s.make_rec_fun_def(&[x], body);
        let mut defs = HashMap::new();
        defs.insert("d".to_string(), def);

        let five = int(&mut s, 5);
        let call = s.try_apply(&d, &[five]).unwrap();
        let goal = s.try_eq(call, five).unwrap();
        let err = s
            .try_expand_rec_defs(&[goal], &defs, ROUNDS, BUDGET, None)
            .expect_err("divergent definition must fail closed");
        assert!(
            matches!(
                err,
                RecExpandError::DepthExceeded(_) | RecExpandError::BudgetExceeded(_)
            ),
            "expected depth/budget failure, got {err:?}"
        );
    }

    #[test]
    fn self_reproducing_definition_fails_closed_no_progress() {
        let mut s = solver();
        let g = s.declare_fun("g", &[Sort::Int], Sort::Int);
        let x = s.declare_const("x", Sort::Int);
        let body = s.try_apply(&g, &[x]).unwrap(); // g(x) := g(x)
        let def = s.make_rec_fun_def(&[x], body);
        let mut defs = HashMap::new();
        defs.insert("g".to_string(), def);

        let five = int(&mut s, 5);
        let call = s.try_apply(&g, &[five]).unwrap();
        let err = s
            .try_expand_rec_defs(&[call], &defs, ROUNDS, BUDGET, None)
            .expect_err("g(x) := g(x) must fail closed");
        assert!(
            matches!(err, RecExpandError::UnsupportedShape(_)),
            "expected no-progress failure, got {err:?}"
        );
    }

    #[test]
    fn breadth_blowup_fails_closed_within_budget() {
        // fib-style over a SYMBOLIC argument: the guard never folds, so the
        // frontier doubles every round. Must fail closed fast (budget), not
        // hang.
        let mut s = solver();
        let fib = s.declare_fun("fib", &[Sort::Int], Sort::Int);
        let x = s.declare_const("x", Sort::Int);
        let one = int(&mut s, 1);
        let two = int(&mut s, 2);
        let guard = s.try_le(x, one).unwrap();
        let xm1 = s.try_sub(x, one).unwrap();
        let xm2 = s.try_sub(x, two).unwrap();
        let c1 = s.try_apply(&fib, &[xm1]).unwrap();
        let c2 = s.try_apply(&fib, &[xm2]).unwrap();
        let sum = s.try_add(c1, c2).unwrap();
        let body = s.try_ite(guard, x, sum).unwrap();
        let def = s.make_rec_fun_def(&[x], body);
        let mut defs = HashMap::new();
        defs.insert("fib".to_string(), def);

        let n = s.declare_const("n", Sort::Int);
        let call = s.try_apply(&fib, &[n]).unwrap();
        let start = std::time::Instant::now();
        let err = s
            .try_expand_rec_defs(&[call], &defs, ROUNDS, 200_000, None)
            .expect_err("symbolic fib must fail closed");
        assert!(
            matches!(
                err,
                RecExpandError::BudgetExceeded(_) | RecExpandError::DepthExceeded(_)
            ),
            "expected budget/depth failure, got {err:?}"
        );
        assert!(
            start.elapsed() < std::time::Duration::from_secs(10),
            "budget must bound WORK, not just expansions"
        );
    }

    #[test]
    fn zero_ary_definition_expands_both_shapes() {
        let mut s = solver();
        let c_decl = s.declare_fun("c", &[], Sort::Int);
        let five = int(&mut s, 5);
        let def = s.make_rec_fun_def(&[], five);
        let mut defs = HashMap::new();
        defs.insert("c".to_string(), def);

        // App shape: `c()` built through apply.
        let app_shape = s.try_apply(&c_decl, &[]).unwrap();
        // Var shape: the interned constant `c`.
        let var_shape = s.declare_const("c", Sort::Int);
        let out = s
            .try_expand_rec_defs(&[app_shape, var_shape], &defs, ROUNDS, BUDGET, None)
            .expect("0-ary def must expand");
        assert_eq!(out, vec![five, five], "both 0-ary shapes must expand to 5");
    }

    #[test]
    fn expansion_under_forall_body() {
        let mut s = solver();
        let f = s.declare_fun("f", &[Sort::Int], Sort::Int);
        let x = s.declare_const("x", Sort::Int);
        let one = int(&mut s, 1);
        let body = s.try_add(x, one).unwrap();
        let def = s.make_rec_fun_def(&[x], body);
        let mut defs = HashMap::new();
        defs.insert("f".to_string(), def);

        let y = s.declare_const("y", Sort::Int);
        let call = s.try_apply(&f, &[y]).unwrap();
        let ge = s.try_ge(call, y).unwrap();
        let quant = s.try_forall(&[y], ge).unwrap();
        let out = s
            .try_expand_rec_defs(&[quant], &defs, ROUNDS, BUDGET, None)
            .expect("expansion under a forall body must work");
        let y_plus_1 = s.try_add(y, one).unwrap();
        let expected_body = s.try_ge(y_plus_1, y).unwrap();
        let expected = s.try_forall(&[y], expected_body).unwrap();
        assert_eq!(out, vec![expected]);
    }

    #[test]
    fn arity_mismatch_fails_closed() {
        let mut s = solver();
        let f = s.declare_fun("f", &[Sort::Int], Sort::Int);
        let x = s.declare_const("x", Sort::Int);
        let one = int(&mut s, 1);
        let body = s.try_add(x, one).unwrap();
        let def = s.make_rec_fun_def(&[x], body);
        let mut defs = HashMap::new();
        defs.insert("f".to_string(), def);
        let _ = f;

        // Raw two-argument application of the 1-ary defined name.
        let a = s.declare_const("a", Sort::Int);
        let b = s.declare_const("b", Sort::Int);
        let bad = Term(
            s.terms_mut()
                .mk_app(Symbol::named("f"), vec![a.0, b.0], Sort::Int),
        );
        let err = s
            .try_expand_rec_defs(&[bad], &defs, ROUNDS, BUDGET, None)
            .expect_err("arity mismatch must fail closed");
        assert!(matches!(err, RecExpandError::UnsupportedShape(_)));
    }

    #[test]
    fn argument_sort_mismatch_fails_closed() {
        let mut s = solver();
        let x = s.declare_const("x", Sort::Int);
        let one = int(&mut s, 1);
        let body = s.try_add(x, one).unwrap();
        let def = s.make_rec_fun_def(&[x], body);
        let mut defs = HashMap::new();
        defs.insert("f".to_string(), def);

        // Raw application with a Real argument against the Int parameter.
        let r = s.declare_const("r", Sort::Real);
        let bad = Term(
            s.terms_mut()
                .mk_app(Symbol::named("f"), vec![r.0], Sort::Int),
        );
        let err = s
            .try_expand_rec_defs(&[bad], &defs, ROUNDS, BUDGET, None)
            .expect_err("argument sort mismatch must fail closed");
        assert!(matches!(err, RecExpandError::UnsupportedShape(_)));
    }

    #[test]
    fn argument_captured_by_body_binder_fails_closed() {
        // def f(x) := forall ((y Int)) (y <= x); goal f(y) with the global y:
        // substitution would capture the actual argument. Must fail closed.
        let mut s = solver();
        let f = s.declare_fun("f", &[Sort::Int], Sort::Bool);
        let x = s.declare_const("x", Sort::Int);
        let y = s.declare_const("y", Sort::Int);
        let le = s.try_le(y, x).unwrap();
        let body = s.try_forall(&[y], le).unwrap();
        let def = s.make_rec_fun_def(&[x], body);
        assert!(def.is_expandable(), "binder shadows no PARAM name");
        let mut defs = HashMap::new();
        defs.insert("f".to_string(), def);

        let call = s.try_apply(&f, &[y]).unwrap();
        let err = s
            .try_expand_rec_defs(&[call], &defs, ROUNDS, BUDGET, None)
            .expect_err("argument capture must fail closed");
        assert!(matches!(err, RecExpandError::UnsupportedShape(_)));

        // A NON-colliding argument still expands.
        let z = s.declare_const("z", Sort::Int);
        let call_z = s.try_apply(&f, &[z]).unwrap();
        let out = s
            .try_expand_rec_defs(&[call_z], &defs, ROUNDS, BUDGET, None)
            .expect("non-capturing argument must expand");
        let le_z = s.try_le(y, z).unwrap();
        let expected = s.try_forall(&[y], le_z).unwrap();
        assert_eq!(out, vec![expected]);
    }

    #[test]
    fn goal_binder_rebinding_zero_ary_def_name_fails_closed() {
        // def c := 5; goal (exists ((c Int)) (= c 7)) — the bound c is the
        // SAME interned Var, so expansion would wrongly rewrite it to 5.
        let mut s = solver();
        let five = int(&mut s, 5);
        let def = s.make_rec_fun_def(&[], five);
        let mut defs = HashMap::new();
        defs.insert("c".to_string(), def);

        let c = s.declare_const("c", Sort::Int);
        let seven = int(&mut s, 7);
        let eq = s.try_eq(c, seven).unwrap();
        let goal = s.try_exists(&[c], eq).unwrap();
        let err = s
            .try_expand_rec_defs(&[goal], &defs, ROUNDS, BUDGET, None)
            .expect_err("goal binder rebinding a def name must fail closed");
        assert!(matches!(err, RecExpandError::UnsupportedShape(_)));
    }

    #[test]
    fn body_binder_shadowing_param_is_not_expandable() {
        // def f(x) := forall ((x Int)) ... — the body binder shadows the
        // parameter; registration marks it non-expandable, and every use
        // fails closed.
        let mut s = solver();
        let f = s.declare_fun("f", &[Sort::Int], Sort::Bool);
        let x = s.declare_const("x", Sort::Int);
        let zero = int(&mut s, 0);
        let ge = s.try_ge(x, zero).unwrap();
        let body = s.try_forall(&[x], ge).unwrap();
        let def = s.make_rec_fun_def(&[x], body);
        assert!(!def.is_expandable());
        let mut defs = HashMap::new();
        defs.insert("f".to_string(), def);

        let three = int(&mut s, 3);
        let call = s.try_apply(&f, &[three]).unwrap();
        let err = s
            .try_expand_rec_defs(&[call], &defs, ROUNDS, BUDGET, None)
            .expect_err("use of a non-expandable def must fail closed");
        assert!(matches!(err, RecExpandError::UnsupportedShape(_)));
    }

    #[test]
    fn trigger_only_occurrence_is_not_residual() {
        // A rec-f application appearing ONLY in a quantifier pattern is
        // semantically inert: expansion must succeed and leave the goal
        // unchanged (never spin, never demote).
        let mut s = solver();
        let f = s.declare_fun("f", &[Sort::Int], Sort::Int);
        let x = s.declare_const("x", Sort::Int);
        let one = int(&mut s, 1);
        let fx_body = s.try_add(x, one).unwrap();
        let def = s.make_rec_fun_def(&[x], fx_body);
        let mut defs = HashMap::new();
        defs.insert("f".to_string(), def);

        let p = s.declare_fun("p", &[Sort::Int], Sort::Bool);
        let y = s.declare_const("y", Sort::Int);
        let py = s.try_apply(&p, &[y]).unwrap();
        let fy = s.try_apply(&f, &[y]).unwrap();
        let trigger = [fy];
        let quant = s.try_forall_with_triggers(&[y], py, &[&trigger]).unwrap();
        let out = s
            .try_expand_rec_defs(&[quant], &defs, ROUNDS, BUDGET, None)
            .expect("trigger-only occurrence must not be residual");
        assert_eq!(out, vec![quant], "trigger-only goal must be unchanged");
    }

    #[test]
    fn contains_rec_fun_apps_is_conservative() {
        let mut s = solver();
        let f = s.declare_fun("f", &[Sort::Int], Sort::Int);
        let x = s.declare_const("x", Sort::Int);
        let one = int(&mut s, 1);
        let body = s.try_add(x, one).unwrap();
        let def = s.make_rec_fun_def(&[x], body);
        let mut defs = HashMap::new();
        defs.insert("f".to_string(), def);

        let three = int(&mut s, 3);
        let call = s.try_apply(&f, &[three]).unwrap();
        let goal = s.try_eq(call, three).unwrap();
        assert!(s.contains_rec_fun_apps(&[goal], &defs));

        let clean = s.try_eq(three, three).unwrap();
        assert!(!s.contains_rec_fun_apps(&[clean], &defs));
    }

    #[test]
    fn builtin_operator_def_name_is_refused_by_expansion() {
        // Defense in depth behind the FFI registration guard: a registry that
        // somehow contains a '+' definition must make expansion FAIL, never
        // splice a body into builtin arithmetic (the '+':='*' wrong-sat class).
        let mut s = solver();
        let x = s.declare_const("x", Sort::Int);
        let y = s.declare_const("y", Sort::Int);
        let body = s.try_mul(x, y).unwrap();
        let def = s.make_rec_fun_def(&[x, y], body);
        let mut defs = HashMap::new();
        defs.insert("+".to_string(), def);

        let two = int(&mut s, 2);
        let goal = s.try_eq(two, two).unwrap();
        let err = s
            .try_expand_rec_defs(&[goal], &defs, ROUNDS, BUDGET, None)
            .expect_err("a builtin-operator def name must fail closed");
        assert!(matches!(err, RecExpandError::UnsupportedShape(_)));
        assert!(rec_def_name_conflates_with_builtin("+"));
        assert!(rec_def_name_conflates_with_builtin("and"));
        assert!(rec_def_name_conflates_with_builtin("ite"));
        assert!(rec_def_name_conflates_with_builtin("abs"));
        assert!(rec_def_name_conflates_with_builtin("select")); // reserved table
        assert!(!rec_def_name_conflates_with_builtin("fact"));
    }

    #[test]
    fn expansion_deadline_fails_closed_with_time_exceeded() {
        // A divergent definition with an already-expired deadline must return
        // TimeExceeded promptly instead of grinding depth/budget down.
        let mut s = solver();
        let d = s.declare_fun("d", &[Sort::Int], Sort::Int);
        let x = s.declare_const("x", Sort::Int);
        let one = int(&mut s, 1);
        let rec = s.try_apply(&d, &[x]).unwrap();
        let body = s.try_add(one, rec).unwrap();
        let def = s.make_rec_fun_def(&[x], body);
        let mut defs = HashMap::new();
        defs.insert("d".to_string(), def);

        let five = int(&mut s, 5);
        let call = s.try_apply(&d, &[five]).unwrap();
        let started = std::time::Instant::now();
        let expired = std::time::Instant::now() - std::time::Duration::from_millis(1);
        let err = s
            .try_expand_rec_defs(&[call], &defs, ROUNDS, BUDGET, Some(expired))
            .expect_err("an expired deadline must fail closed");
        assert!(
            matches!(err, RecExpandError::TimeExceeded(_)),
            "expected TimeExceeded, got {err:?}"
        );
        assert!(
            started.elapsed() < std::time::Duration::from_secs(2),
            "deadline must bound wall time"
        );
        // A live deadline leaves ground expansion untouched.
        let (fdefs, fact) = define_fact(&mut s);
        let five2 = int(&mut s, 5);
        let fcall = s.try_apply(&fact, &[five2]).unwrap();
        let target = int(&mut s, 120);
        let goal = s.try_eq(fcall, target).unwrap();
        let live = std::time::Instant::now() + std::time::Duration::from_secs(5);
        let out = s
            .try_expand_rec_defs(&[goal], &fdefs, ROUNDS, BUDGET, Some(live))
            .expect("ground factorial must expand under a live deadline");
        let truth = s.bool_const(true);
        assert_eq!(out, vec![truth]);
    }

    #[test]
    fn terms_mention_names_sees_apps_and_vars() {
        let mut s = solver();
        let f = s.declare_fun("fm", &[Sort::Int], Sort::Int);
        let x = s.declare_const("xm", Sort::Int);
        let call = s.try_apply(&f, &[x]).unwrap();
        let goal = s.try_eq(call, x).unwrap();
        let mut names = HashSet::new();
        names.insert("fm".to_string());
        assert!(s.terms_mention_names(&[goal], &names));
        let mut names2 = HashSet::new();
        names2.insert("xm".to_string());
        assert!(s.terms_mention_names(&[goal], &names2));
        let mut names3 = HashSet::new();
        names3.insert("absent".to_string());
        assert!(!s.terms_mention_names(&[goal], &names3));
    }

    #[test]
    fn rec_def_names_reaching_undefined_is_transitive() {
        // f := g(x) + 1 (g DEFINED, g := u(x)), u rec-declared but UNDEFINED:
        // both f and g must be reported as reaching u; an unrelated def is not.
        let mut s = solver();
        let g = s.declare_fun("g", &[Sort::Int], Sort::Int);
        let u = s.declare_fun("u", &[Sort::Int], Sort::Int);
        let x = s.declare_const("x", Sort::Int);
        let one = int(&mut s, 1);

        let ux = s.try_apply(&u, &[x]).unwrap();
        let g_def = s.make_rec_fun_def(&[x], ux);
        let gx = s.try_apply(&g, &[x]).unwrap();
        let f_body = s.try_add(gx, one).unwrap();
        let f_def = s.make_rec_fun_def(&[x], f_body);
        let clean_body = s.try_add(x, one).unwrap();
        let clean_def = s.make_rec_fun_def(&[x], clean_body);

        let mut defs = HashMap::new();
        defs.insert("f".to_string(), f_def);
        defs.insert("g".to_string(), g_def);
        defs.insert("clean".to_string(), clean_def);

        let mut undefined = HashSet::new();
        undefined.insert("u".to_string());
        let tainted = s.rec_def_names_reaching(&defs, &undefined);
        assert!(tainted.contains("g"), "g mentions u directly");
        assert!(tainted.contains("f"), "f reaches u through g");
        assert!(
            !tainted.contains("clean"),
            "a downstream checker does not reach u"
        );
    }
}
