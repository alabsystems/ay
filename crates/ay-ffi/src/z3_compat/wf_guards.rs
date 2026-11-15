// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Well-formedness guards of free symbols whose values lower lossily (T5 P0
//! Q12, design §2.10).
//!
//! `Char` and finite-domain values lower to engine `Int`s, so a free symbol
//! whose value holds one may take engine values that are not public values.
//! Each such symbol gets `wf`, built once at declaration:
//!
//! * `wf_Char(x) = 0 <= x <= 196607`, `wf_FD(n)(x) = 0 <= x < n`;
//! * `wf_Array(I, E)(a) = ∀i. wf_E(a[i])` (an index of a bounded sort is
//!   relativized to its carrier);
//! * for a non-recursive datatype `D`, `wf_D(d) = ∧_{c,j} wf(acc_cj(d))` over
//!   every field of every constructor (an accessor of another constructor's
//!   value is still a value of the field's sort), quantifier-free unless a
//!   field is an array;
//! * a function `f` is guarded by `∀x̄. wf(f(x̄))` (trigger `f(x̄)`).
//!
//! A symbol AY cannot guard (a recursive datatype, a sequence of a bounded
//! element sort, an array index with a nested bounded component) is
//! registered with the reason instead.
//!
//! The Solver check asserts the quantifier-free guards of the symbols its
//! goal reaches, and validates a SAT model against the quantified ones
//! instead of asserting them: the engine cannot certify `sat` beside
//! `∀i. wf(A[i])` (measured: `A[0] == CharVal('a')` over
//! `Array(Int, Char)` answered `unknown` with the guard, `sat` in libz3
//! 5.1.0), while a model whose values of every guarded symbol are public
//! values is a model of the goal and its guards. A model that is not, or an
//! `unknown`, re-checks with every guard asserted; a goal with a binder takes
//! the two checks in the other order (see [`WfPhase`] and
//! [`validate_wf_model`]). An Optimize check does the same for a handle with
//! at most one objective, whose optimum must also be attained and finite.

use std::collections::{BTreeSet, HashSet};

use ay_dpll::api::{de_bruijn_index, DatatypeSort, FuncDecl, SolverError, Sort, Term, TermKind};

use super::{bounded_sort_hi, finite_set_engine_public_sort, range_guard_term, Z3Context};

/// Datatype and array nesting deeper than this is not guarded.
const MAX_WF_DEPTH: u32 = 16;

/// A free symbol's well-formedness guard (see the module docs).
pub(crate) struct WfGuard {
    /// The guard, or why it could not be built.
    guard: Result<Term, String>,
    /// Whether the guard holds a quantifier (a function's or an array's).
    quantified: bool,
    /// A missing guard of a sort AY does not guard (rather than an engine
    /// error building one): it refuses only the goals with a binder, and a
    /// goal without one validates the symbol's model value instead. A ground
    /// `Char` term the API builds carries its own range axiom
    /// (`record_ast_sort`).
    structural: bool,
    /// The public sort of the symbol's value (a function's range).
    sort: Sort,
    /// Whether the symbol is a function of arity > 0 (its model value is a
    /// table).
    function: bool,
}

/// A built guard term.
struct Built {
    term: Term,
    quantified: bool,
}

/// Why no guard could be built: a sort AY does not guard (`structural`), or
/// an engine error.
struct Missing {
    reason: String,
    structural: bool,
}

fn engine(e: SolverError) -> Missing {
    Missing {
        reason: e.to_string(),
        structural: false,
    }
}

fn structural(reason: String) -> Missing {
    Missing {
        reason,
        structural: true,
    }
}

/// Whether `sort` holds a `Char` or finite-domain component anywhere.
pub(crate) fn mentions_bounded_scalar(sort: &Sort, datatypes: &mut HashSet<String>) -> bool {
    match sort {
        Sort::Char | Sort::FiniteDomain(..) => true,
        Sort::Array(array) => {
            mentions_bounded_scalar(&array.index_sort, datatypes)
                || mentions_bounded_scalar(&array.element_sort, datatypes)
        }
        Sort::Seq(element) => mentions_bounded_scalar(element, datatypes),
        Sort::Datatype(dt) => {
            datatypes.insert(dt.name.clone())
                && dt.constructors.iter().any(|ctor| {
                    ctor.fields
                        .iter()
                        .any(|field| mentions_bounded_scalar(&field.sort, datatypes))
                })
        }
        _ => false,
    }
}

fn mentions(sort: &Sort) -> bool {
    mentions_bounded_scalar(sort, &mut HashSet::new())
}

/// Whether a value of public sort `sort` needs a well-formedness guard (or
/// the refusal that stands in for one): it holds a `Char` / finite-domain
/// component anywhere but in an array index.
pub(crate) fn needs_wf_guard(sort: &Sort) -> bool {
    match sort {
        Sort::Array(array) => needs_wf_guard(&array.element_sort),
        other => mentions(other),
    }
}

/// Whether a field of `dt` refers back to `dt` (AY spells a self-reference
/// `Uninterpreted(name)`), directly or through arrays, sequences or other
/// datatypes.
fn is_recursive_datatype(dt: &DatatypeSort) -> bool {
    fn refers(sort: &Sort, name: &str, seen: &mut HashSet<String>) -> bool {
        match sort {
            Sort::Uninterpreted(other) => other == name,
            Sort::Array(array) => {
                refers(&array.index_sort, name, seen) || refers(&array.element_sort, name, seen)
            }
            Sort::Seq(element) => refers(element, name, seen),
            Sort::Datatype(inner) => {
                inner.name == name
                    || (seen.insert(inner.name.clone())
                        && inner.constructors.iter().any(|ctor| {
                            ctor.fields
                                .iter()
                                .any(|field| refers(&field.sort, name, seen))
                        }))
            }
            _ => false,
        }
    }
    let mut seen = HashSet::new();
    dt.constructors.iter().any(|ctor| {
        ctor.fields
            .iter()
            .any(|field| refers(&field.sort, &dt.name, &mut seen))
    })
}

/// `wf(t)` for a term `t` of public sort `sort` (see the module docs);
/// `None` when the sort needs no guard.
fn wf_term(
    ctx: &mut Z3Context,
    t: Term,
    sort: &Sort,
    depth: u32,
) -> Result<Option<Built>, Missing> {
    if let Some(hi) = bounded_sort_hi(sort) {
        let term = range_guard_term(ctx, t, hi);
        return Ok(Some(Built {
            term,
            quantified: false,
        }));
    }
    if !mentions(sort) {
        return Ok(None);
    }
    if depth > MAX_WF_DEPTH {
        return Err(structural(format!("the sort {sort} nests too deeply")));
    }
    match sort {
        Sort::Array(_) => closed_wf(ctx, Vec::new(), t, sort, depth),
        // A datatype guard the engine cannot build is treated as one AY does
        // not guard (see `WfGuard::structural`).
        Sort::Datatype(dt) if !is_recursive_datatype(dt) => {
            datatype_wf(ctx, t, dt, depth).map_err(|missing| structural(missing.reason))
        }
        other => Err(structural(format!(
            "the sort {other} holds a Char or finite-domain component that AY lowers to an \
             unbounded Int and does not guard"
        ))),
    }
}

/// `∀vars. wf(t)` for a term `t` of public sort `sort` over the bound
/// `vars` (none for a constant), descending through array sorts into the
/// same quantifier: `∀x̄, i, j. wf(f(x̄)[i][j])`, one quantifier over every
/// index with the innermost select as its trigger, as the engine instantiates
/// it (nested quantifiers left `code(AA[1][3]) > 196607` over
/// `Array(Int, Array(Int, Char))` undecided where the flat one is unsat). An
/// index of a bounded sort is relativized to its carrier.
fn closed_wf(
    ctx: &mut Z3Context,
    mut vars: Vec<Term>,
    t: Term,
    sort: &Sort,
    depth: u32,
) -> Result<Option<Built>, Missing> {
    let mut current = t;
    let mut sort = sort;
    let mut carriers = Vec::new();
    while let Sort::Array(array) = sort {
        if !mentions(&array.element_sort) {
            // Only the index is bounded: the elements need no guard (array
            // extensionality over a bounded index is `bounded_arrays`').
            return Ok(None);
        }
        let index_sort = &array.index_sort;
        if bounded_sort_hi(index_sort).is_none() && mentions(index_sort) {
            return Err(structural(format!(
                "the index sort {index_sort} has a nested Char or finite-domain component"
            )));
        }
        let engine_index = finite_set_engine_public_sort(ctx, index_sort);
        let index = ctx
            .solver
            .try_fresh_var("ay_wf_index", engine_index)
            .map_err(engine)?;
        if let Some(hi) = bounded_sort_hi(index_sort) {
            carriers.push(range_guard_term(ctx, index, hi));
        }
        current = ctx.solver.try_select(current, index).map_err(engine)?;
        vars.push(index);
        sort = &array.element_sort;
    }
    let Some(inner) = wf_term(ctx, current, sort, depth + 1)? else {
        return Ok(None);
    };
    let body = if carriers.is_empty() {
        inner.term
    } else {
        let carrier = ctx.solver.try_and_many(&carriers).map_err(engine)?;
        ctx.solver
            .try_implies(carrier, inner.term)
            .map_err(engine)?
    };
    if vars.is_empty() {
        return Ok(Some(Built {
            term: body,
            quantified: inner.quantified,
        }));
    }
    let term = ctx
        .solver
        .try_forall_with_triggers(&vars, body, &[&[current]])
        .map_err(engine)?;
    Ok(Some(Built {
        term,
        quantified: true,
    }))
}

/// `∧_{c,j} wf(acc_cj(d))` for a non-recursive datatype: every field of
/// every constructor, not only the fields of `d`'s own constructor. An
/// accessor applied to a value of another constructor is a value of the
/// field's sort in z3 (`k(m2(2))` is some `Char`), while AY's engine leaves
/// it free (measured: `k(m2(2)) = 1001` for an `Int` field), so the guard is
/// satisfiable and keeps `Exists x. code(k(ite(x > 0, d, e))) > 196607`
/// unsat when `d` and `e` are built by another constructor.
fn datatype_wf(
    ctx: &mut Z3Context,
    value: Term,
    dt: &DatatypeSort,
    depth: u32,
) -> Result<Option<Built>, Missing> {
    let mut conjuncts = Vec::new();
    let mut quantified = false;
    for field in dt.constructors.iter().flat_map(|ctor| &ctor.fields) {
        if !mentions(&field.sort) {
            continue;
        }
        let access = ctx
            .solver
            .try_datatype_selector(&field.name, value, field.sort.clone())
            .map_err(engine)?;
        if let Some(guard) = wf_term(ctx, access, &field.sort, depth + 1)? {
            quantified |= guard.quantified;
            conjuncts.push(guard.term);
        }
    }
    if conjuncts.is_empty() {
        return Ok(None);
    }
    let term = ctx.solver.try_and_many(&conjuncts).map_err(engine)?;
    Ok(Some(Built { term, quantified }))
}

fn register(
    ctx: &mut Z3Context,
    name: String,
    built: Result<Built, Missing>,
    sort: &Sort,
    function: bool,
) {
    let entry = match built {
        Ok(built) => WfGuard {
            guard: Ok(built.term),
            quantified: built.quantified,
            structural: false,
            sort: sort.clone(),
            function,
        },
        Err(missing) => WfGuard {
            guard: Err(missing.reason),
            quantified: false,
            structural: missing.structural,
            sort: sort.clone(),
            function,
        },
    };
    ctx.wf_guards.insert(name, entry);
}

/// Register the guard `∀x̄. wf(f(x̄))` of the free function `decl` (public
/// signature `domain -> range`), when its range needs one. A guard that
/// cannot be built is registered with its reason.
pub(crate) fn register_function_wf_guard(
    ctx: &mut Z3Context,
    decl: &FuncDecl,
    domain: &[Sort],
    range: &Sort,
) {
    if !needs_wf_guard(range) || ctx.wf_guards.contains_key(decl.name()) {
        return;
    }
    let built = function_guard(ctx, decl, domain, range);
    match built {
        Ok(None) => {}
        Ok(Some(built)) => register(
            ctx,
            decl.name().to_string(),
            Ok(built),
            range,
            !domain.is_empty(),
        ),
        Err(missing) => {
            register(
                ctx,
                decl.name().to_string(),
                Err(missing),
                range,
                !domain.is_empty(),
            );
        }
    }
}

fn function_guard(
    ctx: &mut Z3Context,
    decl: &FuncDecl,
    domain: &[Sort],
    range: &Sort,
) -> Result<Option<Built>, Missing> {
    let mut vars = Vec::with_capacity(domain.len());
    for sort in domain {
        let engine_sort = finite_set_engine_public_sort(ctx, sort);
        vars.push(
            ctx.solver
                .try_fresh_var("ay_wf_arg", engine_sort)
                .map_err(engine)?,
        );
    }
    let head = ctx.solver.try_apply(decl, &vars).map_err(engine)?;
    closed_wf(ctx, vars, head, range, 0)
}

/// Register the guard of a free constant `term` of public sort `sort` whose
/// value is not itself a `Char` / finite-domain value (those carry a ground
/// range axiom) but holds one: an array, a datatype or a sequence with such
/// a component. Once per constant.
pub(crate) fn register_constant_wf_guard(ctx: &mut Z3Context, term: Term, sort: &Sort) {
    if bounded_sort_hi(sort).is_some() || !needs_wf_guard(sort) {
        return;
    }
    let TermKind::Var { name } = ctx.solver.term_kind(term) else {
        return;
    };
    if de_bruijn_index(&name).is_some() || ctx.wf_guards.contains_key(&name) {
        return;
    }
    match wf_term(ctx, term, sort, 0) {
        Ok(None) => {}
        Ok(Some(built)) => register(ctx, name, Ok(built), sort, false),
        Err(missing) => register(ctx, name, Err(missing), sort, false),
    }
}

/// A reached symbol whose model value a SAT answer must validate.
pub(crate) struct WfCheck {
    name: String,
    sort: Sort,
    function: bool,
    /// Whether it has a (quantified) guard; `false` for a missing guard.
    guarded: bool,
    /// Why its guard is missing (for a missing guard).
    reason: String,
}

/// The well-formedness obligations of one goal (see the module docs).
pub(crate) struct WfObligations {
    /// Quantifier-free guards, asserted by every check.
    pub(crate) eager: Vec<Term>,
    /// Quantified guards, asserted by a re-check only.
    pub(crate) lazy: Vec<Term>,
    /// The symbols a SAT model is validated for.
    pub(crate) checks: Vec<WfCheck>,
    /// Whether a binder (quantifier or lambda) occurs in the goal.
    pub(crate) binder: bool,
}

/// The well-formedness obligations of the symbols `names` names (see
/// [`WfObligations`]), or the refusal for a reached symbol without a guard:
/// one an engine error left unbuilt, or one of a sort AY does not guard in a
/// goal with a binder.
pub(crate) fn wf_obligations(
    ctx: &Z3Context,
    names: &BTreeSet<String>,
    binder: bool,
) -> Result<WfObligations, String> {
    let mut obligations = WfObligations {
        eager: Vec::new(),
        lazy: Vec::new(),
        checks: Vec::new(),
        binder,
    };
    for name in names {
        let Some(entry) = ctx.wf_guards.get(name) else {
            continue;
        };
        let check = |guarded: bool, reason: &str| WfCheck {
            name: name.clone(),
            sort: entry.sort.clone(),
            function: entry.function,
            guarded,
            reason: reason.to_string(),
        };
        match &entry.guard {
            Ok(guard) if entry.quantified => {
                obligations.lazy.push(*guard);
                obligations.checks.push(check(true, ""));
            }
            Ok(guard) => obligations.eager.push(*guard),
            // A goal without a binder validates the symbol's model value; a
            // goal with one is refused, as an accessor of a constructor the
            // value does not have, applied under the binder, may escape the
            // sort where no guard reaches it.
            Err(reason) if entry.structural && !binder => {
                obligations.checks.push(check(false, reason));
            }
            Err(reason) => {
                return Err(format!(
                    "{}: a Char or finite-domain valued symbol of the goal has no \
                     well-formedness guard ({reason}); the goal is not decided",
                    super::ffi_surface_text(ctx, name)
                ));
            }
        }
    }
    Ok(obligations)
}

#[path = "wf_guards_phase.rs"]
mod phase;
pub(crate) use phase::{recheck_due, WfPhase};

#[path = "wf_guards_model.rs"]
mod model;
pub(crate) use model::{validate_wf_model, WfVerdict};

/// Every guard of `obligations`, in the order a check asserts them: what an
/// auxiliary query that does not validate a model (consequences, implied
/// equalities) asserts.
pub(crate) fn eager_guards(obligations: &WfObligations) -> Vec<Term> {
    let mut guards = obligations.eager.clone();
    guards.extend(obligations.lazy.iter().copied());
    guards
}
