// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible model and params functions.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via
//! the `ffi_guard_*` helpers (#6192) to prevent undefined behavior from panics
//! unwinding across the `extern "C"` boundary.
//!
//! # The model handle is a genuine snapshot
//!
//! A `Z3_model` wraps the [`Model`] materialized at check time. Every model
//! query in this module — `Z3_model_eval`, `Z3_model_get_const_interp`,
//! enumeration, printing — reads ONLY that snapshot (plus the context's term
//! store, which is append-only). Nothing here consults the live solver's
//! last-check state, so a model handle stays valid and correct after the
//! solver is reused (later checks, push/pop, UNSAT), matching Z3 semantics.
//!
//! `Z3_model_eval` evaluates compound terms by substituting every model-pinned
//! constant with its snapshot value term and re-running AY's eager
//! semantics-preserving fold (`Solver::substitute` + `Solver::simplify`). The
//! result is therefore always a term that is EQUAL to the input under the
//! model: either a literal (fully reduced) or an honest partial evaluation.
//! It never fabricates a value and never reads live solver state.

use std::collections::HashMap as StdHashMap;
use std::collections::HashSet;
use std::ffi::{c_char, c_double, c_uint};
use std::ptr;

use ay_dpll::api::{FpSpecialKind, FuncDecl, Model, ModelValue, Solver, Sort, Term, TermKind};
use num_traits::Signed;

use super::{
    alloc_sort, cache_ast_vector, cache_func_decl, cache_func_decl_with_symbol, cache_func_entry,
    cache_func_interp, cache_string, ffi_guard_const_ptr, ffi_guard_int, ffi_guard_produced,
    ffi_guard_ptr, ffi_guard_uint, ffi_guard_void, record_ast_sort, require_term_ast_or_return,
    term_to_ast, ModelHandle, ParamsHandle, Z3Context, Z3_ast, Z3_ast_vector, Z3_context,
    Z3_func_decl, Z3_func_entry, Z3_func_interp, Z3_model, Z3_params, Z3_sort, Z3_symbol,
};

// ---- Snapshot-model helpers ----

mod floating_point;
mod symbolic_else;
mod value_folds;

/// Sort implied by a scalar model value, if it is one.
fn scalar_value_sort(val: &ModelValue) -> Option<Sort> {
    match val {
        ModelValue::Bool(_) => Some(Sort::Bool),
        ModelValue::Int(_) => Some(Sort::Int),
        ModelValue::Real(_) => Some(Sort::Real),
        ModelValue::FiniteField { field, .. } => Some(Sort::FiniteField(*field)),
        ModelValue::BitVec { width, .. } => Some(Sort::bitvec(*width)),
        ModelValue::String(_) => Some(Sort::String),
        ModelValue::FloatingPointExact(fields) => Some(Sort::FloatingPoint(
            fields.exponent_bits(),
            fields.significand_bits(),
        )),
        ModelValue::FloatingPoint { eb, sb, .. }
        | ModelValue::FloatingPointWide { eb, sb, .. }
        | ModelValue::FloatingPointSpecial { eb, sb, .. } => Some(Sort::FloatingPoint(*eb, *sb)),
        _ => None,
    }
}

/// Best-effort sort inference for a structured array value (used only when the
/// constant was not declared through this context, e.g. defensive fallback).
fn infer_array_sort(default: &ModelValue, stores: &[(ModelValue, ModelValue)]) -> Option<Sort> {
    let element = scalar_value_sort(default)
        .or_else(|| stores.first().and_then(|(_, v)| scalar_value_sort(v)))?;
    let index = stores
        .first()
        .and_then(|(k, _)| scalar_value_sort(k))
        .unwrap_or(Sort::Int);
    Some(Sort::array(index, element))
}

/// Declared-constant name → sort map for this context's solver.
///
/// Model entries are keyed by name; the declared sort is the authoritative
/// sort for non-scalar entries (arrays, sequences, datatypes, uninterpreted).
type DeclaredSorts = ay_core::kani_compat::DetHashMap<String, Sort>;

fn declared_sorts(solver: &Solver) -> DeclaredSorts {
    solver
        .declared_variables()
        .map(|(name, term)| (name.to_string(), solver.term_sort(term)))
        .collect()
}

/// Resolve the sort for a named model entry: declared sort first, then the
/// sort implied by the value, then a defensive fallback (so enumeration can
/// never drop an entry and misalign `num_consts` with `get_const_decl`).
fn resolve_entry_sort(declared: &DeclaredSorts, name: &str, val: &ModelValue) -> Sort {
    if let Some(sort) = declared.get(name) {
        return sort.clone();
    }
    if let Some(sort) = scalar_value_sort(val) {
        return sort;
    }
    match val {
        ModelValue::Array { default, stores } => {
            infer_array_sort(default, stores).unwrap_or_else(|| Sort::array(Sort::Int, Sort::Int))
        }
        ModelValue::ArraySmtlib(_) => Sort::array(Sort::Int, Sort::Int),
        ModelValue::Seq(elems) => Sort::seq(
            elems
                .first()
                .and_then(scalar_value_sort)
                .unwrap_or(Sort::Int),
        ),
        // Datatype / Uninterpreted / Unknown without a declaration: keep the
        // entry (alignment!) under an opaque sort named after the constant.
        _ => Sort::Uninterpreted(name.to_string()),
    }
}

/// Canonical enumeration of EVERY constant the model interprets, in a fixed
/// deterministic order (Bool, Int, Real, BitVec, String, FloatingPoint, Seq,
/// Array, Datatype, Uninterpreted — the same maps [`Model::len`] sums over).
///
/// This is the single index space shared by `Z3_model_get_num_consts`,
/// `Z3_model_get_const_decl` and `Z3_model_to_string`, so an index returned by
/// one is always valid for the others (the pre-fix mismatch — `num_consts`
/// counting arrays that `get_const_decl` skipped, surfacing as unnamed `None`
/// decls — cannot recur by construction).
fn model_entries(solver: &Solver, model: &Model) -> Vec<(String, Sort)> {
    let declared = declared_sorts(solver);
    let mut entries: Vec<(String, Sort)> = Vec::with_capacity(model.len());
    for (name, _) in model.iter_bools() {
        entries.push((name.to_string(), Sort::Bool));
    }
    for (name, _) in model.iter_ints() {
        entries.push((name.to_string(), Sort::Int));
    }
    for (name, _) in model.iter_reals() {
        entries.push((name.to_string(), Sort::Real));
    }
    for (name, (_, width)) in model.iter_bvs() {
        entries.push((name.to_string(), Sort::bitvec(*width)));
    }
    for (name, value) in model.iter_finite_fields() {
        entries.push((name.to_string(), resolve_entry_sort(&declared, name, value)));
    }
    for (name, _) in model.iter_strings() {
        entries.push((name.to_string(), Sort::String));
    }
    for (name, val) in model.iter_fps() {
        entries.push((name.to_string(), resolve_entry_sort(&declared, name, val)));
    }
    for (name, val) in model.iter_seqs() {
        entries.push((name.to_string(), resolve_entry_sort(&declared, name, val)));
    }
    for (name, val) in model.iter_arrays() {
        entries.push((name.to_string(), resolve_entry_sort(&declared, name, val)));
    }
    for (name, val) in model.iter_datatypes() {
        entries.push((name.to_string(), resolve_entry_sort(&declared, name, val)));
    }
    for (name, el) in model.iter_uninterpreteds() {
        let sort = declared
            .get(name)
            .cloned()
            .unwrap_or_else(|| Sort::Uninterpreted(el.to_string()));
        entries.push((name.to_string(), sort));
    }
    debug_assert_eq!(
        entries.len(),
        model.len(),
        "BUG: model entry enumeration must cover exactly the model's assignments"
    );
    entries
}

pub(crate) fn model_entry_display_name(ctx: &Z3Context, identity: &str) -> String {
    model_entry_display_name_owned(ctx, identity, None)
}

fn model_entry_display_name_owned(
    ctx: &Z3Context,
    identity: &str,
    owner: ay_core::render_admission::Owner<'_>,
) -> String {
    let symbol = ctx
        .ffi_const_terms_by_identity
        .get(identity)
        .and_then(|term| ctx.ffi_const_metadata.get(term))
        .map(|(_, symbol)| symbol);
    match symbol {
        Some(super::SymbolKey::String(name)) => ay_core::render_admission::quote(owner, name),
        Some(super::SymbolKey::Integer(value)) => {
            let display = ay_core::render_admission::format(owner, format_args!("s!{value}"));
            ay_core::render_admission::quote(owner, &display)
        }
        None => ay_core::render_admission::quote(owner, identity),
    }
}

/// Convert a snapshot [`ModelValue`] into a value TERM of the given sort.
///
/// Returns `None` when the value cannot be faithfully represented as a term
/// (an unparsed `ArraySmtlib` blob, an `Unknown`, a sort mismatch) — callers
/// treat that as an honest failure, NEVER as a fabricated value.
///
/// Array values become Z3-style store chains over a const-array base:
/// `(store ... ((as const (Array I E)) default) i v)`. Sequence values become
/// `seq.++`/`seq.unit` chains (`seq.empty` when empty), and uninterpreted-sort
/// elements become declared constants carrying the element's token name (the
/// same shape Z3's `S!val!k` universe elements print as).
pub(crate) fn model_value_to_term(
    solver: &mut Solver,
    val: &ModelValue,
    sort: &Sort,
) -> Option<Term> {
    match val {
        ModelValue::Bool(b) => Some(solver.bool_const(*b)),
        // An Int value used at Real sort (function tables print Real-sorted
        // integers as plain numerals) becomes an exact rational constant so
        // the substituted term keeps the surrounding term's sort discipline.
        ModelValue::Int(n) if matches!(sort, Sort::Real) => {
            let denom = num_bigint::BigInt::from(1);
            Some(solver.rational_const_bigint(n, &denom))
        }
        ModelValue::FiniteField { value, field }
            if sort == &Sort::FiniteField(*field) && *value < field.modulus() =>
        {
            Some(solver.finite_field_const(&(*value).into(), *field))
        }
        ModelValue::Int(n) => Some(solver.int_const_bigint(n)),
        ModelValue::Real(r) => Some(solver.rational_const_bigint(r.numer(), r.denom())),
        ModelValue::BitVec { value, width } => Some(solver.bv_const_bigint(value, *width)),
        ModelValue::String(s) => Some(solver.string_const(s)),
        ModelValue::FloatingPoint { .. }
        | ModelValue::FloatingPointWide { .. }
        | ModelValue::FloatingPointExact(_) => floating_point::value_to_term(solver, val, sort),
        ModelValue::FloatingPointSpecial { kind, eb, sb } => match kind {
            FpSpecialKind::PosZero => Some(solver.fp_plus_zero(*eb, *sb)),
            FpSpecialKind::NegZero => Some(solver.fp_minus_zero(*eb, *sb)),
            FpSpecialKind::PosInf => Some(solver.fp_plus_infinity(*eb, *sb)),
            FpSpecialKind::NegInf => Some(solver.fp_minus_infinity(*eb, *sb)),
            FpSpecialKind::NaN => Some(solver.fp_nan(*eb, *sb)),
            _ => None,
        },
        ModelValue::Uninterpreted(element) => match sort {
            // An element of an uninterpreted sort is a constant of that sort
            // whose name is the element token (hash-consed: the same element
            // always resolves to the same term).
            //
            // A sort the API sees as uninterpreted may be a datatype a parsed
            // text declared (its carrier name resolves to the datatype): the
            // token is then that datatype's nullary constructor. Any other
            // refusal leaves the value unrepresented rather than panicking
            // across the FFI boundary (measured: a text-declared enum value
            // `red` panicked in `declare_const`).
            Sort::Uninterpreted(name) => match solver.try_declare_const(element, sort.clone()) {
                Ok(term) => Some(term),
                Err(_) => match solver.resolve_sort_name(name) {
                    Some(datatype @ Sort::Datatype(_)) => {
                        model_value_to_term(solver, val, &datatype)
                    }
                    _ => None,
                },
            },
            // A type variable lowers to the uninterpreted sort of its name;
            // its elements are that sort's (one term per element, whichever
            // spelling of the sort asks first).
            Sort::TypeVar(name) => solver
                .try_declare_const(element, Sort::Uninterpreted(name.clone()))
                .ok(),
            // A bare symbol at a DATATYPE sort is a nullary constructor (an enum
            // literal like `blue`). The model-text parser stores it in the model's
            // uninterpreted map because a lone symbol is syntactically
            // indistinguishable from an uninterpreted-sort element token (it has
            // no argument list, unlike `(mk-pair 3 5)`); the declared datatype
            // sort recorded here disambiguates it. Resolve it to the matching
            // nullary constructor term so `Z3_model_get_const_interp` /
            // `Z3_model_eval` surface `blue` rather than nothing (#phase3-dt).
            Sort::Datatype(dt) => {
                let ctor = dt.constructors.iter().find(|c| c.name == *element)?;
                if !ctor.fields.is_empty() {
                    // A non-nullary constructor cannot appear as a bare symbol;
                    // refuse rather than build an ill-formed nullary application.
                    return None;
                }
                let dt = dt.clone();
                solver.try_datatype_constructor(&dt, element, &[]).ok()
            }
            _ => None,
        },
        ModelValue::Array { default, stores } => {
            let Sort::Array(arr) = sort else { return None };
            let default_term = model_value_to_term(solver, default, &arr.element_sort)?;
            let mut acc = solver.const_array(arr.index_sort.clone(), default_term);
            for (index, value) in stores {
                let index_term = model_value_to_term(solver, index, &arr.index_sort)?;
                let value_term = model_value_to_term(solver, value, &arr.element_sort)?;
                acc = solver.store(acc, index_term, value_term);
            }
            Some(acc)
        }
        // An array interpretation the parser could not structure: refusing is
        // the honest outcome (converting would mean re-parsing arbitrary text).
        ModelValue::ArraySmtlib(_) => None,
        ModelValue::Seq(elems) => {
            let Sort::Seq(element_sort) = sort else {
                return None;
            };
            let mut acc: Option<Term> = None;
            for elem in elems {
                let elem_term = model_value_to_term(solver, elem, element_sort)?;
                let unit = solver.seq_unit(elem_term);
                acc = Some(match acc {
                    None => unit,
                    Some(prefix) => solver.seq_concat(prefix, unit),
                });
            }
            Some(match acc {
                None => solver.seq_empty((**element_sort).clone()),
                Some(t) => t,
            })
        }
        ModelValue::Datatype { constructor, args } => {
            let Sort::Datatype(dt) = sort else {
                return None;
            };
            let ctor = dt.constructors.iter().find(|c| c.name == *constructor)?;
            if ctor.fields.len() != args.len() {
                return None;
            }
            // A self-referential field's declared sort is stored as
            // `Uninterpreted(dt.name)` (the datatype under construction resolves
            // its self-reference to an uninterpreted sort). Resolve it back to
            // the full `Datatype` sort so a NESTED constructor value (e.g. the
            // `tl` of a `cons`, or a datatype field holding another datatype)
            // recurses correctly instead of tripping the `Sort::Datatype` guard
            // and yielding no value (#phase3-dt).
            let field_sorts: Vec<Sort> = ctor
                .fields
                .iter()
                .map(|f| match &f.sort {
                    Sort::Uninterpreted(n) if *n == dt.name => sort.clone(),
                    other => other.clone(),
                })
                .collect();
            let mut arg_terms = Vec::with_capacity(args.len());
            for (arg, field_sort) in args.iter().zip(&field_sorts) {
                arg_terms.push(model_value_to_term(solver, arg, field_sort)?);
            }
            let dt = dt.clone();
            // Fallible build: an unrepresentable value fails honestly (None)
            // rather than panicking across the FFI snapshot boundary.
            solver
                .try_datatype_constructor(&dt, constructor, &arg_terms)
                .ok()
        }
        // `Unknown` (and any future variant): the model genuinely has no value
        // here — fail honestly instead of fabricating one.
        _ => None,
    }
}

/// Z3's `model_completion = true` default value for an unconstrained constant
/// of the given sort (`false` / `0` / `""` / `seq.empty` / `K(I, default)` /
/// `+zero` / `Sort!val!0`), or `None` for sorts with no representable default
/// (the leaf then stays symbolic — an honest partial evaluation).
fn default_value_term(solver: &mut Solver, sort: &Sort) -> Option<Term> {
    match sort {
        Sort::Bool => Some(solver.bool_const(false)),
        Sort::Int => Some(solver.int_const_bigint(&num_bigint::BigInt::from(0))),
        Sort::Real => {
            let zero = num_bigint::BigInt::from(0);
            let one = num_bigint::BigInt::from(1);
            Some(solver.rational_const_bigint(&zero, &one))
        }
        Sort::FiniteField(field) => Some(solver.finite_field_const(&0.into(), *field)),
        Sort::BitVec(bv) => Some(solver.bv_const(0, bv.width)),
        Sort::String => Some(solver.string_const("")),
        // z3 completes a floating-point constant with NaN (measured on 5.1:
        // `m.eval(f, model_completion=True)` is `NaN`, an array of them
        // `K(Int, NaN)`). The published-model backstop reads completion as z3
        // does, so a model only `+zero` satisfies is not published.
        Sort::FloatingPoint(eb, sb) => Some(solver.fp_nan(*eb, *sb)),
        Sort::Seq(element) => Some(solver.seq_empty((**element).clone())),
        Sort::Array(arr) => {
            let default = default_value_term(solver, &arr.element_sort)?;
            Some(solver.const_array(arr.index_sort.clone(), default))
        }
        // `RoundingMode` is a FIXED 5-element FP domain, not an open
        // uninterpreted universe: a `RoundingMode!val!0` fresh element is NOT a
        // valid value of the sort (z3 rejects a model carrying it). z3's API
        // completes an unconstrained rounding-mode constant with
        // `roundTowardZero` (measured on 5.1: `RTZ()`), and the published-model
        // backstop must read completion as z3 does (#P0.2 symbolic
        // RoundingMode).
        Sort::Uninterpreted(name) if name == "RoundingMode" => Some(solver.fp_rounding_mode("RTZ")),
        // Z3 completes an uninterpreted-sort constant with a fresh universe
        // element (`S!val!0`); the same token is reused deterministically.
        Sort::Uninterpreted(name) => {
            let element = format!("{name}!val!0");
            solver.try_declare_const(&element, sort.clone()).ok()
        }
        Sort::TypeVar(name) => {
            let element = format!("{name}!val!0");
            solver
                .try_declare_const(&element, Sort::Uninterpreted(name.clone()))
                .ok()
        }
        // Datatype / RegLan / future sorts: no faithful default — leave the
        // constant symbolic rather than invent a value.
        _ => None,
    }
}

/// Render a model value as SMT-LIB text for `Z3_model_to_string`.
///
/// Structured arrays get the full Z3-style form — a `((as const (Array I E)))`
/// base under a store chain — because [`ModelValue`]'s own `Display` prints the
/// bare default as the chain base, which is not well-formed SMT-LIB. Every
/// other variant's `Display` is already SMT-LIB shaped.
fn render_model_value_smtlib(ctx: &Z3Context, val: &ModelValue, sort: &Sort) -> Option<String> {
    Some(match (val, sort) {
        (ModelValue::FiniteField { value, field }, Sort::FiniteField(expected))
            if field == expected =>
        {
            return ctx
                .solver
                .format_finite_field_literal_with_bindings(*value, *field, |name| {
                    ctx.ffi_used_decl_names.contains(name)
                });
        }
        (ModelValue::FiniteField { .. }, _) => return None,
        (ModelValue::Array { default, stores }, Sort::Array(arr)) => {
            let mut text = format!(
                "((as const {sort}) {})",
                render_model_value_smtlib(ctx, default, &arr.element_sort)?
            );
            for (index, value) in stores {
                text = format!(
                    "(store {text} {} {})",
                    render_model_value_smtlib(ctx, index, &arr.index_sort)?,
                    render_model_value_smtlib(ctx, value, &arr.element_sort)?
                );
            }
            text
        }
        _ => val.to_string(),
    })
}

/// Collect every uninterpreted-sort ELEMENT constant appearing inside the
/// given model-value terms (the terms substituted for pinned/completed
/// leaves), mapped to its element token.
///
/// Value terms are built exclusively from literal constants and element
/// constants (see [`model_value_to_term`] / [`default_value_term`]), so every
/// uninterpreted-sorted `Var` inside one IS a model universe element.
fn collect_element_terms(solver: &Solver, value_terms: &[Term]) -> StdHashMap<Term, String> {
    let mut elements = StdHashMap::new();
    let mut stack: Vec<Term> = value_terms.to_vec();
    let mut seen: HashSet<Term> = HashSet::new();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermKind::Var { name } = solver.term_kind(term) {
            if matches!(solver.term_sort(term), Sort::Uninterpreted(_)) {
                elements.insert(term, name);
            }
        }
        stack.extend(solver.term_children(term));
    }
    elements
}

/// Collect every NULLARY datatype constructor CONSTANT (`red`, `blue`, `nil`,
/// …) appearing in `root`, mapped to its constructor name.
///
/// A nullary constructor is a fully-interpreted, pairwise-distinct value: like
/// a model universe element it folds under `=`/`distinct` by name identity (two
/// different constructors are unequal, the same one equal — a datatype axiom the
/// generic simplifier cannot apply to two distinct `Var`s). It is stored
/// internally as a `Var` at the datatype's sort, so this walks for exactly the
/// `Var`s the datatype theory recognizes as nullary constructors. Feeding these
/// into [`fold_element_predicates`] alongside the universe elements is what makes
/// `Z3_model_eval` over enum/datatype constructor constants match z3py.
fn collect_constructor_constants(solver: &Solver, root: Term) -> StdHashMap<Term, String> {
    let mut out = StdHashMap::new();
    let mut stack = vec![root];
    let mut seen: HashSet<Term> = HashSet::new();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermKind::Var { name } = solver.term_kind(term) {
            if solver.is_nullary_constructor(&name) {
                out.insert(term, name);
            }
        }
        stack.extend(solver.term_children(term));
    }
    out
}

/// Fold `=` / `distinct` applications whose operands are ALL distinct-by-name
/// interpreted constants into boolean literals, by token identity.
///
/// Two kinds of constant qualify, both pairwise-distinct by construction with
/// equality = token identity: a model's uninterpreted-sort universe elements
/// (the same semantics the independent model-check gate uses) and nullary
/// datatype constructor constants (`red`/`blue`, `nil` — distinct by the
/// datatype's distinctness axiom). AY's generic `mk_eq` cannot fold
/// `(= elem_a elem_b)` — the operands are variables to it, soundly left
/// symbolic — so the snapshot evaluator applies this model-level knowledge in a
/// dedicated pass. Only terms recorded in `elements` (universe elements this
/// evaluation substituted in, plus constructor constants it identified) are
/// folded; a genuine unpinned variable of the sort never is.
fn fold_element_predicates(
    solver: &mut Solver,
    root: Term,
    elements: &StdHashMap<Term, String>,
) -> Term {
    if elements.is_empty() {
        return root;
    }
    // Find every =/distinct application over element terms.
    let mut stack = vec![root];
    let mut seen: HashSet<Term> = HashSet::new();
    let mut from = Vec::new();
    let mut to = Vec::new();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        let children = solver.term_children(term);
        if let TermKind::App { name, num_args } = solver.term_kind(term) {
            if (name == "=" || name == "distinct")
                && num_args >= 2
                && children.iter().all(|c| elements.contains_key(c))
            {
                let tokens: Vec<&String> = children.iter().map(|c| &elements[c]).collect();
                let value = if name == "=" {
                    tokens.windows(2).all(|w| w[0] == w[1])
                } else {
                    // distinct: all tokens pairwise different
                    let mut uniq: HashSet<&String> = HashSet::new();
                    tokens.iter().all(|t| uniq.insert(t))
                };
                let literal = solver.bool_const(value);
                from.push(term);
                to.push(literal);
                continue; // no need to descend into a folded node
            }
        }
        stack.extend(children);
    }
    if from.is_empty() {
        return root;
    }
    let substituted = solver.substitute(root, &from, &to);
    solver.simplify(substituted)
}

/// A ground array value — a `store` chain over a `const-array` whose indices
/// and values are all literal constants — as its default plus explicit points
/// (the outermost store of an index wins). `None` for any other term.
fn ground_array_value(solver: &Solver, term: Term) -> Option<(Term, StdHashMap<Term, Term>)> {
    let mut points: StdHashMap<Term, Term> = StdHashMap::new();
    let mut current = term;
    loop {
        let TermKind::App { name, num_args } = solver.term_kind(current) else {
            return None;
        };
        let children = solver.term_children(current);
        match (name.as_str(), num_args) {
            ("const-array", 1) => {
                let default = children[0];
                return matches!(solver.term_kind(default), TermKind::Const)
                    .then_some((default, points));
            }
            ("store", 3) => {
                let (index, value) = (children[1], children[2]);
                if !matches!(solver.term_kind(index), TermKind::Const)
                    || !matches!(solver.term_kind(value), TermKind::Const)
                {
                    return None;
                }
                points.entry(index).or_insert(value);
                current = children[0];
            }
            _ => return None,
        }
    }
}

/// Decide `a = b` for two ground array values, when it is decided: literal
/// constants are hash-consed, so two literals are equal iff they are the same
/// term. Arrays with different defaults differ when the index sort is
/// infinite (Int, Real); over a finite index sort explicit points could cover
/// every index, so that case is left undecided.
fn ground_array_values_equal(solver: &Solver, a: Term, b: Term) -> Option<bool> {
    let (default_a, points_a) = ground_array_value(solver, a)?;
    let (default_b, points_b) = ground_array_value(solver, b)?;
    let read = |points: &StdHashMap<Term, Term>, default: Term, index: &Term| {
        points.get(index).copied().unwrap_or(default)
    };
    let points_agree = points_a
        .keys()
        .chain(points_b.keys())
        .all(|index| read(&points_a, default_a, index) == read(&points_b, default_b, index));
    if default_a == default_b {
        return Some(points_agree);
    }
    let Sort::Array(array) = solver.term_sort(a) else {
        return None;
    };
    matches!(array.index_sort, Sort::Int | Sort::Real).then_some(false)
}

/// Fold `=` / `distinct` over ground array values (z3's evaluator decides
/// `K(Int, 0) != K(Int, 1)` to `true`; the generic simplifier leaves it).
fn fold_ground_array_equalities(solver: &mut Solver, root: Term) -> Term {
    let mut stack = vec![root];
    let mut seen: HashSet<Term> = HashSet::new();
    let (mut from, mut to) = (Vec::new(), Vec::new());
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        let children = solver.term_children(term);
        if let TermKind::App { name, num_args } = solver.term_kind(term) {
            if (name == "=" || name == "distinct")
                && num_args >= 2
                && matches!(solver.term_sort(children[0]), Sort::Array(_))
            {
                let mut decided = Some(true);
                'pairs: for (i, &left) in children.iter().enumerate() {
                    for &right in &children[i + 1..] {
                        match ground_array_values_equal(solver, left, right) {
                            None => {
                                decided = None;
                                break 'pairs;
                            }
                            Some(equal) => {
                                let holds = if name == "=" { equal } else { !equal };
                                if !holds {
                                    decided = Some(false);
                                }
                            }
                        }
                    }
                }
                if let Some(value) = decided {
                    let literal = solver.bool_const(value);
                    from.push(term);
                    to.push(literal);
                    continue;
                }
            }
        }
        stack.extend(children);
    }
    if from.is_empty() {
        return root;
    }
    let substituted = solver.substitute(root, &from, &to);
    solver.simplify(substituted)
}

// ---- Snapshot FUNCTION interpretations (arity > 0) ----

/// A function interpretation captured from the engine's raw model text.
///
/// The parsed [`Model`] structure only stores constants, but the engine's
/// `get-model` text also contains arity > 0 `define-fun` tables of the shape
///
/// ```smtlib
/// (define-fun f ((x0 Int)) Int (ite (= x0 3) 10 0))
/// ```
///
/// This struct is that table, re-parsed into rows so `Z3_model_eval` can
/// resolve ground applications from the SNAPSHOT (never live solver state).
///
/// `Clone` so `Z3_model_translate` can copy the table (pure data — names,
/// sorts, literal values) into a destination context, and so
/// `Z3_model_get_func_interp` can lift one out for materialization without
/// holding a borrow of the model handle while it mutates the solver arena.
#[derive(Clone)]
pub(crate) struct FuncInterp {
    pub(crate) name: String,
    pub(crate) param_sorts: Vec<Sort>,
    /// Result (range) sort declared by the `define-fun` header. Authoritative
    /// for building the range of the model's func_decl and the sort of the
    /// else/row value terms (e.g. an `Int` literal at `Real` result sort).
    pub(crate) result_sort: Sort,
    /// Explicit rows: argument tuple → value.
    pub(crate) rows: Vec<(Vec<ModelValue>, ModelValue)>,
    /// Value for every argument tuple no row matches (the final `else`).
    /// `ModelValue::Unknown` when the else is the symbolic `else_term`.
    pub(crate) else_value: ModelValue,
    /// A symbolic else: private parameter variables (argument `i`; never
    /// declared constants of the context) and the body over them (`x0 + 1`
    /// for `forall y. f(y) = y + 1`; see `symbolic_else`). `None` for a
    /// literal table.
    pub(crate) else_term: Option<(Vec<Term>, Term)>,
}

/// Every function interpretation of `model_text`: the literal tables plus
/// the symbolic ones (`symbolic_else`).
pub(crate) fn model_func_interps(solver: &mut Solver, model_text: &str) -> Vec<FuncInterp> {
    let mut interps = parse_func_interps(model_text);
    let symbolic = symbolic_else::symbolic_func_interps(solver, model_text, &interps);
    interps.extend(symbolic);
    interps
}

/// Parse a sort S-expression from a model `define-fun` parameter/result.
fn parse_sort_sexpr(sexpr: &ay_frontend::SExpr) -> Option<Sort> {
    use ay_frontend::SExpr;
    match sexpr {
        SExpr::Symbol(name) => Some(match name.as_str() {
            "Int" => Sort::Int,
            "Real" => Sort::Real,
            "Bool" => Sort::Bool,
            "String" => Sort::String,
            other => Sort::Uninterpreted(other.to_string()),
        }),
        SExpr::List(items) => match items.as_slice() {
            [SExpr::Symbol(u), SExpr::Symbol(bv), SExpr::Numeral(width)]
                if u == "_" && bv == "BitVec" =>
            {
                Some(Sort::bitvec(width.parse().ok()?))
            }
            [SExpr::Symbol(arr), index, element] if arr == "Array" => Some(Sort::array(
                parse_sort_sexpr(index)?,
                parse_sort_sexpr(element)?,
            )),
            [SExpr::Symbol(seq), element] if seq == "Seq" => {
                Some(Sort::seq(parse_sort_sexpr(element)?))
            }
            _ => None,
        },
        _ => None,
    }
}

/// Parse a LITERAL model value from a function-table S-expression.
///
/// Covers the shapes the engine's table formatter emits for scalar values:
/// booleans, numerals, `(- n)`, decimals, `(/ a b)`, `#x…`/`#b…`,
/// `(_ bvN w)`, string literals, and bare or sort-ascribed element tokens of
/// uninterpreted sorts. Anything else (FP values, nested arrays, …) yields
/// `None` and the whole table is skipped — fail closed, never guess.
fn parse_literal_sexpr(sexpr: &ay_frontend::SExpr) -> Option<ModelValue> {
    use ay_frontend::SExpr;
    use num_bigint::BigInt;
    use num_rational::BigRational;
    match sexpr {
        SExpr::True => Some(ModelValue::Bool(true)),
        SExpr::False => Some(ModelValue::Bool(false)),
        SExpr::Numeral(text) => Some(ModelValue::Int(text.parse::<BigInt>().ok()?)),
        SExpr::Decimal(text) => {
            // "12.5" → 125/10 (exact); BigRational::new normalizes.
            let (int_part, frac_part) = text.split_once('.')?;
            let digits: String = format!("{int_part}{frac_part}");
            let numer = digits.parse::<BigInt>().ok()?;
            let denom = BigInt::from(10u32).pow(u32::try_from(frac_part.len()).ok()?);
            Some(ModelValue::Real(BigRational::new(numer, denom)))
        }
        // The S-expression lexer keeps the `#x` / `#b` prefix in the token
        // text; the digits (and so the width) are what follows it.
        SExpr::Hexadecimal(token) => {
            let hex = token.strip_prefix("#x").unwrap_or(token);
            Some(ModelValue::BitVec {
                value: BigInt::parse_bytes(hex.as_bytes(), 16)?,
                width: u32::try_from(hex.len()).ok()?.checked_mul(4)?,
            })
        }
        SExpr::Binary(token) => {
            let bits = token.strip_prefix("#b").unwrap_or(token);
            Some(ModelValue::BitVec {
                value: BigInt::parse_bytes(bits.as_bytes(), 2)?,
                width: u32::try_from(bits.len()).ok()?,
            })
        }
        SExpr::String(text) => Some(ModelValue::String(text.clone())),
        // A bare symbol in a value position is an uninterpreted-sort element
        // token (e.g. `@S!0`).
        SExpr::Symbol(token) => Some(ModelValue::Uninterpreted(token.clone())),
        SExpr::List(items) => match items.as_slice() {
            // AY's model printer emits abstract uninterpreted-sort elements in
            // validator-safe form `(as @S!0 S)`.  The S-expression parser has
            // already removed optional pipe quoting.  Restrict this case to
            // the engine's `@...` abstract atoms so datatype constructor
            // ascriptions are never mistaken for open-sort elements.
            [SExpr::Symbol(as_kw), SExpr::Symbol(element), _]
                if as_kw == "as" && element.starts_with('@') =>
            {
                Some(ModelValue::Uninterpreted(element.clone()))
            }
            [SExpr::Symbol(minus), inner] if minus == "-" => match parse_literal_sexpr(inner)? {
                ModelValue::Int(n) => Some(ModelValue::Int(-n)),
                ModelValue::Real(r) => Some(ModelValue::Real(-r)),
                _ => None,
            },
            [SExpr::Symbol(div), numer, denom] if div == "/" => {
                let numer = match parse_literal_sexpr(numer)? {
                    ModelValue::Int(n) => BigRational::from(n),
                    ModelValue::Real(r) => r,
                    _ => return None,
                };
                let denom = match parse_literal_sexpr(denom)? {
                    ModelValue::Int(n) => BigRational::from(n),
                    ModelValue::Real(r) => r,
                    _ => return None,
                };
                if denom == BigRational::from(BigInt::from(0)) {
                    return None;
                }
                Some(ModelValue::Real(numer / denom))
            }
            [SExpr::Symbol(u), SExpr::Symbol(bv), SExpr::Numeral(width)] if u == "_" => {
                let value = bv.strip_prefix("bv")?.parse::<BigInt>().ok()?;
                Some(ModelValue::BitVec {
                    value,
                    width: width.parse().ok()?,
                })
            }
            _ => None,
        },
        _ => None,
    }
}

/// Parse the nested-`ite` body of a function table into rows + else value.
///
/// Shape (see the engine's `format_function_body`):
/// `(ite (and (= x0 a) (= x1 b)) v REST)` … terminating in a literal else.
fn parse_table_body(
    body: &ay_frontend::SExpr,
    param_names: &[String],
    rows: &mut Vec<(Vec<ModelValue>, ModelValue)>,
) -> Option<ModelValue> {
    use ay_frontend::SExpr;
    if let SExpr::List(items) = body {
        if let [SExpr::Symbol(ite), cond, then_val, else_val] = items.as_slice() {
            if ite == "ite" {
                let args = parse_row_condition(cond, param_names)?;
                let value = parse_literal_sexpr(then_val)?;
                rows.push((args, value));
                return parse_table_body(else_val, param_names, rows);
            }
        }
    }
    parse_literal_sexpr(body)
}

/// Parse a row condition `(= xi lit)` or `(and (= x0 l0) (= x1 l1) …)` into
/// the full argument tuple (every parameter must be constrained exactly once).
fn parse_row_condition(
    cond: &ay_frontend::SExpr,
    param_names: &[String],
) -> Option<Vec<ModelValue>> {
    use ay_frontend::SExpr;
    let eqs: Vec<&SExpr> = match cond {
        SExpr::List(items) => match items.first() {
            Some(SExpr::Symbol(op)) if op == "and" => items.iter().skip(1).collect(),
            Some(SExpr::Symbol(op)) if op == "=" => vec![cond],
            _ => return None,
        },
        _ => return None,
    };
    let mut args: Vec<Option<ModelValue>> = vec![None; param_names.len()];
    for eq in eqs {
        let SExpr::List(parts) = eq else { return None };
        let [SExpr::Symbol(op), SExpr::Symbol(param), lit] = parts.as_slice() else {
            return None;
        };
        if op != "=" {
            return None;
        }
        let idx = param_names.iter().position(|p| p == param)?;
        if args[idx].is_some() {
            return None; // duplicate constraint: unexpected shape
        }
        args[idx] = Some(parse_literal_sexpr(lit)?);
    }
    args.into_iter().collect()
}

/// Parse every arity > 0 `define-fun` in the engine's raw model text into a
/// [`FuncInterp`]. Tables that do not match the expected shape are skipped
/// (their applications then stay symbolic — honest partial evaluation).
pub(crate) fn parse_func_interps(model_text: &str) -> Vec<FuncInterp> {
    use ay_frontend::SExpr;
    let Ok(root) = ay_frontend::sexp::parse_sexp(model_text) else {
        return Vec::new();
    };
    let SExpr::List(ref items) = root else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for item in items {
        let SExpr::List(parts) = item else { continue };
        let [SExpr::Symbol(kw), SExpr::Symbol(name), SExpr::List(params), result_sort_sexpr, body] =
            parts.as_slice()
        else {
            continue;
        };
        if kw != "define-fun" || params.is_empty() {
            continue; // constants are already covered by the parsed Model
        }
        let parsed: Option<(Vec<String>, Vec<Sort>)> = params
            .iter()
            .map(|p| {
                let SExpr::List(pair) = p else { return None };
                let [SExpr::Symbol(pname), psort] = pair.as_slice() else {
                    return None;
                };
                Some((pname.clone(), parse_sort_sexpr(psort)?))
            })
            .collect::<Option<Vec<(String, Sort)>>>()
            .map(|pairs| pairs.into_iter().unzip());
        let Some((param_names, param_sorts)) = parsed else {
            continue;
        };
        let mut rows = Vec::new();
        let Some(else_value) = parse_table_body(body, &param_names, &mut rows) else {
            continue; // unexpected table shape: skip, fail closed
        };
        // Result sort from the `define-fun` header. If it is a shape
        // `parse_sort_sexpr` does not model (only reached for exotic result
        // sorts), fall back to the sort implied by the else value so the table
        // is still exposed with an honest, value-consistent range — never a
        // fabricated one.
        let result_sort = parse_sort_sexpr(result_sort_sexpr)
            .or_else(|| scalar_value_sort(&else_value))
            .unwrap_or(Sort::Int);
        out.push(FuncInterp {
            name: name.clone(),
            param_sorts,
            result_sort,
            rows,
            else_value,
            else_term: None,
        });
    }
    out
}

/// Name of a top-level `define-fun` item of a raw model text.
fn define_fun_name(item: &ay_frontend::SExpr) -> Option<&str> {
    use ay_frontend::SExpr;
    let SExpr::List(parts) = item else {
        return None;
    };
    match parts.as_slice() {
        [SExpr::Symbol(kw), SExpr::Symbol(name), ..] if kw == "define-fun" => Some(name),
        _ => None,
    }
}

/// The engine's raw model text with every top-level `define-fun` whose name is
/// not in `keep` removed. Other items (declarations of model universe
/// elements) are kept. The text is returned verbatim when nothing is removed or
/// when it does not parse (an unparsable text yields no function tables
/// anyway); otherwise the kept items are re-rendered with the parser-faithful
/// raw renderer.
pub(crate) fn retain_model_text_symbols(
    model_text: &str,
    keep: &std::collections::BTreeSet<String>,
) -> String {
    use ay_frontend::SExpr;
    let Ok(root) = ay_frontend::sexp::parse_sexp(model_text) else {
        return model_text.to_string();
    };
    let SExpr::List(ref items) = root else {
        return model_text.to_string();
    };
    let dropped = |item: &SExpr| define_fun_name(item).is_some_and(|name| !keep.contains(name));
    if !items.iter().any(dropped) {
        return model_text.to_string();
    }
    let kept: Vec<String> = items
        .iter()
        .filter(|&item| !dropped(item))
        .map(SExpr::to_raw_string)
        .collect();
    format!("(\n  {}\n)", kept.join("\n  "))
}

/// Constants (`define-fun` with no parameters) of the raw model text that the
/// parsed constants-only [`Model`] does not carry, with their printed value.
///
/// The parser drops a value it cannot represent (e.g. an irrational algebraic
/// `(root-obj ...)`), so a non-empty result means the published model would
/// silently lose an assignment the engine's validated model relies on.
pub(crate) fn unrepresented_model_constants(
    model_text: &str,
    model: &Model,
) -> Vec<(String, String)> {
    use ay_frontend::SExpr;
    let Ok(root) = ay_frontend::sexp::parse_sexp(model_text) else {
        return Vec::new();
    };
    let SExpr::List(ref items) = root else {
        return Vec::new();
    };
    let mut missing = Vec::new();
    for item in items {
        let SExpr::List(parts) = item else { continue };
        let [SExpr::Symbol(kw), SExpr::Symbol(name), SExpr::List(params), _sort, body] =
            parts.as_slice()
        else {
            continue;
        };
        if kw == "define-fun" && params.is_empty() && model.value_by_name(name).is_none() {
            missing.push((name.clone(), body.to_raw_string()));
        }
    }
    missing
}

/// Function `define-fun`s (arity > 0) of the raw model text that the parsed
/// tables `interps` do not carry WHOLE, with their printed body.
///
/// A table is carried whole when [`parse_func_interps`] produced it (same name
/// and arity) and every row argument, row value and the else value converts to
/// a term at its declared sort — exactly what `Z3_model_get_func_interp` and
/// `Z3_model_eval` will build from it. Anything else (a body that is not a
/// literal table, e.g. `(+ x0 1)`; a value the reader cannot carry) would make
/// the published function differ from the one the engine validated.
pub(crate) fn unrepresented_function_tables(
    solver: &mut Solver,
    model_text: &str,
    interps: &[FuncInterp],
) -> Vec<(String, String)> {
    use ay_frontend::SExpr;
    let Ok(root) = ay_frontend::sexp::parse_sexp(model_text) else {
        return vec![(
            "<model>".to_string(),
            "an unreadable model text".to_string(),
        )];
    };
    let SExpr::List(ref items) = root else {
        return vec![(
            "<model>".to_string(),
            "an unreadable model text".to_string(),
        )];
    };
    let mut missing = Vec::new();
    for item in items {
        let SExpr::List(parts) = item else { continue };
        let [SExpr::Symbol(kw), SExpr::Symbol(name), SExpr::List(params), _sort, body] =
            parts.as_slice()
        else {
            continue;
        };
        if kw != "define-fun" || params.is_empty() {
            continue;
        }
        let carried = interps
            .iter()
            .find(|fi| fi.name == *name && fi.param_sorts.len() == params.len())
            .is_some_and(|fi| func_interp_converts(solver, fi));
        if !carried {
            missing.push((name.clone(), body.to_raw_string()));
        }
    }
    missing
}

/// Every row and the else value of `fi` convert to terms at their sorts.
fn func_interp_converts(solver: &mut Solver, fi: &FuncInterp) -> bool {
    (fi.else_term.is_some()
        || model_value_to_term(solver, &fi.else_value, &fi.result_sort).is_some())
        && fi.rows.iter().all(|(args, value)| {
            args.len() == fi.param_sorts.len()
                && args
                    .iter()
                    .zip(&fi.param_sorts)
                    .all(|(arg, sort)| model_value_to_term(solver, arg, sort).is_some())
                && model_value_to_term(solver, value, &fi.result_sort).is_some()
        })
}

/// Count the arity > 0 `define-fun`s in the raw model text — INCLUDING those
/// whose table shape [`parse_func_interps`] fails to parse (it skips them
/// silently). `None` when the text itself does not parse.
///
/// The transitive-closure SAT gate compares this count against the parsed
/// table count so a silently-skipped function table can never hide a universe
/// element from the closure verification (fail closed). A `define-fun` whose
/// header shape is unreadable is conservatively counted as arity > 0.
pub(crate) fn count_nonconst_define_funs(model_text: &str) -> Option<usize> {
    use ay_frontend::SExpr;
    let root = ay_frontend::sexp::parse_sexp(model_text).ok()?;
    let SExpr::List(ref items) = root else {
        return None;
    };
    let mut count = 0usize;
    for item in items {
        let SExpr::List(parts) = item else { continue };
        if !matches!(parts.first(), Some(SExpr::Symbol(kw)) if kw == "define-fun") {
            continue;
        }
        match parts.get(2) {
            Some(SExpr::List(params)) if params.is_empty() => {} // constant
            _ => count += 1, // arity > 0, or unreadable header (conservative)
        }
    }
    Some(count)
}

#[cfg(test)]
#[test]
fn parse_function_table_accepts_ascribed_uninterpreted_arguments() {
    let model_text = r#"(model
      (define-fun f ((x0 S) (x1 S)) Bool
        (ite (and (= x0 (as @S!0 S)) (= x1 (as |@S!1| S))) true false)))"#;
    let interps = parse_func_interps(model_text);

    assert_eq!(interps.len(), 1);
    assert_eq!(interps[0].rows.len(), 1);
    assert_eq!(
        interps[0].rows[0].0,
        vec![
            ModelValue::Uninterpreted("@S!0".to_string()),
            ModelValue::Uninterpreted("@S!1".to_string()),
        ]
    );
    assert_eq!(interps[0].rows[0].1, ModelValue::Bool(true));
    assert_eq!(interps[0].else_value, ModelValue::Bool(false));
}

/// The fields of each function table, as `captured_function_tables` returns
/// them, sorted by name.
#[cfg(test)]
type TableFields = Vec<(
    String,
    Vec<Sort>,
    Sort,
    Vec<(Vec<ModelValue>, ModelValue)>,
    ModelValue,
)>;

/// The function tables `parse_func_interps` reads from `solver`'s
/// `Solver::model_str_for_decoder`, sorted by name.
#[cfg(test)]
fn captured_function_tables(solver: &Solver) -> TableFields {
    let text = solver
        .model_str_for_decoder()
        .expect("the text a handle captures");
    let mut fields: TableFields = parse_func_interps(&text)
        .into_iter()
        .map(|interp| {
            (
                interp.name,
                interp.param_sorts,
                interp.result_sort,
                interp.rows,
                interp.else_value,
            )
        })
        .collect();
    fields.sort_by(|left, right| left.0.cmp(&right.0));
    fields
}

/// For each pair of `ay_dpll::overload_pairs` (#overloaded-nil-surface),
/// `captured_function_tables` gives the same tables for `pair.overloaded` as
/// for `pair.renamed`.
#[cfg(test)]
#[test]
fn function_tables_read_the_same_whether_or_not_a_constructor_is_overloaded() {
    let mut tables = 0;
    let mut ascribed = 0;
    for pair in ay_dpll::overload_pairs() {
        let (overloaded_solver, overloaded) = pair
            .solve(&pair.overloaded)
            .unwrap_or_else(|error| panic!("{error}"));
        let (renamed_solver, renamed) = pair
            .solve(&pair.renamed)
            .unwrap_or_else(|error| panic!("{error}"));
        let context = format!("{}:\n{overloaded}\n{renamed}", pair.label);
        assert_eq!(
            renamed_solver.model_str_for_decoder().as_deref(),
            Some(renamed.as_str()),
            "{context}"
        );
        let read = captured_function_tables(&overloaded_solver);
        assert_eq!(read, captured_function_tables(&renamed_solver), "{context}");
        tables += read.len();
        ascribed += usize::from(overloaded.contains("(as ") && overloaded != renamed);
    }
    // Not vacuous: at least 20 tables were read, and at least 20 overloaded
    // scripts print a model that holds `(as ` and differs from their renamed
    // twin's.
    assert!(tables >= 20, "{tables}");
    assert!(ascribed >= 20, "{ascribed}");
}

/// In these scripts `f` returns the application of a constructor named `as`,
/// and its table in the decoder text holds the cell paired below;
/// `captured_function_tables` reads no table `f` from any of them.
#[cfg(test)]
#[test]
fn a_function_table_of_applications_of_as_is_skipped_as_before() {
    let solve = |script: &str| {
        let mut solver = Solver::new(ay_dpll::api::Logic::All);
        solver.parse_smtlib2(script).expect("script");
        assert_eq!(solver.check_sat(), ay_dpll::api::SolveResult::Sat);
        solver
    };
    let (overloaded, renamed) = ay_dpll::as_application_pair();
    for (script, cell) in [
        (ay_dpll::AS_APPLICATION_UNIT, "(as Unit Unit)"),
        (ay_dpll::AS_APPLICATION_OWN_SORT, "(as nil L1)"),
        (overloaded.as_str(), "(as nil Other)"),
        (renamed.as_str(), "(as nil Other)"),
    ] {
        let solver = solve(script);
        let text = solver.model_str_for_decoder().expect("captured text");
        let table = text
            .split("(define-fun f ((x0 Int)) P")
            .nth(1)
            .unwrap_or_else(|| panic!("f is printed: {text}"));
        assert!(table.contains(cell), "{text}");
        let read = captured_function_tables(&solver);
        assert!(
            read.iter().all(|(name, ..)| name != "f"),
            "{cell}: {read:?}"
        );
    }
    assert_eq!(
        captured_function_tables(&solve(&overloaded)),
        captured_function_tables(&solve(&renamed))
    );
}

/// The free constants of `root` (outside every binder of the same name);
/// `None` when the scopes cannot be separated (see `value_folds`).
pub(crate) fn scoped_free_leaves(solver: &Solver, root: Term) -> Option<Vec<Term>> {
    value_folds::scoped_leaves(solver, root).map(|leaves| leaves.free)
}

/// One round of resolving ground uninterpreted-function applications against
/// the snapshot's function tables.
///
/// An application `f(a₁ … aₙ)` is resolved only when every argument is
/// DETERMINED — a literal constant or a model universe element — by matching
/// the argument tuple against the table rows (falling back to the table's
/// else value). Returns the rewritten root and the value terms introduced.
fn resolve_uf_round(
    solver: &mut Solver,
    root: Term,
    interps: &[FuncInterp],
    elements: &StdHashMap<Term, String>,
    scope: &UfScope<'_>,
) -> (Term, Vec<Term>) {
    if interps.is_empty() && scope.absent_functions.is_empty() {
        return (root, Vec::new());
    }
    let mut stack = vec![root];
    let mut seen: HashSet<Term> = HashSet::new();
    let mut from: Vec<Term> = Vec::new();
    let mut to: Vec<Term> = Vec::new();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        let children = solver.term_children(term);
        if let TermKind::App { name, num_args } = solver.term_kind(term) {
            if let Some(interp) = interps
                .iter()
                .find(|fi| fi.name == name && fi.param_sorts.len() == num_args)
            {
                // A table with no rows and a literal `else` is that constant
                // everywhere, whatever the arguments (`fSeq(seq.unit 0)` under
                // `fSeq = [else -> 1]`); otherwise a row lookup needs literal
                // arguments.
                let constant = interp.rows.is_empty() && interp.else_term.is_none();
                let determined = constant
                    || children.iter().all(|&arg| {
                        matches!(solver.term_kind(arg), TermKind::Const)
                            || elements.contains_key(&arg)
                    });
                if determined {
                    let result_sort = solver.term_sort(term);
                    if let Some(value_term) =
                        lookup_uf_value(solver, interp, &children, &result_sort)
                    {
                        from.push(term);
                        to.push(value_term);
                        continue;
                    }
                } else if children
                    .iter()
                    .any(|&arg| value_folds::mentions_any(solver, arg, scope.bound))
                {
                    // An application at a quantifier's variable is the table
                    // itself, as a first-match `ite` over the rows.
                    let result_sort = solver.term_sort(term);
                    if let Some(table) = table_term(solver, interp, &children, &result_sort) {
                        from.push(term);
                        to.push(table);
                        continue;
                    }
                }
            } else if num_args > 0 && scope.absent_functions.contains(&name) {
                // Model completion: z3 gives a function the model does not
                // interpret its sort's default everywhere.
                let result_sort = solver.term_sort(term);
                if let Some(value_term) = default_value_term(solver, &result_sort) {
                    from.push(term);
                    to.push(value_term);
                    continue;
                }
            }
        }
        stack.extend(children);
    }
    if from.is_empty() {
        return (root, Vec::new());
    }
    let substituted = solver.substitute(root, &from, &to);
    (solver.simplify(substituted), to)
}

/// What UF resolution may use besides the tables: the bound-variable
/// occurrences of the evaluated term, and the caller's functions the model
/// leaves uninterpreted (empty without model completion).
struct UfScope<'a> {
    bound: &'a HashSet<Term>,
    absent_functions: HashSet<String>,
}

/// `interp` applied to arbitrary `args`: `ite(args = row₁, v₁, …, else)`.
fn table_term(
    solver: &mut Solver,
    interp: &FuncInterp,
    args: &[Term],
    result_sort: &Sort,
) -> Option<Term> {
    let mut table = if interp.else_term.is_some() {
        symbolic_else::instantiate_else(solver, interp, args)?
    } else {
        model_value_to_term(solver, &interp.else_value, result_sort)?
    };
    for (row_args, row_value) in interp.rows.iter().rev() {
        if row_args.len() != args.len() {
            return None;
        }
        let mut conditions = Vec::with_capacity(args.len());
        for ((row_arg, param_sort), &arg) in row_args.iter().zip(&interp.param_sorts).zip(args) {
            let row_term = model_value_to_term(solver, row_arg, param_sort)?;
            conditions.push(solver.try_eq(arg, row_term).ok()?);
        }
        let condition = match conditions.as_slice() {
            [single] => *single,
            _ => solver.try_and_many(&conditions).ok()?,
        };
        let value = model_value_to_term(solver, row_value, result_sort)?;
        table = solver.try_ite(condition, value, table).ok()?;
    }
    Some(table)
}

/// Match a determined argument tuple against a function table.
///
/// Row argument values are converted to terms with the table's parameter
/// sorts; hash-consing makes the comparison canonical (`Int 5` interns to the
/// same term everywhere). A row whose values cannot be converted fails the
/// whole lookup (fail closed) rather than skipping to the else value.
/// `result_sort` is the application term's sort (used to build the value
/// term, e.g. to declare an element constant of the right uninterpreted
/// sort).
fn lookup_uf_value(
    solver: &mut Solver,
    interp: &FuncInterp,
    args: &[Term],
    result_sort: &Sort,
) -> Option<Term> {
    for (row_args, row_value) in &interp.rows {
        if row_args.len() != args.len() {
            return None;
        }
        let mut all_equal = true;
        for ((row_arg, param_sort), &arg) in
            row_args.iter().zip(&interp.param_sorts).zip(args.iter())
        {
            let row_term = model_value_to_term(solver, row_arg, param_sort)?;
            if row_term != arg {
                all_equal = false;
                break;
            }
        }
        if all_equal {
            return model_value_to_term(solver, row_value, result_sort);
        }
    }
    if interp.else_term.is_some() {
        return symbolic_else::instantiate_else(solver, interp, args);
    }
    model_value_to_term(solver, &interp.else_value, result_sort)
}

// ---- Model operations ----

/// Increment model reference count (no-op).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_model_inc_ref(_c: Z3_context, _m: Z3_model) {}

/// Decrement model reference count (no-op).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_model_dec_ref(_c: Z3_context, _m: Z3_model) {}

/// Get number of constant declarations in model.
///
/// Counts EXACTLY the entries `Z3_model_get_const_decl` enumerates (the two
/// share [`model_entries`]'s index space), so every index below this count
/// yields a named decl — including array/datatype/uninterpreted-sort entries.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_model_get_num_consts(_c: Z3_context, m: Z3_model) -> c_uint {
    if m.is_null() {
        return 0;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_uint` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_uint(_c, 0, |ctx| {
            let model = &(*m).model;
            model_entries(&ctx.solver, model).len() as c_uint
        })
    }
}

/// Use the existing typed model renderer for an owned reconstructed scalar
/// model. Prepay decimal/binary text and formatting scratch before rendering;
/// this operation does not create retained output-memory custody.
pub(crate) fn render_converted_model_text(
    ctx: &Z3Context,
    model: Model,
    decision: &ay_dpll::api::TacticDecision,
) -> Option<(Model, String)> {
    if !decision.validate(&ctx.solver) {
        return None;
    }
    let declared = counted_declared_sorts(ctx, decision)?;
    if !decision.validate(&ctx.solver) {
        return None;
    }
    let handle = ModelHandle {
        model,
        func_interps: Vec::new(),
        complete_functions: false,
        user_const_interps: Vec::new(),
        user_func_interps: Vec::new(),
        rec_def_count: 0,
        _ctx: ptr::null_mut(),
    };
    let admission = RendererAdmission { ctx, decision };
    let owner = Some(&admission as &dyn ay_core::term::TermConstructionAdmission);
    if scalar_model_surface(&handle, &declared, owner)? != ModelSurface::PublicScalar {
        return None;
    }
    let text =
        render_model_handle_with_sorts(ctx, &handle, &declared, ModelSurface::NativeScalar, owner)?;
    if !decision.validate(&ctx.solver) {
        return None;
    }
    Some((handle.model, text))
}

pub(crate) fn render_model_handle_text(ctx: &Z3Context, handle: &ModelHandle) -> Option<String> {
    let declared = declared_sorts(&ctx.solver);
    let surface = scalar_model_surface(handle, &declared, None)?;
    render_model_handle_with_sorts(ctx, handle, &declared, surface, None)
}

struct RendererAdmission<'a> {
    ctx: &'a Z3Context,
    decision: &'a ay_dpll::api::TacticDecision,
}
impl ay_core::term::TermConstructionAdmission for RendererAdmission<'_> {
    fn admit(
        &self,
        work: usize,
        bytes: usize,
    ) -> Result<(), ay_core::original_query::CountedAdmissionError> {
        let original = self.decision.admission();
        // Enter the original guarded payment before invoking source polls;
        // callback reentry must pass its existing no-reentry fence too.
        original.admit(work, bytes)?;
        if self.decision.validate(&self.ctx.solver) {
            Ok(())
        } else {
            use ay_core::original_query::{
                CountedAdmissionError, OriginalAdmissionError, QueryError,
            };
            Err(original.refuse(CountedAdmissionError::Original(
                OriginalAdmissionError::Query(QueryError::Invalid(
                    "tactic renderer source changed",
                )),
            )))
        }
    }
    fn refuse(
        &self,
        error: ay_core::original_query::CountedAdmissionError,
    ) -> ay_core::original_query::CountedAdmissionError {
        self.decision.admission().refuse(error)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ModelSurface {
    GeneralProjection,
    PublicScalar,
    NativeScalar,
}

fn scalar_model_surface(
    handle: &ModelHandle,
    declared: &DeclaredSorts,
    owner: ay_core::render_admission::Owner<'_>,
) -> Option<ModelSurface> {
    let model = &handle.model;
    if !handle.func_interps.is_empty()
        || !handle.user_const_interps.is_empty()
        || !handle.user_func_interps.is_empty()
        || model.iter_strings().next().is_some()
        || model.iter_fps().next().is_some()
        || model.iter_arrays().next().is_some()
        || model.iter_seqs().next().is_some()
        || model.iter_datatypes().next().is_some()
        || model.iter_uninterpreteds().next().is_some()
    {
        return Some(ModelSurface::GeneralProjection);
    }
    let supported = |name: &str, sort: Sort| -> Option<bool> {
        if !ay_core::render_admission::pay(owner, name.len().checked_add(1)?, 0) {
            return None;
        }
        Some(declared.get(name).is_none_or(|actual| actual == &sort))
    };
    for (name, _) in model.iter_bools() {
        if !supported(name, Sort::Bool)? {
            return Some(ModelSurface::GeneralProjection);
        }
    }
    for (name, _) in model.iter_ints() {
        if !supported(name, Sort::Int)? {
            return Some(ModelSurface::GeneralProjection);
        }
    }
    for (name, _) in model.iter_reals() {
        if !supported(name, Sort::Real)? {
            return Some(ModelSurface::GeneralProjection);
        }
    }
    for (name, (_, width)) in model.iter_bvs() {
        if *width == 0 || !supported(name, Sort::bitvec(*width))? {
            return Some(ModelSurface::GeneralProjection);
        }
    }
    for (name, value) in model.iter_finite_fields() {
        let ModelValue::FiniteField { field, .. } = value else {
            return Some(ModelSurface::GeneralProjection);
        };
        if !supported(name, Sort::FiniteField(*field))? {
            return Some(ModelSurface::GeneralProjection);
        }
    }
    Some(ModelSurface::PublicScalar)
}

fn counted_declared_sorts(
    ctx: &Z3Context,
    decision: &ay_dpll::api::TacticDecision,
) -> Option<DeclaredSorts> {
    let owner = decision.admission();
    let mut result = DeclaredSorts::default();
    if !decision.admit_declaration_scan(&ctx.solver) {
        return None;
    }
    // This existing iterator borrows the native map without the sorted
    // declared_variables() Vec. Lookup-map semantics do not depend on order.
    for (name, term) in ctx.solver.declared_vars() {
        owner.admit(name.len().checked_add(1)?, name.len()).ok()?;
        if !decision.validate(&ctx.solver) {
            return None;
        }
        if result.len() == result.capacity() {
            for key in result.keys() {
                owner.admit(key.len(), 0).ok()?;
                if !decision.validate(&ctx.solver) {
                    return None;
                }
            }
        }
        ay_core::term::reserve_map_counted(&mut result, 1, owner).ok()?;
        if !decision.validate(&ctx.solver) {
            return None;
        }
        ay_core::TermStore::inspect_sort_with_progress(
            ctx.solver.var_sort(term)?,
            &mut |work, bytes| owner.admit(work, bytes).is_ok() && decision.validate(&ctx.solver),
        )
        .ok()?;
        if !decision.validate(&ctx.solver) {
            return None;
        }
        result.insert(name.to_owned(), ctx.solver.var_sort(term)?.clone());
    }
    decision.validate(&ctx.solver).then_some(result)
}

#[cfg(test)]
#[path = "model_params/owned_renderer_tests.rs"]
mod owned_renderer_tests;

fn render_model_handle_with_sorts(
    ctx: &Z3Context,
    handle: &ModelHandle,
    declared: &DeclaredSorts,
    surface: ModelSurface,
    owner: ay_core::render_admission::Owner<'_>,
) -> Option<String> {
    if owner.is_some() && surface == ModelSurface::GeneralProjection {
        return None;
    }
    let model = &handle.model;
    // A recursive function is listed by the model but never printed
    // (libz3 5.1.0: `fact` is in `m.decls()` and absent from
    // `m.sexpr()`), so the text agrees with `Z3_model_get_func_interp`.
    let recursive = |name: &str| ctx.rec_fun_defs.contains_key(name);
    let mut parts = Vec::new();
    macro_rules! text {
        ($($args:tt)*) => { ay_core::render_admission::format(owner, format_args!($($args)*)) };
    }
    macro_rules! part {
        ($value:expr) => {{
            if !ay_core::render_admission::reserve(&mut parts, 1, owner) {
                return None;
            }
            parts.push($value);
        }};
    }
    macro_rules! display_name {
        ($identity:expr) => {
            match surface {
                ModelSurface::NativeScalar => ay_core::render_admission::quote(owner, $identity),
                _ => model_entry_display_name_owned(ctx, $identity, owner),
            }
        };
    }
    for (name, val) in model.iter_bools() {
        if recursive(name) {
            continue;
        }
        let display_name = display_name!(name);
        part!(text!("(define-fun {display_name} () Bool {val})"));
    }
    for (name, val) in model.iter_ints() {
        if recursive(name) {
            continue;
        }
        let display_name = display_name!(name);
        if let Some(owner) = owner {
            let numeral = ay_dpll::format_bigint_with_admission(val, owner).ok()?;
            part!(text!("(define-fun {display_name} () Int {numeral})"));
            continue;
        }
        // A `Char` or finite-domain constant is an engine `Int`; its
        // value is printed at its own sort, as libz3 5.1.0 prints
        // `(define-fun c () Unicode (_ Char 104))` and
        // `(define-fun x () S 1)`.
        if let Some(text) = declared
            .get(name)
            .and_then(|sort| bounded_value_text(ctx, sort, val))
        {
            part!(text!("(define-fun {display_name} () {text})"));
            continue;
        }
        if val.is_negative() {
            let abs = val.abs();
            part!(text!("(define-fun {display_name} () Int (- {abs}))"));
        } else {
            part!(text!("(define-fun {display_name} () Int {val})"));
        }
    }
    for (name, val) in model.iter_reals() {
        if recursive(name) {
            continue;
        }
        let display_name = display_name!(name);
        if let Some(owner) = owner {
            let numeral = ay_dpll::format_rational_with_admission(val, owner).ok()?;
            part!(text!("(define-fun {display_name} () Real {numeral})"));
            continue;
        }
        if val.is_integer() {
            let n = val.numer();
            if n.is_negative() {
                part!(text!("(define-fun {display_name} () Real (- {}))", n.abs()));
            } else {
                part!(text!("(define-fun {display_name} () Real {n}.0)"));
            }
        } else {
            let n = val.numer();
            let d = val.denom();
            if n.is_negative() {
                part!(text!(
                    "(define-fun {display_name} () Real (- (/ {} {d})))",
                    n.abs()
                ));
            } else {
                part!(text!("(define-fun {display_name} () Real (/ {n} {d}))"));
            }
        }
    }
    for (name, (val, width)) in model.iter_bvs() {
        if recursive(name) {
            continue;
        }
        let display_name = display_name!(name);
        // Canonical BV printer: `#x` only at multiple-of-4 widths, else
        // `#b`. Open-coding hex here emitted `(_ BitVec 5) #x11`, whose
        // numeral reparses as 8 bits and contradicts its own ascription.
        let numeral = match owner {
            Some(owner) => ay_dpll::format_bitvec_with_admission(val, *width, owner).ok()?,
            None => ay_dpll::format_bitvec(val, *width),
        };
        part!(text!(
            "(define-fun {display_name} () (_ BitVec {width}) {numeral})"
        ));
    }
    for (name, val) in model.iter_strings() {
        if recursive(name) {
            continue;
        }
        let display_name = display_name!(name);
        // Escape special characters for SMT-LIB string literal
        let escaped = val.replace('\\', "\\\\").replace('"', "\\\"");
        part!(text!("(define-fun {display_name} () String \"{escaped}\")"));
    }
    // Non-scalar entries: render with the entry's resolved sort and the
    // value's SMT-LIB `Display` form (store chains for arrays, ctor
    // applications for datatypes, element tokens for uninterpreted).
    for (name, val) in model.iter_fps() {
        if recursive(name) {
            continue;
        }
        let display_name = display_name!(name);
        let sort = resolve_entry_sort(&declared, name, val);
        part!(text!("(define-fun {display_name} () {sort} {val})"));
    }
    for (name, val) in model.iter_seqs() {
        if recursive(name) {
            continue;
        }
        let display_name = display_name!(name);
        let sort = resolve_entry_sort(&declared, name, val);
        part!(text!("(define-fun {display_name} () {sort} {val})"));
    }
    for (name, val) in model.iter_arrays().chain(model.iter_finite_fields()) {
        if recursive(name) {
            continue;
        }
        let display_name = display_name!(name);
        let sort = resolve_entry_sort(&declared, name, val);
        let rendered = match (owner, val) {
            (Some(owner), ModelValue::FiniteField { value, field }) => {
                ctx.solver.format_finite_field_literal_with_admission(
                    *value,
                    *field,
                    |name| ctx.ffi_used_decl_names.contains(name),
                    owner,
                )?
            }
            _ => render_model_value_smtlib(ctx, val, &sort)?,
        };
        part!(text!("(define-fun {display_name} () {sort} {rendered})"));
    }
    for (name, val) in model.iter_datatypes() {
        if recursive(name) {
            continue;
        }
        let display_name = display_name!(name);
        let sort = resolve_entry_sort(&declared, name, val);
        part!(text!("(define-fun {display_name} () {sort} {val})"));
    }
    for (name, el) in model.iter_uninterpreteds() {
        if recursive(name) {
            continue;
        }
        let display_name = display_name!(name);
        let sort = declared
            .get(name)
            .cloned()
            .unwrap_or_else(|| Sort::Uninterpreted(el.to_string()));
        part!(text!("(define-fun {display_name} () {sort} {el})"));
    }
    // Function interpretations (z3 prints them too: a model with only
    // functions is not the empty string).
    for fi in &handle.func_interps {
        if recursive(&fi.name) {
            continue;
        }
        let display_name = display_name!(&fi.name);
        let params: Vec<String> = fi
            .param_sorts
            .iter()
            .enumerate()
            .map(|(i, sort)| text!("(x!{i} {sort})"))
            .collect();
        let mut body = match &fi.else_term {
            Some((params, term)) => {
                let mut text = super::finite_field::format_public_term_in_context(ctx, *term)?;
                for (i, &param) in params.iter().enumerate().rev() {
                    if let Some(name) = ctx.solver.var_name(param) {
                        text = text
                            .replace(&text!("|{name}|"), &text!("x!{i}"))
                            .replace(&name, &text!("x!{i}"));
                    }
                }
                text
            }
            None => render_model_value_smtlib(ctx, &fi.else_value, &fi.result_sort)?,
        };
        for (args, value) in fi.rows.iter().rev() {
            let conditions: Vec<String> = args
                .iter()
                .zip(&fi.param_sorts)
                .enumerate()
                .map(|(i, (arg, sort))| {
                    Some(text!(
                        "(= x!{i} {})",
                        render_model_value_smtlib(ctx, arg, sort)?
                    ))
                })
                .collect::<Option<Vec<_>>>()?;
            let condition = match conditions.as_slice() {
                [single] => single.clone(),
                _ => text!("(and {})", conditions.join(" ")),
            };
            let value = render_model_value_smtlib(ctx, value, &fi.result_sort)?;
            body = text!("(ite {condition} {value} {body})");
        }
        part!(text!(
            "(define-fun {display_name} ({}) {} {body})",
            params.join(" "),
            fi.result_sort
        ));
    }
    let text = ay_core::render_admission::join(owner, &parts, "\n");
    if owner.is_some_and(|owner| owner.check().is_err()) {
        return None;
    }
    Some(match surface {
        // Primitive sorts/literals have no retained AST identities to project.
        // Native snapshots keep their exact keys; public names were already
        // quoted above. A second projection would corrupt free '__db0' names.
        ModelSurface::PublicScalar => text,
        // Internal readers consume a model container, not a concatenation of
        // top-level definitions. Keep native keys for their scope/membership
        // checks instead of accidentally bypassing those checks on bare text.
        ModelSurface::NativeScalar => text!("(model {text})"),
        ModelSurface::GeneralProjection => super::ffi_surface_text(ctx, &text),
    })
}

/// Convert model to string. Returns null with an error if a model value cannot
/// be rendered within the output bounds without capturing a declaration.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_model_to_string(c: Z3_context, m: Z3_model) -> *const c_char {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_const_ptr` handles the null case internally and catches any unwinding panic
    // so it cannot cross the FFI boundary.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            if m.is_null() {
                return cache_string(ctx, "(model)".to_string());
            }
            let output = render_model_handle_text(ctx, &*m);
            match output {
                Some(text) => cache_string(ctx, text),
                None => {
                    ctx.last_error = super::Z3_INVALID_ARG;
                    ctx.error_msg = Some("model value rendering refused".into());
                    ptr::null()
                }
            }
        })
    }
}

/// Evaluate a term in the model SNAPSHOT.
///
/// Sets `*v` to the evaluated term and returns true on success. Evaluation
/// reads ONLY the model handle's snapshot (never the solver's live check
/// state): every constant leaf the model pins is substituted with its snapshot
/// value term, then the whole term is re-folded through AY's eager
/// semantics-preserving simplifier. The result is always EQUAL to the input
/// under the model:
///
/// * fully reduced to a literal when every leaf is pinned and every operator
///   folds (the common quantifier-free case);
/// * otherwise an honest PARTIAL evaluation (unpinned constants under
///   `model_completion = false` behave as the identity — exactly Z3's
///   documented semantics; an operator AY cannot ground-fold stays symbolic
///   rather than being given a fabricated value).
///
/// `model_completion = true` additionally substitutes Z3's default value for
/// every constant the model does not pin (`false`, `0`, `""`, `#x00..`,
/// `seq.empty`, a constant array of defaults, `+zero`, `S!val!0`).
///
/// Returns false (honest failure, no `*v` written) for null/invalid arguments,
/// for a `let`, and for a term where one constant occurs both free and bound
/// (substitution would not be capture-safe). A quantifier's variables are
/// left in place and its free constants are evaluated.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_model_eval(
    c: Z3_context,
    m: Z3_model,
    t: Z3_ast,
    model_completion: bool,
    v: *mut Z3_ast,
) -> bool {
    if t == 0 || v.is_null() || m.is_null() {
        return false;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_int` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let handle = &*m;
            let term = require_term_ast_or_return!(ctx, t, "Z3_model_eval", "term", 0);
            let Some(result_term) = eval_term_under_model(ctx, handle, term, model_completion)
            else {
                return 0;
            };
            let result_sort = eval_result_sort(ctx, t, term, result_term);
            let result_ast = term_to_ast(ctx, result_term);
            let result_ast = record_ast_sort(ctx, result_ast, result_sort);
            // An input returned unchanged (an unassigned constant without model
            // completion) is the same term in z3; anything else is the
            // evaluator's own construction.
            if result_term != term {
                super::provenance::mark_produced_term(ctx, result_term);
            }
            *v = result_ast;
            1
        }) != 0
    }
}

/// The core of [`Z3_model_eval`]: evaluate `term` under the model snapshot
/// `handle` (substitution of pinned constants, optional per-sort completion,
/// universe-element / constructor folding, bounded UF-table resolution) and
/// return the reduced term. `None` for a `let`, a constant that occurs both
/// free and bound (capture safety), or a recursive definition that cannot be
/// expanded. A partially-reduced result is returned as-is (honest partial
/// evaluation, never fabrication); with model completion a caller function the
/// model does not interpret takes z3's default (`complete_functions`).
///
/// Shared by `Z3_model_eval` and `Z3_model_extrapolate` (`misc_ext.rs`).
pub(crate) fn eval_term_under_model(
    ctx: &mut Z3Context,
    handle: &ModelHandle,
    term: Term,
    model_completion: bool,
) -> Option<Term> {
    let model = &handle.model;

    // Recursive definitions first (P1.1): a rec-f application must never be
    // resolved as a plain UF against the snapshot (the model of a fully
    // expanded goal does not constrain `f` at all). Expand it through the
    // registered definitions; if expansion fails, refuse honestly (`None` →
    // `Z3_model_eval` returns false) — never a fabricated or plain-UF value.
    let term = if ctx.rec_fun_defs.is_empty() {
        term
    } else {
        // Stale-definition gate: the registry is add-only (redefinition is
        // rejected at `Z3_add_rec_def`), so a model created when the registry
        // was SMALLER predates some definition. Evaluating a rec-f mention
        // through the LIVE registry could then contradict the model's own
        // certifying constraints (the model pinned `f` as a plain UF before
        // `f` was defined — skeptic finding 3's surface). Refuse honestly.
        if ctx.rec_fun_defs.len() != handle.rec_def_count {
            let def_names: HashSet<String> = ctx.rec_fun_defs.keys().cloned().collect();
            if ctx.solver.terms_mention_names(&[term], &def_names) {
                return None;
            }
        }
        // Finding-2 gate: expansion must never surface a rec-declared-but-
        // undefined function (its completion-defaulted value would be
        // fabricated). Refuse honestly.
        let tainted = super::solver::rec_defs_tainted_by_undefined(ctx);
        if !tainted.is_empty() && ctx.solver.terms_mention_names(&[term], &tainted) {
            return None;
        }
        match ctx.solver.try_expand_rec_defs(
            &[term],
            &ctx.rec_fun_defs,
            super::solver::REC_DEF_MAX_ROUNDS,
            super::solver::REC_DEF_WORK_BUDGET,
            Some(super::solver::rec_def_expansion_deadline(ctx)),
        ) {
            Ok(expanded) => expanded[0],
            Err(_) => return None,
        }
    };

    // Free constants are substituted; quantifiers' variables are not (a term
    // where one constant occurs both free and bound is refused).
    let scoped = value_folds::scoped_leaves(&ctx.solver, term)?;
    let leaves = scoped.free;

    // Build the snapshot substitution: every pinned leaf goes to its
    // model value term; with completion, unpinned leaves go to Z3's
    // per-sort default. A leaf whose value cannot be represented as a
    // term stays symbolic (partial evaluation, never fabrication).
    let mut from = Vec::with_capacity(leaves.len());
    let mut to = Vec::with_capacity(leaves.len());
    for leaf in leaves {
        let Some(name) = ctx.solver.var_name(leaf) else {
            continue;
        };
        let sort = ctx.solver.term_sort(leaf);
        if let Some(val) = model.value_by_name(&name) {
            if let Some(value_term) = model_value_to_term(&mut ctx.solver, &val, &sort) {
                from.push(leaf);
                to.push(value_term);
            }
        } else if ctx.solver.is_nullary_constructor(&name) {
            // A nullary datatype constructor constant (an enum value like
            // `blue`, or `nil`) is a fully-interpreted, pairwise-distinct
            // value — NOT an unconstrained leaf. It is stored internally as
            // a `Var` at the datatype's uninterpreted-encoded sort, so a
            // naive `model_completion` would default it to that sort's
            // shared universe element (`Color!val!0`) and collapse distinct
            // constructors to equal (`red == blue` -> true, wrong). Leave it
            // in place; the constructor-constant fold below folds `=` /
            // `distinct` over it by constructor-name identity.
        } else if model_completion {
            if let Some(default_term) = default_value_term(&mut ctx.solver, &sort) {
                from.push(leaf);
                to.push(default_term);
            }
        }
    }

    nullary_function_values(ctx, handle, term, model_completion, &mut from, &mut to);
    let substituted = ctx.solver.substitute(term, &from, &to);
    // A native `^` with a literal positive integer exponent folds like the
    // engine reads it (z3: `2**3` evaluates to `8`), not as an opaque power.
    let lowered = ctx.solver.lower_native_powers(substituted);
    let mut current = ctx.solver.simplify(lowered);
    // Model-level knowledge the generic simplifier cannot apply:
    // equality over the model's uninterpreted-sort universe elements
    // is token identity.
    let mut elements = collect_element_terms(&ctx.solver, &to);
    // Nullary datatype constructor constants (`red`/`blue`, `nil`) are the
    // SAME kind of thing for folding: fully-interpreted, pairwise-distinct
    // values whose `=`/`distinct` is constructor-name identity (a datatype
    // axiom the generic simplifier does not apply to two distinct `Var`s).
    // Fold them the same way — this is what makes `red == blue` -> false,
    // `Distinct(red,green,blue)` -> true match z3py.
    for (elem_term, ctor_name) in collect_constructor_constants(&ctx.solver, current) {
        elements.insert(elem_term, ctor_name);
    }
    current = fold_element_predicates(&mut ctx.solver, current, &elements);
    // Resolve ground uninterpreted-function applications against the
    // snapshot's function tables. Each round can expose new ground
    // applications (f(g(1))), so iterate to a bounded fixpoint.
    let interps = &handle.func_interps;
    let absent_functions: HashSet<String> = if model_completion && handle.complete_functions {
        ctx.ffi_func_names
            .values()
            .filter(|name| {
                !ctx.rec_fun_defs.contains_key(*name)
                    && !interps.iter().any(|interp| &interp.name == *name)
            })
            .cloned()
            .collect()
    } else {
        HashSet::new()
    };
    let uf_scope = UfScope {
        bound: &scoped.bound,
        absent_functions,
    };
    for _ in 0..8 {
        let (next, introduced) =
            resolve_uf_round(&mut ctx.solver, current, interps, &elements, &uf_scope);
        if next == current {
            break;
        }
        for (elem_term, token) in collect_element_terms(&ctx.solver, &introduced) {
            elements.insert(elem_term, token);
        }
        current = fold_element_predicates(&mut ctx.solver, next, &elements);
    }
    current = fold_ground_array_equalities(&mut ctx.solver, current);
    // The value folds z3's evaluator applies (`bv2nat`, `int2bv`, `^` over
    // values; quantifiers over literal bodies), to a bounded fixpoint.
    for _ in 0..4 {
        let folded = value_folds::fold_values(&mut ctx.solver, current);
        let next = ctx.solver.simplify(folded);
        if next == current {
            break;
        }
        current = next;
    }
    // A Boolean the simplifier leaves over values (floating-point operations
    // over literals, a bounded quantifier) is decided by AY's independent
    // model checker when it is closed; it answers only an exact value.
    if ctx.solver.bool_value(current).is_none() && ctx.solver.term_sort(current) == Sort::Bool {
        if let Some(value) = ctx.solver.independent_closed_bool(current) {
            current = ctx.solver.bool_const(value);
        }
    }
    // A closed floating-point term over values (`fp.add(RNE, NaN, NaN)` of a
    // completed constant) is reduced to its value, as z3's evaluator does.
    if matches!(ctx.solver.term_sort(current), Sort::FloatingPoint(..)) {
        if let Some(value) = ctx.solver.independent_closed_fp(current) {
            current = value;
        }
    }
    if matches!(ctx.solver.term_sort(current), Sort::FiniteField(_)) {
        if let Some(value) = ctx.solver.independent_closed_finite_field(current) {
            current = value;
        }
    }
    Some(current)
}

/// The values of the nullary FUNCTION applications in `term` (a
/// `Z3_mk_func_decl` of arity 0 applied with `Z3_mk_app`, which the engine
/// keeps as an application, not a constant): the model's value of the name,
/// or with model completion z3's default for a caller function the model
/// leaves out. Appended to the substitution `from -> to`.
fn nullary_function_values(
    ctx: &mut Z3Context,
    handle: &ModelHandle,
    term: Term,
    model_completion: bool,
    from: &mut Vec<Term>,
    to: &mut Vec<Term>,
) {
    for (app, name) in value_folds::nullary_applications(&ctx.solver, term) {
        let sort = ctx.solver.term_sort(app);
        let value = match handle.model.value_by_name(&name) {
            Some(value) => model_value_to_term(&mut ctx.solver, &value, &sort),
            None if model_completion
                && handle.complete_functions
                && ctx.ffi_func_names.values().any(|caller| *caller == name) =>
            {
                default_value_term(&mut ctx.solver, &sort)
            }
            None => None,
        };
        if let Some(value) = value {
            from.push(app);
            to.push(value);
        }
    }
}

/// `<sort> <value>` for an in-range value of a `Char` (`Unicode (_ Char 104)`)
/// or finite-domain (`S 1`) sort, z3's model text for them; `None` for any
/// other sort or an out-of-range value.
fn bounded_value_text(ctx: &Z3Context, sort: &Sort, value: &num_bigint::BigInt) -> Option<String> {
    let hi = super::bounded_sort_hi(sort)?;
    let code = i64::try_from(value)
        .ok()
        .filter(|code| (0..=hi).contains(code))?;
    let sort_text = super::render_public_sort(ctx, sort);
    Some(if sort.is_char() {
        format!("{sort_text} (_ Char {code})")
    } else {
        format!("{sort_text} {code}")
    })
}

/// The public sort an evaluation result carries: the input's `Char` or
/// finite-domain sort when the result is the input itself or an in-range
/// numeral of its `Int` carrier (`m.eval(c)` of a `Char` constant is a
/// `Char` value, as in libz3 5.1.0), else the result term's own sort.
fn eval_result_sort(ctx: &Z3Context, input: Z3_ast, input_term: Term, result: Term) -> Sort {
    let own = ctx.solver.term_sort(result);
    let Some(public) = super::lookup_ast_sort(ctx, input).cloned() else {
        return own;
    };
    let Some(hi) = super::bounded_sort_hi(&public) else {
        return own;
    };
    let in_range = ctx
        .solver
        .numeral_string(result)
        .and_then(|text| text.parse::<i64>().ok())
        .is_some_and(|code| (0..=hi).contains(&code));
    if result == input_term || (own == Sort::Int && in_range) {
        public
    } else {
        own
    }
}

/// Get the i-th constant declaration from the model.
///
/// Enumerates the SAME index space `Z3_model_get_num_consts` counts (see
/// [`model_entries`]): booleans, integers, reals, bitvectors, strings, floats,
/// sequences, arrays, datatypes, uninterpreted-sort constants — every entry
/// named, every index below `num_consts` valid.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_model_get_const_decl(
    c: Z3_context,
    m: Z3_model,
    i: c_uint,
) -> Z3_func_decl {
    if m.is_null() {
        return ptr::null_mut();
    }
    // All model dereferences must be inside the ffi_guard closure so that any
    // panic during model iteration is caught by catch_unwind instead of
    // propagating across the extern "C" boundary (UB).
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let model = &(*m).model;
            let entries = model_entries(&ctx.solver, model);
            match entries.get(i as usize) {
                Some((name, sort)) => {
                    if let Some(term) = ctx.ffi_const_terms_by_identity.get(name).copied() {
                        if let Some((_, symbol)) = ctx.ffi_const_metadata.get(&term).cloned() {
                            // The constant's PUBLIC sort (a finite-domain or Char
                            // constant is an Int in the model): applying the decl
                            // must give back this constant, as in z3.
                            let ast = term_to_ast(ctx, term);
                            let public = super::public_ast_sort(ctx, ast, term);
                            let decl = FuncDecl::new(name.clone(), vec![], public);
                            return cache_func_decl_with_symbol(ctx, decl, symbol);
                        }
                    }
                    cache_func_decl(ctx, FuncDecl::new(name.clone(), vec![], sort.clone()))
                }
                None => ptr::null_mut(),
            }
        })
    }
}

/// Get the interpretation of a constant in the model.
///
/// Given a func_decl (obtained from `Z3_model_get_const_decl`), returns
/// the value assigned to that constant in the model.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_model_get_const_interp(
    c: Z3_context,
    m: Z3_model,
    d: Z3_func_decl,
) -> Z3_ast {
    if m.is_null() || d.is_null() {
        return 0;
    }
    // All model/decl dereferences must be inside the ffi_guard closure so that
    // any panic is caught by catch_unwind instead of propagating across the
    // extern "C" boundary (UB).
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_produced(c, |ctx| {
            let model = &(*m).model;
            let decl = &(*d).decl;
            let name = decl.name().to_string();

            // A user-provided constant interpretation set on a hand-built model
            // (Z3_mk_model + Z3_add_const_interp) takes precedence and reads back
            // exactly the value AST the caller stored.
            for (udecl, uast) in &(*m).user_const_interps {
                if *uast != 0 && udecl.name() == name {
                    let _term = require_term_ast_or_return!(
                        ctx,
                        *uast,
                        "Z3_model_get_const_interp",
                        "stored interpretation",
                        0
                    );
                    return *uast;
                }
            }

            // A 0-ary recursively defined constant (Z3_add_rec_def) has no
            // finite model entry of its own — any snapshot value for its name
            // would be a residual-mode artifact, not the definition. Report
            // "no interpretation" (honest; `Z3_model_eval` still resolves it
            // by expanding the definition).
            if ctx.rec_fun_defs.contains_key(&name) {
                return 0;
            }
            let Some(val) = model.value_by_name(&name) else {
                return 0; // no interpretation for this constant
            };
            let declared = declared_sorts(&ctx.solver);
            let sort = resolve_entry_sort(&declared, &name, &val);
            match model_value_to_term(&mut ctx.solver, &val, &sort) {
                Some(term) => {
                    let ast = term_to_ast(ctx, term);
                    record_ast_sort(ctx, ast, sort)
                }
                // Value exists but cannot be faithfully represented as a term
                // (e.g. an unparsed ArraySmtlib blob): honest not-found, never
                // a fabricated value.
                None => 0,
            }
        })
    }
}

/// Get the number of function interpretations in the model.
///
/// Counts the arity > 0 function tables the snapshot carries (parsed from the
/// engine's raw model text at materialization time; see
/// [`ModelHandle::func_interps`](super::ModelHandle)).
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_model_get_num_funcs(c: Z3_context, m: Z3_model) -> c_uint {
    if m.is_null() {
        return 0;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_uint` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe { ffi_guard_uint(c, 0, |_ctx| (*m).func_interps.len() as c_uint) }
}

/// Check whether the model has an interpretation for a given func_decl.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_model_has_interp(_c: Z3_context, m: Z3_model, d: Z3_func_decl) -> bool {
    if m.is_null() || d.is_null() {
        return false;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_int` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_int(_c, 0, |ctx| {
            let model = &(*m).model;
            let decl = &(*d).decl;
            let name = decl.name();
            // Recursively defined names never report a snapshot interp (see
            // `Z3_model_get_const_interp`/`Z3_model_get_func_interp`) — keep
            // this predicate aligned so has-interp and get-interp agree.
            // A user-stored interp on a hand-built model still counts.
            if ctx.rec_fun_defs.contains_key(name) {
                let user_has = (*m)
                    .user_const_interps
                    .iter()
                    .any(|(udecl, uast)| *uast != 0 && udecl.name() == name);
                return i32::from(user_has);
            }
            // `value_by_name` searches EVERY sort map (including arrays,
            // datatypes and uninterpreted-sort constants), keeping this
            // predicate aligned with the enumeration and interp lookups. A
            // function declaration has an interpretation when the snapshot
            // carries its table (z3: `Z3_model_has_interp(m, f)` is true for
            // an interpreted `f`; it reported false for every function).
            let arity = decl.domain().len();
            let has_table = arity > 0
                && (*m)
                    .func_interps
                    .iter()
                    .any(|fi| fi.name == name && fi.param_sorts.len() == arity);
            i32::from(has_table || model.value_by_name(name).is_some())
        }) != 0
    }
}

// ---- Function interpretations (arity > 0) ----

/// Materialize a snapshot [`FuncInterp`] table into a C-API `Z3_func_interp`
/// handle in `ctx`'s term arena.
///
/// Every entry argument, entry value and the `else` value is converted to a
/// REAL value term of the model (via [`model_value_to_term`], the same builder
/// `Z3_model_get_const_interp` uses), recording each AST's sort so `Z3_get_sort`
/// works on them. A row whose arguments or value cannot be faithfully
/// represented is dropped (fail closed) rather than fabricated; the `else` AST
/// is `0` when it cannot be represented. The resulting graph is exactly the one
/// the engine committed — reading an entry and falling back to `else` recovers
/// the same function values the model's `define-fun` table encodes.
fn build_func_interp_handle(ctx: &mut Z3Context, fi: &FuncInterp) -> Z3_func_interp {
    let arity = fi.param_sorts.len() as c_uint;

    // else value
    let else_term = match &fi.else_term {
        Some(_) => symbolic_else::else_body_over_bound_vars(&mut ctx.solver, fi),
        None => model_value_to_term(&mut ctx.solver, &fi.else_value, &fi.result_sort),
    };
    let else_ast = match else_term {
        Some(term) => {
            let ast = term_to_ast(ctx, term);
            record_ast_sort(ctx, ast, fi.result_sort.clone())
        }
        None => 0,
    };

    let mut entries: Vec<*mut super::FuncEntryHandle> = Vec::with_capacity(fi.rows.len());
    for (row_args, row_value) in &fi.rows {
        // Convert the argument tuple; a row that arity-mismatches or carries an
        // unrepresentable argument is skipped (never fabricated).
        if row_args.len() != fi.param_sorts.len() {
            continue;
        }
        let mut arg_asts = Vec::with_capacity(row_args.len());
        let mut ok = true;
        for (arg_val, param_sort) in row_args.iter().zip(&fi.param_sorts) {
            match model_value_to_term(&mut ctx.solver, arg_val, param_sort) {
                Some(term) => {
                    let ast = term_to_ast(ctx, term);
                    let ast = record_ast_sort(ctx, ast, param_sort.clone());
                    arg_asts.push(ast);
                }
                None => {
                    ok = false;
                    break;
                }
            }
        }
        if !ok {
            continue;
        }
        let value_ast = match model_value_to_term(&mut ctx.solver, row_value, &fi.result_sort) {
            Some(term) => {
                let ast = term_to_ast(ctx, term);
                record_ast_sort(ctx, ast, fi.result_sort.clone())
            }
            None => continue,
        };
        entries.push(cache_func_entry(ctx, arg_asts, value_ast));
    }

    cache_func_interp(ctx, arity, entries, else_ast)
}

/// Return the interpretation of function `f` in model `m`, or NULL when the
/// model assigns no arity > 0 interpretation for `f` (Z3: "the `f` does not
/// matter").
///
/// The match is by declared NAME and ARITY against the snapshot's function
/// tables (parsed from the engine's real `get-model` text at check time). The
/// returned handle exposes the SAME finite map the model committed and that
/// `get-model` serializes as `(define-fun f …)` — never a fabricated graph.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_model_get_func_interp(
    c: Z3_context,
    m: Z3_model,
    f: Z3_func_decl,
) -> Z3_func_interp {
    if m.is_null() || f.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `c` is the caller's context pointer (valid or null); `ffi_guard_ptr`
    // handles null and catches unwinding panics. `m`/`f` are dereferenced only
    // inside the guarded closure.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let decl = &(*f).decl;
            let decl_name = decl.name().to_string();
            let decl_arity = decl.arity();
            // A user-provided function interpretation set on a hand-built model
            // (Z3_mk_model + Z3_add_func_interp) takes precedence and returns the
            // exact arena-owned handle the caller has been populating.
            for (udecl, uinterp) in &(*m).user_func_interps {
                if !uinterp.is_null() && udecl.arity() == decl_arity && udecl.name() == decl_name {
                    return *uinterp;
                }
            }
            // A recursively defined function (Z3_add_rec_def) has no finite
            // interpretation table: any snapshot table under its name would
            // be a residual-mode artifact, not the definition. Refuse with an
            // honest error rather than publish a fabricated-looking graph.
            if ctx.rec_fun_defs.contains_key(&decl_name) {
                ctx.last_error = super::Z3_INVALID_ARG;
                ctx.error_msg = Some(format!(
                    "Z3_model_get_func_interp: {decl_name} is recursively defined \
                     (Z3_add_rec_def); recursive functions have no finite \
                     interpretation table"
                ));
                return ptr::null_mut();
            }
            // Clone the matching table so no borrow of `*m` is held while the
            // solver arena is mutated during materialization.
            let interps = &(*m).func_interps;
            let found = interps
                .iter()
                .find(|fi| fi.name == decl_name && fi.param_sorts.len() == decl_arity)
                .cloned();
            match found {
                Some(fi) => build_func_interp_handle(ctx, &fi),
                None => ptr::null_mut(),
            }
        })
    }
}

/// Return the declaration of the i-th function interpretation in the model.
///
/// Enumerates the SAME tables `Z3_model_get_num_funcs` counts; each decl
/// carries the function's real name, domain (parameter sorts) and range (the
/// `define-fun` result sort).
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_model_get_func_decl(
    c: Z3_context,
    m: Z3_model,
    i: c_uint,
) -> Z3_func_decl {
    if m.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `m` was null-checked above and the caller guarantees it is a live
    // model handle; `ffi_guard_ptr` checks `c` before reading its tables.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let interps = &(*m).func_interps;
            match interps.get(i as usize) {
                Some(fi) => {
                    let decl = FuncDecl::new(
                        fi.name.clone(),
                        fi.param_sorts.clone(),
                        fi.result_sort.clone(),
                    );
                    cache_func_decl(ctx, decl)
                }
                None => ptr::null_mut(),
            }
        })
    }
}

/// Increment the reference counter of a `Z3_func_interp` (bookkeeping no-op:
/// the handle is arena-owned by the context, matching AY's non-RC convention).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_func_interp_inc_ref(_c: Z3_context, _f: Z3_func_interp) {}

/// Decrement the reference counter of a `Z3_func_interp` (bookkeeping no-op).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_func_interp_dec_ref(_c: Z3_context, _f: Z3_func_interp) {}

/// Return the number of entries (finite-map points) of the interpretation.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_func_interp_get_num_entries(
    c: Z3_context,
    f: Z3_func_interp,
) -> c_uint {
    if f.is_null() {
        return 0;
    }
    // SAFETY: `f` is dereferenced inside the guarded closure; `ffi_guard_uint`
    // handles a null context and catches panics.
    unsafe {
        ffi_guard_uint(c, 0, |_ctx| {
            let entries = &(*f).entries;
            entries.len() as c_uint
        })
    }
}

/// Return the i-th entry of the interpretation, or NULL if out of range.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_func_interp_get_entry(
    c: Z3_context,
    f: Z3_func_interp,
    i: c_uint,
) -> Z3_func_entry {
    if f.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `f` is dereferenced inside the guarded closure.
    unsafe {
        ffi_guard_ptr(c, |_ctx| {
            let entries = &(*f).entries;
            match entries.get(i as usize) {
                Some(&e) => e,
                None => ptr::null_mut(),
            }
        })
    }
}

/// Return the `else` (default) value of the interpretation. `0` (null AST) when
/// the value could not be faithfully represented as a term.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_func_interp_get_else(c: Z3_context, f: Z3_func_interp) -> Z3_ast {
    if f.is_null() {
        return 0;
    }
    // SAFETY: `f` is dereferenced inside the guarded closure.
    unsafe {
        ffi_guard_produced(c, |ctx| {
            let ast = (*f).else_ast;
            if ast == 0 {
                return 0;
            }
            let _term = require_term_ast_or_return!(
                ctx,
                ast,
                "Z3_func_interp_get_else",
                "stored default value",
                0
            );
            ast
        })
    }
}

/// Return the arity (number of arguments) of the interpretation.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_func_interp_get_arity(c: Z3_context, f: Z3_func_interp) -> c_uint {
    if f.is_null() {
        return 0;
    }
    // SAFETY: `f` is dereferenced inside the guarded closure.
    unsafe { ffi_guard_uint(c, 0, |_ctx| (*f).arity) }
}

/// Increment the reference counter of a `Z3_func_entry` (bookkeeping no-op:
/// arena-owned, matching AY's non-RC convention).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_func_entry_inc_ref(_c: Z3_context, _e: Z3_func_entry) {}

/// Decrement the reference counter of a `Z3_func_entry` (bookkeeping no-op).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_func_entry_dec_ref(_c: Z3_context, _e: Z3_func_entry) {}

/// Return the value of a finite-map entry (the function's value at its args).
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_func_entry_get_value(c: Z3_context, e: Z3_func_entry) -> Z3_ast {
    if e.is_null() {
        return 0;
    }
    // SAFETY: `e` is dereferenced inside the guarded closure.
    unsafe {
        ffi_guard_produced(c, |ctx| {
            let ast = (*e).value;
            let _term = require_term_ast_or_return!(
                ctx,
                ast,
                "Z3_func_entry_get_value",
                "stored entry value",
                0
            );
            ast
        })
    }
}

/// Return the number of arguments in a finite-map entry.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_func_entry_get_num_args(c: Z3_context, e: Z3_func_entry) -> c_uint {
    if e.is_null() {
        return 0;
    }
    // SAFETY: `e` is dereferenced inside the guarded closure.
    unsafe {
        ffi_guard_uint(c, 0, |_ctx| {
            let args = &(*e).args;
            args.len() as c_uint
        })
    }
}

/// Return the i-th argument of a finite-map entry. `0` (null AST) if out of
/// range.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_func_entry_get_arg(
    c: Z3_context,
    e: Z3_func_entry,
    i: c_uint,
) -> Z3_ast {
    if e.is_null() {
        return 0;
    }
    // SAFETY: `e` is dereferenced inside the guarded closure.
    unsafe {
        ffi_guard_produced(c, |ctx| {
            let args = &(*e).args;
            let Some(&ast) = args.get(i as usize) else {
                return 0;
            };
            let _term = require_term_ast_or_return!(
                ctx,
                ast,
                "Z3_func_entry_get_arg",
                "stored entry argument",
                0
            );
            ast
        })
    }
}

// ---- Model translation & uninterpreted-sort universes ----

/// Translate model `m` from context `c` into context `dst`.
///
/// AY models are self-contained snapshots (a [`Model`] of constant assignments
/// plus parsed function tables — all pure data, no shared term handles), so the
/// translation is a deep clone into a fresh handle owned by `dst`'s arena.
/// Value terms are rebuilt lazily in `dst`'s solver on demand (e.g. by
/// `Z3_model_get_const_interp`/`Z3_model_get_func_interp` against the returned
/// handle), exactly as for a natively produced model.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_model_translate(
    c: Z3_context,
    m: Z3_model,
    dst: Z3_context,
) -> Z3_model {
    if m.is_null() || dst.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `c`/`dst` are caller context pointers; `ffi_guard_ptr` handles a
    // null `c` and catches panics. `m` and `dst` are dereferenced inside the
    // closure. When `dst == c` the handle we already hold is reused, so no two
    // `&mut Z3Context` ever alias.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let src_model = &(*m).model;
            let src_interps = &(*m).func_interps;
            let model = src_model.clone();
            let same_context = ptr::eq(dst.cast_const(), ptr::from_ref::<Z3Context>(ctx));
            // A symbolic else is a term of the SOURCE context's arena, which
            // the copy cannot carry across. Dropping it left the function
            // uninterpreted in the translated model (z3 carries `[else -> 1 +
            // Var(0)]`, and `g(4)` evaluates to 5 there), so the translation
            // is refused instead.
            if let Some(symbolic) = src_interps
                .iter()
                .find(|fi| fi.else_term.is_some())
                .filter(|_| !same_context)
            {
                ctx.last_error = super::Z3_INVALID_USAGE;
                ctx.error_msg = Some(super::ffi_surface_text(
                    ctx,
                    &format!(
                        "Z3_model_translate: the model interprets {} with a symbolic else \
                         that cannot be carried to another context",
                        symbolic.name
                    ),
                ));
                return ptr::null_mut();
            }
            let func_interps: Vec<FuncInterp> = src_interps.clone();
            // User-provided const/func interps (Z3_add_*_interp) are NOT carried
            // across a model translation: the stored value ASTs / func-interp
            // handles live in the SOURCE context's arena and would dangle in the
            // destination. A translated model exposes only the engine snapshot.
            // The stale-definition stamp is taken against the DESTINATION
            // registry: the translated handle lives in (and is evaluated
            // against) `dst`.
            let dst_rec_def_count = if ptr::eq(dst.cast_const(), ptr::from_ref::<Z3Context>(ctx)) {
                ctx.rec_fun_defs.len()
            } else {
                (*dst).rec_fun_defs.len()
            };
            // Across contexts every entry is renamed to the destination's
            // declaration of the same name and signature (z3 translates the
            // declarations; measured: `m.decls()` listed `!ay.z3-const!0`).
            let mut model = model;
            let mut func_interps = func_interps;
            let mut renamed_all = true;
            if !ptr::eq(dst.cast_const(), ptr::from_ref::<Z3Context>(ctx)) {
                let dst_ctx = &mut *dst;
                renamed_all = translate_model_names(ctx, dst_ctx, &mut model, &mut func_interps);
            }
            // Completion of absent functions needs every table.
            let complete_functions = (*m).complete_functions && renamed_all;
            let handle = Box::into_raw(Box::new(ModelHandle {
                model,
                func_interps,
                user_const_interps: Vec::new(),
                user_func_interps: Vec::new(),
                rec_def_count: dst_rec_def_count,
                complete_functions,
                _ctx: dst,
            }));
            if ptr::eq(dst.cast_const(), ptr::from_ref::<Z3Context>(ctx)) {
                ctx.model_cache.push(handle);
            } else {
                let dst_ctx = &mut *dst;
                dst_ctx.model_cache.push(handle);
            }
            handle
        })
    }
}

/// Rename the entries of a model translated from `src` into `dst` to `dst`'s
/// declarations of the same caller-visible name and signature; `false` when
/// some entry has no such declaration (it keeps the source identity).
fn translate_model_names(
    src: &Z3Context,
    dst: &mut Z3Context,
    model: &mut Model,
    func_interps: &mut [FuncInterp],
) -> bool {
    let mut renames: StdHashMap<String, String> = StdHashMap::new();
    let mut all = true;
    let names: Vec<String> = model.names().map(str::to_string).collect();
    for name in names {
        let Some(&term) = src.ffi_const_terms_by_identity.get(&name) else {
            all = false;
            continue;
        };
        let Some((_, symbol)) = src.ffi_const_metadata.get(&term) else {
            all = false;
            continue;
        };
        let sort = src.solver.term_sort(term);
        // A datatype the target does not know yet is declared there, as z3's
        // translation carries the sort (its constructors build the values).
        if let Sort::Datatype(dt) = &sort {
            if dst.solver.resolve_sort_name(&dt.name).is_none()
                && dst.solver.try_declare_datatype(dt).is_err()
            {
                all = false;
                continue;
            }
        }
        let Some(target) = super::terms::ffi_api_constant(dst, symbol, &sort) else {
            all = false;
            continue;
        };
        match dst.ffi_const_metadata.get(&target) {
            Some((identity, _)) => {
                renames.insert(name, identity.clone());
            }
            None => all = false,
        }
    }
    model.rename_names(|name| renames.get(name).cloned());
    for interp in func_interps.iter_mut() {
        let source = src
            .ffi_func_decls
            .iter()
            .find_map(|((symbol, domain, range), decl)| {
                (decl.name() == interp.name)
                    .then(|| (symbol.clone(), domain.clone(), range.clone()))
            });
        let Some((symbol, domain, range)) = source else {
            all = false;
            continue;
        };
        match super::ffi_try_declare_function(dst, &symbol, &domain, &range) {
            Ok(decl) => {
                dst.ffi_used_decl_names.insert(symbol.display_name());
                interp.name = decl.name().to_string();
            }
            Err(_) => all = false,
        }
    }
    all
}

/// Reconstruct the finite universes of the uninterpreted sorts the model
/// interprets, purely from real model data.
///
/// Groups the model's uninterpreted-sort CONSTANT assignments (each `x → token`
/// from [`Model::iter_uninterpreteds`]) by the constant's DECLARED sort, keeping
/// only genuine `Sort::Uninterpreted(_)` sorts (never fabricating a sort from a
/// bare element token). Distinct element tokens are distinct universe values
/// (uninterpreted equality is token identity). Sorts and elements keep
/// first-seen order for determinism.
///
/// This is an honest subset: it contains exactly the universe elements the
/// model actually committed via named constants. If Z3 pads a universe with
/// extra fresh elements not tied to any constant, those are not recovered — a
/// documented limitation, never a fabricated element.
pub(crate) fn model_sort_universes(solver: &Solver, model: &Model) -> Vec<(Sort, Vec<String>)> {
    let declared = declared_sorts(solver);
    let mut order: Vec<Sort> = Vec::new();
    let mut map: StdHashMap<Sort, Vec<String>> = StdHashMap::new();
    for (name, element) in model.iter_uninterpreteds() {
        let sort = match declared.get(name) {
            Some(s) if matches!(s, Sort::Uninterpreted(_)) => s.clone(),
            _ => continue, // only real uninterpreted sorts
        };
        let universe = map.entry(sort.clone()).or_insert_with(|| {
            order.push(sort.clone());
            Vec::new()
        });
        if !universe.iter().any(|e| e == element) {
            universe.push(element.to_string());
        }
    }
    order
        .into_iter()
        .map(|s| {
            let universe = map.remove(&s).unwrap_or_default();
            (s, universe)
        })
        .collect()
}

/// Return the number of uninterpreted sorts the model assigns a universe to.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_model_get_num_sorts(c: Z3_context, m: Z3_model) -> c_uint {
    if m.is_null() {
        return 0;
    }
    // SAFETY: `m` is dereferenced inside the guarded closure.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            model_sort_universes(&ctx.solver, &(*m).model).len() as c_uint
        })
    }
}

/// Return the i-th uninterpreted sort the model interprets.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_model_get_sort(c: Z3_context, m: Z3_model, i: c_uint) -> Z3_sort {
    if m.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `m` is dereferenced inside the guarded closure.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let universes = model_sort_universes(&ctx.solver, &(*m).model);
            match universes.into_iter().nth(i as usize) {
                Some((sort, _)) => alloc_sort(ctx, sort),
                None => ptr::null_mut(),
            }
        })
    }
}

/// Return the finite set of distinct values interpreting sort `s` in the model,
/// as an AST vector of element constants of that sort.
///
/// Returns an EMPTY (valid) vector when `s` is not one of the uninterpreted
/// sorts the model interprets — honest, never a fabricated universe.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_model_get_sort_universe(
    c: Z3_context,
    m: Z3_model,
    s: Z3_sort,
) -> Z3_ast_vector {
    if m.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `m`/`s` are dereferenced inside the guarded closure.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let target = s.as_ref().map(|h| h.sort.clone());
            let universes = model_sort_universes(&ctx.solver, &(*m).model);
            let mut asts: Vec<Z3_ast> = Vec::new();
            if let Some(target) = target {
                if let Some((sort, tokens)) =
                    universes.into_iter().find(|(sort, _)| *sort == target)
                {
                    for token in tokens {
                        let val = ModelValue::Uninterpreted(token);
                        if let Some(term) = model_value_to_term(&mut ctx.solver, &val, &sort) {
                            let ast = term_to_ast(ctx, term);
                            let ast = record_ast_sort(ctx, ast, sort.clone());
                            asts.push(ast);
                        }
                    }
                }
            }
            cache_ast_vector(ctx, asts)
        })
    }
}

// ---- Params ----

/// Create a params object stored until `Z3_solver_set_params` applies it.
///
/// AY currently honors only the `timeout` parameter, expressed in milliseconds.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_params(c: Z3_context) -> Z3_params {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let handle = Box::into_raw(Box::new(ParamsHandle {
                params: Vec::new(),
                kinds: Vec::new(),
            }));
            ctx.params_cache.push(handle);
            handle
        })
    }
}

/// Increment params reference count (no-op).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_params_inc_ref(_c: Z3_context, _p: Z3_params) {}

/// Decrement params reference count (no-op).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_params_dec_ref(_c: Z3_context, _p: Z3_params) {}

/// Set a boolean parameter.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_params_set_bool(_c: Z3_context, p: Z3_params, k: Z3_symbol, v: bool) {
    if p.is_null() || k.is_null() {
        return;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_void` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_void(_c, |_ctx| {
            let params = &mut (*p).params;
            let key = (*k).display_name();
            params.push((key, v.to_string()));
            (*p).kinds.push(super::StoredParamKind::Bool);
        });
    }
}

/// Set an unsigned int parameter.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_params_set_uint(_c: Z3_context, p: Z3_params, k: Z3_symbol, v: c_uint) {
    if p.is_null() || k.is_null() {
        return;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_void` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_void(_c, |_ctx| {
            let params = &mut (*p).params;
            let key = (*k).display_name();
            params.push((key, v.to_string()));
            (*p).kinds.push(super::StoredParamKind::UInt);
        });
    }
}

/// Set a double parameter.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_params_set_double(
    _c: Z3_context,
    p: Z3_params,
    k: Z3_symbol,
    v: c_double,
) {
    if p.is_null() || k.is_null() {
        return;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_void` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_void(_c, |_ctx| {
            let params = &mut (*p).params;
            let key = (*k).display_name();
            params.push((key, v.to_string()));
            (*p).kinds.push(super::StoredParamKind::Double);
        });
    }
}

/// Set a symbol parameter.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_params_set_symbol(
    _c: Z3_context,
    p: Z3_params,
    k: Z3_symbol,
    v: Z3_symbol,
) {
    if p.is_null() || k.is_null() || v.is_null() {
        return;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_void` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_void(_c, |_ctx| {
            let params = &mut (*p).params;
            let key = (*k).display_name();
            let val = (*v).display_name();
            params.push((key, val));
            (*p).kinds.push(super::StoredParamKind::Symbol);
        });
    }
}
