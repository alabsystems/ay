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
    cache_func_interp, cache_string, ffi_guard_ast, ffi_guard_const_ptr, ffi_guard_int,
    ffi_guard_ptr, ffi_guard_uint, ffi_guard_void, record_ast_sort, require_term_ast_or_return,
    term_to_ast, ModelHandle, ParamsHandle, Z3Context, Z3_ast, Z3_ast_vector, Z3_context,
    Z3_func_decl, Z3_func_entry, Z3_func_interp, Z3_model, Z3_params, Z3_sort, Z3_symbol,
};

// ---- Snapshot-model helpers ----

/// Sort implied by a scalar model value, if it is one.
fn scalar_value_sort(val: &ModelValue) -> Option<Sort> {
    match val {
        ModelValue::Bool(_) => Some(Sort::Bool),
        ModelValue::Int(_) => Some(Sort::Int),
        ModelValue::Real(_) => Some(Sort::Real),
        ModelValue::BitVec { width, .. } => Some(Sort::bitvec(*width)),
        ModelValue::String(_) => Some(Sort::String),
        ModelValue::FloatingPoint { eb, sb, .. }
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
fn declared_sorts(solver: &Solver) -> StdHashMap<String, Sort> {
    solver
        .declared_variables()
        .map(|(name, term)| (name.to_string(), solver.term_sort(term)))
        .collect()
}

/// Resolve the sort for a named model entry: declared sort first, then the
/// sort implied by the value, then a defensive fallback (so enumeration can
/// never drop an entry and misalign `num_consts` with `get_const_decl`).
fn resolve_entry_sort(declared: &StdHashMap<String, Sort>, name: &str, val: &ModelValue) -> Sort {
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

fn model_entry_display_name(ctx: &Z3Context, identity: &str) -> String {
    let display = ctx
        .ffi_const_terms_by_identity
        .get(identity)
        .and_then(|term| ctx.ffi_const_metadata.get(term))
        .map(|(_, symbol)| symbol.display_name())
        .unwrap_or_else(|| identity.to_string());
    ay_core::quote_symbol(&display)
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
        ModelValue::Int(n) => Some(solver.int_const_bigint(n)),
        ModelValue::Real(r) => Some(solver.rational_const_bigint(r.numer(), r.denom())),
        ModelValue::BitVec { value, width } => Some(solver.bv_const_bigint(value, *width)),
        ModelValue::String(s) => Some(solver.string_const(s)),
        ModelValue::FloatingPoint {
            sign,
            exponent,
            significand,
            eb,
            sb,
        } => {
            let sign_bv = solver.bv_const(i64::from(*sign), 1);
            let exp_bv = solver.bv_const(*exponent as i64, *eb);
            let sig_bv = solver.bv_const(*significand as i64, *sb - 1);
            Some(solver.fp_from_bvs(sign_bv, exp_bv, sig_bv, *eb, *sb))
        }
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
            Sort::Uninterpreted(_) => Some(solver.declare_const(element, sort.clone())),
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
        Sort::BitVec(bv) => Some(solver.bv_const(0, bv.width)),
        Sort::String => Some(solver.string_const("")),
        Sort::FloatingPoint(eb, sb) => Some(solver.fp_plus_zero(*eb, *sb)),
        Sort::Seq(element) => Some(solver.seq_empty((**element).clone())),
        Sort::Array(arr) => {
            let default = default_value_term(solver, &arr.element_sort)?;
            Some(solver.const_array(arr.index_sort.clone(), default))
        }
        // `RoundingMode` is a FIXED 5-element FP domain, not an open
        // uninterpreted universe: a `RoundingMode!val!0` fresh element is NOT a
        // valid value of the sort (z3 rejects a model carrying it). Complete an
        // unconstrained RM constant with a concrete IEEE-default mode, mirroring
        // the SMT-LIB completion path (`completion.rs`
        // `unconstrained_default_value`) which returns `roundNearestTiesToEven`
        // (#P0.2 symbolic RoundingMode).
        Sort::Uninterpreted(name) if name == "RoundingMode" => Some(solver.fp_rounding_mode("RNE")),
        // Z3 completes an uninterpreted-sort constant with a fresh universe
        // element (`S!val!0`); the same token is reused deterministically.
        Sort::Uninterpreted(name) => {
            let element = format!("{name}!val!0");
            Some(solver.declare_const(&element, sort.clone()))
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
fn render_model_value_smtlib(val: &ModelValue, sort: &Sort) -> String {
    match (val, sort) {
        (ModelValue::Array { default, stores }, Sort::Array(arr)) => {
            let mut text = format!(
                "((as const {sort}) {})",
                render_model_value_smtlib(default, &arr.element_sort)
            );
            for (index, value) in stores {
                text = format!(
                    "(store {text} {} {})",
                    render_model_value_smtlib(index, &arr.index_sort),
                    render_model_value_smtlib(value, &arr.element_sort)
                );
            }
            text
        }
        _ => val.to_string(),
    }
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
    pub(crate) else_value: ModelValue,
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
        SExpr::Hexadecimal(hex) => Some(ModelValue::BitVec {
            value: BigInt::parse_bytes(hex.as_bytes(), 16)?,
            width: u32::try_from(hex.len()).ok()?.checked_mul(4)?,
        }),
        SExpr::Binary(bits) => Some(ModelValue::BitVec {
            value: BigInt::parse_bytes(bits.as_bytes(), 2)?,
            width: u32::try_from(bits.len()).ok()?,
        }),
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
        });
    }
    out
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
) -> (Term, Vec<Term>) {
    if interps.is_empty() {
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
                let determined = children.iter().all(|&arg| {
                    matches!(solver.term_kind(arg), TermKind::Const) || elements.contains_key(&arg)
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
    model_value_to_term(solver, &interp.else_value, result_sort)
}

/// Collect the distinct named-constant leaves of `term` (post-order over the
/// hash-consed DAG, deduplicated).
///
/// Returns `None` if the term contains a binder (`forall`/`exists`/`let`):
/// substituting under binders is not capture-safe, so `Z3_model_eval` refuses
/// those terms honestly instead of risking a wrong evaluation.
fn collect_named_leaves(solver: &Solver, root: Term) -> Option<Vec<Term>> {
    let mut stack = vec![root];
    let mut seen: HashSet<Term> = HashSet::new();
    let mut leaves = Vec::new();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match solver.term_kind(term) {
            TermKind::Forall | TermKind::Exists | TermKind::Let => return None,
            TermKind::Var { .. } => leaves.push(term),
            TermKind::Const => {}
            TermKind::App { .. } | TermKind::Not | TermKind::Ite => {
                stack.extend(solver.term_children(term));
            }
            // Future TermKind variants: treat as opaque (leave symbolic).
            _ => {}
        }
    }
    Some(leaves)
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

/// Convert model to string.
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
            let model = &(*m).model;
            let mut parts = Vec::new();
            for (name, val) in model.iter_bools() {
                let display_name = model_entry_display_name(ctx, name);
                parts.push(format!("(define-fun {display_name} () Bool {val})"));
            }
            for (name, val) in model.iter_ints() {
                let display_name = model_entry_display_name(ctx, name);
                if val.is_negative() {
                    let abs = val.abs();
                    parts.push(format!("(define-fun {display_name} () Int (- {abs}))"));
                } else {
                    parts.push(format!("(define-fun {display_name} () Int {val})"));
                }
            }
            for (name, val) in model.iter_reals() {
                let display_name = model_entry_display_name(ctx, name);
                if val.is_integer() {
                    let n = val.numer();
                    if n.is_negative() {
                        parts.push(format!(
                            "(define-fun {display_name} () Real (- {}))",
                            n.abs()
                        ));
                    } else {
                        parts.push(format!("(define-fun {display_name} () Real {n}.0)"));
                    }
                } else {
                    let n = val.numer();
                    let d = val.denom();
                    if n.is_negative() {
                        parts.push(format!(
                            "(define-fun {display_name} () Real (- (/ {} {d})))",
                            n.abs()
                        ));
                    } else {
                        parts.push(format!("(define-fun {display_name} () Real (/ {n} {d}))"));
                    }
                }
            }
            for (name, (val, width)) in model.iter_bvs() {
                let display_name = model_entry_display_name(ctx, name);
                let hex_str = format!("{val:x}");
                let hex_width = (*width as usize).div_ceil(4);
                let padded = format!("{hex_str:0>hex_width$}");
                parts.push(format!(
                    "(define-fun {display_name} () (_ BitVec {width}) #x{padded})"
                ));
            }
            for (name, val) in model.iter_strings() {
                let display_name = model_entry_display_name(ctx, name);
                // Escape special characters for SMT-LIB string literal
                let escaped = val.replace('\\', "\\\\").replace('"', "\\\"");
                parts.push(format!(
                    "(define-fun {display_name} () String \"{escaped}\")"
                ));
            }
            // Non-scalar entries: render with the entry's resolved sort and the
            // value's SMT-LIB `Display` form (store chains for arrays, ctor
            // applications for datatypes, element tokens for uninterpreted).
            let declared = declared_sorts(&ctx.solver);
            for (name, val) in model.iter_fps() {
                let display_name = model_entry_display_name(ctx, name);
                let sort = resolve_entry_sort(&declared, name, val);
                parts.push(format!("(define-fun {display_name} () {sort} {val})"));
            }
            for (name, val) in model.iter_seqs() {
                let display_name = model_entry_display_name(ctx, name);
                let sort = resolve_entry_sort(&declared, name, val);
                parts.push(format!("(define-fun {display_name} () {sort} {val})"));
            }
            for (name, val) in model.iter_arrays() {
                let display_name = model_entry_display_name(ctx, name);
                let sort = resolve_entry_sort(&declared, name, val);
                let rendered = render_model_value_smtlib(val, &sort);
                parts.push(format!("(define-fun {display_name} () {sort} {rendered})"));
            }
            for (name, val) in model.iter_datatypes() {
                let display_name = model_entry_display_name(ctx, name);
                let sort = resolve_entry_sort(&declared, name, val);
                parts.push(format!("(define-fun {display_name} () {sort} {val})"));
            }
            for (name, el) in model.iter_uninterpreteds() {
                let display_name = model_entry_display_name(ctx, name);
                let sort = declared
                    .get(name)
                    .cloned()
                    .unwrap_or_else(|| Sort::Uninterpreted(el.to_string()));
                parts.push(format!("(define-fun {display_name} () {sort} {el})"));
            }
            let output = super::ffi_surface_text(ctx, &parts.join("\n"));
            cache_string(ctx, output)
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
/// Returns false (honest failure, no `*v` written) for null/invalid arguments
/// and for binder-containing terms (`forall`/`exists`/`let`), where
/// substitution would not be capture-safe.
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
            let result_sort = ctx.solver.term_sort(result_term);
            let result_ast = term_to_ast(ctx, result_term);
            record_ast_sort(ctx, result_ast, result_sort);
            *v = result_ast;
            1
        }) != 0
    }
}

/// The core of [`Z3_model_eval`]: evaluate `term` under the model snapshot
/// `handle` (substitution of pinned constants, optional per-sort completion,
/// universe-element / constructor folding, bounded UF-table resolution) and
/// return the reduced term. `None` only for a binder-containing term (refused
/// honestly for capture safety). A partially-reduced result is returned as-is
/// (honest partial evaluation, never fabrication).
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

    // Binder-containing terms are refused honestly (capture safety).
    let leaves = collect_named_leaves(&ctx.solver, term)?;

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

    let substituted = ctx.solver.substitute(term, &from, &to);
    let mut current = ctx.solver.simplify(substituted);
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
    for _ in 0..8 {
        let (next, introduced) = resolve_uf_round(&mut ctx.solver, current, interps, &elements);
        if next == current {
            break;
        }
        for (elem_term, token) in collect_element_terms(&ctx.solver, &introduced) {
            elements.insert(elem_term, token);
        }
        current = fold_element_predicates(&mut ctx.solver, next, &elements);
    }
    Some(current)
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
                    let decl = FuncDecl::new(name.clone(), vec![], sort.clone());
                    if let Some(term) = ctx.ffi_const_terms_by_identity.get(name).copied() {
                        if let Some((_, symbol)) = ctx.ffi_const_metadata.get(&term).cloned() {
                            return cache_func_decl_with_symbol(ctx, decl, symbol);
                        }
                    }
                    cache_func_decl(ctx, decl)
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
        ffi_guard_ast(c, |ctx| {
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
                    record_ast_sort(ctx, ast, sort);
                    ast
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
            // predicate aligned with the enumeration and interp lookups.
            i32::from(model.value_by_name(name).is_some())
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
    let else_ast = match model_value_to_term(&mut ctx.solver, &fi.else_value, &fi.result_sort) {
        Some(term) => {
            let ast = term_to_ast(ctx, term);
            record_ast_sort(ctx, ast, fi.result_sort.clone());
            ast
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
                    record_ast_sort(ctx, ast, param_sort.clone());
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
                record_ast_sort(ctx, ast, fi.result_sort.clone());
                ast
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
    // SAFETY: see `Z3_model_get_func_interp`.
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
        ffi_guard_ast(c, |ctx| {
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
        ffi_guard_ast(c, |ctx| {
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
        ffi_guard_ast(c, |ctx| {
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
            let func_interps = src_interps.clone();
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
            let handle = Box::into_raw(Box::new(ModelHandle {
                model,
                func_interps,
                user_const_interps: Vec::new(),
                user_func_interps: Vec::new(),
                rec_def_count: dst_rec_def_count,
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
                            record_ast_sort(ctx, ast, sort.clone());
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
            let handle = Box::into_raw(Box::new(ParamsHandle { params: Vec::new() }));
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
        });
    }
}
