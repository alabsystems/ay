// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3 5.0.0 finite-set C API.
//!
//! AY represents `(FiniteSet T)` internally by its characteristic array
//! `(Array T Bool)`, while retaining a distinct public sort and application
//! surface. The representation is exact for the constructor algebra. Free
//! finite-set values use the same array carrier as a sound over-approximation:
//! UNSAT remains sound, and SAT is conservatively demoted to UNKNOWN because an
//! arbitrary array over an infinite basis need not have finite support.

use std::collections::{HashMap, HashSet};
use std::ffi::c_uint;
use std::ptr;

use ay_dpll::api::{Sort, Term};

use super::{
    alloc_sort, apply_surface_replacements, cache_func_decl_with_params, checked_ast_to_term,
    ffi_guard_ast, ffi_guard_int, ffi_guard_ptr, ffi_surface_text_base, lookup_ast_sort,
    record_ast_sort, term_to_ast, Z3Context, Z3_ast, Z3_context, Z3_func_decl, Z3_sort,
    Z3_INVALID_ARG, Z3_SORT_ERROR, Z3_UNKNOWN_SORT,
};

/// Public finite-set application kind retained over an engine lowering.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum FiniteSetOp {
    Empty,
    Singleton,
    Union,
    Intersect,
    Difference,
    Member,
    Size,
    Subset,
    Map,
    Filter,
    Range,
}

/// Decision obligations attached to a term that exposes a finite-set carrier.
///
/// These are deliberately term-local. A Z3 context is an AST arena shared by
/// independent solver handles, so constructing an unused finite-set term must
/// not change any handle's answer.
#[derive(Clone, Debug, Default)]
pub(crate) struct FiniteSetTermProvenance {
    pub(crate) arbitrary_reason: Option<String>,
    pub(crate) quantifier_reason: Option<String>,
}

/// Finite-set obligations reachable from one concrete decision goal.
#[derive(Clone, Debug, Default)]
pub(crate) struct FiniteSetDecisionGate {
    pub(crate) uses_finite_set: bool,
    pub(crate) arbitrary_reason: Option<String>,
    pub(crate) quantifier_reason: Option<String>,
}

impl FiniteSetOp {
    pub(crate) const fn name(self) -> &'static str {
        match self {
            Self::Empty => "set.empty",
            Self::Singleton => "set.singleton",
            Self::Union => "set.union",
            Self::Intersect => "set.intersect",
            Self::Difference => "set.difference",
            Self::Member => "set.in",
            Self::Size => "set.size",
            Self::Subset => "set.subset",
            Self::Map => "set.map",
            Self::Filter => "set.filter",
            Self::Range => "set.range",
        }
    }

    pub(crate) const fn decl_kind(self) -> c_uint {
        match self {
            Self::Empty => super::Z3_OP_FINITE_SET_EMPTY,
            Self::Singleton => super::Z3_OP_FINITE_SET_SINGLETON,
            Self::Union => super::Z3_OP_FINITE_SET_UNION,
            Self::Intersect => super::Z3_OP_FINITE_SET_INTERSECT,
            Self::Difference => super::Z3_OP_FINITE_SET_DIFFERENCE,
            Self::Member => super::Z3_OP_FINITE_SET_IN,
            Self::Size => super::Z3_OP_FINITE_SET_SIZE,
            Self::Subset => super::Z3_OP_FINITE_SET_SUBSET,
            Self::Map => super::Z3_OP_FINITE_SET_MAP,
            Self::Filter => super::Z3_OP_FINITE_SET_FILTER,
            Self::Range => super::Z3_OP_FINITE_SET_RANGE,
        }
    }
}

/// Intern a frontend-retained public sort in this Z3 context.
///
/// The frontend and engine share core [`Sort`] values, while FiniteSet identity
/// is deliberately context-private on the C surface. Ambiguous/unknown
/// occurrence sorts must be resolved by frontend metadata before they reach
/// this adapter.
pub(crate) fn intern_frontend_public_sort(
    ctx: &mut Z3Context,
    sort: &ay_frontend::PublicSort,
) -> Option<Sort> {
    match sort {
        ay_frontend::PublicSort::Core(sort) => Some(sort.clone()),
        ay_frontend::PublicSort::Array(index, element) => Some(Sort::array(
            intern_frontend_public_sort(ctx, index)?,
            intern_frontend_public_sort(ctx, element)?,
        )),
        ay_frontend::PublicSort::Seq(element) => {
            Some(Sort::seq(intern_frontend_public_sort(ctx, element)?))
        }
        ay_frontend::PublicSort::FiniteSet(element) => {
            let basis = intern_frontend_public_sort(ctx, element)?;
            Some(public_sort_for_basis(ctx, basis))
        }
        ay_frontend::PublicSort::AmbiguousSet(_) | ay_frontend::PublicSort::Unknown => None,
        _ => None,
    }
}

/// Convert a C-surface public sort into frontend parser metadata.
pub(crate) fn frontend_public_sort(ctx: &Z3Context, sort: &Sort) -> ay_frontend::PublicSort {
    if let Some(basis) = finite_set_basis(ctx, sort) {
        return ay_frontend::PublicSort::FiniteSet(Box::new(frontend_public_sort(ctx, basis)));
    }
    match sort {
        Sort::Array(array) => ay_frontend::PublicSort::Array(
            Box::new(frontend_public_sort(ctx, &array.index_sort)),
            Box::new(frontend_public_sort(ctx, &array.element_sort)),
        ),
        Sort::Seq(element) => {
            ay_frontend::PublicSort::Seq(Box::new(frontend_public_sort(ctx, element)))
        }
        other => ay_frontend::PublicSort::Core(other.clone()),
    }
}

/// Exact public structure of a finite-set application.
#[derive(Clone, Debug)]
pub(crate) struct FiniteSetApp {
    pub(crate) op: FiniteSetOp,
    pub(crate) args: Vec<Z3_ast>,
    pub(crate) domain: Vec<Sort>,
    pub(crate) range: Sort,
}

/// Z3-style application identity. The result sort distinguishes polymorphic
/// nullary `set.empty` applications.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct FiniteSetAppKey {
    op: FiniteSetOp,
    args: Vec<Z3_ast>,
    range: Sort,
}

/// Return the public finite-set basis for `sort`.
pub(crate) fn finite_set_basis<'a>(ctx: &'a Z3Context, sort: &Sort) -> Option<&'a Sort> {
    ctx.finite_set_sorts.get(sort)
}

/// Whether a public sort contains a finite-set sort at any depth.
///
/// Array and sequence nesting is lowered recursively. Datatype nesting is
/// detected too so callers can reject it: rebuilding an already-declared
/// datatype with lowered field sorts would create a different datatype.
pub(crate) fn sort_mentions_finite_set(ctx: &Z3Context, sort: &Sort) -> bool {
    if finite_set_basis(ctx, sort).is_some() {
        return true;
    }
    match sort {
        Sort::Array(array) => {
            sort_mentions_finite_set(ctx, &array.index_sort)
                || sort_mentions_finite_set(ctx, &array.element_sort)
        }
        Sort::Seq(element) => sort_mentions_finite_set(ctx, element),
        Sort::Datatype(datatype) => datatype.constructors.iter().any(|constructor| {
            constructor
                .fields
                .iter()
                .any(|field| sort_mentions_finite_set(ctx, &field.sort))
        }),
        _ => false,
    }
}

/// Whether lowering `sort` would require changing a datatype definition.
pub(crate) fn has_unsupported_finite_set_datatype_embedding(ctx: &Z3Context, sort: &Sort) -> bool {
    match sort {
        Sort::Array(array) => {
            has_unsupported_finite_set_datatype_embedding(ctx, &array.index_sort)
                || has_unsupported_finite_set_datatype_embedding(ctx, &array.element_sort)
        }
        Sort::Seq(element) => has_unsupported_finite_set_datatype_embedding(ctx, element),
        Sort::Datatype(datatype) => datatype.constructors.iter().any(|constructor| {
            constructor
                .fields
                .iter()
                .any(|field| sort_mentions_finite_set(ctx, &field.sort))
        }),
        _ => finite_set_basis(ctx, sort)
            .is_some_and(|basis| has_unsupported_finite_set_datatype_embedding(ctx, basis)),
    }
}

/// Convert a public sort into the sort used by AY's term engine.
///
/// The recursion matters for nested finite sets and arrays whose domain or
/// range contains a finite-set sort.
pub(crate) fn finite_set_engine_public_sort(ctx: &Z3Context, sort: &Sort) -> Sort {
    if let Some(basis) = finite_set_basis(ctx, sort) {
        return Sort::array(finite_set_engine_public_sort(ctx, basis), Sort::Bool);
    }
    match sort {
        Sort::Array(array) => Sort::array(
            finite_set_engine_public_sort(ctx, &array.index_sort),
            finite_set_engine_public_sort(ctx, &array.element_sort),
        ),
        Sort::Seq(element) => Sort::seq(finite_set_engine_public_sort(ctx, element)),
        other => other.clone(),
    }
}

/// Exact public rendering for a sort that may contain FiniteSet recursively.
pub(crate) fn render_public_sort(ctx: &Z3Context, sort: &Sort) -> String {
    if let Some(basis) = finite_set_basis(ctx, sort) {
        return format!("(FiniteSet {})", render_public_sort(ctx, basis));
    }
    match sort {
        Sort::Array(array) => format!(
            "(Array {} {})",
            render_public_sort(ctx, &array.index_sort),
            render_public_sort(ctx, &array.element_sort)
        ),
        Sort::Seq(element) => format!("(Seq {})", render_public_sort(ctx, element)),
        Sort::Char => "Unicode".to_string(),
        // Do not invoke the full surface projection here: it renders every
        // retained FiniteSet witness, whose typed `set.empty` applications
        // recursively render their range sort through this function.
        other => ffi_surface_text_base(ctx, &other.to_string()),
    }
}

/// Exact public sort text `(FiniteSet basis)`.
pub(crate) fn finite_set_sort_text(ctx: &Z3Context, sort: &Sort) -> Option<String> {
    finite_set_basis(ctx, sort).map(|_| render_public_sort(ctx, sort))
}

/// Record that a term has an arbitrary finite-set carrier.
///
/// The characteristic-array encoding is an over-approximation of finite
/// support. UNSAT remains sound, while a SAT result for a goal reaching this
/// term requires a finiteness certificate.
pub(crate) fn activate_finite_set_sat_gate(ctx: &mut Z3Context, term: Term, source: &str) {
    let provenance = ctx.finite_set_term_provenance.entry(term).or_default();
    provenance.arbitrary_reason.get_or_insert_with(|| {
        format!(
            "{source} introduced an arbitrary FiniteSet value; AY cannot certify \
             finite support for its characteristic-array backing"
        )
    });
}

/// Record that a term contains a finite-set binder represented by an
/// unrestricted characteristic array. Quantifier polarity means neither SAT
/// nor UNSAT is preserved for a goal that reaches this term.
pub(crate) fn activate_finite_set_quantifier_gate(ctx: &mut Z3Context, term: Term, source: &str) {
    let provenance = ctx.finite_set_term_provenance.entry(term).or_default();
    provenance.quantifier_reason.get_or_insert_with(|| {
        format!(
            "{source} introduced a quantified FiniteSet carrier; AY cannot restrict \
             the binder to finite-support characteristic arrays"
        )
    });
}

/// Attach a finite-set semantic axiom to the public witness it defines.
///
/// Unlike ordinary theory-global axioms, this equation must only enter checks
/// whose goal reaches `owner`; otherwise an unused constructor could affect a
/// sibling solver handle.
pub(crate) fn record_reachable_finite_set_axiom(ctx: &mut Z3Context, owner: Term, axiom: Term) {
    let axioms = ctx.finite_set_reachable_axioms.entry(owner).or_default();
    if !axioms.contains(&axiom) {
        axioms.push(axiom);
    }
    ctx.clear_decision_check_artifacts();
}

fn reachable_finite_set_terms(ctx: &Z3Context, roots: &[Term]) -> HashSet<Term> {
    let mut reachable = HashSet::new();
    let mut pending = roots.to_vec();
    while let Some(term) = pending.pop() {
        if !reachable.insert(term) {
            continue;
        }
        pending.extend(ctx.solver.term_children(term));
        if let Some(application) = ctx.finite_set_apps.get(&term) {
            pending.extend(
                application
                    .args
                    .iter()
                    .filter_map(|&ast| checked_ast_to_term(ctx, ast)),
            );
        }
    }
    reachable
}

/// Compute finite-set decision obligations from exactly the supplied roots.
pub(crate) fn finite_set_decision_gate(ctx: &Z3Context, roots: &[Term]) -> FiniteSetDecisionGate {
    let reachable = reachable_finite_set_terms(ctx, roots);
    let mut gate = FiniteSetDecisionGate::default();
    for term in reachable {
        if ctx.finite_set_apps.contains_key(&term)
            || lookup_ast_sort(ctx, term_to_ast(ctx, term))
                .is_some_and(|sort| sort_mentions_finite_set(ctx, sort))
        {
            gate.uses_finite_set = true;
        }
        if let Some(provenance) = ctx.finite_set_term_provenance.get(&term) {
            gate.uses_finite_set = true;
            if gate.arbitrary_reason.is_none() {
                gate.arbitrary_reason
                    .clone_from(&provenance.arbitrary_reason);
            }
            if gate.quantifier_reason.is_none() {
                gate.quantifier_reason
                    .clone_from(&provenance.quantifier_reason);
            }
        }
    }
    gate
}

/// Return semantic finite-set axioms reachable from exactly `roots`.
pub(crate) fn reachable_finite_set_axioms(ctx: &Z3Context, roots: &[Term]) -> Vec<Term> {
    let mut seen = HashSet::new();
    let mut result = Vec::new();
    for owner in reachable_finite_set_terms(ctx, roots) {
        if let Some(axioms) = ctx.finite_set_reachable_axioms.get(&owner) {
            for &axiom in axioms {
                if seen.insert(axiom) {
                    result.push(axiom);
                }
            }
        }
    }
    result
}

fn public_sort_for_basis(ctx: &mut Z3Context, basis: Sort) -> Sort {
    if let Some(sort) = ctx.finite_set_sorts_by_basis.get(&basis) {
        return sort.clone();
    }
    let identity = format!("!ay.finite-set-sort!{}", ctx.next_ffi_fresh_id);
    ctx.next_ffi_fresh_id += 1;
    let public = Sort::Uninterpreted(identity);
    ctx.finite_set_sorts.insert(public.clone(), basis.clone());
    ctx.finite_set_sorts_by_basis.insert(basis, public.clone());
    public
}

fn invalid_ast(ctx: &mut Z3Context, operation: &str, message: impl Into<String>) -> Z3_ast {
    ctx.last_error = Z3_INVALID_ARG;
    ctx.error_msg = Some(format!("{operation}: {}", message.into()));
    0
}

fn require_sort_handle(ctx: &mut Z3Context, sort: Z3_sort, operation: &str) -> Option<Z3_sort> {
    if sort.is_null() || !ctx.sort_cache.contains(&sort) {
        ctx.last_error = Z3_INVALID_ARG;
        ctx.error_msg = Some(format!(
            "{operation}: null, invalid, or foreign sort handle"
        ));
        None
    } else {
        Some(sort)
    }
}

fn sort_error(ctx: &mut Z3Context, operation: &str, message: impl Into<String>) -> Z3_ast {
    ctx.last_error = Z3_SORT_ERROR;
    ctx.error_msg = Some(format!("{operation}: {}", message.into()));
    0
}

pub(crate) fn public_ast_sort(ctx: &Z3Context, ast: Z3_ast, term: Term) -> Sort {
    lookup_ast_sort(ctx, ast)
        .cloned()
        .unwrap_or_else(|| ctx.solver.sort_of(term))
}

/// The one typed declaration parameter on Z3 5.0.0's polymorphic
/// `set.empty` declaration is its instantiated FiniteSet range sort.
pub(crate) fn finite_set_empty_decl_parameter(
    ctx: &Z3Context,
    decl: &ay_dpll::api::FuncDecl,
) -> Option<Sort> {
    (decl.name() == FiniteSetOp::Empty.name()
        && decl.arity() == 0
        && finite_set_basis(ctx, decl.range()).is_some())
    .then(|| decl.range().clone())
}

fn validate_finite_set(
    ctx: &mut Z3Context,
    operation: &str,
    ast: Z3_ast,
) -> Option<(Term, Sort, Sort)> {
    let Some(term) = checked_ast_to_term(ctx, ast) else {
        invalid_ast(ctx, operation, "null, foreign, or invalid finite-set AST");
        return None;
    };
    let Some(public) = lookup_ast_sort(ctx, ast).cloned() else {
        sort_error(ctx, operation, "expression has no public finite-set sort");
        return None;
    };
    let Some(basis) = finite_set_basis(ctx, &public).cloned() else {
        sort_error(ctx, operation, "expected a FiniteSet expression");
        return None;
    };
    let expected = finite_set_engine_public_sort(ctx, &public);
    let actual = ctx.solver.sort_of(term);
    if actual != expected {
        sort_error(
            ctx,
            operation,
            format!("finite-set backing sort mismatch: got {actual}, expected {expected}"),
        );
        return None;
    }
    Some((term, public, basis))
}

fn record_application(
    ctx: &mut Z3Context,
    backing: Term,
    op: FiniteSetOp,
    args: Vec<Z3_ast>,
    domain: Vec<Sort>,
    range: Sort,
) -> Z3_ast {
    let key = FiniteSetAppKey {
        op,
        args: args.clone(),
        range: range.clone(),
    };
    if let Some(&term) = ctx.finite_set_app_cache.get(&key) {
        return term_to_ast(ctx, term);
    }

    // A distinct witness preserves Z3 application identity even when AY
    // simplifies two different public applications to the same backing term.
    let witness_sort = finite_set_engine_public_sort(ctx, &range);
    let witness = ctx.solver.fresh_var("finite_set_app", witness_sort);
    let definition = ctx.solver.eq(witness, backing);
    record_reachable_finite_set_axiom(ctx, witness, definition);
    ctx.finite_set_apps.insert(
        witness,
        FiniteSetApp {
            op,
            args,
            domain,
            range: range.clone(),
        },
    );
    ctx.finite_set_app_backings.insert(witness, backing);
    ctx.finite_set_app_cache.insert(key, witness);
    let ast = term_to_ast(ctx, witness);
    record_ast_sort(ctx, ast, range);
    ast
}

pub(crate) fn finite_set_app_for_ast(ctx: &Z3Context, ast: Z3_ast) -> Option<&FiniteSetApp> {
    checked_ast_to_term(ctx, ast).and_then(|term| ctx.finite_set_apps.get(&term))
}

pub(crate) fn finite_set_decl_for_ast(ctx: &mut Z3Context, ast: Z3_ast) -> Option<Z3_func_decl> {
    let app = finite_set_app_for_ast(ctx, ast)?.clone();
    let handle = cache_func_decl_with_params(
        ctx,
        ay_dpll::api::FuncDecl::new(app.op.name().to_string(), app.domain, app.range),
        Vec::new(),
    );
    // SAFETY: the cache helper just allocated this handle in `ctx`'s arena,
    // and no alias to it has escaped this function yet.
    unsafe {
        (*handle).finite_set_op = Some(app.op);
    }
    Some(handle)
}

/// Retain exact FiniteSet surface identity for one parsed occurrence.
///
/// A fresh witness is mandatory: a FiniteSet constructor and a legacy
/// Set/Array constructor can hash-cons to the same lowered engine term.
/// Annotating that shared term globally would assign two public sorts to one
/// AST handle. The witness plus its background equality keeps occurrences
/// distinct while preserving the already-elaborated semantics.
pub(crate) fn retain_parsed_finite_set_application(
    ctx: &mut Z3Context,
    backing: Term,
    op: FiniteSetOp,
    args: &[Term],
    domain: Vec<Sort>,
    range: Sort,
) -> Option<Term> {
    let arg_asts = args
        .iter()
        .copied()
        .map(|arg| term_to_ast(ctx, arg))
        .collect();
    let ast = record_application(ctx, backing, op, arg_asts, domain, range);
    checked_ast_to_term(ctx, ast)
}

/// Parsed formula roots after restoring Z3 5.0.0 public FiniteSet identity.
pub(crate) struct RetainedParsedFiniteSetBatch {
    pub(crate) assertions: Vec<Term>,
    pub(crate) soft_constraints: Vec<Term>,
    pub(crate) objectives: Vec<Term>,
}

fn parsed_finite_set_op(op: ay_frontend::FiniteSetOp) -> Result<FiniteSetOp, String> {
    match op {
        ay_frontend::FiniteSetOp::Empty => Ok(FiniteSetOp::Empty),
        ay_frontend::FiniteSetOp::Singleton => Ok(FiniteSetOp::Singleton),
        ay_frontend::FiniteSetOp::Union => Ok(FiniteSetOp::Union),
        ay_frontend::FiniteSetOp::Intersect => Ok(FiniteSetOp::Intersect),
        ay_frontend::FiniteSetOp::Difference => Ok(FiniteSetOp::Difference),
        ay_frontend::FiniteSetOp::In => Ok(FiniteSetOp::Member),
        ay_frontend::FiniteSetOp::Size => Ok(FiniteSetOp::Size),
        ay_frontend::FiniteSetOp::Subset => Ok(FiniteSetOp::Subset),
        ay_frontend::FiniteSetOp::Map => Ok(FiniteSetOp::Map),
        ay_frontend::FiniteSetOp::Filter => Ok(FiniteSetOp::Filter),
        ay_frontend::FiniteSetOp::Range => Ok(FiniteSetOp::Range),
        _ => Err("unsupported future FiniteSet operator in parsed metadata".to_string()),
    }
}

fn parsed_public_sort_for_term(
    ctx: &mut Z3Context,
    sort: &ay_frontend::PublicSort,
    term: Term,
) -> Result<Sort, String> {
    match sort {
        ay_frontend::PublicSort::Unknown => Ok(ctx.solver.term_sort(term)),
        ay_frontend::PublicSort::AmbiguousSet(_) => {
            Err("frontend left a shared set occurrence publicly ambiguous".to_string())
        }
        _ => intern_frontend_public_sort(ctx, sort)
            .ok_or_else(|| format!("cannot intern parsed public sort {sort}")),
    }
}

fn retain_parsed_public_term(
    ctx: &mut Z3Context,
    node: ay_dpll::api::ParsedPublicTermMetadata,
) -> Result<(Term, Sort), String> {
    let original = node.engine_term;
    let public_sort = parsed_public_sort_for_term(ctx, &node.public_sort, original)?;
    let original_argument_terms: Vec<Term> = node
        .arguments
        .iter()
        .map(|argument| argument.engine_term)
        .collect();
    let mut arguments = Vec::with_capacity(node.arguments.len());
    let mut domain = Vec::with_capacity(node.arguments.len());
    for argument in node.arguments {
        let (term, sort) = retain_parsed_public_term(ctx, argument)?;
        arguments.push(term);
        domain.push(sort);
    }

    let retained = if let Some(op) = node.finite_set_op {
        retain_parsed_finite_set_application(
            ctx,
            original,
            parsed_finite_set_op(op)?,
            &arguments,
            domain,
            public_sort.clone(),
        )
        .ok_or_else(|| "could not retain parsed FiniteSet application".to_string())?
    } else if arguments.is_empty() {
        original
    } else {
        let engine_children = ctx.solver.term_children(original);
        if engine_children.len() == arguments.len() {
            ctx.solver
                .try_update_term(original, &arguments)
                .map_err(|error| format!("cannot rebuild parsed public parent: {error}"))?
        } else if arguments.len() == 1 && original == original_argument_terms[0] {
            // An SMT-LIB annotation is semantically transparent.
            arguments[0]
        } else if arguments == original_argument_terms {
            // The elaborator normalized this non-FiniteSet parent but none of
            // its public children changed identity, so the original DAG is
            // still faithful.
            original
        } else {
            return Err(format!(
                "parsed public parent has {} source arguments but {} engine children",
                arguments.len(),
                engine_children.len()
            ));
        }
    };

    let ast = term_to_ast(ctx, retained);
    record_ast_sort(ctx, ast, public_sort.clone());
    if !node.public_bound_sorts.is_empty() {
        let public_bounds = node
            .public_bound_sorts
            .iter()
            .map(|sort| {
                intern_frontend_public_sort(ctx, sort)
                    .ok_or_else(|| format!("cannot intern parsed binder sort {sort}"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        ctx.parsed_quantifier_public_bound_sorts
            .insert(retained, public_bounds);
    }
    Ok((retained, public_sort))
}

fn retain_parsed_formula(
    ctx: &mut Z3Context,
    formula: ay_dpll::api::ParsedSmtlib2Formula,
) -> Result<Term, String> {
    let original_root = formula.term;
    let metadata = formula.metadata;
    let missing_root = metadata.root.is_none();
    let root = match metadata.root {
        Some(root) => retain_parsed_public_term(ctx, root)?.0,
        None => formula.term,
    };
    if metadata.finite_sets.uses_finite_set && missing_root {
        return Err("FiniteSet formula is missing occurrence metadata".to_string());
    }
    if metadata.finite_sets.has_arbitrary_value {
        activate_finite_set_sat_gate(ctx, root, "parsed SMT-LIB");
        if original_root != root {
            activate_finite_set_sat_gate(ctx, original_root, "parsed SMT-LIB");
        }
    }
    if metadata.finite_sets.has_finite_set_binder {
        activate_finite_set_quantifier_gate(ctx, root, "parsed SMT-LIB");
        if original_root != root {
            activate_finite_set_quantifier_gate(ctx, original_root, "parsed SMT-LIB");
        }
    }
    Ok(root)
}

/// Restore public FiniteSet applications, sorts, signatures, and term-local
/// decision provenance for one strict parser transaction.
pub(crate) fn retain_parsed_finite_set_batch(
    ctx: &mut Z3Context,
    batch: ay_dpll::api::ParsedSmtlib2Batch,
) -> Result<RetainedParsedFiniteSetBatch, String> {
    for signature in batch.symbol_signatures {
        if signature.internal_name != signature.name {
            ctx.ffi_decl_symbols.insert(
                signature.internal_name.clone(),
                super::SymbolKey::String(signature.name.clone()),
            );
        }
        let mentions_finite_set = signature.result.contains_finite_set()
            || signature
                .arguments
                .iter()
                .any(ay_frontend::PublicSort::contains_finite_set);
        if !mentions_finite_set {
            continue;
        }
        let domain = signature
            .arguments
            .iter()
            .map(|sort| {
                intern_frontend_public_sort(ctx, sort)
                    .ok_or_else(|| format!("cannot intern parsed declaration sort {sort}"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let range = intern_frontend_public_sort(ctx, &signature.result)
            .ok_or_else(|| format!("cannot intern parsed declaration sort {}", signature.result))?;
        ctx.finite_set_decl_signatures
            .insert(signature.internal_name, (domain, range));
    }

    let assertions = batch
        .assertions
        .into_iter()
        .map(|formula| retain_parsed_formula(ctx, formula))
        .collect::<Result<Vec<_>, _>>()?;
    let soft_constraints = batch
        .soft_constraints
        .into_iter()
        .map(|formula| retain_parsed_formula(ctx, formula))
        .collect::<Result<Vec<_>, _>>()?;
    let objectives = batch
        .objectives
        .into_iter()
        .map(|formula| retain_parsed_formula(ctx, formula))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(RetainedParsedFiniteSetBatch {
        assertions,
        soft_constraints,
        objectives,
    })
}

/// Render a retained application through its exact Z3 5.0.0 public surface.
fn render_finite_set_ast_raw(ctx: &Z3Context, ast: Z3_ast) -> Option<String> {
    let app = finite_set_app_for_ast(ctx, ast)?.clone();
    let args = app
        .args
        .iter()
        .map(|&arg| {
            render_finite_set_ast_raw(ctx, arg).or_else(|| {
                let term = checked_ast_to_term(ctx, arg)?;
                ctx.solver
                    .format_term_checked(term)
                    .map(|text| ffi_surface_text_base(ctx, &text))
            })
        })
        .collect::<Option<Vec<_>>>()?;
    if app.op == FiniteSetOp::Empty {
        let sort = finite_set_sort_text(ctx, &app.range)?;
        Some(format!("(as set.empty {sort})"))
    } else {
        Some(format!("({} {})", app.op.name(), args.join(" ")))
    }
}

/// Token substitutions that project retained FiniteSet witnesses even when
/// they occur below a generic AST such as `ite`, `=`, or an Array term.
pub(crate) fn finite_set_surface_replacements(ctx: &Z3Context) -> HashMap<String, String> {
    let mut replacements = HashMap::new();
    for &term in ctx.finite_set_apps.keys() {
        let ast = term_to_ast(ctx, term);
        let Some(internal) = ctx.solver.format_term_checked(term) else {
            continue;
        };
        let Some(public) = render_finite_set_ast_raw(ctx, ast) else {
            continue;
        };
        replacements.insert(internal, public);
    }

    // A generic argument of one retained application may itself contain a
    // retained witness. Resolve those dependencies to a fixed point.
    for _ in 0..replacements.len() {
        let previous = replacements.clone();
        let mut changed = false;
        for value in replacements.values_mut() {
            let projected = apply_surface_replacements(value, &previous);
            changed |= projected != *value;
            *value = projected;
        }
        if !changed {
            break;
        }
    }
    replacements
}

/// Render a retained application through its exact Z3 5.0.0 public surface.
pub(crate) fn render_finite_set_ast(ctx: &Z3Context, ast: Z3_ast) -> Option<String> {
    let raw = render_finite_set_ast_raw(ctx, ast)?;
    Some(apply_surface_replacements(
        &raw,
        &finite_set_surface_replacements(ctx),
    ))
}

/// Create `(FiniteSet elem_sort)`.
///
/// # Safety
/// `c` and `elem_sort` follow the Z3 C API contracts.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_finite_set_sort(c: Z3_context, elem_sort: Z3_sort) -> Z3_sort {
    // SAFETY: the guard authenticates the context; require_sort_handle
    // authenticates the sort before it is dereferenced.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(elem_sort) = require_sort_handle(ctx, elem_sort, "Z3_mk_finite_set_sort")
            else {
                return ptr::null_mut();
            };
            let basis = (*elem_sort).sort.clone();
            if has_unsupported_finite_set_datatype_embedding(ctx, &basis) {
                ctx.last_error = Z3_SORT_ERROR;
                ctx.error_msg = Some(
                    "Z3_mk_finite_set_sort: a datatype containing FiniteSet fields cannot be \
                     lowered without changing the datatype identity"
                        .to_string(),
                );
                return ptr::null_mut();
            }
            let public = public_sort_for_basis(ctx, basis);
            alloc_sort(ctx, public)
        })
    }
}

/// True iff `s` is a Z3 5.0.0 finite-set sort.
///
/// # Safety
/// `c` and `s` follow the Z3 C API contracts.
#[no_mangle]
pub unsafe extern "C" fn Z3_is_finite_set_sort(c: Z3_context, s: Z3_sort) -> bool {
    // SAFETY: the guard and sort authenticator validate both handles.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let Some(s) = require_sort_handle(ctx, s, "Z3_is_finite_set_sort") else {
                return 0;
            };
            i32::from(finite_set_basis(ctx, &(*s).sort).is_some())
        }) != 0
    }
}

/// Return the element sort of a finite-set sort.
///
/// # Safety
/// `c` and `s` follow the Z3 C API contracts.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_finite_set_sort_basis(c: Z3_context, s: Z3_sort) -> Z3_sort {
    // SAFETY: the guard and sort authenticator validate both handles.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(s) = require_sort_handle(ctx, s, "Z3_get_finite_set_sort_basis") else {
                return ptr::null_mut();
            };
            let Some(basis) = finite_set_basis(ctx, &(*s).sort).cloned() else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_get_finite_set_sort_basis: expected FiniteSet sort".to_string());
                return ptr::null_mut();
            };
            alloc_sort(ctx, basis)
        })
    }
}

/// Empty finite set.
///
/// # Safety
/// Standard Z3 context/sort contract.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_finite_set_empty(c: Z3_context, set_sort: Z3_sort) -> Z3_ast {
    // SAFETY: guarded and sort-authenticated before dereference.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let Some(set_sort) = require_sort_handle(ctx, set_sort, "Z3_mk_finite_set_empty")
            else {
                return 0;
            };
            let public = (*set_sort).sort.clone();
            let Some(basis) = finite_set_basis(ctx, &public).cloned() else {
                return sort_error(ctx, "Z3_mk_finite_set_empty", "expected FiniteSet sort");
            };
            let engine_basis = finite_set_engine_public_sort(ctx, &basis);
            let ff = ctx.solver.bool_const(false);
            let backing = ctx.solver.const_array(engine_basis, ff);
            record_application(
                ctx,
                backing,
                FiniteSetOp::Empty,
                Vec::new(),
                Vec::new(),
                public,
            )
        })
    }
}

/// Singleton finite set.
///
/// # Safety
/// Standard Z3 context/AST contract.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_finite_set_singleton(c: Z3_context, elem: Z3_ast) -> Z3_ast {
    // SAFETY: the guard authenticates the context and the AST is checked before use.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let Some(elem_term) = checked_ast_to_term(ctx, elem) else {
                return invalid_ast(ctx, "Z3_mk_finite_set_singleton", "invalid element AST");
            };
            let basis = public_ast_sort(ctx, elem, elem_term);
            let engine_basis = finite_set_engine_public_sort(ctx, &basis);
            if ctx.solver.sort_of(elem_term) != engine_basis {
                return sort_error(
                    ctx,
                    "Z3_mk_finite_set_singleton",
                    "element engine sort does not match its public sort",
                );
            }
            let public = public_sort_for_basis(ctx, basis.clone());
            let ff = ctx.solver.bool_const(false);
            let tt = ctx.solver.bool_const(true);
            let empty = ctx.solver.const_array(engine_basis, ff);
            let backing = ctx.solver.store(empty, elem_term, tt);
            record_application(
                ctx,
                backing,
                FiniteSetOp::Singleton,
                vec![elem],
                vec![basis],
                public,
            )
        })
    }
}

fn finite_set_binary(
    ctx: &mut Z3Context,
    operation: &str,
    left_ast: Z3_ast,
    right_ast: Z3_ast,
    op: FiniteSetOp,
) -> Z3_ast {
    let Some((left, public, basis)) = validate_finite_set(ctx, operation, left_ast) else {
        return 0;
    };
    let Some((right, right_public, right_basis)) = validate_finite_set(ctx, operation, right_ast)
    else {
        return 0;
    };
    if public != right_public || basis != right_basis {
        return sort_error(ctx, operation, "finite-set sorts differ");
    }
    let backing_sort = finite_set_engine_public_sort(ctx, &public);
    let backing = match op {
        FiniteSetOp::Union => ctx.solver.array_map("or", &[left, right], backing_sort),
        FiniteSetOp::Intersect => ctx.solver.array_map("and", &[left, right], backing_sort),
        FiniteSetOp::Difference
            if finite_set_app_for_ast(ctx, right_ast)
                .is_some_and(|app| app.op == FiniteSetOp::Empty) =>
        {
            left
        }
        FiniteSetOp::Difference => {
            let not_right = ctx.solver.array_map("not", &[right], backing_sort.clone());
            ctx.solver
                .array_map("and", &[left, not_right], backing_sort)
        }
        _ => return invalid_ast(ctx, operation, "invalid internal binary operator"),
    };
    record_application(
        ctx,
        backing,
        op,
        vec![left_ast, right_ast],
        vec![public.clone(), public.clone()],
        public,
    )
}

/// Binary finite-set union.
///
/// # Safety
/// Standard Z3 context/AST contract.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_finite_set_union(c: Z3_context, s1: Z3_ast, s2: Z3_ast) -> Z3_ast {
    // SAFETY: the helper validates every AST and sort.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            finite_set_binary(ctx, "Z3_mk_finite_set_union", s1, s2, FiniteSetOp::Union)
        })
    }
}

/// Binary finite-set intersection.
///
/// # Safety
/// Standard Z3 context/AST contract.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_finite_set_intersect(
    c: Z3_context,
    s1: Z3_ast,
    s2: Z3_ast,
) -> Z3_ast {
    // SAFETY: the helper validates every AST and sort.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            finite_set_binary(
                ctx,
                "Z3_mk_finite_set_intersect",
                s1,
                s2,
                FiniteSetOp::Intersect,
            )
        })
    }
}

/// Binary finite-set difference.
///
/// # Safety
/// Standard Z3 context/AST contract.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_finite_set_difference(
    c: Z3_context,
    s1: Z3_ast,
    s2: Z3_ast,
) -> Z3_ast {
    // SAFETY: the helper validates every AST and sort.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            finite_set_binary(
                ctx,
                "Z3_mk_finite_set_difference",
                s1,
                s2,
                FiniteSetOp::Difference,
            )
        })
    }
}

/// Finite-set membership.
///
/// # Safety
/// Standard Z3 context/AST contract.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_finite_set_member(
    c: Z3_context,
    elem: Z3_ast,
    set: Z3_ast,
) -> Z3_ast {
    // SAFETY: guarded; every AST is authenticated before use.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let Some(elem_term) = checked_ast_to_term(ctx, elem) else {
                return invalid_ast(ctx, "Z3_mk_finite_set_member", "invalid element AST");
            };
            let Some((set_term, set_sort, basis)) =
                validate_finite_set(ctx, "Z3_mk_finite_set_member", set)
            else {
                return 0;
            };
            if public_ast_sort(ctx, elem, elem_term) != basis {
                return sort_error(
                    ctx,
                    "Z3_mk_finite_set_member",
                    "element sort differs from set basis",
                );
            }
            let backing = ctx.solver.select(set_term, elem_term);
            record_application(
                ctx,
                backing,
                FiniteSetOp::Member,
                vec![elem, set],
                vec![basis, set_sort],
                Sort::Bool,
            )
        })
    }
}

/// Finite-set subset.
///
/// # Safety
/// Standard Z3 context/AST contract.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_finite_set_subset(c: Z3_context, s1: Z3_ast, s2: Z3_ast) -> Z3_ast {
    // SAFETY: guarded; every AST is authenticated before use.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let Some((left, public, basis)) =
                validate_finite_set(ctx, "Z3_mk_finite_set_subset", s1)
            else {
                return 0;
            };
            let Some((right, right_public, right_basis)) =
                validate_finite_set(ctx, "Z3_mk_finite_set_subset", s2)
            else {
                return 0;
            };
            if public != right_public || basis != right_basis {
                return sort_error(ctx, "Z3_mk_finite_set_subset", "finite-set sorts differ");
            }
            let left_app = finite_set_app_for_ast(ctx, s1).cloned();
            let right_app = finite_set_app_for_ast(ctx, s2).cloned();
            let known = if s1 == s2
                || left_app
                    .as_ref()
                    .is_some_and(|app| app.op == FiniteSetOp::Empty)
                || right_app
                    .as_ref()
                    .is_some_and(|app| app.op == FiniteSetOp::Union && app.args.contains(&s1))
            {
                Some(true)
            } else if left_app
                .as_ref()
                .is_some_and(|app| app.op == FiniteSetOp::Singleton)
                && right_app
                    .as_ref()
                    .is_some_and(|app| app.op == FiniteSetOp::Empty)
            {
                Some(false)
            } else {
                None
            };
            let has_finite_set_binder = known.is_none() && sort_mentions_finite_set(ctx, &basis);
            let backing = if let Some(value) = known {
                ctx.solver.bool_const(value)
            } else {
                let engine_basis = finite_set_engine_public_sort(ctx, &basis);
                let x = ctx.solver.fresh_var("finite_set_subset_x", engine_basis);
                let in_left = ctx.solver.select(left, x);
                let in_right = ctx.solver.select(right, x);
                let body = ctx.solver.implies(in_left, in_right);
                match ctx.solver.try_forall(&[x], body) {
                    Ok(backing) => backing,
                    Err(error) => {
                        return invalid_ast(
                            ctx,
                            "Z3_mk_finite_set_subset",
                            format!("cannot construct exact subset quantifier: {error}"),
                        );
                    }
                }
            };
            let result = record_application(
                ctx,
                backing,
                FiniteSetOp::Subset,
                vec![s1, s2],
                vec![public.clone(), public],
                Sort::Bool,
            );
            if has_finite_set_binder {
                if let Some(term) = checked_ast_to_term(ctx, result) {
                    activate_finite_set_quantifier_gate(ctx, term, "Z3_mk_finite_set_subset");
                }
            }
            result
        })
    }
}

/// Cardinality of a finite set.
///
/// AY creates an Int witness constrained by the real `set.has_size` predicate.
/// The executor decides small finite bases and returns UNKNOWN for unsupported
/// infinite-domain cardinality instead of treating it as uninterpreted.
///
/// # Safety
/// Standard Z3 context/AST contract.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_finite_set_size(c: Z3_context, set: Z3_ast) -> Z3_ast {
    // SAFETY: guarded; the set AST is authenticated before use.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let Some((set_term, set_sort, _basis)) =
                validate_finite_set(ctx, "Z3_mk_finite_set_size", set)
            else {
                return 0;
            };
            let known_app = finite_set_app_for_ast(ctx, set).cloned();
            let (size, cardinality_axiom) = match known_app {
                Some(FiniteSetApp {
                    op: FiniteSetOp::Empty,
                    ..
                }) => (ctx.solver.int_const(0), None),
                Some(FiniteSetApp {
                    op: FiniteSetOp::Singleton,
                    ..
                }) => (ctx.solver.int_const(1), None),
                Some(FiniteSetApp {
                    op: FiniteSetOp::Range,
                    args,
                    ..
                }) => {
                    let Some(low) = checked_ast_to_term(ctx, args[0]) else {
                        return invalid_ast(
                            ctx,
                            "Z3_mk_finite_set_size",
                            "invalid range lower bound",
                        );
                    };
                    let Some(high) = checked_ast_to_term(ctx, args[1]) else {
                        return invalid_ast(
                            ctx,
                            "Z3_mk_finite_set_size",
                            "invalid range upper bound",
                        );
                    };
                    let zero = ctx.solver.int_const(0);
                    let one = ctx.solver.int_const(1);
                    let ordered = ctx.solver.le(low, high);
                    let span = ctx.solver.sub(high, low);
                    let inclusive_span = ctx.solver.add(span, one);
                    (ctx.solver.ite(ordered, inclusive_span, zero), None)
                }
                _ => {
                    let size = ctx.solver.fresh_var("finite_set_size", Sort::Int);
                    let cardinality = ctx.solver.set_has_size(set_term, size);
                    let zero = ctx.solver.int_const(0);
                    let nonnegative = ctx.solver.le(zero, size);
                    let definition = ctx.solver.and(cardinality, nonnegative);
                    (size, Some(definition))
                }
            };
            let result = record_application(
                ctx,
                size,
                FiniteSetOp::Size,
                vec![set],
                vec![set_sort],
                Sort::Int,
            );
            if let (Some(owner), Some(axiom)) =
                (checked_ast_to_term(ctx, result), cardinality_axiom)
            {
                record_reachable_finite_set_axiom(ctx, owner, axiom);
            }
            result
        })
    }
}

fn array_public_signature(
    ctx: &mut Z3Context,
    operation: &str,
    ast: Z3_ast,
) -> Option<(Term, Sort, Sort)> {
    let Some(term) = checked_ast_to_term(ctx, ast) else {
        invalid_ast(ctx, operation, "invalid array AST");
        return None;
    };
    let public = public_ast_sort(ctx, ast, term);
    let Sort::Array(array) = public else {
        sort_error(ctx, operation, "expected an array/function argument");
        return None;
    };
    Some((term, array.index_sort, array.element_sort))
}

/// Apply an array-encoded function to every element of a finite set.
///
/// The exact characteristic function is
/// `lambda y. exists x. set[x] && f[x] = y`.
///
/// # Safety
/// Standard Z3 context/AST contract.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_finite_set_map(c: Z3_context, f: Z3_ast, set: Z3_ast) -> Z3_ast {
    // SAFETY: guarded; every AST and sort is validated before construction.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let Some((f_term, domain, image)) =
                array_public_signature(ctx, "Z3_mk_finite_set_map", f)
            else {
                return 0;
            };
            let Some((set_term, set_sort, basis)) =
                validate_finite_set(ctx, "Z3_mk_finite_set_map", set)
            else {
                return 0;
            };
            if domain != basis {
                return sort_error(
                    ctx,
                    "Z3_mk_finite_set_map",
                    "function domain differs from set basis",
                );
            }
            let has_finite_set_binder =
                sort_mentions_finite_set(ctx, &domain) || sort_mentions_finite_set(ctx, &image);
            let engine_domain = finite_set_engine_public_sort(ctx, &domain);
            let engine_image = finite_set_engine_public_sort(ctx, &image);
            let known_source = finite_set_app_for_ast(ctx, set).cloned();
            let backing = match known_source {
                Some(FiniteSetApp {
                    op: FiniteSetOp::Empty,
                    ..
                }) => {
                    let ff = ctx.solver.bool_const(false);
                    ctx.solver.const_array(engine_image.clone(), ff)
                }
                Some(FiniteSetApp {
                    op: FiniteSetOp::Singleton,
                    args,
                    ..
                }) => {
                    let Some(element) = checked_ast_to_term(ctx, args[0]) else {
                        return invalid_ast(
                            ctx,
                            "Z3_mk_finite_set_map",
                            "invalid singleton source element",
                        );
                    };
                    let mapped_element = ctx.solver.select(f_term, element);
                    let ff = ctx.solver.bool_const(false);
                    let tt = ctx.solver.bool_const(true);
                    let empty = ctx.solver.const_array(engine_image.clone(), ff);
                    ctx.solver.store(empty, mapped_element, tt)
                }
                _ => {
                    let x = ctx.solver.fresh_var("finite_set_map_x", engine_domain);
                    let y = ctx
                        .solver
                        .fresh_var("finite_set_map_image", engine_image.clone());
                    let in_source = ctx.solver.select(set_term, x);
                    let fx = ctx.solver.select(f_term, x);
                    let same_image = ctx.solver.eq(fx, y);
                    let preimage = ctx.solver.and(in_source, same_image);
                    let exists = match ctx.solver.try_exists(&[x], preimage) {
                        Ok(exists) => exists,
                        Err(error) => {
                            return invalid_ast(
                                ctx,
                                "Z3_mk_finite_set_map",
                                format!("cannot construct exact image quantifier: {error}"),
                            );
                        }
                    };
                    ctx.solver.lambda_array(y, exists)
                }
            };
            let function_sort = Sort::array(domain.clone(), image.clone());
            let output = public_sort_for_basis(ctx, image);
            let result = record_application(
                ctx,
                backing,
                FiniteSetOp::Map,
                vec![f, set],
                vec![function_sort, set_sort],
                output,
            );
            if has_finite_set_binder {
                if let Some(term) = checked_ast_to_term(ctx, result) {
                    activate_finite_set_quantifier_gate(ctx, term, "Z3_mk_finite_set_map");
                }
            }
            result
        })
    }
}

/// Filter a finite set by an array-encoded predicate.
///
/// The exact characteristic function is `lambda x. set[x] && predicate[x]`.
///
/// # Safety
/// Standard Z3 context/AST contract.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_finite_set_filter(
    c: Z3_context,
    predicate: Z3_ast,
    set: Z3_ast,
) -> Z3_ast {
    // SAFETY: guarded; every AST and sort is validated before construction.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let Some((predicate_term, domain, range)) =
                array_public_signature(ctx, "Z3_mk_finite_set_filter", predicate)
            else {
                return 0;
            };
            if range != Sort::Bool {
                return sort_error(
                    ctx,
                    "Z3_mk_finite_set_filter",
                    "predicate range must be Bool",
                );
            }
            let Some((set_term, set_sort, basis)) =
                validate_finite_set(ctx, "Z3_mk_finite_set_filter", set)
            else {
                return 0;
            };
            if domain != basis {
                return sort_error(
                    ctx,
                    "Z3_mk_finite_set_filter",
                    "predicate domain differs from set basis",
                );
            }
            let has_finite_set_binder = sort_mentions_finite_set(ctx, &basis);
            let engine_basis = finite_set_engine_public_sort(ctx, &basis);
            let x = ctx.solver.fresh_var("finite_set_filter_x", engine_basis);
            let in_source = ctx.solver.select(set_term, x);
            let accepted = ctx.solver.select(predicate_term, x);
            let body = ctx.solver.and(in_source, accepted);
            let backing = ctx.solver.lambda_array(x, body);
            let result = record_application(
                ctx,
                backing,
                FiniteSetOp::Filter,
                vec![predicate, set],
                vec![Sort::array(domain, Sort::Bool), set_sort.clone()],
                set_sort,
            );
            if has_finite_set_binder {
                if let Some(term) = checked_ast_to_term(ctx, result) {
                    activate_finite_set_quantifier_gate(ctx, term, "Z3_mk_finite_set_filter");
                }
            }
            result
        })
    }
}

/// Inclusive integer range `[low, high]`.
///
/// This follows the Z3 5.0.0 implementation (and installed C header), including
/// the singleton result when `low == high` and empty result when `low > high`.
///
/// # Safety
/// Standard Z3 context/AST contract.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_finite_set_range(
    c: Z3_context,
    low: Z3_ast,
    high: Z3_ast,
) -> Z3_ast {
    // SAFETY: guarded; both ASTs and their sorts are validated.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let Some(low_term) = checked_ast_to_term(ctx, low) else {
                return invalid_ast(ctx, "Z3_mk_finite_set_range", "invalid low endpoint");
            };
            let Some(high_term) = checked_ast_to_term(ctx, high) else {
                return invalid_ast(ctx, "Z3_mk_finite_set_range", "invalid high endpoint");
            };
            if public_ast_sort(ctx, low, low_term) != Sort::Int
                || public_ast_sort(ctx, high, high_term) != Sort::Int
            {
                return sort_error(ctx, "Z3_mk_finite_set_range", "both endpoints must be Int");
            }
            let x = ctx.solver.fresh_var("finite_set_range_x", Sort::Int);
            let lower = ctx.solver.le(low_term, x);
            let upper = ctx.solver.le(x, high_term);
            let body = ctx.solver.and(lower, upper);
            let backing = ctx.solver.lambda_array(x, body);
            let output = public_sort_for_basis(ctx, Sort::Int);
            record_application(
                ctx,
                backing,
                FiniteSetOp::Range,
                vec![low, high],
                vec![Sort::Int, Sort::Int],
                output,
            )
        })
    }
}

// Z3 5.0.0 exposes finite-set sorts through the UNKNOWN sort-kind sentinel.
pub(crate) const FINITE_SET_SORT_KIND: c_uint = Z3_UNKNOWN_SORT;
