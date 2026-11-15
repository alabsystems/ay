// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Function symbols a proof APPLIES, and sort symbols it spells, that no
//! checker can resolve.
//!
//! The exporter's undeclared-symbol obligation ("every symbol free in the
//! document is declared by the problem, defined by the preamble, or bound")
//! was enforced by `collect_auxiliary_proof_declarations`, which walks `Var`
//! nodes only. An application HEAD is invisible to it: `default` in
//! `(default a)` is a `TermData::App` symbol, not a variable. MEASURED on a
//! four-line QF_AUFBV refutation (`= c (store ((as const ..) false) 1 true)`
//! against `= c ((as const ..) true)`): the array-default axioms reached the
//! proof as `hole` steps over `(default (store ...))`, the document was
//! written, the certificate line said `carcara_surface=supported`, and pinned
//! Carcara answered `invalid` with
//! `parser error: identifier 'default' is not defined` before checking a
//! rule. No `hole` repairs an unparseable document, so it is the same class
//! as an undeclarable Skolem constant, and it gets the same decline
//! (`AlethePrintError::UndeclarableProofSymbols`).
//!
//! A head resolves for pinned Carcara when it is
//!
//! * an operator of its grammar (`alethe_parser::BUILTIN_OPERATORS`, or
//!   `BUILTIN_INDEXED` for an `(_ name idx..)` head);
//! * applied by the problem's own assertions under a name source text can
//!   declare, i.e. not one of AY's own identities ([`is_internal_identity`]):
//!   the internal namespaces (`__ay_`, `!ay.`, `map[...]`) and a parametric
//!   instance's members (`member@D!{T..}`). The frontend's `__ay_overload_N`
//!   member of an overloaded or re-declared datatype, and `val@Opt!{Int}`,
//!   stand in the assertions for names the problem spells differently;
//! * a constructor or selector of a datatype the problem declares, read from
//!   the sorts involved or the term store's constructor registry, unless it
//!   is such an identity; or
//! * an internal spelling the printer re-spells on the way out:
//!   `const-array` as `((as const S) v)`, `is-C` as `((_ is C) t)`, and the
//!   clause constructor `cl`; or
//! * a function symbol of the SMT-LIB FloatingPoint theory
//!   ([`FLOATING_POINT_THEORY_OPERATORS`], and
//!   [`FLOATING_POINT_THEORY_INDEXED`] for `(_ +zero 11 53)` and the
//!   conversions) in a proof that has a FloatingPoint-sorted term. The theory
//!   declares these symbols, so they are not free in the document: a checker
//!   of the theory resolves them, as AY's strict checker does. Pinned Carcara
//!   has no FloatingPoint theory, so such a document is not one it can parse,
//!   and [`crate::carcara_proof_surface`] already discloses every proof with
//!   a FloatingPoint-sorted term as `unsupported`. Accepting the theory's
//!   heads only in such a proof is what keeps this rule from putting
//!   `supported` beside a document pinned Carcara cannot parse: a
//!   rounding-mode constant has the uninterpreted `RoundingMode` sort, which
//!   that verdict does not flag, so in a proof with no FloatingPoint-sorted
//!   term it is still a candidate. MEASURED before this rule: the refutation
//!   of `(forall ((q (_ FloatingPoint 11 53))) (fp.isNaN q))` instantiates
//!   the quantifier at `(_ +zero 11 53)`. The export declined it as "free in
//!   1 symbol(s) … (+zero)", so the strict-accepted document that owner
//!   decision D7 has AY publish (disclosed `carcara_surface=unsupported`)
//!   was lost, and Trust's `FP` row went from `Proved` to `Unknown`.
//!
//! A nullary parametric member (`nil@List!{Int}`) is a `Var`, which the
//! problem's assertions can mention and the variable walk therefore accepts;
//! it is collected here too.
//!
//! SORT identities are the same defect one level up: the printer writes a
//! datatype or uninterpreted sort by its name (`format_sort_alethe`), so a
//! binder over a parametric instance ships `|Opt!{Int}|` and one over a sort
//! declared again after a `pop` ships `__ay_datatype_sort_0`. MEASURED: an
//! inline Skolem `(choice ((x |Opt!{Int}|)) (not (P x)))` in a `forall_inst`
//! step, disclosed `carcara_surface=supported`, and pinned Carcara answered
//! `invalid` (`sort 'Opt!{Int}' is not defined`); likewise
//! `sort '__ay_datatype_sort_0' is not defined`. Every such identity a proof
//! term's sort (or a quantifier binder) carries is a candidate as well.
//!
//! Everything else is a CANDIDATE, and [`decline_if_shipped`] refuses a step
//! whose shipped bytes spell one. Deciding on the bytes keeps the guard exact
//! about what reaches the document: a candidate every occurrence of which a
//! rendering channel re-spells (an authored surface, a Skolem `choice`) never
//! ships and refuses nothing.

use crate::alethe_parser::{BUILTIN_INDEXED, BUILTIN_OPERATORS};
use crate::alethe_printer::first_symbol_token_in;
use crate::AlethePrintError;
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{Proof, Sort, Symbol, TermData, TermId, TermStore};

/// Whether `name` lies in one of AY's internal namespaces, which SMT-LIB
/// source text can never declare.
///
/// The same shapes as `ay_frontend::INTERNAL_NAMESPACES` (a dev-dependency
/// only, so this crate restates them; `application_heads_tests.rs` pins the
/// two together).
pub(crate) fn is_internal_namespace_name(name: &str) -> bool {
    name.starts_with("__ay_")
        || name.starts_with("!ay.")
        || (name.len() >= "map[]".len() && name.starts_with("map[") && name.ends_with(']'))
}

/// Whether `name` is the frontend's identity for a member of a parametric
/// datatype INSTANCE: `member@D!{T..}` (`ay_frontend` `mangle_member` over
/// `mangle_datatype_instance`). The problem file spells it `member` (or
/// `(as member (D T))`); no source text declares the mangled identity, so a
/// step that prints it raw is unparseable. MEASURED: `(= x (some a))`,
/// `(= x (some b))`, `(not (= a b))` over `(Opt Int)` printed
/// `(|val@Opt!{Int}| x)` in a `hole` step, disclosed
/// `carcara_surface=supported`, and pinned Carcara answered `invalid`
/// (`identifier 'val@Opt!{Int}' is not defined`).
fn is_parametric_instance_member(name: &str) -> bool {
    name.split_once('@')
        .is_some_and(|(_, instance)| instance.contains("!{"))
}

/// The SMT-LIB FloatingPoint theory's plain function symbols, spelled as
/// AY's terms carry them: the frontend elaborates the long rounding-mode
/// names to the short ones, and the long ones are the theory's too. The
/// z3 extension `fp.to_ieee_bv` is not the theory's, so it is not listed.
const FLOATING_POINT_THEORY_OPERATORS: &[&str] = &[
    "fp",
    "fp.abs",
    "fp.neg",
    "fp.add",
    "fp.sub",
    "fp.mul",
    "fp.div",
    "fp.fma",
    "fp.sqrt",
    "fp.rem",
    "fp.roundToIntegral",
    "fp.min",
    "fp.max",
    "fp.leq",
    "fp.lt",
    "fp.geq",
    "fp.gt",
    "fp.eq",
    "fp.isNormal",
    "fp.isSubnormal",
    "fp.isZero",
    "fp.isInfinite",
    "fp.isNaN",
    "fp.isNegative",
    "fp.isPositive",
    "fp.to_real",
    "RNE",
    "RNA",
    "RTP",
    "RTN",
    "RTZ",
    "roundNearestTiesToEven",
    "roundNearestTiesToAway",
    "roundTowardPositive",
    "roundTowardNegative",
    "roundTowardZero",
];

/// The SMT-LIB FloatingPoint theory's indexed heads: the five constants
/// `(_ +zero eb sb)`, `(_ -zero eb sb)`, `(_ +oo eb sb)`, `(_ -oo eb sb)` and
/// `(_ NaN eb sb)`, and the conversions.
const FLOATING_POINT_THEORY_INDEXED: &[&str] = &[
    "+zero",
    "-zero",
    "+oo",
    "-oo",
    "NaN",
    "to_fp",
    "to_fp_unsigned",
    "fp.to_ubv",
    "fp.to_sbv",
];

/// Whether `symbol` is a function symbol of the SMT-LIB FloatingPoint theory.
fn is_floating_point_theory_head(symbol: &Symbol) -> bool {
    match symbol {
        Symbol::Named(name) => FLOATING_POINT_THEORY_OPERATORS.contains(&&**name),
        Symbol::Indexed(name, _) => FLOATING_POINT_THEORY_INDEXED.contains(&&**name),
        _ => false,
    }
}

/// Whether `sort` is, or is built from, a FloatingPoint sort through arrays
/// or sequences. `carcara_sort_gap` (`alethe_printer.rs`) flags every such
/// sort as outside pinned Carcara's grammar; it flags more (a datatype field,
/// `Seq` and `Char` themselves), so this is the narrower test.
fn spells_floating_point(sort: &Sort) -> bool {
    match sort {
        Sort::FloatingPoint(..) => true,
        Sort::Array(array) => {
            spells_floating_point(&array.index_sort) || spells_floating_point(&array.element_sort)
        }
        Sort::Seq(element) => spells_floating_point(element),
        _ => false,
    }
}

/// An identity of AY's own that no problem file declares, whatever the
/// problem's assertions apply.
fn is_internal_identity(name: &str) -> bool {
    is_internal_namespace_name(name) || is_parametric_instance_member(name)
}

/// Whether a sort NAME is one of AY's own identities: an internal namespace
/// (`__ay_datatype_sort_N` for a sort declared again after a `pop`) or a
/// parametric instance's carrier (`D!{T..}`, `mangle_datatype_instance`).
/// The problem file spells the first by its surface name and the second as
/// `(D T..)`; neither identity is declared by any source text.
fn is_internal_sort_identity(name: &str) -> bool {
    is_internal_namespace_name(name) || name.contains("!{")
}

/// Every internal sort identity `sort` spells when printed: a datatype or
/// uninterpreted sort by its name, an array or sequence through its operands
/// (`format_sort_alethe`). Datatype field sorts are never printed.
fn collect_internal_sort_identities(sort: &Sort, out: &mut HashSet<String>) {
    match sort {
        Sort::Datatype(datatype) if is_internal_sort_identity(&datatype.name) => {
            out.insert(datatype.name.clone());
        }
        Sort::Uninterpreted(name) | Sort::FiniteDomain(name, _) | Sort::TypeVar(name)
            if is_internal_sort_identity(name) =>
        {
            out.insert(name.clone());
        }
        Sort::Array(array) => {
            collect_internal_sort_identities(&array.index_sort, out);
            collect_internal_sort_identities(&array.element_sort, out);
        }
        Sort::Seq(element) => collect_internal_sort_identities(element, out),
        _ => {}
    }
}

/// Every symbol some term of `proof` applies, or some sort of it spells, that
/// pinned Carcara cannot resolve against `problem_assertions` (see the module
/// doc).
///
/// Empty for the overwhelming majority of proofs, in which case the exporter
/// scans no bytes at all.
pub(crate) fn unresolvable_proof_symbols(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
) -> HashSet<String> {
    let mut pending: HashSet<String> = HashSet::default();
    let mut sorts: HashSet<String> = HashSet::default();
    // FloatingPoint theory heads wait until the walk knows whether the proof
    // has a FloatingPoint-sorted term (see the module doc).
    let mut floating_point_heads: HashSet<String> = HashSet::default();
    let mut floating_point_sorted = false;
    let mut visited: HashSet<TermId> = HashSet::default();
    let mut stack = crate::variables::collect_proof_term_roots(proof);
    while let Some(term) = stack.pop() {
        if term.index() >= terms.len() || !visited.insert(term) {
            continue;
        }
        // A bound variable's sort is printed in its binder, and an inline
        // Skolem `choice` binds the witness's own sort.
        collect_internal_sort_identities(terms.sort(term), &mut sorts);
        floating_point_sorted |= spells_floating_point(terms.sort(term));
        match terms.get(term) {
            TermData::App(symbol, args) => {
                if let Some(name) = printed_unresolved_head(terms, term, symbol, args) {
                    if is_floating_point_theory_head(symbol) {
                        floating_point_heads.insert(name);
                    } else {
                        pending.insert(name);
                    }
                }
            }
            // A nullary member of a parametric instance is a `Var`
            // (`nil@List!{Int}`); the problem's own assertions can mention it,
            // so the declaration walk accepts it, and it prints raw.
            TermData::Var(name, _) if is_parametric_instance_member(name) => {
                pending.insert(name.to_string());
            }
            TermData::Forall(binders, ..) | TermData::Exists(binders, ..) => {
                for (_, sort) in binders {
                    collect_internal_sort_identities(sort, &mut sorts);
                    floating_point_sorted |= spells_floating_point(sort);
                }
            }
            _ => {}
        }
        stack.extend(terms.children(term));
    }
    if !floating_point_sorted {
        pending.extend(floating_point_heads);
    }
    if !pending.is_empty() {
        let declared =
            crate::variables::application_symbol_names(terms, problem_assertions.iter().copied());
        pending.retain(|name| is_internal_identity(name) || !declared.contains(name));
    }
    pending.extend(sorts);
    pending
}

/// The identifier `term`'s head puts on the wire when no operator, datatype
/// declaration or printer re-spelling resolves it; `None` otherwise.
fn printed_unresolved_head(
    terms: &TermStore,
    term: TermId,
    symbol: &Symbol,
    args: &[TermId],
) -> Option<String> {
    let (name, indexed) = match symbol {
        Symbol::Named(name) => (&**name, false),
        Symbol::Indexed(name, _) => (&**name, true),
        // `Symbol` is `#[non_exhaustive]`; the printer has no spelling for
        // another kind and refuses it on its own.
        _ => return None,
    };
    if indexed {
        return (!BUILTIN_INDEXED.contains(&name)).then(|| name.to_string());
    }
    // The printer's own re-spellings (`term_format.rs`, `format_term_data`).
    if (name == "cl" && args.is_empty()) || is_printable_const_array(terms, term, name, args) {
        return None;
    }
    if let (Some(constructor), [_]) = (name.strip_prefix("is-"), args) {
        // Printed `((_ is C) t)`: what must resolve is the constructor `C`.
        return is_internal_identity(constructor).then(|| constructor.to_string());
    }
    if BUILTIN_OPERATORS.contains(&name) {
        return None;
    }
    if is_builtin_complex_application(terms, term, name, args) {
        return None;
    }
    if !is_internal_identity(name) && is_datatype_member(terms, term, name, args) {
        return None;
    }
    Some(name.to_string())
}

/// Builtin Complex operators are introduced by the nominal theory, even
/// when a reconstruction proof introduces a constructor absent from the
/// authored assertions. Pinned Carcara's separate sort-surface disclosure
/// still reports Complex as unsupported; this permits AY-native export only.
fn is_builtin_complex_application(
    terms: &TermStore,
    term: TermId,
    name: &str,
    args: &[TermId],
) -> bool {
    if terms.is_declared_function(name) {
        return false;
    }
    match (name, args) {
        ("complex.make", [real, imaginary]) => {
            terms.sort(term) == &Sort::Complex
                && terms.sort(*real) == &Sort::Real
                && terms.sort(*imaginary) == &Sort::Real
        }
        ("complex.real" | "complex.imag", [value]) => {
            terms.sort(term) == &Sort::Real && terms.sort(*value) == &Sort::Complex
        }
        _ => false,
    }
}

/// The exact shape `AlethePrinter::format_const_array` re-spells.
fn is_printable_const_array(terms: &TermStore, term: TermId, name: &str, args: &[TermId]) -> bool {
    if name != "const-array" {
        return false;
    }
    let [value] = args else {
        return false;
    };
    matches!(terms.sort(term), Sort::Array(array) if terms.sort(*value) == &array.element_sort)
}

/// Whether `name` is a constructor or selector the problem's datatype
/// declarations introduce.
fn is_datatype_member(terms: &TermStore, term: TermId, name: &str, args: &[TermId]) -> bool {
    if terms.constructor_field_names(name).is_some() || terms.name_is_registered_selector(name) {
        return true;
    }
    if let Sort::Datatype(datatype) = terms.sort(term) {
        if datatype.constructors.iter().any(|ctor| ctor.name == name) {
            return true;
        }
    }
    let [operand] = args else {
        return false;
    };
    match terms.sort(*operand) {
        Sort::Datatype(datatype) => datatype
            .constructors
            .iter()
            .any(|ctor| ctor.fields.iter().any(|field| field.name == name)),
        _ => false,
    }
}

/// Decline one rendered command (a step, or a preamble definition) that
/// spells a member of `candidates` as a symbol token: the document would be
/// unparseable, so the export refuses it exactly as it refuses an
/// undeclarable free constant.
///
/// # Errors
///
/// [`AlethePrintError::UndeclarableProofSymbols`] naming the first such
/// symbol of the command.
pub(crate) fn decline_if_shipped(
    rendered: &str,
    candidates: &HashSet<String>,
) -> Result<(), AlethePrintError> {
    if candidates.is_empty() {
        return Ok(());
    }
    match first_symbol_token_in(rendered, candidates) {
        Some(name) => Err(crate::undeclarable_proof_symbols_error(
            std::slice::from_ref(name),
        )),
        None => Ok(()),
    }
}

#[cfg(test)]
#[path = "application_heads_tests.rs"]
mod tests;
