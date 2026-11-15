// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A datatype selector over a constructor, printed as Clean's `dt_project`.
//!
//! AY's strict checker validates the selector-projection axiom
//! `(= (S (C a_0 .. a_n)) a_i)` (`TheoryLemmaKind::DatatypeSelectorProject`,
//! `validate_datatype_selector_project`), but pinned Carcara 9a352ee has no
//! datatype rule, so the printer printed the step as `:rule hole` and a
//! Carcara-claiming consumer refused the UNSAT (Trust's four datatype rows).
//! Clean's vendored Carcara checks it as `dt_project` (Clean 4dc90e8ea,
//! `third-party/carcara` DOWNSTREAM.md row C2): the conclusion is the single
//! literal `(= (S (C t_0 .. t_n)) t_i)`, no premises, no arguments, `C` a
//! constructor of a declared NON-parametric datatype applied at its declared
//! arity, `S` its `i`-th selector, and `t_i` the same term as the right side.
//! The reversed orientation is refused there; it takes a `symm` step.
//!
//! In [`AletheDialect::Clean`] this prints
//!
//! ```text
//! (step t1 (cl (= (fst (mk a b)) a)) :rule dt_project)
//! ```
//!
//! and, for `(= a (fst (mk a b)))`,
//!
//! ```text
//! (step t1.dt (cl (= (fst (mk a b)) a)) :rule dt_project)
//! (step t1 (cl (= a (fst (mk a b)))) :rule symm :premises (t1.dt))
//! ```
//!
//! and notes [`CleanOnlySpelling::DatatypeSelectorProject`], so the document
//! is disclosed `carcara_surface=clean-dialect`. In
//! [`AletheDialect::PinnedCarcara`] nothing here runs and the step stays the
//! honest `hole`, byte for byte.
//!
//! Two judgements, both fail-closed to the hole:
//!
//! * On the IR, with the strict checker's own matcher
//!   (`checker::datatype_axiom::selector_projection`) over the term store's
//!   constructor-field registry (`TermStore::constructor_field_names`, the
//!   mirror of the registry the strict checker is given): the clause is ONE
//!   literal, an equality, one side `(S (C a_0 .. a_n))` with `S` the
//!   registered `i`-th selector of `C`, and the other side `a_i`. A
//!   constructor of a parametric datatype instance declines: Clean refuses
//!   every parametric datatype.
//! * On the PRINTED clause: `(cl (= (S (C A_0 .. A_n)) V))` (or the reversed
//!   equality), `S` and `C` plain symbols (an `(as ..)` or `(_ ..)` head
//!   declines), exactly the IR arity of arguments, and `A_i` byte-identical
//!   to `V`. That byte identity is what Clean's hash-consed `t_i == rhs`
//!   compares; two spellings the store identifies decline instead. A name an
//!   IR anchor binds anywhere in the proof declines as well, because Clean
//!   refuses the step under an anchor that binds `S` or `C`. So does an
//!   AY-internal identity (`__ay_..`, such as the frontend's
//!   `__ay_overload_N` for a selector two datatypes share, or one
//!   redeclared after `pop`): the problem never declares that name, so the
//!   step would cite a symbol no checker can resolve. Measured on two
//!   datatypes that share the field name `f1`, the document printed
//!   `(step t1 (cl (= (__ay_overload_1 (mkq a b)) b)) :rule dt_project)`;
//!   it now keeps the hole (the `assume` beside it still prints the internal
//!   name, a printer gap that predates this lowering).
//!
//! A wrong line here is a Clean `invalid`, never a false accept: Clean
//! re-derives the projection from the problem's own declarations.
//!
//! [`dt_project_lowering_supported`] asks the same two judgements without a
//! proof, for the executor's known-wire-gap screen, which otherwise reads the
//! kind's wire rule (`hole`) and withheld the Clean dialect's hole-free
//! document under `:check-proofs-strict`.

use super::dialect::{self, AletheDialect, CleanOnlySpelling};
use super::surface_tokens::{split_alethe_application_bounded, split_smt_term_slices_bounded};
use super::AlethePrinter;
use crate::checker::{unit_selector_projection, ProjectionOrientation};
use ay_core::kani_compat::DetHashMap;
use ay_core::{ProofId, Sort, Symbol, TermData, TermId, TermStore};

/// Byte cap on one printed clause the judgement reads.
const MAX_PRINTED_CLAUSE_BYTES: usize = 1 << 20;

/// The prefix of the identities AY's frontend mints for names the problem
/// does not declare under that spelling (`__ay_overload_N`).
const INTERNAL_IDENTITY_PREFIX: &str = "__ay_";

impl AlethePrinter<'_> {
    /// The `dt_project` lowering of a `DatatypeSelectorProject` lemma, or
    /// `None` (the caller prints the hole). See the module doc.
    pub(super) fn format_dt_project(&self, id: ProofId, clause: &[TermId]) -> Option<String> {
        if dialect::current() != AletheDialect::Clean {
            return None;
        }
        let projection = judged_projection(self.terms, clause)?;
        let printed = self.format_clause(clause);
        let binders = self.anchor_binder_names.borrow();
        let text = printed_dt_project(id, &printed, projection, &|name| binders.contains(name))?;
        dialect::note_clean_only(CleanOnlySpelling::DatatypeSelectorProject);
        Some(text)
    }
}

/// Whether a render in `dialect` prints the `DatatypeSelectorProject` lemma
/// `clause` as `dt_project` under the export's effective `overrides`: the
/// lowering's IR judgement and its printed-text judgement, over the clause
/// as a fresh printer with those overrides spells it.
///
/// The known-wire-gap screen asks this before it falls back to the kind's
/// wire rule, which is `hole` for every dialect. Like the screen's other
/// lowering predicates it sees no proof, so it cannot see the anchor binders
/// the printer also declines on: it can only be optimistic about a hole,
/// which the document still discloses, never about an invalid step. Always
/// `false` in [`AletheDialect::PinnedCarcara`], whose checker has no
/// datatype rule.
#[must_use]
pub fn dt_project_lowering_supported(
    dialect: AletheDialect,
    terms: &TermStore,
    clause: &[TermId],
    overrides: Option<&DetHashMap<TermId, String>>,
) -> bool {
    if dialect != AletheDialect::Clean {
        return false;
    }
    let Some(projection) = judged_projection(terms, clause) else {
        return false;
    };
    let printed = dialect::discarding_notes(|| {
        AlethePrinter::new_with_overrides_and_budget(terms, overrides, None).format_clause(clause)
    });
    printed_dt_project(ProofId(0), &printed, projection, &|_| false).is_some()
}

/// The IR judgement: `clause` is the strict checker's selector projection
/// over a constructor of a non-parametric datatype.
fn judged_projection(terms: &TermStore, clause: &[TermId]) -> Option<PrintedProjection> {
    let selectors_of = |ctor: &str| terms.constructor_field_names(ctor);
    let projection = unit_selector_projection(terms, clause, &selectors_of)?;
    if is_parametric_instance(terms, projection.constructor) {
        return None;
    }
    Some(PrintedProjection {
        orientation: projection.orientation,
        field: projection.field,
        arity: projection.arity,
    })
}

/// What the IR judgement fixed, for the printed-text judgement.
#[derive(Clone, Copy, Debug)]
pub(super) struct PrintedProjection {
    /// Which printed side must be the selector application.
    pub(super) orientation: ProjectionOrientation,
    /// The projected field `i`.
    pub(super) field: usize,
    /// The constructor's field count.
    pub(super) arity: usize,
}

/// The `dt_project` commands for the printed clause `printed_clause` under
/// `id`, or `None` when the text is not exactly the projection the IR
/// judgement fixed. `bound` answers whether an anchor binds a printed name.
pub(super) fn printed_dt_project(
    id: ProofId,
    printed_clause: &str,
    projection: PrintedProjection,
    bound: &dyn Fn(&str) -> bool,
) -> Option<String> {
    let literals =
        split_alethe_application_bounded(printed_clause, "cl", 1, MAX_PRINTED_CLAUSE_BYTES).ok()?;
    let [literal] = literals.as_slice() else {
        return None;
    };
    let sides = split_alethe_application_bounded(literal, "=", 2, MAX_PRINTED_CLAUSE_BYTES).ok()?;
    let [left, right] = sides.as_slice() else {
        return None;
    };
    let (selection, value) = match projection.orientation {
        ProjectionOrientation::SelectorFirst => (*left, *right),
        ProjectionOrientation::ValueFirst => (*right, *left),
    };
    let selected = application(selection, 1)?;
    let [selector, construction] = selected.as_slice() else {
        return None;
    };
    // `application` returns exactly `arity` arguments after the head, so the
    // constructor is printed at the declared arity the IR judgement fixed.
    let constructed = application(construction, projection.arity)?;
    let (constructor, arguments) = constructed.split_first()?;
    if !is_declarable_symbol(selector)
        || !is_declarable_symbol(constructor)
        || bound(selector)
        || bound(constructor)
        || arguments.get(projection.field) != Some(&value)
    {
        return None;
    }
    Some(match projection.orientation {
        ProjectionOrientation::SelectorFirst => {
            format!("(step {id} {printed_clause} :rule dt_project)")
        }
        ProjectionOrientation::ValueFirst => format!(
            "(step {id}.dt (cl (= {selection} {value})) :rule dt_project)\n\
             (step {id} {printed_clause} :rule symm :premises ({id}.dt))"
        ),
    })
}

/// The head and the `arguments` arguments of one printed application
/// `(HEAD ARG ..)`, or `None` for anything else (an atom, or another count).
fn application(printed: &str, arguments: usize) -> Option<Vec<&str>> {
    let inner = printed.strip_prefix('(')?.strip_suffix(')')?;
    let items =
        split_smt_term_slices_bounded(inner, arguments.saturating_add(1), MAX_PRINTED_CLAUSE_BYTES)
            .ok()?;
    (items.len() == arguments.saturating_add(1)).then_some(items)
}

/// Whether `token` is one SMT-LIB symbol a problem can have declared: a
/// quoted `|..|` symbol, or a simple symbol (letters, digits and
/// `~!@$%^&*_-+=<>.?/`, not starting with a digit), and in either spelling
/// not an AY-internal `__ay_..` identity (see the module doc). An indexed
/// `(_ ..)` or qualified `(as ..)` head is not.
fn is_declarable_symbol(token: &str) -> bool {
    let name = token
        .strip_prefix('|')
        .and_then(|quoted| quoted.strip_suffix('|'))
        .unwrap_or(token);
    if name.starts_with(INTERNAL_IDENTITY_PREFIX) {
        return false;
    }
    if token.len() >= 2 && token.starts_with('|') && token.ends_with('|') {
        return !token[1..token.len() - 1].contains(['|', '\\']);
    }
    let mut bytes = token.bytes();
    bytes.next().is_some_and(|first| !first.is_ascii_digit())
        && token
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || b"~!@$%^&*_-+=<>.?/".contains(&byte))
}

/// Whether `constructor` (an application `(C ..)`) builds an instance of a
/// parametric datatype. The frontend names such an instance's carrier
/// `D!{T..}` and its members `member@D!{T..}` (`mangle_datatype_instance`,
/// `mangle_member`); Clean refuses every parametric datatype, so both
/// spellings decline, and a monomorphic datatype a user happened to name
/// that way declines too, which only costs the lowering.
fn is_parametric_instance(terms: &TermStore, constructor: TermId) -> bool {
    let TermData::App(Symbol::Named(name), _) = terms.get(constructor) else {
        return true;
    };
    let carrier = match terms.sort(constructor) {
        Sort::Uninterpreted(carrier) => carrier.as_str(),
        Sort::Datatype(datatype) => datatype.name.as_str(),
        _ => return true,
    };
    carrier.contains("!{") || name.ends_with(&format!("@{carrier}"))
}

#[cfg(test)]
#[path = "dt_project_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "dt_project_screen_tests.rs"]
mod screen_tests;
