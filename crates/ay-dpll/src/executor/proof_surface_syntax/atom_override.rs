// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Guards for authored spellings that elaborate to canonical atoms.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{quote_symbol, TermId, TermStore};
use ay_frontend::command::Term as FrontendTerm;
use ay_frontend::Context;

use super::{format_frontend_term, realify_real_context_numerals, strip_frontend_annotations};

/// Record only the authored spelling of a whole assertion, without attaching
/// surface spellings to any of its canonical subterms.
///
/// Certified theory rules must print their arrays, indices, and other
/// load-bearing operands from the exact terms the checker validated.  A
/// reintroduced authored premise still needs its top-level input spelling to
/// match the problem, but recursively applying that spelling to a ROW lemma
/// can change a checked canonical index such as `(+ x (- 1))` back into the
/// source's `(+ (- x 1) 0)`.  Root-only collection preserves premise identity
/// without contaminating independently certified theory steps.
pub(in crate::executor) fn collect_root_surface_term_override(
    ctx: &mut Context,
    canonical: TermId,
    parsed: &FrontendTerm,
    overrides: &mut HashMap<TermId, String>,
) {
    let parsed = strip_frontend_annotations(parsed);
    if override_would_hijack_atom(&ctx.terms, canonical, parsed)
        && !authored_conjunction_folded_onto_variable(ctx, canonical, parsed)
    {
        return;
    }
    let echo = realify_real_context_numerals(ctx, parsed, false, &mut Vec::new());
    let surface = format_frontend_term(&echo);
    // An atom's IDENTITY spelling (`p` recorded for the variable `p`) is
    // byte-identical to what the printer emits with no override at all, so it
    // carries no information — but a plain `insert` still lets it CLOBBER a
    // real spelling already recorded for the same `TermId`.
    //
    // Measured on `(assert (and p (= x x)))` + `(assert (not p))`: the first
    // assertion folds to the bare `p` and correctly records the authored
    // conjunction against it; the SECOND assertion then descends through its
    // own `(not p)` to the operand `p` and overwrote that entry with `"p"`, so
    // the printer's folded-conjunction bridge never saw an authored spelling
    // and the exported `assume` was the bare atom — no assertion of the
    // problem, and carcara refuses the document at its first premise.
    //
    // The same reasoning `collect_bound_surface_overrides` already applies to
    // identity entries under a binder: an identity override is at best a no-op
    // and at worst destroys provenance, so it never displaces one.
    if overrides.contains_key(&canonical)
        && surface_is_atom_identity(&ctx.terms, canonical, &surface)
    {
        return;
    }
    overrides.insert(canonical, surface);
}

/// `true` when `surface` is exactly how the Alethe printer renders the atomic
/// `canonical` with no override in play.
fn surface_is_atom_identity(terms: &TermStore, canonical: TermId, surface: &str) -> bool {
    matches!(terms.get(canonical), TermData::Var(name, _) if quote_symbol(name) == surface)
}

/// `true` when `parsed` is a flat authored `and` that elaboration FOLDED onto
/// one of its own conjuncts, and that conjunct is a plain VARIABLE.
///
/// This is the one spelling class whose whole-assertion override stays
/// recordable on an atomic canonical. Everything the hijack guard below
/// protects against — an entry keyed on the fold RESULT re-spelling every
/// unrelated occurrence of that atom — is removed by the Alethe printer's
/// folded-conjunction plan (`plan_folded_and_assumes`), which recognizes
/// exactly this shape, prints the authored spelling ONLY at the `assume`, and
/// switches the term to its canonical rendering for the whole rest of the
/// document before any step is emitted.
///
/// Without it the `assume` prints the bare atom. Measured on
/// `(assert (and p (= x x)))` + `(assert (not p))` in each of
/// QF_DT / QF_UF / QF_LIA / QF_AX: AY published `unsat` stamped
/// `trust_free=yes ay_self_checkable=yes` while carcara answered `invalid` —
/// "could not match term to any of the original problem premises" — because
/// `p` alone is no assertion of the problem.
///
/// Deliberately NOT extended to constants. `true`/`false` are shared by every
/// assertion that folds to them, so one authored spelling would be recorded
/// against a `TermId` several assertions claim; a variable fold result is the
/// assertion's own atom. (A constant fold still declines, exactly as before.)
fn authored_conjunction_folded_onto_variable(
    ctx: &mut Context,
    canonical: TermId,
    parsed: &FrontendTerm,
) -> bool {
    if !matches!(ctx.terms.get(canonical), TermData::Var(..)) {
        return false;
    }
    let FrontendTerm::App(op, args) = parsed else {
        return false;
    };
    if op != "and" || args.len() < 2 {
        return false;
    }
    args.iter().any(|arg| {
        let arg = strip_frontend_annotations(arg);
        super::parsed_term_is_binder_free(arg)
            && ctx.elaborate_surface_subterm(arg) == Some(canonical)
    })
}

/// `true` when recording `parsed` as the printed spelling of `canonical`
/// would REWRITE an atom rather than re-spell a composite: elaboration
/// FOLDED the authored application away entirely (`(bvand x x)` -> `x`,
/// `(bvmul x #x00000000)` -> `#x00000000`, a whole assertion -> `false`),
/// leaving a plain variable or constant as the canonical term.
///
/// The override map is keyed by canonical `TermId` and consulted at EVERY
/// print site, so such an entry re-spells every unrelated occurrence of that
/// atom. Measured on `(assert (not (= (bvand x x) x)))`: the exported
/// `assume` printed as `(not (= (bvand (bvand x x) (bvand x x)) (bvand x
/// x)))` — no longer the problem's own assertion — so an external checker
/// rejects the whole document on `assume` matching before any derivation is
/// even considered (the pre-existing defect recorded by
/// `published_assumption_scope` in the folded-atom assumption tests).
///
/// Two spelling classes stay recordable for an atomic canonical:
/// * ATOMIC spellings — a bare identifier or literal (`alias_source`,
///   `true`) — are pure renames of the atom itself, the bread and butter of
///   alias provenance (`require_original_alias_only`), never structure
///   introduced by a fold; and
/// * ground constant expressions — `(- 1)`, `(/ 1 2)` — mention no
///   identifier, print a constant the source itself wrote, and the realify
///   lane depends on them.
pub(super) fn override_would_hijack_atom(
    terms: &TermStore,
    canonical: TermId,
    parsed: &FrontendTerm,
) -> bool {
    if !matches!(terms.get(canonical), TermData::Var(..) | TermData::Const(_)) {
        return false;
    }
    let composite = matches!(
        parsed,
        FrontendTerm::App(..) | FrontendTerm::IndexedApp(..) | FrontendTerm::QualifiedApp(..)
    );
    composite && parsed_term_mentions_identifier(parsed)
}

/// `true` when the parsed source term mentions any identifier (a bare
/// `Symbol` leaf). Ground constant arithmetic (`(- 1)`, `(/ 1 2)`,
/// `(concat #b0 #b1)`) mentions none; binder or match constructs are
/// conservatively treated as mentioning one (they are never ground constant
/// spellings).
fn parsed_term_mentions_identifier(term: &FrontendTerm) -> bool {
    let mut stack: Vec<&FrontendTerm> = vec![term];
    while let Some(t) = stack.pop() {
        match strip_frontend_annotations(t) {
            FrontendTerm::Const(_) => {}
            FrontendTerm::Symbol(_) => return true,
            FrontendTerm::App(_, args)
            | FrontendTerm::IndexedApp(_, _, args)
            | FrontendTerm::QualifiedApp(_, _, args) => stack.extend(args.iter()),
            _ => return true,
        }
    }
    false
}
