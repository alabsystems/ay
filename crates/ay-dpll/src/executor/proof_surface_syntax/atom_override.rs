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
    let surface = authored_root_surface(ctx, parsed);
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

/// The printed spelling [`collect_root_surface_term_override`] records for a
/// whole authored assertion: annotations stripped, Real-context numerals
/// realified.
pub(in crate::executor) fn authored_root_surface(
    ctx: &mut Context,
    parsed: &FrontendTerm,
) -> String {
    let parsed = strip_frontend_annotations(parsed);
    let echo = realify_real_context_numerals(ctx, parsed, false, &mut Vec::new());
    format_frontend_term(&echo)
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
    // A ground expression that merely EVALUATES to a constant (`(<= 0 2)`
    // for `true`, `(div (- 4 (mod 4 2)) 2)` for `2`) is a different term, not
    // another spelling of the same value the way `(- 1)` spells `-1` or
    // `(/ 1 2)` spells `1/2`. A constant is shared by every subterm that
    // folds to it, so such an entry re-spells unrelated occurrences (an
    // `(assume (and .. (<= 0 2) .. (not true)))` conjunct then prints as
    // `(not (<= 0 2))`).
    let constant = matches!(terms.get(canonical), TermData::Const(_));
    composite
        && ((constant && !is_numeric_literal_spelling(parsed))
            || parsed_term_mentions_identifier(parsed))
}

/// `true` when spelling the `forall_inst` instance `instance` from the
/// authored body of `parsed_forall` would REWRITE an atom
/// ([`override_would_hijack_atom`]): the store folded the instance to a
/// variable or constant, while the authored body is composite.
///
/// The instance of `(forall ((q Bool)) (and q q))` at `false` is the SHARED
/// `false` term; recording `(and false false)` against it would re-spell every
/// `false` in the document, the `false` axiom first. The same holds for
/// `(= q true)` and `(not (not q))`, and for a variable fold result such as
/// `p` for `(and p x)` at `true`. Declining the entry is fail-closed: the
/// instance prints canonically and the printer's own `forall_inst` judgement
/// reads the bytes that ship.
pub(in crate::executor) fn forall_instance_would_hijack_atom(
    terms: &TermStore,
    instance: TermId,
    parsed_forall: &FrontendTerm,
) -> bool {
    let FrontendTerm::Forall(_, body) = strip_frontend_annotations(parsed_forall) else {
        return false;
    };
    override_would_hijack_atom(terms, instance, strip_frontend_annotations(body))
}

/// `n`, `(- n)`, `(/ n m)` and `(- (/ n m))` over numeral or decimal
/// literals: the only SMT-LIB spellings of an arithmetic constant.
fn is_numeric_literal_spelling(term: &FrontendTerm) -> bool {
    match strip_frontend_annotations(term) {
        FrontendTerm::Const(_) => true,
        FrontendTerm::App(op, args) if op == "-" && args.len() == 1 => {
            is_numeric_literal_spelling(&args[0])
        }
        FrontendTerm::App(op, args) if op == "/" && args.len() == 2 => args
            .iter()
            .all(|arg| matches!(strip_frontend_annotations(arg), FrontendTerm::Const(_))),
        _ => false,
    }
}

/// `true` when `parsed` names a nullary `define-fun` the proof exporter
/// hands the printer as a definition premise.
///
/// Such a spelling may head an `assume`, where the printer bridges it to the
/// canonical term through `(= name body)`, but never a DESCENDANT override:
/// that entry re-spells its `TermId` at every occurrence, and pinned carcara
/// 1.1.0, run without `--apply-function-defs`, reads the name as an opaque
/// constant, so every step over that occurrence disagrees with the expanded
/// term AY checked. MEASURED on `(define-fun m () Bool (< x 3))`, `(assert m)`,
/// `(assert (or r (not m)))`, `(assert (not r))`: the descendant entry
/// `(not (< x 3))` -> `(not m)` survived after both roots were bridged, and
/// before those bridges existed the same entry published a `trust_free=yes`
/// document carcara refused at an `equiv_neg2` over `(not m)` and
/// `(not (< x 3))`.
pub(super) fn names_nullary_macro(ctx: &Context, parsed: &FrontendTerm) -> bool {
    let mut stack: Vec<&FrontendTerm> = vec![parsed];
    while let Some(term) = stack.pop() {
        match strip_frontend_annotations(term) {
            FrontendTerm::Symbol(name) => {
                if ctx.source_nullary_definition_for_proof(name).is_some() {
                    return true;
                }
            }
            FrontendTerm::App(_, args)
            | FrontendTerm::IndexedApp(_, _, args)
            | FrontendTerm::QualifiedApp(_, _, args) => stack.extend(args.iter()),
            _ => {}
        }
    }
    false
}

/// Whether a DESCENDANT subterm `child`, authored as `parsed`, records its
/// spelling: not a fold onto an atom ([`override_would_hijack_atom`]), not a
/// fold onto one of its own operands ([`override_folds_onto_own_operand`]),
/// not already spelled, and naming no nullary macro ([`names_nullary_macro`]).
pub(super) fn records_descendant_spelling(
    ctx: &mut Context,
    child: TermId,
    parsed: &FrontendTerm,
    overrides: &HashMap<TermId, String>,
) -> bool {
    !override_would_hijack_atom(&ctx.terms, child, parsed)
        && !overrides.contains_key(&child)
        && !names_nullary_macro(ctx, parsed)
        && !override_folds_onto_own_operand(ctx, child, parsed)
}

/// `true` when elaboration folded the authored application `parsed` onto
/// (the canonical form of) ONE OF ITS OWN OPERANDS: `(and true X)`,
/// `(or false X)`, `(and X X)`, `(ite c X X)` all intern as the term `X`
/// already is.
///
/// This is the composite twin of [`override_would_hijack_atom`], which only
/// sees a fold whose result is a variable or constant. The override map is
/// keyed by canonical `TermId` and consulted at EVERY print site, so
/// recording `(and true X)` against `X` re-spells every occurrence of `X` —
/// including the one inside the recorded spelling's own operand. Measured
/// (Trust's in-process ay lane, 2026-10-06) on
/// `(assert (and (<= a b) (and true (not (<= a b)))))`: the descendant entry
/// `(not (<= a b))` -> `(and true (not (<= a b)))` made the raw re-interned
/// root print as `(and (<= a b) (and true (and true (not (<= a b)))))`, so the
/// fold-to-`false` complement rescue (`authored_fold_identity`) refused its
/// own candidate at the "prints as authored" gate, the proof was erased to
/// the bare hole, and mandatory strict certification turned a correct
/// `unsat` into `unknown (incomplete self-check-rejected)`.
///
/// Refusing the entry is fail-closed: a dropped override only makes `X` print
/// in its canonical form — which is what the proof's own steps mention —
/// never changes what any step claims. A genuine re-spelling
/// (`(>= x 0)` on `(<= 0 x)`) keeps its entry: no operand of it elaborates to
/// the whole canonical term.
pub(super) fn override_folds_onto_own_operand(
    ctx: &mut Context,
    canonical: TermId,
    parsed: &FrontendTerm,
) -> bool {
    let operands: &[FrontendTerm] = match strip_frontend_annotations(parsed) {
        FrontendTerm::App(_, args)
        | FrontendTerm::IndexedApp(_, _, args)
        | FrontendTerm::QualifiedApp(_, _, args) => args,
        _ => return false,
    };
    operands.iter().any(|operand| {
        let operand = strip_frontend_annotations(operand);
        super::parsed_term_is_binder_free(operand)
            && ctx.elaborate_surface_subterm(operand) == Some(canonical)
    })
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

#[cfg(test)]
#[path = "atom_override_tests.rs"]
mod tests;
