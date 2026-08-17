// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Surface-syntax preservation helpers for Alethe proof export.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{quote_symbol, TermId};
use ay_frontend::command::{
    Constant as FrontendConstant, Index as FrontendIndex, MatchPattern as FrontendMatchPattern,
    QualifiedIdentifier as FrontendQualifiedIdentifier, Sort as FrontendSort, Term as FrontendTerm,
};
use ay_frontend::{Context, SExpr};

#[path = "proof_surface_syntax/atom_override.rs"]
mod atom_override;
#[path = "proof_surface_syntax_realify.rs"]
mod realify;
pub(super) use atom_override::collect_root_surface_term_override;
use atom_override::override_would_hijack_atom;
use realify::realify_real_context_numerals;

pub(super) fn strip_frontend_annotations(term: &FrontendTerm) -> &FrontendTerm {
    match term {
        FrontendTerm::Annotated(inner, _) => strip_frontend_annotations(inner),
        other => other,
    }
}

/// Bound canonical DAG work performed while collecting one source's surface
/// overrides. Quantified roots search the canonical body once per binding,
/// so that multiplicity is charged before `find_bound_var` runs.
pub(super) fn surface_override_collection_work(
    terms: &ay_core::TermStore,
    canonical: TermId,
) -> Option<usize> {
    const MAX_COLLECTION_WORK: usize = 8 * 1024 * 1024;
    let (root, traversals) = match terms.get(canonical) {
        TermData::Forall(bindings, body, _) | TermData::Exists(bindings, body, _) => {
            (*body, bindings.len().checked_add(2)?)
        }
        _ => (canonical, 2),
    };
    super::proof_trust_surgery_provenance::canonical_term_work(terms, root)?
        .max(1)
        .checked_mul(traversals)
        .filter(|&work| work <= MAX_COLLECTION_WORK)
}

/// Bound aggregate canonical work for one override batch. Repeated roots are
/// charged repeatedly because each collector invocation traverses them again.
pub(super) fn surface_override_roots_have_bounded_work(
    terms: &ay_core::TermStore,
    roots: impl IntoIterator<Item = TermId>,
) -> bool {
    const MAX_ROOTS: usize = 8_192;
    const MAX_WORK: usize = 32 * 1024 * 1024;
    let mut root_count = 0usize;
    roots
        .into_iter()
        .try_fold(0usize, |used, root| {
            root_count = root_count.checked_add(1)?;
            if root_count > MAX_ROOTS {
                return None;
            }
            used.checked_add(surface_override_collection_work(terms, root)?.max(1))
                .filter(|&next| next <= MAX_WORK)
        })
        .is_some()
}

/// Bound an existing override map before a rebuild clones it transactionally.
pub(super) fn surface_override_map_is_bounded(overrides: &HashMap<TermId, String>) -> bool {
    const MAX_OVERRIDES: usize = 8_192;
    const MAX_BYTES: usize = 8 * 1024 * 1024;
    overrides.len() <= MAX_OVERRIDES
        && overrides
            .values()
            .try_fold(0usize, |bytes, spelling| bytes.checked_add(spelling.len()))
            .is_some_and(|bytes| bytes <= MAX_BYTES)
}

pub(super) fn collect_surface_term_overrides(
    ctx: &mut Context,
    canonical: TermId,
    parsed: &FrontendTerm,
    overrides: &mut HashMap<TermId, String>,
) -> bool {
    if !super::proof_trust_surgery_surface_audit::surface_source_is_bounded(parsed) {
        return false;
    }
    if surface_override_collection_work(&ctx.terms, canonical).is_none() {
        return false;
    }
    collect_surface_term_overrides_prechecked(ctx, canonical, parsed, overrides);
    true
}

fn collect_surface_term_overrides_prechecked(
    ctx: &mut Context,
    canonical: TermId,
    parsed: &FrontendTerm,
    overrides: &mut HashMap<TermId, String>,
) {
    collect_root_surface_term_override(ctx, canonical, parsed, overrides);
    let parsed = strip_frontend_annotations(parsed);

    if let (FrontendTerm::App(op, args), TermData::Not(inner)) = (parsed, ctx.terms.get(canonical))
    {
        if op == "not" && args.len() == 1 {
            let inner = *inner;
            collect_surface_term_overrides_prechecked(ctx, inner, &args[0], overrides);
            return;
        }
    }

    // Certified `sko_forall` export must use one surface identity for the
    // quantified body, its Hilbert-choice predicate, and the instantiated
    // body.  The generic collector intentionally skips open subterms, but here
    // the already-elaborated binder gives us the exact local environment, so
    // descending is deterministic and does not create a fresh quantifier.
    if let (
        FrontendTerm::Forall(parsed_bindings, parsed_body),
        TermData::Forall(canonical_bindings, canonical_body, _),
    ) = (parsed, ctx.terms.get(canonical).clone())
    {
        if parsed_bindings.len() == canonical_bindings.len() {
            let mut env = Vec::with_capacity(parsed_bindings.len());
            let mut recovered_all_bindings = true;
            for ((surface_name, _), (canonical_name, canonical_sort)) in
                parsed_bindings.iter().zip(&canonical_bindings)
            {
                let Some(canonical_var) =
                    find_bound_var(ctx, canonical_body, canonical_name, canonical_sort)
                else {
                    recovered_all_bindings = false;
                    break;
                };
                env.push((surface_name.clone(), canonical_var));
            }
            // A provenance-preserving preprocessing pass may have rewritten
            // the canonical body while retaining this authored quantifier as
            // its source (integer `<` normalization is the boundary case).
            // The whole bodies then need not have the same TermId. Descend
            // anyway: each individual surface subterm is re-elaborated under
            // the exact recovered binder and is attached only to its own
            // hash-consed TermId. The printer subsequently accepts a mapping
            // only through exact Boolean-complement structure in the checked
            // proof.
            if recovered_all_bindings {
                collect_bound_surface_overrides(ctx, parsed_body, &env, overrides);
            }
        }
        return;
    }

    collect_subterm_surface_overrides(ctx, parsed, overrides);
}

/// Recover the exact fresh variable identity used by an elaborated binder.
///
/// Quantifier variables are deliberately not entered in `TermStore`'s global
/// name table, so `mk_var(canonical_name, ..)` would create a distinct Var
/// with the same printed name. Search the already-elaborated body instead and
/// fail closed if preprocessing somehow left two identities ambiguous.
fn find_bound_var(
    ctx: &Context,
    body: TermId,
    canonical_name: &str,
    canonical_sort: &ay_core::Sort,
) -> Option<TermId> {
    const MAX_CANONICAL_SCAN: usize = 100_000;
    const MAX_CANONICAL_DEPTH: usize = 256;
    let mut stack = vec![(body, 0usize)];
    let mut visited = HashSet::default();
    let mut found = None;
    while let Some((term, depth)) = stack.pop() {
        if depth > MAX_CANONICAL_DEPTH || visited.len() >= MAX_CANONICAL_SCAN {
            return None;
        }
        if !visited.insert(term) {
            continue;
        }
        if matches!(ctx.terms.get(term), TermData::Var(name, _) if name == canonical_name)
            && ctx.terms.sort(term) == canonical_sort
        {
            if found.is_some_and(|prior| prior != term) {
                return None;
            }
            found = Some(term);
        }
        let child_count = match ctx.terms.get(term) {
            TermData::Const(_) | TermData::Var(..) => 0,
            TermData::App(_, args) => args.len(),
            TermData::Let(bindings, _) => bindings.len().checked_add(1)?,
            TermData::Not(_) => 1,
            TermData::Ite(..) => 3,
            TermData::Forall(..) | TermData::Exists(..) => 1,
            _ => return None,
        };
        if stack
            .len()
            .saturating_add(visited.len())
            .saturating_add(child_count)
            > MAX_CANONICAL_SCAN
        {
            return None;
        }
        stack.extend(
            ctx.terms
                .children(term)
                .into_iter()
                .map(|child| (child, depth + 1)),
        );
    }
    found
}

/// Collect exact surface spellings below an already-elaborated binder.
///
/// Unlike the closed-term collector, every node is re-elaborated with the
/// caller-provided local environment.  This is restricted to the body of a
/// binder whose canonical `TermId` was already matched above, so a failure at
/// any child is simply skipped and can never authorize a proof step.
fn collect_bound_surface_overrides(
    ctx: &mut Context,
    parsed: &FrontendTerm,
    env: &[(String, TermId)],
    overrides: &mut HashMap<TermId, String>,
) {
    let parsed = strip_frontend_annotations(parsed);
    if let Some(canonical) = ctx.elaborate_surface_subterm_with_bindings(parsed, env) {
        if bound_override_respells_target(ctx, parsed, canonical, env) {
            let echo = realify_real_context_numerals(ctx, parsed, false, &mut Vec::new());
            let surface = format_frontend_term(&echo);
            // A free atom whose authored and canonical Alethe spellings are
            // identical needs no override. Keeping that identity entry would
            // make an exact ground quantifier instance look surface-mutated to
            // the rigid rule-role audit. Bound variables are the exception:
            // their authored name can differ from the recovered canonical
            // binder identity.
            let bound_symbol = env.iter().any(|(_, bound)| *bound == canonical);
            let identity_free_symbol = matches!(
                (parsed, ctx.terms.get(canonical)),
                (FrontendTerm::Symbol(surface), TermData::Var(canonical, _))
                    if !bound_symbol && format_frontend_symbol(surface) == quote_symbol(canonical)
            );
            let identity_free_constant =
                matches!(
                    (parsed, ctx.terms.get(canonical)),
                    (FrontendTerm::Const(_), TermData::Const(_))
                ) && super::proof_trust_surgery_surface_audit::render_roots_have_bounded_payload(
                    &ctx.terms,
                    &[canonical],
                    1,
                    surface.len().saturating_mul(4).saturating_add(64),
                ) && surface == ay_proof::format_term_alethe(&ctx.terms, canonical);
            if !(identity_free_symbol || identity_free_constant) {
                overrides.entry(canonical).or_insert(surface);
            }
        }
    }
    match parsed {
        FrontendTerm::App(_, args)
        | FrontendTerm::IndexedApp(_, _, args)
        | FrontendTerm::QualifiedApp(_, _, args) => {
            for arg in args {
                collect_bound_surface_overrides(ctx, arg, env, overrides);
            }
        }
        // The certified Skolem lane rejects nested binders/lets.  Do not try
        // to approximate their shadowing here; the strict checker fails them
        // closed before printing.
        FrontendTerm::Const(_) | FrontendTerm::Symbol(_) => {}
        _ => {}
    }
}

/// `true` when attaching `parsed`'s surface spelling to `canonical` RE-SPELLS
/// that term rather than RE-WRITING it.
///
/// A surface override replaces the printed form of ONE `TermId` EVERYWHERE in
/// the exported document, so it is admissible only while the spelling still
/// denotes what the id denotes. Elaboration FOLDS: `(+ x 0)` and `(* 1 x)`
/// intern as the bare `x`, `(bvand x x)` as `x`, `(bvsub x x)` as a constant.
/// Registering the composite spelling on the fold RESULT does not re-spell the
/// composite — it renames the variable, so every occurrence the problem file
/// spells `x` prints as `(+ x 0)`.
///
/// Inside a binder that is not cosmetic. The certified `sko_forall` printer
/// re-reads these overrides in `register_substituted_surface_overrides` and
/// installs the binder-substituted spelling on the Skolem WITNESS. A
/// bound-variable override makes that spelling disagree with the `(choice
/// ...)` the same pass already installed for the same witness, so
/// `insert_skolem_override` reports `term tN acquired incompatible choice
/// renderings` and the WHOLE document is replaced by the unverifiable marker.
/// Measured on `(assert (not (forall ((x Int)) (or (<= (+ x 0) y) p))))`:
/// `unsat` was still correct, but `(get-proof)` returned
/// `(error "UNVERIFIABLE PROOF: ... acquired incompatible choice renderings")`
/// instead of a certificate.
///
/// The admissibility test is exactly the containment a fold destroys: a
/// COMPOSITE surface term may only be attached to a canonical term that
/// STRICTLY CONTAINS every operand's canonical form. This still admits every
/// genuine re-spelling — `(<= (+ x 0) y)` keeps its authored spelling on
/// `(<= x y)` because both `x` and `y` occur strictly inside it, and a
/// canonicalized `(=> a b)` keeps it on `(or (not a) b)` — while refusing
/// every spelling whose own operand IS the target. Leaves (symbols,
/// constants, nullary applications) have no operands and cannot re-write
/// anything, so they are admitted unchanged; that keeps `define-fun`
/// abbreviations printing under their authored name.
///
/// Fail-closed: an operand that does not re-elaborate is refused. Dropping an
/// override can only make a term print in its canonical form, never change
/// what the proof claims.
fn bound_override_respells_target(
    ctx: &mut Context,
    parsed: &FrontendTerm,
    canonical: TermId,
    env: &[(String, TermId)],
) -> bool {
    let operands: &[FrontendTerm] = match parsed {
        FrontendTerm::App(_, args)
        | FrontendTerm::IndexedApp(_, _, args)
        | FrontendTerm::QualifiedApp(_, _, args) => args,
        _ => return true,
    };
    if operands.is_empty() {
        return true;
    }
    for operand in operands {
        let operand = strip_frontend_annotations(operand);
        let Some(operand_id) = ctx.elaborate_surface_subterm_with_bindings(operand, env) else {
            return false;
        };
        if !term_strictly_contains(&ctx.terms, canonical, operand_id) {
            return false;
        }
    }
    true
}

/// `true` when `needle` occurs as a PROPER subterm of `haystack`.
///
/// Deliberately strict: `haystack == needle` is `false`, which is the whole
/// point at the call site — a fold that returned one of its own operands has
/// not produced a term the operand's spelling may rename.
fn term_strictly_contains(terms: &ay_core::TermStore, haystack: TermId, needle: TermId) -> bool {
    let mut stack: Vec<TermId> = terms.children(haystack);
    let mut visited = HashSet::default();
    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        if term == needle {
            return true;
        }
        stack.extend(terms.children(term));
    }
    false
}

/// Connectives whose surface subterms are safe to re-elaborate for override
/// collection: pure logical structure with no fresh-variable or
/// side-constraint elaboration paths.
fn is_override_descent_connective(op: &str) -> bool {
    matches!(
        op,
        "not" | "and" | "or" | "=>" | "implies" | "xor" | "=" | "distinct" | "ite"
    )
}

/// `true` when the parsed term contains no binding construct, so it is closed
/// at the top level and re-elaborates (deterministically, via hash-consing)
/// to the exact canonical `TermId` it produced when originally asserted.
pub(super) fn parsed_term_is_binder_free(term: &FrontendTerm) -> bool {
    let mut stack: Vec<&FrontendTerm> = vec![term];
    while let Some(t) = stack.pop() {
        match strip_frontend_annotations(t) {
            FrontendTerm::Const(_) | FrontendTerm::Symbol(_) => {}
            FrontendTerm::App(_, args)
            | FrontendTerm::IndexedApp(_, _, args)
            | FrontendTerm::QualifiedApp(_, _, args) => stack.extend(args.iter()),
            _ => return false,
        }
    }
    true
}

/// Recurse through pure connective structure, mapping each composite surface
/// subterm back to its canonical `TermId` (by re-elaboration — exact even
/// when canonicalization reordered or desugared it, e.g. `(=> a b)` stored as
/// `(or (not a) b)`, or commutative-argument sorting) and recording its
/// surface rendering. This keeps nested occurrences of an assertion's
/// subterms printing with the problem file's own syntax, so steps like
/// `equiv_pos2` over `(= c (=> a b))` print the implication — not the
/// internal or-term — and stay consistent with the `assume` of the source
/// assertion.
///
/// Child overrides never overwrite an existing entry: the first surface
/// spelling encountered stays authoritative, and the top-level assertion
/// override (inserted unconditionally above) keeps its original precedence.
fn collect_subterm_surface_overrides(
    ctx: &mut Context,
    parsed: &FrontendTerm,
    overrides: &mut HashMap<TermId, String>,
) {
    let FrontendTerm::App(op, args) = parsed else {
        return;
    };
    if !is_override_descent_connective(op) {
        return;
    }
    for arg in args {
        let arg = strip_frontend_annotations(arg);
        // Only composite subterms can print differently from their surface
        // form; symbols and constants already render identically.
        if !matches!(arg, FrontendTerm::App(..)) {
            continue;
        }
        if !parsed_term_is_binder_free(arg) {
            continue;
        }
        let Some(child) = ctx.elaborate_surface_subterm(arg) else {
            continue;
        };
        // A subterm that FOLDED to a plain variable/constant must not
        // register its spelling: keyed by the atom's TermId, it would
        // re-spell every unrelated occurrence of that atom (see
        // `override_would_hijack_atom`). Still descend — deeper subterms
        // that survived elaboration keep their own faithful spellings.
        if !override_would_hijack_atom(&ctx.terms, child, arg) && !overrides.contains_key(&child) {
            let echo = realify_real_context_numerals(ctx, arg, false, &mut Vec::new());
            overrides.insert(child, format_frontend_term(&echo));
        }
        collect_subterm_surface_overrides(ctx, arg, overrides);
    }
}

/// Deep override collection for the trust-surgery ite-lift: unlike the
/// connective-only descent above, this walks through arithmetic operators,
/// comparisons, and `ite` so that TERM-level subterms of an atomic assertion
/// (the lifted `(ite c u v)` and its condition) also print with the problem
/// file's syntax. Restricted to pure, side-constraint-free operators —
/// everything here re-elaborates deterministically via hash-consing.
pub(super) fn collect_deep_arith_surface_overrides(
    ctx: &mut Context,
    parsed: &FrontendTerm,
    overrides: &mut HashMap<TermId, String>,
) {
    let FrontendTerm::App(op, args) = strip_frontend_annotations(parsed) else {
        return;
    };
    if !is_override_descent_connective(op)
        && !matches!(op.as_str(), "<" | "<=" | ">" | ">=" | "+" | "-" | "*")
    {
        return;
    }
    for arg in args {
        let arg = strip_frontend_annotations(arg);
        if !matches!(arg, FrontendTerm::App(..)) {
            continue;
        }
        if !parsed_term_is_binder_free(arg) {
            continue;
        }
        if let Some(child) = ctx.elaborate_surface_subterm(arg) {
            // Same fold guard as the connective collector: an override on a
            // folded-to-atom subterm re-spells the atom everywhere.
            if !override_would_hijack_atom(&ctx.terms, child, arg)
                && !overrides.contains_key(&child)
            {
                let echo = realify_real_context_numerals(ctx, arg, false, &mut Vec::new());
                overrides.insert(child, format_frontend_term(&echo));
            }
        }
        collect_deep_arith_surface_overrides(ctx, arg, overrides);
    }
}

/// Collect a compositional surface spelling for every binder-free node of an
/// authored array expression.
///
/// Array proof printers compare a printed `store`/`select` with the separately
/// printed base array, indices, and value that the strict checker certified.
/// The generic collector records a whole `store` but deliberately stops at
/// that theory boundary, which can leave its children canonical and make the
/// two renderings disagree. This narrow collector is used only after an exact
/// authored array premise has been authenticated; every inserted key is the
/// term obtained by re-elaborating that precise source subtree.
pub(super) fn collect_deep_array_surface_overrides(
    ctx: &mut Context,
    parsed: &FrontendTerm,
    overrides: &mut HashMap<TermId, String>,
) {
    collect_deep_array_surface_overrides_inner(ctx, parsed, overrides, &mut HashSet::default());
}

fn collect_deep_array_surface_overrides_inner(
    ctx: &mut Context,
    parsed: &FrontendTerm,
    overrides: &mut HashMap<TermId, String>,
    seen: &mut HashSet<TermId>,
) {
    let parsed = strip_frontend_annotations(parsed);
    if parsed_term_is_binder_free(parsed)
        && matches!(
            parsed,
            FrontendTerm::App(..) | FrontendTerm::IndexedApp(..) | FrontendTerm::QualifiedApp(..)
        )
    {
        if let Some(canonical) = ctx.elaborate_surface_subterm(parsed) {
            let echo = realify_real_context_numerals(ctx, parsed, false, &mut Vec::new());
            // Walk is preorder.  Preserve the outermost authenticated source
            // spelling when simplification collapses a parent and child onto
            // the same TermId (for example `(+ (- x 1) 0)` and `(- x 1)`).
            // The enclosing authored `store` contains that outer spelling,
            // so replacing it while descending would make a separately
            // printed certified ROW index disagree with the store operand.
            if seen.insert(canonical) {
                overrides.insert(canonical, format_frontend_term(&echo));
            }
        }
    }

    match parsed {
        FrontendTerm::App(_, args)
        | FrontendTerm::IndexedApp(_, _, args)
        | FrontendTerm::QualifiedApp(_, _, args) => {
            for arg in args {
                collect_deep_array_surface_overrides_inner(ctx, arg, overrides, seen);
            }
        }
        _ => {}
    }
}
pub(super) fn format_frontend_term(term: &FrontendTerm) -> String {
    format_frontend_term_impl(term, false)
}

/// Render an authored term without discarding SMT-LIB annotations.
pub(super) fn format_authored_frontend_term(term: &FrontendTerm) -> String {
    format_frontend_term_impl(term, true)
}

/// Render the exact surface substitution used by a `forall_inst` step.
///
/// Binder values are rendered through the same override-aware Alethe printer
/// as the step's `:args`.  The body walk accepts only the binder-free fragment
/// supported by the strict quantifier checker; nested binding constructs fail
/// closed.  This keeps a source spelling such as `(> x 0)` aligned with its
/// ground instance even though the internal canonical term is `(< 0 x)`.
pub(super) fn format_forall_instance_surface(
    terms: &ay_core::TermStore,
    parsed_forall: &FrontendTerm,
    values: &[TermId],
    overrides: &HashMap<TermId, String>,
) -> Option<String> {
    fn render(term: &FrontendTerm, substitution: &HashMap<String, String>) -> Option<String> {
        match strip_frontend_annotations(term) {
            FrontendTerm::Const(constant) => Some(format_frontend_constant(constant)),
            FrontendTerm::Symbol(name) => Some(
                substitution
                    .get(name)
                    .cloned()
                    .unwrap_or_else(|| format_frontend_symbol(name)),
            ),
            FrontendTerm::App(name, args) => {
                let rendered = args
                    .iter()
                    .map(|arg| render(arg, substitution))
                    .collect::<Option<Vec<_>>>()?;
                let head = format_frontend_symbol(name);
                Some(if rendered.is_empty() {
                    head
                } else {
                    format!("({head} {})", rendered.join(" "))
                })
            }
            FrontendTerm::IndexedApp(name, indices, args) => {
                let rendered = args
                    .iter()
                    .map(|arg| render(arg, substitution))
                    .collect::<Option<Vec<_>>>()?;
                let head = format_indexed_head(name, indices);
                Some(if rendered.is_empty() {
                    head
                } else {
                    format!("({head} {})", rendered.join(" "))
                })
            }
            FrontendTerm::QualifiedApp(identifier, sort, args) => {
                let rendered = args
                    .iter()
                    .map(|arg| render(arg, substitution))
                    .collect::<Option<Vec<_>>>()?;
                let head = format_qualified_head(identifier, sort);
                Some(if rendered.is_empty() {
                    head
                } else {
                    format!("({head} {})", rendered.join(" "))
                })
            }
            _ => None,
        }
    }

    let FrontendTerm::Forall(bindings, body) = strip_frontend_annotations(parsed_forall) else {
        return None;
    };
    if bindings.len() != values.len() {
        return None;
    }
    let mut substitution = HashMap::default();
    for ((name, _), &value) in bindings.iter().zip(values) {
        if substitution
            .insert(
                name.clone(),
                ay_proof::format_term_alethe_with_overrides(terms, value, overrides),
            )
            .is_some()
        {
            // Duplicate surface binders cannot be represented by a name-keyed
            // simultaneous substitution without choosing an identity.
            return None;
        }
    }
    render(body, &substitution)
}

fn format_frontend_term_impl(term: &FrontendTerm, preserve_annotations: bool) -> String {
    let term = if preserve_annotations {
        term
    } else {
        strip_frontend_annotations(term)
    };
    match term {
        FrontendTerm::Const(c) => format_frontend_constant(c),
        FrontendTerm::Symbol(name) => format_frontend_symbol(name),
        FrontendTerm::App(name, args) => {
            format_frontend_application(name, args, preserve_annotations)
        }
        FrontendTerm::IndexedApp(name, indices, args) => format_frontend_head_application(
            &format_indexed_head(name, indices),
            args,
            preserve_annotations,
        ),
        FrontendTerm::QualifiedApp(name, sort, args) => format_frontend_head_application(
            &format_qualified_head(name, sort),
            args,
            preserve_annotations,
        ),
        FrontendTerm::Let(bindings, body) => {
            format_frontend_let(bindings, body, preserve_annotations)
        }
        FrontendTerm::Forall(bindings, body) => {
            format_frontend_quantifier("forall", bindings, body, preserve_annotations)
        }
        FrontendTerm::Exists(bindings, body) => {
            format_frontend_quantifier("exists", bindings, body, preserve_annotations)
        }
        FrontendTerm::Lambda(bindings, body) => {
            format_frontend_quantifier("lambda", bindings, body, preserve_annotations)
        }
        FrontendTerm::Match(scrutinee, cases) => {
            format_frontend_match(scrutinee, cases, preserve_annotations)
        }
        FrontendTerm::Annotated(inner, attributes) => {
            let mut rendered = vec![format_frontend_term_impl(inner, true)];
            for (keyword, value) in attributes {
                rendered.push(keyword.clone());
                rendered.push(format_annotation_value(keyword, value));
            }
            format!("(! {})", rendered.join(" "))
        }
        other => unreachable!("unsupported frontend term in proof export override: {other:?}"),
    }
}

fn format_frontend_match(
    scrutinee: &FrontendTerm,
    cases: &[(FrontendMatchPattern, FrontendTerm)],
    preserve_annotations: bool,
) -> String {
    let rendered_cases: Vec<String> = cases
        .iter()
        .map(|(pattern, body)| {
            format!(
                "({} {})",
                format_frontend_match_pattern(pattern),
                format_frontend_term_impl(body, preserve_annotations)
            )
        })
        .collect();
    format!(
        "(match {} ({}))",
        format_frontend_term_impl(scrutinee, preserve_annotations),
        rendered_cases.join(" ")
    )
}

fn format_frontend_match_pattern(pattern: &FrontendMatchPattern) -> String {
    match pattern {
        FrontendMatchPattern::Symbol(name) => format_frontend_symbol(name),
        FrontendMatchPattern::Constructor(ctor, vars) => {
            let rendered_vars: Vec<String> =
                vars.iter().map(|v| format_frontend_symbol(v)).collect();
            if rendered_vars.is_empty() {
                format!("({})", format_frontend_symbol(ctor))
            } else {
                format!(
                    "({} {})",
                    format_frontend_symbol(ctor),
                    rendered_vars.join(" ")
                )
            }
        }
        other => unreachable!("unsupported frontend match pattern in proof export: {other:?}"),
    }
}

fn format_frontend_application(
    name: &str,
    args: &[FrontendTerm],
    preserve_annotations: bool,
) -> String {
    format_frontend_head_application(&format_frontend_symbol(name), args, preserve_annotations)
}

fn format_frontend_head_application(
    head: &str,
    args: &[FrontendTerm],
    preserve_annotations: bool,
) -> String {
    if args.is_empty() {
        head.to_string()
    } else {
        let rendered_args: Vec<String> = args
            .iter()
            .map(|term| format_frontend_term_impl(term, preserve_annotations))
            .collect();
        format!("({head} {})", rendered_args.join(" "))
    }
}

fn format_indexed_head(name: &str, indices: &[FrontendIndex]) -> String {
    let rendered_indices = indices
        .iter()
        .map(format_frontend_index)
        .collect::<Vec<_>>()
        .join(" ");
    format!("(_ {} {})", format_frontend_symbol(name), rendered_indices)
}

fn format_qualified_head(identifier: &FrontendQualifiedIdentifier, sort: &FrontendSort) -> String {
    let rendered_identifier = match identifier {
        FrontendQualifiedIdentifier::Symbol(name) => format_frontend_symbol(name),
        FrontendQualifiedIdentifier::Indexed(name, indices) => format_indexed_head(name, indices),
        _ => "<unsupported-qualified-identifier>".to_string(),
    };
    format!(
        "(as {} {})",
        rendered_identifier,
        format_frontend_sort(sort)
    )
}

fn format_frontend_let(
    bindings: &[(String, FrontendTerm)],
    body: &FrontendTerm,
    preserve_annotations: bool,
) -> String {
    let rendered_bindings: Vec<String> = bindings
        .iter()
        .map(|(name, value)| {
            format!(
                "({} {})",
                quote_symbol(name),
                format_frontend_term_impl(value, preserve_annotations)
            )
        })
        .collect();
    format!(
        "(let ({}) {})",
        rendered_bindings.join(" "),
        format_frontend_term_impl(body, preserve_annotations)
    )
}

fn format_frontend_quantifier(
    keyword: &str,
    bindings: &[(String, FrontendSort)],
    body: &FrontendTerm,
    preserve_annotations: bool,
) -> String {
    let rendered_bindings: Vec<String> = bindings
        .iter()
        .map(|(name, sort)| format!("({} {})", quote_symbol(name), format_frontend_sort(sort)))
        .collect();
    format!(
        "({keyword} ({}) {})",
        rendered_bindings.join(" "),
        format_frontend_term_impl(body, preserve_annotations)
    )
}

fn format_annotation_value(keyword: &str, value: &SExpr) -> String {
    if keyword == ":pattern" {
        if let SExpr::List(terms) = value {
            let rendered = terms
                .iter()
                .map(|term| {
                    FrontendTerm::from_sexp(term)
                        .map(|term| format_frontend_term_impl(&term, true))
                        .unwrap_or_else(|_| term.to_string())
                })
                .collect::<Vec<_>>();
            return format!("({})", rendered.join(" "));
        }
    } else if keyword == ":no-pattern" {
        if let Ok(term) = FrontendTerm::from_sexp(value) {
            return format_frontend_term_impl(&term, true);
        }
    }
    value.to_string()
}

fn format_frontend_symbol(name: &str) -> String {
    quote_symbol(name)
}

fn format_frontend_index(index: &FrontendIndex) -> String {
    match index {
        FrontendIndex::Numeral(value)
        | FrontendIndex::Decimal(value)
        | FrontendIndex::Hexadecimal(value)
        | FrontendIndex::Binary(value) => value.clone(),
        FrontendIndex::Symbol(value) => quote_symbol(value),
        _ => "<unsupported-index>".to_string(),
    }
}

fn format_frontend_sort(sort: &FrontendSort) -> String {
    match sort {
        FrontendSort::Simple(name) => format_frontend_symbol(name),
        FrontendSort::Parameterized(name, params) => {
            let rendered_params: Vec<String> = params.iter().map(format_frontend_sort).collect();
            format!(
                "({} {})",
                format_frontend_symbol(name),
                rendered_params.join(" ")
            )
        }
        FrontendSort::Indexed(name, indices) => format_indexed_head(name, indices),
        other => unreachable!("unsupported frontend sort in proof export override: {other:?}"),
    }
}

fn format_frontend_constant(constant: &FrontendConstant) -> String {
    match constant {
        FrontendConstant::True => "true".to_string(),
        FrontendConstant::False => "false".to_string(),
        FrontendConstant::Numeral(n)
        | FrontendConstant::Decimal(n)
        | FrontendConstant::Hexadecimal(n)
        | FrontendConstant::Binary(n) => n.clone(),
        FrontendConstant::String(s) => ay_core::string_literal(s),
        other => unreachable!("unsupported frontend constant in proof export override: {other:?}"),
    }
}

#[cfg(test)]
#[path = "proof_surface_syntax_tests.rs"]
mod tests;
