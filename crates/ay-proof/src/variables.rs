// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof variable and declaration collection.
//!
//! Walks proof structures to discover referenced variables, filter auxiliary
//! declarations, and collect free variables with proper binding-scope tracking.

// #8529/#8857: Use deterministic hash set for reproducible proof output.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{Proof, ProofStep, Sort, TermData, TermId, TermStore};
use std::collections::BTreeMap;

/// One surface symbol observed at two different sorts inside a single proof
/// (#A9, ad-hoc overloading).
///
/// SMT-LIB 2.6 §4.2.3 lets independent datatype declarations reuse a
/// constructor name, and §3.6.4 `(as f σ)` exists precisely to disambiguate
/// such overloads — `(declare-datatypes ((A 0) (B 0)) (((e) (f)) ((e) (g))))`
/// is well formed and AY solves it. Alethe/Carcara preambles, by contrast, are
/// a FLAT namespace of `(declare-fun <name> () <sort>)` lines with no overload
/// resolution, so there is no faithful rendering: emitting one declaration
/// would silently retype the other occurrence, and emitting both would be a
/// duplicate declaration the checker rejects.
///
/// The collectors therefore report the clash and the exporter DECLINES to
/// write a certificate (the caller keeps its verdict). Previously this was a
/// `debug_assert_eq!` that aborted the process with exit 101 *after* the
/// correct `unsat` had already been printed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SymbolSortConflict {
    /// The surface symbol carrying more than one sort.
    pub name: String,
    /// Sort recorded for the first occurrence encountered.
    pub first: Sort,
    /// Conflicting sort of a later occurrence.
    pub second: Sort,
}

/// Record `name: sort`, reporting a clash instead of silently keeping one sort.
fn record_symbol_sort(
    vars: &mut BTreeMap<String, Sort>,
    name: &str,
    sort: Sort,
) -> Result<(), SymbolSortConflict> {
    match vars.get(name) {
        Some(existing) if *existing != sort => Err(SymbolSortConflict {
            name: name.to_string(),
            first: existing.clone(),
            second: sort,
        }),
        Some(_) => Ok(()),
        None => {
            vars.insert(name.to_string(), sort);
            Ok(())
        }
    }
}

/// Collect all variables referenced in proof terms, sorted by name.
///
/// Walks all terms in the proof recursively to find `Var` nodes,
/// including Skolem variables introduced by theory solvers (e.g.,
/// `_mod_q_*`, `_div_r_*`) that are not registered in `TermStore::names`.
///
/// # Errors
///
/// Returns [`SymbolSortConflict`] when one surface symbol appears at two
/// different sorts — see that type for why the proof is then unrenderable.
pub(crate) fn collect_proof_variables(
    proof: &Proof,
    terms: &TermStore,
) -> Result<Vec<(String, Sort)>, SymbolSortConflict> {
    let mut vars: BTreeMap<String, Sort> = BTreeMap::new();
    let mut visited: HashSet<TermId> = HashSet::default();

    for step in &proof.steps {
        match step {
            ProofStep::Assume(t) => collect_term_vars(*t, terms, &mut vars, &mut visited)?,
            ProofStep::Resolution { clause, pivot, .. } => {
                for t in clause {
                    collect_term_vars(*t, terms, &mut vars, &mut visited)?;
                }
                collect_term_vars(*pivot, terms, &mut vars, &mut visited)?;
            }
            ProofStep::TheoryLemma { clause, .. } => {
                for t in clause {
                    collect_term_vars(*t, terms, &mut vars, &mut visited)?;
                }
            }
            ProofStep::Step { clause, args, .. } => {
                for t in clause {
                    collect_term_vars(*t, terms, &mut vars, &mut visited)?;
                }
                for t in args {
                    collect_term_vars(*t, terms, &mut vars, &mut visited)?;
                }
            }
            ProofStep::Anchor { .. } => {}
            _ => unreachable!("unexpected ProofStep variant"),
        }
    }

    Ok(vars.into_iter().collect())
}

/// Recursively collect variable names and sorts from a term.
fn collect_term_vars(
    term_id: TermId,
    terms: &TermStore,
    vars: &mut BTreeMap<String, Sort>,
    visited: &mut HashSet<TermId>,
) -> Result<(), SymbolSortConflict> {
    if !visited.insert(term_id) {
        return Ok(());
    }
    let term = terms.get(term_id);
    match term {
        TermData::Var(name, _) => {
            let sort = terms.sort(term_id).clone();
            record_symbol_sort(vars, name, sort)?;
        }
        TermData::Const(_) => {}
        TermData::Not(t) => collect_term_vars(*t, terms, vars, visited)?,
        TermData::Ite(c, t, e) => {
            collect_term_vars(*c, terms, vars, visited)?;
            collect_term_vars(*t, terms, vars, visited)?;
            collect_term_vars(*e, terms, vars, visited)?;
        }
        TermData::App(_, args) => {
            for a in args {
                collect_term_vars(*a, terms, vars, visited)?;
            }
        }
        TermData::Let(bindings, body) => {
            for (_, t) in bindings {
                collect_term_vars(*t, terms, vars, visited)?;
            }
            collect_term_vars(*body, terms, vars, visited)?;
        }
        TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
            collect_term_vars(*body, terms, vars, visited)?;
            for trigger_set in triggers {
                for t in trigger_set {
                    collect_term_vars(*t, terms, vars, visited)?;
                }
            }
        }
        _ => unreachable!("unexpected TermData variant"),
    }
    Ok(())
}

/// Collect auxiliary proof declarations that are not in the problem scope.
///
/// # Errors
///
/// Returns [`SymbolSortConflict`] when one surface symbol appears at two
/// different sorts — see that type for why the proof is then unrenderable.
pub(crate) fn collect_auxiliary_proof_declarations(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
) -> Result<Vec<(String, Sort)>, SymbolSortConflict> {
    let proof_free_vars = collect_free_vars_from_roots(terms, collect_proof_term_roots(proof))?;
    let problem_free_vars =
        collect_free_vars_from_roots(terms, problem_assertions.iter().copied())?;

    // A symbol that is FREE in the proof and NOT in the problem scope has no
    // declaration anywhere the checker can see: the problem file does not
    // declare it, so the proof document must. That is the whole obligation —
    // there is no second condition to test.
    //
    // This used to additionally require the name to match one of six hard-coded
    // prefixes (`_mod_`, `_div_`, `__ay_`, `_sk_`, `sk_`, `skolem`). Every
    // internal symbol family outside that list was silently DROPPED from the
    // preamble, producing a document no checker can even parse. Measured on
    // QF_DT/20230720-blocksworld: the eager datatype engine's field-split
    // symbols (`s_tmp___!left`, 281 occurrences in one proof) fall through, and
    // carcara stops at
    //   `parser error: identifier 's_tmp___!left' is not defined (line 4)`
    // before checking a single rule. The `reduce-args` tactic's per-constant
    // `f!k` names are in the same position.
    //
    // Nothing is lost by dropping the prefix test. Bound variables are already
    // excluded by the binder tracking in `collect_free_vars_in_term`, and
    // Skolem witnesses rendered as Alethe `choice` terms are skipped at the
    // emission site (`is_skolem_witness_name`), which is where that decision
    // belongs — the printer, not this collector, knows what it resugared away.
    Ok(proof_free_vars
        .into_iter()
        .filter(|(name, _)| !problem_free_vars.contains_key(name))
        .collect())
}

/// Free variable names of `roots`, with their sorts discarded.
///
/// Used by the Skolem-`choice` preamble guard: a `define-fun` may only be
/// emitted when every free symbol of its body is one an external checker can
/// already resolve. Sorts are irrelevant to that question, and the caller has
/// nothing to do with a clash, so a [`SymbolSortConflict`] is reported as "no
/// resolvable symbols" — the guard then withholds every definition, which is
/// the fail-closed direction.
pub(crate) fn free_var_names(
    terms: &TermStore,
    roots: impl IntoIterator<Item = TermId>,
) -> HashSet<String> {
    collect_free_vars_from_roots(terms, roots)
        .map(|vars| vars.into_keys().collect())
        .unwrap_or_default()
}

/// Names of every FUNCTION symbol applied anywhere under `roots`.
///
/// [`collect_free_vars_from_roots`] deliberately walks only `Var` nodes, so an
/// application head — `P` in `(P x)` — is invisible to it. That is right for
/// the declaration collector (AY never declared function symbols) but wrong for
/// building a checker scope: carcara resolves `P` against the problem file, and
/// a scope missing it would reject a perfectly good `define-fun` body.
///
/// Built-in operators come back too (`=`, `+`, `select`, ...). That is
/// harmless and deliberate: [`ProblemScope`](crate::ProblemScope) is documented
/// to err toward "declared", because the dangerous direction is a MISSING
/// declaration causing a false reject.
pub(crate) fn application_symbol_names(
    terms: &TermStore,
    roots: impl IntoIterator<Item = TermId>,
) -> HashSet<String> {
    let mut names: HashSet<String> = HashSet::default();
    let mut visited: HashSet<TermId> = HashSet::default();
    let mut stack: Vec<TermId> = roots.into_iter().collect();
    while let Some(term_id) = stack.pop() {
        if !visited.insert(term_id) {
            continue;
        }
        match terms.get(term_id) {
            TermData::Var(..) | TermData::Const(_) => {}
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(cond, then_branch, else_branch) => {
                stack.push(*cond);
                stack.push(*then_branch);
                stack.push(*else_branch);
            }
            TermData::App(symbol, args) => {
                match symbol {
                    ay_core::Symbol::Named(name) | ay_core::Symbol::Indexed(name, _) => {
                        names.insert(name.clone());
                    }
                    // `Symbol` is `#[non_exhaustive]`. An unrecognised head
                    // simply contributes no name; the preamble check then
                    // withholds any definition that mentions it, which is the
                    // fail-closed direction.
                    _ => {}
                }
                stack.extend(args.iter().copied());
            }
            TermData::Let(bindings, body) => {
                for (name, value) in bindings {
                    // A `let`-bound name is resolvable wherever it is in scope.
                    names.insert(name.clone());
                    stack.push(*value);
                }
                stack.push(*body);
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                stack.push(*body);
                for trigger_set in triggers {
                    stack.extend(trigger_set.iter().copied());
                }
            }
            _ => {}
        }
    }
    names
}

fn collect_proof_term_roots(proof: &Proof) -> Vec<TermId> {
    let mut roots = Vec::new();
    for step in &proof.steps {
        match step {
            ProofStep::Assume(term) => roots.push(*term),
            ProofStep::Resolution { clause, pivot, .. } => {
                roots.extend(clause.iter().copied());
                roots.push(*pivot);
            }
            ProofStep::TheoryLemma { clause, .. } => roots.extend(clause.iter().copied()),
            ProofStep::Step { clause, args, .. } => {
                roots.extend(clause.iter().copied());
                roots.extend(args.iter().copied());
            }
            ProofStep::Anchor { .. } => {}
            _ => unreachable!("unexpected ProofStep variant"),
        }
    }
    roots
}

/// The problem's declared symbol names, as the Alethe exporter sees them.
///
/// This is exactly the set `collect_auxiliary_proof_declarations` treats as
/// "already declared elsewhere", so a symbol the exporter chose NOT to declare
/// is in here by construction. The round-trip self-check uses it as the
/// in-process fallback scope when the problem text is not on disk (stdin).
///
/// Returns an empty set on a sort conflict: the exporter declines to emit a
/// certificate at all in that case, so there is nothing to check.
pub(crate) fn problem_scope_symbol_names(
    terms: &TermStore,
    problem_assertions: &[TermId],
) -> Vec<String> {
    collect_free_vars_from_roots(terms, problem_assertions.iter().copied())
        .map(|vars| vars.into_keys().collect())
        .unwrap_or_default()
}

fn collect_free_vars_from_roots(
    terms: &TermStore,
    roots: impl IntoIterator<Item = TermId>,
) -> Result<BTreeMap<String, Sort>, SymbolSortConflict> {
    let mut free_vars = BTreeMap::new();
    let mut bound_names = Vec::new();
    // Terms are a DAG and proof roots repeat heavily (every literal of every
    // clause of every step); without memoization this walk is superquadratic
    // in proof size (the PEQ Alethe-export hotspot). `visited` marks terms
    // already walked under an EMPTY binder context — there the free-var
    // contribution is context-independent and `free_vars` only accumulates,
    // so skipping repeats collects exactly the same map.
    let mut visited: HashSet<TermId> = HashSet::default();
    for root in roots {
        collect_free_vars_in_term(terms, root, &mut bound_names, &mut free_vars, &mut visited)?;
    }
    Ok(free_vars)
}

fn collect_free_vars_in_term(
    terms: &TermStore,
    term_id: TermId,
    bound_names: &mut Vec<String>,
    free_vars: &mut BTreeMap<String, Sort>,
    visited: &mut HashSet<TermId>,
) -> Result<(), SymbolSortConflict> {
    // Memoize only outside binders: under a non-empty bound-name context the
    // same term can contribute different free variables.
    let memoize = bound_names.is_empty();
    if memoize && !visited.insert(term_id) {
        return Ok(());
    }
    match terms.get(term_id) {
        TermData::Var(name, _) => {
            if !bound_names.iter().any(|bound| bound == name) {
                // #A9: a surface name carrying two sorts is ad-hoc overloading,
                // not a solver bug — report it so the exporter can decline.
                let sort = terms.sort(term_id).clone();
                record_symbol_sort(free_vars, name, sort)?;
            }
        }
        TermData::Const(_) => {}
        TermData::Not(inner) => {
            collect_free_vars_in_term(terms, *inner, bound_names, free_vars, visited)?;
        }
        TermData::Ite(cond, then_term, else_term) => {
            collect_free_vars_in_term(terms, *cond, bound_names, free_vars, visited)?;
            collect_free_vars_in_term(terms, *then_term, bound_names, free_vars, visited)?;
            collect_free_vars_in_term(terms, *else_term, bound_names, free_vars, visited)?;
        }
        TermData::App(_, args) => {
            for &arg in args {
                collect_free_vars_in_term(terms, arg, bound_names, free_vars, visited)?;
            }
        }
        TermData::Let(bindings, body) => {
            for (_, binding_value) in bindings {
                collect_free_vars_in_term(terms, *binding_value, bound_names, free_vars, visited)?;
            }
            let bound_base = bound_names.len();
            for (name, _) in bindings {
                bound_names.push(name.clone());
            }
            // A propagated conflict abandons the entire walk (the `?` unwinds
            // out of `collect_free_vars_from_roots`), so the binder context
            // only has to be restored on the success path.
            collect_free_vars_in_term(terms, *body, bound_names, free_vars, visited)?;
            bound_names.truncate(bound_base);
        }
        TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
            let bound_base = bound_names.len();
            for (name, _) in vars {
                bound_names.push(name.clone());
            }
            collect_free_vars_in_term(terms, *body, bound_names, free_vars, visited)?;
            for trigger_set in triggers {
                for &trigger_term in trigger_set {
                    collect_free_vars_in_term(
                        terms,
                        trigger_term,
                        bound_names,
                        free_vars,
                        visited,
                    )?;
                }
            }
            bound_names.truncate(bound_base);
        }
        _ => unreachable!("unexpected TermData variant"),
    }
    Ok(())
}
