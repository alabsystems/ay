// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};

/// Red zone size for `stacker::maybe_grow` in substitution recursion (#8414).
///
/// Quantifier instantiation on datatype-heavy problems can produce deeply nested
/// terms that overflow the default thread stack during substitution.
const SUBST_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack segment size allocated by stacker for substitution recursion.
const SUBST_STACK_SIZE: usize = 1024 * 1024;

/// Collect all free variable names in a term, respecting binders.
///
/// Traverses the term DAG, collecting `Var` names while tracking variables
/// that are bound by enclosing `Forall`/`Exists`/`Let` binders.
///
/// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
pub(super) fn collect_free_var_names(
    terms: &TermStore,
    term: TermId,
    bound: &HashSet<String>,
    out: &mut HashSet<String>,
) {
    stacker::maybe_grow(SUBST_STACK_RED_ZONE, SUBST_STACK_SIZE, || {
        match terms.get(term) {
            TermData::Var(name, _) if !bound.contains(name) => {
                out.insert(name.clone());
            }
            TermData::Const(_) => {}
            TermData::App(_, args) => {
                for &arg in args {
                    collect_free_var_names(terms, arg, bound, out);
                }
            }
            TermData::Not(inner) => {
                collect_free_var_names(terms, *inner, bound, out);
            }
            TermData::Ite(c, t, e) => {
                collect_free_var_names(terms, *c, bound, out);
                collect_free_var_names(terms, *t, bound, out);
                collect_free_var_names(terms, *e, bound, out);
            }
            TermData::Let(bindings, body) => {
                for (_, val) in bindings {
                    collect_free_var_names(terms, *val, bound, out);
                }
                let mut inner_bound = bound.clone();
                for (name, _) in bindings {
                    inner_bound.insert(name.clone());
                }
                collect_free_var_names(terms, *body, &inner_bound, out);
            }
            TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                let mut inner_bound = bound.clone();
                for (name, _) in vars {
                    inner_bound.insert(name.clone());
                }
                collect_free_var_names(terms, *body, &inner_bound, out);
                for set in triggers {
                    for &t in set {
                        collect_free_var_names(terms, t, &inner_bound, out);
                    }
                }
            }
            _ => {}
        }
    }) // stacker::maybe_grow
}

/// Build a capture-avoiding substitution for a quantifier.
///
/// Removes bound variable names from `subst` keys, AND checks if any substitution
/// value contains a free variable matching a bound name. If so, alpha-renames the
/// conflicting bound variable to a fresh name.
///
/// Returns `None` if the resulting substitution is empty (no changes needed).
/// When alpha-renaming occurs, `vars` is updated in place with the new names
/// and the returned substitution includes the rename mappings.
fn capture_avoiding_subst(
    terms: &mut TermStore,
    vars: &mut [(String, Sort)],
    subst: &HashMap<String, TermId>,
) -> Option<HashMap<String, TermId>> {
    // Step 1: remove bound variable names from substitution keys
    let mut inner = subst.clone();
    for (name, _) in vars.iter() {
        inner.remove(name);
    }
    if inner.is_empty() {
        return None;
    }

    // Step 2: collect free variable names in all substitution values
    let bound_set = HashSet::default();
    let mut free_in_values = HashSet::default();
    for (_, &val) in inner.iter() {
        collect_free_var_names(terms, val, &bound_set, &mut free_in_values);
    }

    // Step 3: check for capture conflicts and alpha-rename if needed
    for (name, sort) in vars.iter_mut() {
        if free_in_values.contains(name.as_str()) {
            // This bound variable name conflicts with a free var in a substitution value.
            // Alpha-rename: generate a fresh variable name.
            let fresh_var = terms.mk_fresh_var(name, sort.clone());
            let fresh_name = match terms.get(fresh_var) {
                TermData::Var(n, _) => n.clone(),
                _ => {
                    // Production soundness gate: mk_fresh_var should always
                    // return a Var term. If not, skip alpha-renaming entirely
                    // to avoid producing a malformed substitution. This makes
                    // the instantiation incomplete (may miss some matches) but
                    // preserves soundness.
                    safe_eprintln!(
                        "BUG: mk_fresh_var did not return Var in capture_avoiding_subst — skipping substitution"
                    );
                    return None;
                }
            };
            // Add a rename mapping: old bound name -> fresh variable term
            inner.insert(name.clone(), fresh_var);
            // Update the bound variable list
            *name = fresh_name;
        }
    }

    Some(inner)
}

/// Apply substitution to a quantifier body and triggers, returning (new_body, new_triggers).
fn subst_quantifier_parts(
    terms: &mut TermStore,
    body: TermId,
    triggers: &[Vec<TermId>],
    subst: &HashMap<String, TermId>,
) -> (TermId, Vec<Vec<TermId>>) {
    let new_body = subst_vars(terms, body, subst);
    let new_triggers = triggers
        .iter()
        .map(|set| set.iter().map(|&t| subst_vars(terms, t, subst)).collect())
        .collect();
    (new_body, new_triggers)
}

/// Substitute into a Let binding with capture-avoidance.
fn subst_let(
    terms: &mut TermStore,
    term: TermId,
    bindings: &[(String, TermId)],
    body: TermId,
    subst: &HashMap<String, TermId>,
) -> TermId {
    // Substitute into binding values (these are outside the let scope)
    let mut new_bindings: Vec<(String, TermId)> = bindings
        .iter()
        .map(|(name, val)| (name.clone(), subst_vars(terms, *val, subst)))
        .collect();

    // Build inner substitution: remove let-bound names from keys
    let mut inner_subst = subst.clone();
    for (name, _) in bindings {
        inner_subst.remove(name);
    }

    if !inner_subst.is_empty() {
        // Check for variable capture: free vars in substitution values
        // might be captured by let-bound names
        let bound_set = HashSet::default();
        let mut free_in_values = HashSet::default();
        for (_, &val) in inner_subst.iter() {
            collect_free_var_names(terms, val, &bound_set, &mut free_in_values);
        }

        // Alpha-rename conflicting let-bound names
        for (name, val) in new_bindings.iter_mut() {
            if free_in_values.contains(name.as_str()) {
                let sort = terms.sort(*val).clone();
                let fresh_var = terms.mk_fresh_var(name, sort);
                let fresh_name = match terms.get(fresh_var) {
                    TermData::Var(n, _) => n.clone(),
                    _ => {
                        // Production soundness gate: mk_fresh_var should always
                        // return a Var term. If not, skip this let-binding's
                        // alpha-rename. The substitution will be incomplete but
                        // sound (may produce a conservatively larger term).
                        safe_eprintln!(
                            "BUG: mk_fresh_var did not return Var in subst_let — skipping alpha-rename"
                        );
                        continue;
                    }
                };
                inner_subst.insert(name.clone(), fresh_var);
                *name = fresh_name;
            }
        }
    }

    let new_body = subst_vars(terms, body, &inner_subst);
    let changed = new_bindings
        .iter()
        .zip(bindings.iter())
        .any(|(a, b)| a.0 != b.0 || a.1 != b.1)
        || new_body != body;
    if changed {
        inline_let_bindings(terms, &new_bindings, new_body)
    } else {
        term
    }
}

/// Inline a parallel let-binding into its body.
///
/// E-matching-generated instantiations feed directly into the solve pipeline,
/// where surviving `let` nodes are treated conservatively or opaquely by some
/// downstream components. Inline changed lets here so quantifier instances stay
/// in the same let-free shape the frontend normally produces.
fn inline_let_bindings(
    terms: &mut TermStore,
    bindings: &[(String, TermId)],
    body: TermId,
) -> TermId {
    if bindings.is_empty() {
        return body;
    }

    let binding_subst: HashMap<String, TermId> = bindings
        .iter()
        .map(|(name, value)| (name.clone(), *value))
        .collect();
    subst_vars(terms, body, &binding_subst)
}

/// Substitute variables in a term according to a substitution map.
///
/// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
pub(crate) fn subst_vars(
    terms: &mut TermStore,
    term: TermId,
    subst: &HashMap<String, TermId>,
) -> TermId {
    stacker::maybe_grow(SUBST_STACK_RED_ZONE, SUBST_STACK_SIZE, || {
        match terms.get(term).clone() {
            TermData::Var(name, _) => *subst.get(&name).unwrap_or(&term),
            TermData::Const(_) => term,
            TermData::App(sym, args) => {
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&arg| subst_vars(terms, arg, subst))
                    .collect();
                if new_args == args {
                    term
                } else {
                    mk_app_simplified(terms, &sym, new_args, term)
                }
            }
            TermData::Not(inner) => {
                let new_inner = subst_vars(terms, inner, subst);
                if new_inner == inner {
                    term
                } else {
                    terms.mk_not(new_inner)
                }
            }
            TermData::Ite(c, t, e) => {
                let nc = subst_vars(terms, c, subst);
                let nt = subst_vars(terms, t, subst);
                let ne = subst_vars(terms, e, subst);
                if nc == c && nt == t && ne == e {
                    term
                } else {
                    terms.mk_ite(nc, nt, ne)
                }
            }
            TermData::Let(bindings, body) => subst_let(terms, term, &bindings, body, subst),
            TermData::Forall(vars, body, triggers) => {
                let mut vars = vars;
                let Some(inner) = capture_avoiding_subst(terms, &mut vars, subst) else {
                    return term;
                };
                let (nb, nt) = subst_quantifier_parts(terms, body, &triggers, &inner);
                if nb == body && nt == triggers {
                    term
                } else {
                    terms.mk_forall_with_triggers(vars, nb, nt)
                }
            }
            TermData::Exists(vars, body, triggers) => {
                let mut vars = vars;
                let Some(inner) = capture_avoiding_subst(terms, &mut vars, subst) else {
                    return term;
                };
                let (nb, nt) = subst_quantifier_parts(terms, body, &triggers, &inner);
                if nb == body && nt == triggers {
                    term
                } else {
                    terms.mk_exists_with_triggers(vars, nb, nt)
                }
            }
            // Future TermData variants: return term unchanged (identity substitution).
            _ => term,
        }
    }) // stacker::maybe_grow
}

/// Substitute variables without applying any semantic simplification.
///
/// This is the certificate-producing counterpart of [`subst_vars`]:
/// applications, negations, and ITEs are rebuilt with raw constructors so an
/// instance such as `(< 0 0)` cannot collapse to `false` before the checker
/// compares it with the authored quantifier body.
///
/// The historical `_qf` name is retained for call-site stability, but the
/// strict checker now accepts capture-safe substitution beneath preserved
/// `forall`/`exists` binders. Mirror that exact lane here: nested binding lists
/// and trigger-group structure are preserved, shadowed names are blocked, and a
/// replacement which contains any source/nested binder name (or another binder
/// or let) fails closed. Lets in the authored body remain unsupported, exactly
/// like the checker.
pub(crate) fn subst_vars_exact_qf(
    terms: &mut TermStore,
    term: TermId,
    subst: &HashMap<String, TermId>,
) -> Option<TermId> {
    const WORK_LIMIT: usize = 100_000;

    fn nested_binder_names(
        terms: &TermStore,
        root: TermId,
        work: &mut usize,
    ) -> Option<HashSet<String>> {
        let mut names = HashSet::default();
        let mut seen = HashSet::default();
        let mut stack = vec![root];
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            if *work >= WORK_LIMIT {
                return None;
            }
            *work += 1;
            match terms.get(term) {
                TermData::Forall(bindings, body, triggers)
                | TermData::Exists(bindings, body, triggers) => {
                    names.extend(bindings.iter().map(|(name, _)| name.clone()));
                    stack.push(*body);
                    stack.extend(triggers.iter().flatten().copied());
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(condition, then_branch, else_branch) => {
                    stack.extend([*condition, *then_branch, *else_branch]);
                }
                TermData::Let(..) => return None,
                _ => {}
            }
        }
        Some(names)
    }

    fn replacement_is_ground_for(
        terms: &TermStore,
        root: TermId,
        source_binders: &HashSet<String>,
        work: &mut usize,
    ) -> Option<bool> {
        let mut seen = HashSet::default();
        let mut stack = vec![root];
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            if *work >= WORK_LIMIT {
                return None;
            }
            *work += 1;
            match terms.get(term) {
                TermData::Var(name, _) if source_binders.contains(name) => return Some(false),
                TermData::Var(..) | TermData::Const(..) => {}
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(condition, then_branch, else_branch) => {
                    stack.extend([*condition, *then_branch, *else_branch]);
                }
                TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..) => {
                    return Some(false);
                }
                _ => return Some(false),
            }
        }
        Some(true)
    }

    fn replacement_avoids_nested_names(
        terms: &TermStore,
        root: TermId,
        nested_names: &HashSet<String>,
        work: &mut usize,
    ) -> Option<bool> {
        let mut seen = HashSet::default();
        let mut stack = vec![root];
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            if *work >= WORK_LIMIT {
                return None;
            }
            *work += 1;
            match terms.get(term) {
                TermData::Var(name, _) if nested_names.contains(name) => return Some(false),
                TermData::Var(..) | TermData::Const(..) => {}
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(condition, then_branch, else_branch) => {
                    stack.extend([*condition, *then_branch, *else_branch]);
                }
                TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..) => {
                    return Some(false);
                }
                _ => return Some(false),
            }
        }
        Some(true)
    }

    fn visit(
        terms: &mut TermStore,
        term: TermId,
        subst: &HashMap<String, TermId>,
        blocked: &HashSet<String>,
        matched_var_ids: &mut HashMap<String, u32>,
        work: &mut usize,
    ) -> Option<TermId> {
        // Deliberately do not memoize this exact walk. The strict checker visits
        // every structural pattern/instance occurrence, including repeated DAG
        // edges; producer memoization could otherwise emit a proof which later
        // exceeds the checker's shared work limit.
        if *work >= WORK_LIMIT {
            return None;
        }
        *work += 1;
        stacker::maybe_grow(SUBST_STACK_RED_ZONE, SUBST_STACK_SIZE, || {
            match terms.get(term).clone() {
                TermData::Var(name, id) => {
                    if blocked.contains(&name) {
                        return Some(term);
                    }
                    let Some(&replacement) = subst.get(&name) else {
                        return Some(term);
                    };
                    if terms.sort(term) != terms.sort(replacement) {
                        return None;
                    }
                    match matched_var_ids.get(&name) {
                        Some(&seen) if seen != id => return None,
                        Some(_) => {}
                        None => {
                            matched_var_ids.insert(name, id);
                        }
                    }
                    Some(replacement)
                }
                TermData::Const(_) => Some(term),
                TermData::App(symbol, args) => {
                    let sort = terms.sort(term).clone();
                    let rewritten: Vec<TermId> = args
                        .iter()
                        .copied()
                        .map(|arg| visit(terms, arg, subst, blocked, matched_var_ids, work))
                        .collect::<Option<_>>()?;
                    if rewritten == args {
                        Some(term)
                    } else {
                        Some(terms.mk_app(symbol, rewritten, sort))
                    }
                }
                TermData::Not(inner) => {
                    let rewritten = visit(terms, inner, subst, blocked, matched_var_ids, work)?;
                    if rewritten == inner {
                        Some(term)
                    } else {
                        Some(terms.mk_not_raw(rewritten))
                    }
                }
                TermData::Ite(condition, then_branch, else_branch) => {
                    let rewritten_condition =
                        visit(terms, condition, subst, blocked, matched_var_ids, work)?;
                    let rewritten_then =
                        visit(terms, then_branch, subst, blocked, matched_var_ids, work)?;
                    let rewritten_else =
                        visit(terms, else_branch, subst, blocked, matched_var_ids, work)?;
                    if (rewritten_condition, rewritten_then, rewritten_else)
                        == (condition, then_branch, else_branch)
                    {
                        Some(term)
                    } else {
                        Some(terms.mk_ite_raw(rewritten_condition, rewritten_then, rewritten_else))
                    }
                }
                TermData::Forall(bindings, body, triggers) => {
                    let mut nested_blocked = blocked.clone();
                    nested_blocked.extend(bindings.iter().map(|(name, _)| name.clone()));
                    let rewritten_body =
                        visit(terms, body, subst, &nested_blocked, matched_var_ids, work)?;
                    let rewritten_triggers: Vec<Vec<TermId>> = triggers
                        .iter()
                        .map(|group| {
                            group
                                .iter()
                                .copied()
                                .map(|trigger| {
                                    visit(
                                        terms,
                                        trigger,
                                        subst,
                                        &nested_blocked,
                                        matched_var_ids,
                                        work,
                                    )
                                })
                                .collect::<Option<Vec<_>>>()
                        })
                        .collect::<Option<_>>()?;
                    if rewritten_body == body && rewritten_triggers == triggers {
                        Some(term)
                    } else {
                        Some(terms.mk_forall_with_triggers(
                            bindings,
                            rewritten_body,
                            rewritten_triggers,
                        ))
                    }
                }
                TermData::Exists(bindings, body, triggers) => {
                    let mut nested_blocked = blocked.clone();
                    nested_blocked.extend(bindings.iter().map(|(name, _)| name.clone()));
                    let rewritten_body =
                        visit(terms, body, subst, &nested_blocked, matched_var_ids, work)?;
                    let rewritten_triggers: Vec<Vec<TermId>> = triggers
                        .iter()
                        .map(|group| {
                            group
                                .iter()
                                .copied()
                                .map(|trigger| {
                                    visit(
                                        terms,
                                        trigger,
                                        subst,
                                        &nested_blocked,
                                        matched_var_ids,
                                        work,
                                    )
                                })
                                .collect::<Option<Vec<_>>>()
                        })
                        .collect::<Option<_>>()?;
                    if rewritten_body == body && rewritten_triggers == triggers {
                        Some(term)
                    } else {
                        Some(terms.mk_exists_with_triggers(
                            bindings,
                            rewritten_body,
                            rewritten_triggers,
                        ))
                    }
                }
                TermData::Let(..) => None,
                _ => None,
            }
        })
    }

    let mut work = 0usize;
    let nested_names = nested_binder_names(terms, term, &mut work)?;
    let source_binders = subst.keys().cloned().collect::<HashSet<_>>();
    for &replacement in subst.values() {
        // Keep the two scans separate and in checker order. Besides checking
        // the same predicates, this ensures the producer consumes at least the
        // same shared work budget as `forall_inst` validation.
        if replacement_is_ground_for(terms, replacement, &source_binders, &mut work) != Some(true)
            || replacement_avoids_nested_names(terms, replacement, &nested_names, &mut work)
                != Some(true)
        {
            return None;
        }
    }
    let mut matched_var_ids = HashMap::default();
    let blocked = HashSet::default();
    visit(
        terms,
        term,
        subst,
        &blocked,
        &mut matched_var_ids,
        &mut work,
    )
}

/// Construct an App term using simplifying constructors where available.
pub(crate) fn mk_app_simplified(
    terms: &mut TermStore,
    sym: &Symbol,
    args: Vec<TermId>,
    original: TermId,
) -> TermId {
    let name = sym.name();
    match name {
        // BV binary operations with constant folding
        "bvadd" if args.len() == 2 => terms.mk_bvadd(args),
        "bvsub" if args.len() == 2 => terms.mk_bvsub(args),
        "bvmul" if args.len() == 2 => terms.mk_bvmul(args),
        "bvand" if args.len() == 2 => terms.mk_bvand(args),
        "bvor" if args.len() == 2 => terms.mk_bvor(args),
        "bvxor" if args.len() == 2 => terms.mk_bvxor(args),
        "bvshl" if args.len() == 2 => terms.mk_bvshl(args),
        "bvlshr" if args.len() == 2 => terms.mk_bvlshr(args),
        "bvashr" if args.len() == 2 => terms.mk_bvashr(args),
        "bvudiv" if args.len() == 2 => terms.mk_bvudiv(args),
        "bvurem" if args.len() == 2 => terms.mk_bvurem(args),
        "bvsdiv" if args.len() == 2 => terms.mk_bvsdiv(args),
        "bvsrem" if args.len() == 2 => terms.mk_bvsrem(args),
        "bvconcat" if args.len() == 2 => terms.mk_bvconcat(args),
        // BV unary operations
        "bvnot" if args.len() == 1 => terms.mk_bvnot(args[0]),
        "bvneg" if args.len() == 1 => terms.mk_bvneg(args[0]),
        // Indexed BV operations
        "zero_extend" if args.len() == 1 => {
            if let Symbol::Indexed(_, indices) = sym {
                if let Some(&i) = indices.first() {
                    return terms.mk_bvzero_extend(i, args[0]);
                }
            }
            let sort = terms.sort(original).clone();
            terms.mk_app(sym.clone(), args, sort)
        }
        "sign_extend" if args.len() == 1 => {
            if let Symbol::Indexed(_, indices) = sym {
                if let Some(&i) = indices.first() {
                    return terms.mk_bvsign_extend(i, args[0]);
                }
            }
            let sort = terms.sort(original).clone();
            terms.mk_app(sym.clone(), args, sort)
        }
        // Array operations
        "select" if args.len() == 2 => terms.mk_select(args[0], args[1]),
        "store" if args.len() == 3 => terms.mk_store(args[0], args[1], args[2]),
        // Arithmetic operations with constant folding (#2862).
        // Without this, E-matching instantiation of (+ x 1) with x=5 produces
        // the unsimplified term (+ 5 1) instead of 6, which the DPLL(T) solver
        // may fail to recognize as equal to 6 in combined theory reasoning.
        "+" => terms.mk_add(args),
        "-" if args.len() == 1 => terms.mk_neg(args[0]),
        "-" => terms.mk_sub(args),
        "*" => terms.mk_mul(args),
        "<=" if args.len() == 2 => terms.mk_le(args[0], args[1]),
        "<" if args.len() == 2 => terms.mk_lt(args[0], args[1]),
        ">=" if args.len() == 2 => terms.mk_ge(args[0], args[1]),
        ">" if args.len() == 2 => terms.mk_gt(args[0], args[1]),
        // Equality
        "=" if args.len() == 2 => terms.mk_eq_coerce(args[0], args[1]),
        // Fallback
        _ => {
            let sort = terms.sort(original).clone();
            terms.mk_app(sym.clone(), args, sort)
        }
    }
}

/// Instantiate a quantifier body with the given binding.
/// `actual_var_names[i]` is the real name of the i-th bound variable in the body.
pub(super) fn instantiate_body(
    terms: &mut TermStore,
    body: TermId,
    actual_var_names: &[String],
    binding: &[TermId],
) -> TermId {
    let subst: HashMap<String, TermId> = actual_var_names
        .iter()
        .zip(binding.iter())
        .map(|(name, &t)| (name.clone(), t))
        .collect();
    subst_vars(terms, body, &subst)
}
