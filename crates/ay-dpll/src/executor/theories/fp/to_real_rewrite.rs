// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! FP-to-Real term rewriting: replace `fp.to_real(arg)` with variables or values.
//!
//! Extracted from `to_real.rs` for code health. Contains the two recursive
//! rewrite passes (variable substitution and model-value substitution) plus
//! the shared `rebuild_rewritten_app` helper.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};
use ay_fp::FpModel;

/// Rebuild an application term using sort-aware TermStore constructors.
///
/// When rewriting changes a function's arguments, we must rebuild through
/// the typed constructors (mk_eq, mk_lt, etc.) rather than raw mk_app
/// so that the TermStore's sort tracking stays correct.
pub(super) fn rebuild_rewritten_app(
    terms: &mut TermStore,
    sym: ay_core::term::Symbol,
    args: Vec<TermId>,
    sort: Sort,
) -> TermId {
    match sym.name() {
        "=" if args.len() == 2 => terms.mk_eq_coerce(args[0], args[1]),
        "<" if args.len() == 2 => terms.mk_lt(args[0], args[1]),
        "<=" if args.len() == 2 => terms.mk_le(args[0], args[1]),
        ">" if args.len() == 2 => terms.mk_gt(args[0], args[1]),
        ">=" if args.len() == 2 => terms.mk_ge(args[0], args[1]),
        "+" => terms.mk_add(args),
        "-" => terms.mk_sub(args),
        "*" => terms.mk_mul(args),
        "/" if args.len() == 2 => terms.mk_div(args[0], args[1]),
        "and" => terms.mk_and(args),
        "or" => terms.mk_or(args),
        "=>" if args.len() == 2 => terms.mk_implies(args[0], args[1]),
        "xor" if args.len() == 2 => terms.mk_xor(args[0], args[1]),
        _ => terms.mk_app(sym, args, sort),
    }
}

/// Rewrite a term, replacing `fp.to_real(arg)` with a free Real variable.
///
/// Used by the Real-guided pre-solve to solve the Real constraints independently
/// of the FP model. Each `fp.to_real(arg)` is replaced with the corresponding
/// fresh Real variable from `fp_arg_to_var`.
pub(super) fn rewrite_fp_to_real_with_vars(
    terms: &mut TermStore,
    term: TermId,
    fp_arg_to_var: &HashMap<TermId, TermId>,
    cache: &mut HashMap<TermId, TermId>,
) -> TermId {
    if let Some(&cached) = cache.get(&term) {
        return cached;
    }

    let result = match terms.get(term).clone() {
        TermData::App(sym, args) if sym.name() == "fp.to_real" && args.len() == 1 => {
            let fp_arg = args[0];
            if let Some(&var) = fp_arg_to_var.get(&fp_arg) {
                var
            } else {
                term
            }
        }
        TermData::App(sym, args) => {
            let new_args: Vec<TermId> = args
                .iter()
                .map(|&a| rewrite_fp_to_real_with_vars(terms, a, fp_arg_to_var, cache))
                .collect();
            if new_args == args {
                term
            } else {
                let sort = terms.sort(term).clone();
                rebuild_rewritten_app(terms, sym, new_args, sort)
            }
        }
        TermData::Not(inner) => {
            let new_inner = rewrite_fp_to_real_with_vars(terms, inner, fp_arg_to_var, cache);
            if new_inner == inner {
                term
            } else {
                terms.mk_not(new_inner)
            }
        }
        TermData::Ite(c, t, e) => {
            let nc = rewrite_fp_to_real_with_vars(terms, c, fp_arg_to_var, cache);
            let nt = rewrite_fp_to_real_with_vars(terms, t, fp_arg_to_var, cache);
            let ne = rewrite_fp_to_real_with_vars(terms, e, fp_arg_to_var, cache);
            if nc == c && nt == t && ne == e {
                term
            } else {
                terms.mk_ite(nc, nt, ne)
            }
        }
        TermData::Let(bindings, body) => {
            let new_bindings: Vec<(String, TermId)> = bindings
                .iter()
                .map(|(name, val)| {
                    let new_val = rewrite_fp_to_real_with_vars(terms, *val, fp_arg_to_var, cache);
                    (name.clone(), new_val)
                })
                .collect();
            let new_body = rewrite_fp_to_real_with_vars(terms, body, fp_arg_to_var, cache);
            if new_bindings
                .iter()
                .zip(bindings.iter())
                .all(|((_, nv), (_, ov))| *nv == *ov)
                && new_body == body
            {
                term
            } else {
                terms.mk_let(new_bindings, new_body)
            }
        }
        _ => term,
    };

    cache.insert(term, result);
    result
}

/// Rewrite a term, replacing `fp.to_real(arg)` applications with concrete values.
///
/// For finite FP model values, replaces with the exact rational.
/// For NaN/infinity, replaces with a stable UF application on the FP operand,
/// ensuring congruence: equal FP inputs produce equal Real outputs.
///
/// A rounding-mode constant the FP circuit decided (it has bits, so the FP
/// model carries its decoded mode in `rm_values`) is replaced by that mode's
/// literal. The FP values substituted above were computed UNDER that mode, so
/// the mixed subproblem must not choose the mode again: left symbolic, the
/// child solve re-decided it from the domain axioms alone (`r = RNE`) while
/// `x` held the value `to_fp` gives under the circuit's mode (`RTZ`), and the
/// merged model printed a mode that falsifies the formula.
pub(super) fn rewrite_fp_to_real_for_model(
    terms: &mut TermStore,
    term: TermId,
    fp_model: &FpModel,
    cache: &mut HashMap<TermId, TermId>,
    undef_vars: &mut HashMap<String, TermId>,
) -> TermId {
    if let Some(&cached) = cache.get(&term) {
        return cached;
    }

    let result = match terms.get(term).clone() {
        TermData::App(sym, args) if sym.name() == "fp.to_real" && args.len() == 1 => {
            let fp_arg = args[0];
            if let Some(fp_val) = fp_model.values.get(&fp_arg) {
                if let Some(rational) = fp_val.to_rational() {
                    // Finite value: replace with exact rational constant
                    terms.mk_rational(rational)
                } else {
                    // NaN or infinity: use a fresh Real variable keyed on the
                    // FP value's SMT-LIB representation. This ensures:
                    // - fp.to_real(x) maps to the same variable across occurrences
                    // - congruence: if x == y in the model (same FP value), they
                    //   produce the same fresh variable via identical smtlib key
                    // - the mixed subproblem stays FP-free (no FP-sorted args)
                    let key = fp_val.to_smtlib();
                    *undef_vars.entry(key.clone()).or_insert_with(|| {
                        // Use __fp_undef_ prefix (NOT __ay_) to avoid model
                        // validation's internal-symbol skip heuristic (#6241).
                        let name = format!("__fp_undef_{}", key.replace(' ', "_"));
                        terms.mk_var(&name, Sort::Real)
                    })
                }
            } else {
                // FP arg not in model — leave as-is
                term
            }
        }
        TermData::Var(..) => match fp_model.rm_values.get(&term) {
            Some(&mode) => crate::executor::rm_domain::rm_literal_term(terms, mode),
            None => term,
        },
        TermData::App(sym, args) => {
            let new_args: Vec<TermId> = args
                .iter()
                .map(|&a| rewrite_fp_to_real_for_model(terms, a, fp_model, cache, undef_vars))
                .collect();
            if new_args == args {
                term
            } else {
                let sort = terms.sort(term).clone();
                rebuild_rewritten_app(terms, sym, new_args, sort)
            }
        }
        TermData::Not(inner) => {
            let new_inner = rewrite_fp_to_real_for_model(terms, inner, fp_model, cache, undef_vars);
            if new_inner == inner {
                term
            } else {
                terms.mk_not(new_inner)
            }
        }
        TermData::Ite(c, t, e) => {
            let nc = rewrite_fp_to_real_for_model(terms, c, fp_model, cache, undef_vars);
            let nt = rewrite_fp_to_real_for_model(terms, t, fp_model, cache, undef_vars);
            let ne = rewrite_fp_to_real_for_model(terms, e, fp_model, cache, undef_vars);
            if nc == c && nt == t && ne == e {
                term
            } else {
                terms.mk_ite(nc, nt, ne)
            }
        }
        TermData::Let(bindings, body) => {
            let new_bindings: Vec<(String, TermId)> = bindings
                .iter()
                .map(|(name, val)| {
                    let new_val =
                        rewrite_fp_to_real_for_model(terms, *val, fp_model, cache, undef_vars);
                    (name.clone(), new_val)
                })
                .collect();
            let new_body = rewrite_fp_to_real_for_model(terms, body, fp_model, cache, undef_vars);
            if new_bindings
                .iter()
                .zip(bindings.iter())
                .all(|((_, nv), (_, ov))| *nv == *ov)
                && new_body == body
            {
                term
            } else {
                terms.mk_let(new_bindings, new_body)
            }
        }
        _ => term,
    };

    cache.insert(term, result);
    result
}

/// The decided rounding modes the mixed subproblem's verdict can depend on,
/// appended (once each, in first-visit order) from one assertion that
/// [`rewrite_fp_to_real_for_model`] is about to rewrite.
///
/// The rewrite replaces every decided mode with its literal, so an UNSAT child
/// may be UNSAT under those modes rather than under the site values. A
/// blocking clause over the site bits alone would then exclude assignments
/// that differ only in a mode, and an exact block could refute a satisfiable
/// formula; the refinement loop adds these modes' bits to its block unless
/// the child stays UNSAT with them free (`modes_the_refutation_needs`).
///
/// An assertion built only from Boolean connectives and mode (in)equalities,
/// with no Boolean variable — the domain axioms of `rm_domain`, or
/// `(distinct r1 RTN)` — contributes nothing: it has no `fp.to_real`, so the FP
/// circuit bit-blasted it and its modes satisfy it, and with its modes replaced
/// it is a closed true formula. Blocking therefore stays exactly as strong as
/// before on every formula whose modes the Real side never reads. Modes inside
/// an `fp.to_real` operand are covered by the site's own bits.
pub(super) fn collect_child_mode_dependencies(
    terms: &TermStore,
    assertion: TermId,
    fp_model: &FpModel,
    out: &mut Vec<TermId>,
) {
    if fp_model.rm_values.is_empty() || is_closed_mode_formula(terms, assertion) {
        return;
    }
    let mut visited = ay_core::kani_compat::DetHashSet::default();
    let mut stack = vec![assertion];
    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::Var(..) => {
                if fp_model.rm_values.contains_key(&term) && !out.contains(&term) {
                    out.push(term);
                }
            }
            TermData::App(sym, _) if sym.name() == "fp.to_real" => {}
            TermData::App(_, args) => stack.extend(args.iter().rev()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => stack.extend([*e, *t, *c]),
            TermData::Let(bindings, body) => {
                stack.push(*body);
                stack.extend(bindings.iter().rev().map(|(_, value)| *value));
            }
            _ => {}
        }
    }
}

/// Whether `root` is built only from Boolean constants and connectives, `ite`,
/// and `=`/`distinct` over rounding-mode terms: once its mode constants are
/// literals it has no free symbol left.
fn is_closed_mode_formula(terms: &TermStore, root: TermId) -> bool {
    use crate::executor::rm_domain::{is_rm_literal, is_rm_sort};
    let mut visited = ay_core::kani_compat::DetHashSet::default();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::Const(ay_core::term::Constant::Bool(_)) => {}
            TermData::Var(..) if is_rm_sort(terms.sort(term)) => {}
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => stack.extend([*c, *t, *e]),
            TermData::App(..) if is_rm_literal(terms, term) => {}
            TermData::App(sym, args) => match sym.name() {
                "and" | "or" | "=>" | "xor" | "not" | "ite" | "=" | "distinct" => {
                    stack.extend_from_slice(args);
                }
                _ => return false,
            },
            _ => return false,
        }
    }
    true
}
